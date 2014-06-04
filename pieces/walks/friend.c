#include "pieces/walks/friend.h"
#include "pieces/walks/orphan.h"
#include "pieces/walks/generate_moves.h"
#include "solving/move_generator.h"
#include "solving/observation.h"
#include "solving/find_square_observer_tracking_back_from_target.h"
#include "debugging/trace.h"
#include "pieces/pieces.h"

void locate_observees(piece_walk_type walk, square pos_observees[])
{
  unsigned int current = 0;
  square const *bnp;

  for (bnp = boardnum; current<being_solved.number_of_pieces[trait[nbply]][walk]; ++bnp)
    if (get_walk_of_piece_on_square(*bnp)==walk && TSTFLAG(being_solved.spec[*bnp],trait[nbply]))
    {
      pos_observees[current] = *bnp;
      ++current;
    }
}

void isolate_observee(piece_walk_type walk, square const pos_observees[], unsigned int isolated_observee)
{
  unsigned int orphan_id;

  for (orphan_id = 0; orphan_id<being_solved.number_of_pieces[trait[nbply]][walk]; ++orphan_id)
    if (orphan_id!=isolated_observee)
      occupy_square(pos_observees[orphan_id],Dummy,being_solved.spec[pos_observees[orphan_id]]);
}

void restore_observees(piece_walk_type walk, square const pos_observees[])
{
  unsigned int orphan_id;

  for (orphan_id = 0; orphan_id<being_solved.number_of_pieces[trait[nbply]][walk]; ++orphan_id)
    occupy_square(pos_observees[orphan_id],walk,being_solved.spec[pos_observees[orphan_id]]);
}

static boolean find_next_friend_in_chain(square sq_target,
                                         piece_walk_type friend_observer)
{
  boolean result = false;

  replace_observation_target(sq_target);
  observing_walk[nbply] = friend_observer;
  if ((*checkfunctions[friend_observer])(EVALUATE(observer)))
    result = true;
  else
  {
    --being_solved.number_of_pieces[trait[nbply]][Friend];

    if (being_solved.number_of_pieces[trait[nbply]][Friend]>0)
    {
      unsigned int k;
      square pos_remaining_friends[63];

      occupy_square(sq_target,Dummy,being_solved.spec[sq_target]);
      locate_observees(Friend,pos_remaining_friends);

      for (k = 0; k<being_solved.number_of_pieces[trait[nbply]][Friend]; k++)
      {
        boolean is_friend_observed;

        isolate_observee(Friend,pos_remaining_friends,k);
        move_generation_stack[CURRMOVE_OF_PLY(nbply)].capture = sq_target;
        observing_walk[nbply] = Friend;
        is_friend_observed = (*checkfunctions[friend_observer])(EVALUATE(observer));
        restore_observees(Friend,pos_remaining_friends);

        if (is_friend_observed
            && find_next_friend_in_chain(pos_remaining_friends[k],friend_observer))
        {
          result = true;
          break;
        }
      }

      occupy_square(sq_target,Friend,being_solved.spec[sq_target]);
    }

    ++being_solved.number_of_pieces[trait[nbply]][Friend];
  }

  return result;
}

/* Generate moves for a Friend
 */
void friend_generate_moves(void)
{
  numecoup const save_nbcou = CURRMOVE_OF_PLY(nbply);
  Side const camp = trait[nbply];

  piece_walk_type const *friend_observer;
  for (friend_observer = orphanpieces; *friend_observer!=Empty; ++friend_observer)
    if (being_solved.number_of_pieces[camp][*friend_observer]>0)
    {
      boolean found_chain;

      siblingply(trait[nbply]);
      push_observation_target(initsquare);
      found_chain = find_next_friend_in_chain(curr_generation->departure,
                                              *friend_observer);
      finply();

      if (found_chain)
      {
        move_generation_current_walk = *friend_observer;
        generate_moves_for_piece_based_on_walk();
      }
    }

  move_generation_current_walk = Friend;

  remove_duplicate_moves_of_single_piece(save_nbcou);
}

boolean friend_check(validator_id evaluate)
{
  square const sq_target = move_generation_stack[CURRMOVE_OF_PLY(nbply)].capture;
  piece_walk_type const *pfr;
  boolean result = false;
  square pos_friends[63];

  TraceFunctionEntry(__func__);
  TraceSquare(sq_target);
  TraceFunctionParamListEnd();

  locate_observees(Friend,pos_friends);

  siblingply(trait[nbply]);
  push_observation_target(sq_target);

  for (pfr = orphanpieces; *pfr!=Empty; pfr++)
    if (being_solved.number_of_pieces[trait[nbply]][*pfr]>0)
    {
      unsigned int k;
      for (k = 0; k<being_solved.number_of_pieces[trait[nbply]][Friend]; ++k)
      {
        boolean does_friend_observe;

        isolate_observee(Friend,pos_friends,k);
        observing_walk[nbply] = Friend;
        does_friend_observe = (*checkfunctions[*pfr])(evaluate);
        restore_observees(Friend,pos_friends);

        if (does_friend_observe
            && find_next_friend_in_chain(pos_friends[k],*pfr))
        {
          result = true;
          break;
        }
      }

      if (result)
        break;
    }

  finply();

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}
