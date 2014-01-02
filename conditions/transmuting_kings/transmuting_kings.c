#include "conditions/transmuting_kings/transmuting_kings.h"
#include "solving/move_generator.h"
#include "solving/observation.h"
#include "solving/find_square_observer_tracking_back_from_target.h"
#include "stipulation/stipulation.h"
#include "stipulation/proxy.h"
#include "stipulation/branch.h"
#include "stipulation/fork.h"
#include "debugging/trace.h"
#include "pieces/pieces.h"

#include <assert.h>

PieNam transmuting_kings_potential_transmutations[nr_sides][PieceCount];

boolean transmuting_kings_testing_transmutation[nr_sides];

static boolean testing_with_non_transmuting_king[maxply+1];

static enum
{
  dont_know,
  does_transmute,
  does_not_transmute
} is_king_transmuting_as_observing_walk[maxply+1];

static boolean is_king_transmuting_as_any_walk[maxply+1];

/* Initialise the sequence of king transmuters
 * @param side for which side to initialise?
 */
void transmuting_kings_init_transmuters_sequence(Side side)
{
  unsigned int tp = 0;
  PieNam p;

  for (p = King; p<PieceCount; ++p) {
    if (may_exist[p] && p!=Dummy && p!=Hamster)
    {
      transmuting_kings_potential_transmutations[side][tp] = p;
      tp++;
    }
  }

  transmuting_kings_potential_transmutations[side][tp] = Empty;
}

/* Determine whether the moving side's king is transmuting as a specific walk
 * @param p the piece
 */
boolean transmuting_kings_is_king_transmuting_as(PieNam walk)
{
  boolean result;
  Side const side_attacking = trait[nbply];

  TraceFunctionEntry(__func__);
  TracePiece(walk);
  TraceFunctionParamListEnd();

  if (transmuting_kings_testing_transmutation[side_attacking])
    result = false;
  else
  {
    transmuting_kings_testing_transmutation[side_attacking] = true;

    siblingply(advers(side_attacking));
    push_observation_target(king_square[side_attacking]);
    observing_walk[nbply] = walk;
    result = is_square_observed_recursive(slices[temporary_hack_is_square_observed_specific[trait[nbply]]].next2,EVALUATE(observation));
    finply();

    transmuting_kings_testing_transmutation[side_attacking] = false;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Generate moves of a potentially transmuting king
 * @param si identifies move generator slice
 * @return true iff the king is transmuting (which doesn't necessarily mean that
 *              any moves were generated!)
 */
boolean generate_moves_of_transmuting_king(slice_index si)
{
  boolean result = false;
  Side const side_moving = trait[nbply];
  Side const side_transmuting = advers(side_moving);
  PieNam const *ptrans;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  for (ptrans = transmuting_kings_potential_transmutations[side_moving]; *ptrans!=Empty; ++ptrans)
    if (number_of_pieces[side_transmuting][*ptrans]>0
        && transmuting_kings_is_king_transmuting_as(*ptrans))
    {
      generate_moves_for_piece(slices[si].next1,*ptrans);
      result = true;
    }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Generate moves for a single piece
 * @param identifies generator slice
 * @param p walk to be used for generating
 */
void transmuting_kings_generate_moves_for_piece(slice_index si, PieNam p)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TracePiece(p);
  TraceFunctionParamListEnd();

  if (!(p==King && generate_moves_of_transmuting_king(si)))
    generate_moves_for_piece(slices[si].next1,p);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

typedef struct
{
    Side side;
    slice_index past_detector;
} instrumentation_state_type;

static void instrument_testing(slice_index si, stip_structure_traversal *st)
{
  instrumentation_state_type * const state = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (slices[si].starter==state->side)
  {
    assert(state->past_detector==no_slice);
    is_square_observed_insert_slice(si,alloc_pipe(STTransmutingKingDetectNonTransmutation));
    stip_traverse_structure_children(si,st);
    assert(state->past_detector!=no_slice);
    is_square_observed_insert_slice(si,
                                    alloc_fork_slice(STTransmutingKingIsSquareObserved,
                                                     state->past_detector));
    state->past_detector = no_slice;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void remember_detector(slice_index si, stip_structure_traversal *st)
{
  instrumentation_state_type * const state = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children(si,st);

  if (slices[si].starter==no_side /* just inserted */
      && state->past_detector==no_slice)
  {
    slices[si].starter = state->side;
    state->past_detector = alloc_proxy_slice();
    pipe_append(si,state->past_detector);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Inialise the observation machinery with transmuting kings
 * @param si identifies root slice of solving machinery
 * @param side for whom
 * @note invoked by transmuting_kings_initialise_observing()
 */
void transmuting_kings_initialise_observing(slice_index si, Side side)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceEnumerator(Side,side,"");
  TraceFunctionParamListEnd();

  {
    instrumentation_state_type state = { side, no_slice  };
    stip_structure_traversal st;

    stip_structure_traversal_init(&st,&state);
    stip_structure_traversal_override_single(&st,
                                             STTestingIfSquareIsObserved,
                                             &instrument_testing);
    stip_structure_traversal_override_single(&st,
                                             STTransmutingKingDetectNonTransmutation,
                                             &remember_detector);
    stip_traverse_structure(si,&st);
  }

  stip_instrument_observation_validation(si,side,STTransmutingKingsEnforceObserverWalk);
  stip_instrument_check_validation(si,side,STTransmutingKingsEnforceObserverWalk);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Inialise the solving machinery with transmuting kings
 * @param si identifies root slice of solving machinery
 * @param side for whom
 */
void transmuting_kings_initialise_solving(slice_index si, Side side)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceEnumerator(Side,side,"");
  TraceFunctionParamListEnd();

  solving_instrument_move_generation(si,side,STTransmutingKingsMovesForPieceGenerator);

  transmuting_kings_initialise_observing(si,side);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Determine whether a square is observed be the side at the move according to
 * Transmuting Kings
 * @param si identifies next slice
 * @return true iff sq_target is observed by the side at the move
 */
boolean transmuting_king_is_square_observed(slice_index si, validator_id evaluate)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (is_square_observed_recursive(slices[si].next1,evaluate))
    result = true;
  else
  {
    square const sq_king = king_square[trait[nbply]];
    if (sq_king==initsquare || is_king_transmuting_as_any_walk[nbply])
      result = false;
    else
    {
      testing_with_non_transmuting_king[nbply] = true;
      observing_walk[nbply] = get_walk_of_piece_on_square(sq_king);
      result = is_square_observed_recursive(slices[si].next2,evaluate);
      testing_with_non_transmuting_king[nbply] = false;
    }
  }

  is_king_transmuting_as_any_walk[nbply] = false;

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Find out if the royal piece is not transmuted (i.e. moves according to its
 * original walk)
 * @param si identifies next slice
 * @return true iff sq_target is observed by the side at the move
 */
boolean transmuting_king_detect_non_transmutation(slice_index si, validator_id evaluate)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  assert(!testing_with_non_transmuting_king[nbply]);

  is_king_transmuting_as_observing_walk[nbply] = dont_know;

  result = is_square_observed_recursive(slices[si].next1,evaluate);

  if (!result && !is_king_transmuting_as_any_walk[nbply])
    switch (is_king_transmuting_as_observing_walk[nbply])
    {
      case dont_know:
        is_king_transmuting_as_any_walk[nbply] = transmuting_kings_is_king_transmuting_as(observing_walk[nbply]);
        break;

      case does_not_transmute:
        break;

      case does_transmute:
        is_king_transmuting_as_any_walk[nbply] = true;
        break;

      default:
        assert(0);
        break;
    }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Make sure to behave correctly while detecting observations by vaulting kings
 */
boolean transmuting_kings_enforce_observer_walk(slice_index si)
{
  boolean result;
  square const sq_king = king_square[trait[nbply]];

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (transmuting_kings_testing_transmutation[advers(trait[nbply])])
    result = validate_observation_recursive(slices[si].next1);
  else if (testing_with_non_transmuting_king[nbply])
  {
    assert(observing_walk[nbply]==get_walk_of_piece_on_square(sq_king));
    if (move_generation_stack[CURRMOVE_OF_PLY(nbply)].departure==sq_king)
      result = validate_observation_recursive(slices[si].next1);
    else
      result = false;
  }
  else if (move_generation_stack[CURRMOVE_OF_PLY(nbply)].departure==sq_king)
  {
    if (transmuting_kings_is_king_transmuting_as(observing_walk[nbply]))
    {
      PieNam const save_walk = observing_walk[nbply];
      observing_walk[nbply] = get_walk_of_piece_on_square(sq_king);
      result = validate_observation_recursive(slices[si].next1);
      observing_walk[nbply] = save_walk;
      is_king_transmuting_as_observing_walk[nbply] = does_transmute;
    }
    else
    {
      result = false;
      is_king_transmuting_as_observing_walk[nbply] = does_not_transmute;
    }
  }
  else
    result = validate_observation_recursive(slices[si].next1);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}
