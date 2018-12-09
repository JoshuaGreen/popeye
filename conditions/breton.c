#include "conditions/breton.h"
#include "position/position.h"
#include "solving/ply.h"
#include "solving/pipe.h"
#include "solving/move_effect_journal.h"
#include "solving/post_move_iteration.h"
#include "solving/has_solution_type.enum.h"
#include "stipulation/move.h"

static square const *breton_state[maxply+1];

static boolean advance_breton_victim_position(slice_index si,
                                              move_effect_journal_index_type const capture)
{
  piece_walk_type const walk_capturee = move_effect_journal[capture].u.piece_removal.walk;
  Side const side_capturee = advers(SLICE_STARTER(si));

  boolean result = true;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  while (*breton_state[nbply]
         && !(get_walk_of_piece_on_square(*breton_state[nbply])==walk_capturee
              && TSTFLAG(being_solved.spec[*breton_state[nbply]],side_capturee)))
    ++breton_state[nbply];

  if (*breton_state[nbply]==0)
    result = false;

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Try to solve in solve_nr_remaining half-moves.
 * @param si slice index
 * @note assigns solve_result the length of solution found and written, i.e.:
 *            previous_move_is_illegal the move just played is illegal
 *            this_move_is_illegal     the move being played is illegal
 *            immobility_on_next_move  the moves just played led to an
 *                                     unintended immobility on the next move
 *            <=n+1 length of shortest solution found (n+1 only if in next
 *                                     branch)
 *            n+2 no solution found in this branch
 *            n+3 no solution found in next branch
 *            (with n denominating solve_nr_remaining)
 */
void breton_remover_solve(slice_index si)
{
  move_effect_journal_index_type const base = move_effect_journal_base[nbply];
  move_effect_journal_index_type const capture = base+move_effect_journal_index_offset_capture;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (move_effect_journal[capture].type==move_effect_piece_removal)
  {
    if (!post_move_am_i_iterating())
    {
      /* try to start a new iteration */
      breton_state[nbply] = boardnum;

      if (advance_breton_victim_position(si,capture))
      {
        /* we got a winner! */
        move_effect_journal_do_piece_removal(move_effect_reason_breton,
                                             *breton_state[nbply]);
        post_move_iteration_solve_delegate(si);
      }
      else
      {
        /* no Breton removal for this regular removal */
        pipe_solve_delegate(si);
      }
    }
    else if (post_move_have_i_lock())
    {
      /* try to advance the current iteration */
      ++breton_state[nbply];
      if (advance_breton_victim_position(si,capture))
      {
        /* we got a winner! */
        move_effect_journal_do_piece_removal(move_effect_reason_breton,
                                             *breton_state[nbply]);
        post_move_iteration_solve_delegate(si);
      }
      else
      {
        /* end the current iteration */
        solve_result = this_move_is_illegal;
        post_move_iteration_end();
      }
    }
    else
    {
      /* replay the current step of iteration - somebody else is advancing */
      move_effect_journal_do_piece_removal(move_effect_reason_breton,
                                           *breton_state[nbply]);
      post_move_iteration_solve_delegate(si);
    }
  }
  else
    pipe_solve_delegate(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Instrument slices with move tracers
 */
void solving_insert_breton(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  stip_instrument_moves(si,STBretonRemover);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
