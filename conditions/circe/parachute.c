#include "conditions/circe/parachute.h"
#include "position/position.h"
#include "conditions/circe/circe.h"
#include "conditions/circe/rebirth_avoider.h"
#include "conditions/haunted_chess.h"
#include "solving/observation.h"
#include "solving/check.h"
#include "solving/move_generator.h"
#include "stipulation/stipulation.h"
#include "solving/has_solution_type.h"
#include "stipulation/structure_traversal.h"
#include "stipulation/pipe.h"
#include "stipulation/fork.h"
#include "stipulation/move.h"

#include "solving/pipe.h"
#include "debugging/trace.h"
#include "debugging/assert.h"

#include <string.h>

static void move_effect_journal_do_circe_parachute_remember(move_effect_reason_type reason,
                                                            square sq_rebirth)
{
  move_effect_journal_entry_type * const entry = move_effect_journal_allocate_entry(move_effect_remember_parachuted,reason);

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",reason);
  TraceSquare(sq_rebirth);
  TraceFunctionParamListEnd();

  entry->u.handle_ghost.ghost.on = sq_rebirth;
  entry->u.handle_ghost.ghost.walk = get_walk_of_piece_on_square(sq_rebirth);
  entry->u.handle_ghost.ghost.flags = being_solved.spec[sq_rebirth];

  underworld_make_space(0);

  underworld[0] = entry->u.handle_ghost.ghost;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void move_effect_journal_undo_circe_parachute_remember(move_effect_journal_entry_type const *entry)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  underworld_lose_space(0);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void move_effect_journal_redo_circe_parachute_remember(move_effect_journal_entry_type const *entry)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  underworld_make_space(0);

  underworld[0] = entry->u.handle_ghost.ghost;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void move_effect_journal_do_circe_volcanic_remember(move_effect_reason_type reason,
                                                    square sq_rebirth)
{
  move_effect_journal_entry_type * const entry = move_effect_journal_allocate_entry(move_effect_remember_volcanic,reason);

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",reason);
  TraceFunctionParamListEnd();

  entry->u.handle_ghost.ghost.on = sq_rebirth;
  entry->u.handle_ghost.ghost.walk = get_walk_of_piece_on_square(sq_rebirth);
  entry->u.handle_ghost.ghost.flags = being_solved.spec[sq_rebirth];

  TraceSquare(entry->u.handle_ghost.ghost.on);
  TraceWalk(entry->u.handle_ghost.ghost.walk);
  TraceValue("%u\n",GetPieceId(entry->u.handle_ghost.ghost.flags));

  underworld_make_space(nr_ghosts);

  underworld[nr_ghosts-1] = entry->u.handle_ghost.ghost;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void move_effect_journal_undo_circe_volcanic_remember(move_effect_journal_entry_type const *entry)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  underworld_lose_space(nr_ghosts-1);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

void move_effect_journal_redo_circe_volcanic_remember(move_effect_journal_entry_type const *entry)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  underworld_make_space(nr_ghosts);

  underworld[nr_ghosts-1] = entry->u.handle_ghost.ghost;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
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
void circe_parachute_remember_solve(slice_index si)
{
  circe_rebirth_context_elmt_type const * const context = &circe_rebirth_context_stack[circe_rebirth_context_stack_pointer];
  square const sq_rebirth = context->rebirth_square;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  move_effect_journal_do_circe_parachute_remember(move_effect_reason_assassin_circe_rebirth,
                                                  sq_rebirth);
  move_effect_journal_do_piece_removal(move_effect_reason_assassin_circe_rebirth,
                                       sq_rebirth);
  pipe_dispatch_delegate(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static boolean volcanic_rebirth[maxply+1];

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
void circe_volcanic_remember_solve(slice_index si)
{
  circe_rebirth_context_elmt_type const * const context = &circe_rebirth_context_stack[circe_rebirth_context_stack_pointer];
  square const sq_rebirth = context->rebirth_square;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  move_effect_journal_do_circe_volcanic_remember(move_effect_reason_volcanic_remember,
                                                 sq_rebirth);
  move_effect_journal_do_piece_removal(move_effect_reason_assassin_circe_rebirth,
                                       sq_rebirth);
  volcanic_rebirth[nbply] = true;
  pipe_dispatch_delegate(si);

  volcanic_rebirth[nbply] = false;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
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
void circe_volcanic_swapper_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (volcanic_rebirth[nbply])
  {
    piece_type const tmp = underworld[nr_ghosts-1];
    circe_rebirth_context_elmt_type const * const context = &circe_rebirth_context_stack[circe_rebirth_context_stack_pointer];

    underworld[nr_ghosts-1].walk = get_walk_of_piece_on_square(tmp.on);
    underworld[nr_ghosts-1].flags = being_solved.spec[tmp.on];

    move_effect_journal_do_piece_removal(move_effect_reason_volcanic_remember,tmp.on);
    move_effect_journal_do_piece_readdition(move_effect_reason_volcanic_remember,
                                            tmp.on,
                                            tmp.walk,
                                            tmp.flags,
                                            context->rebirth_as);
  }

  pipe_dispatch_delegate(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
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
void circe_parachute_uncoverer_solve(slice_index si)
{
  unsigned int i = 0;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  while (i<nr_ghosts)
  {
    square const from = underworld[i].on;

    if (is_square_empty(from))
    {
      circe_rebirth_context_elmt_type const * const context = &circe_rebirth_context_stack[circe_rebirth_context_stack_pointer];
      move_effect_journal_do_piece_readdition(move_effect_reason_volcanic_uncover,
                                              from,
                                              underworld[i].walk,
                                              underworld[i].flags,
                                              context->rebirth_as);
      move_effect_journal_do_forget_ghost(i);
    }
    else
      ++i;
  }

  pipe_dispatch_delegate(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Initialise the solving machinery with Circe Parachute
 * @param si identifies root slice of stipulation
 * @param interval_start start of the slices interval to be initialised
 */
void circe_parachute_initialise_solving(slice_index si,
                                        slice_type interval_start)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceEnumerator(slice_type,interval_start,"");
  TraceFunctionParamListEnd();

  circe_insert_rebirth_avoider(si,
                               interval_start,
                               STCirceDeterminedRebirth,
                               alloc_fork_slice(STCirceTestRebirthSquareEmpty,no_slice),
                               STCirceRebirthOnNonEmptySquare,
                               STCircePlacingReborn);

  circe_instrument_solving(si,
                           interval_start,
                           STCirceRebirthOnNonEmptySquare,
                           alloc_pipe(STCirceParachuteRemember));

  stip_instrument_moves(si,STCirceParachuteUncoverer);

  check_no_king_is_possible();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Initialise the solving machinery with Circe Volcanic
 * @param si identifies root slice of stipulation
 * @param interval_start start of the slices interval to be initialised
 */
void circe_volcanic_initialise_solving(slice_index si,
                                       slice_type interval_start)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceEnumerator(slice_type,interval_start,"");
  TraceFunctionParamListEnd();

  circe_insert_rebirth_avoider(si,
                               interval_start,
                               STCirceDeterminedRebirth,
                               alloc_fork_slice(STCirceTestRebirthSquareEmpty,no_slice),
                               STCirceRebirthOnNonEmptySquare,
                               STCircePlacingReborn);

  circe_instrument_solving(si,
                           interval_start,
                           STCirceRebirthOnNonEmptySquare,
                           alloc_pipe(STCirceVolcanicRemember));

  circe_instrument_solving(si,
                           interval_start,
                           STCirceDeterminedRebirth,
                           alloc_pipe(STCirceVolcanicSwapper));

  stip_instrument_moves(si,STCirceParachuteUncoverer);

  check_no_king_is_possible();

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
