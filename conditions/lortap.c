#include "conditions/lortap.h"
#include "solving/move_generator.h"
#include "solving/observation.h"
#include "stipulation/pipe.h"
#include "stipulation/branch.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

static boolean is_mover_unsupported(numecoup n)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  siblingply(trait[nbply]);
  push_observation_target(move_generation_stack[n].departure);
  result = !is_square_observed(EVALUATE(observer));
  finply();

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Validate an observation according to Lortap
 * @return true iff the observation is valid
 */
boolean lortap_validate_observation(slice_index si)
{
  return (is_mover_unsupported(CURRMOVE_OF_PLY(nbply))
          && validate_observation_recursive(slices[si].next1));
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
void lortap_remove_supported_captures_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  move_generator_filter_captures(MOVEBASE_OF_PLY(nbply),&is_mover_unsupported);

  pipe_solve_delegate(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_remover(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children(si,st);

  {
    slice_index const prototype = alloc_pipe(STLortapRemoveSupportedCaptures);
    slice_insertion_insert_contextually(si,st->context,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Initialise solving in Lortap
 * @param si identifies the root slice of the stipulation
 */
void lortap_initialise_solving(slice_index si)
{
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  stip_structure_traversal_init(&st,0);
  stip_structure_traversal_override_single(&st,
                                           STDoneGeneratingMoves,
                                           &insert_remover);
  stip_traverse_structure(si,&st);

  stip_instrument_observation_validation(si,nr_sides,STLortapRemoveSupportedCaptures);
  stip_instrument_check_validation(si,nr_sides,STLortapRemoveSupportedCaptures);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
