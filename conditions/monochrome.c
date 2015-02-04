#include "conditions/monochrome.h"
#include "stipulation/pipe.h"
#include "stipulation/slice_insertion.h"
#include "solving/observation.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

boolean monochrome_is_move_monochrome(numecoup n)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  if (move_generation_stack[n].capture==queenside_castling)
    result = false;
  else
    result = (SquareCol(move_generation_stack[n].departure)
              ==SquareCol(move_generation_stack[n].arrival));

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Validate the geometry of observation according to Monochrome Chess
 * @return true iff the observation is valid
 */
boolean monochrome_validate_observation_geometry(slice_index si)
{
  return (monochrome_is_move_monochrome(CURRMOVE_OF_PLY(nbply))
          && pipe_validate_observation_recursive(si));
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
void monochrome_remove_bichrome_moves_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  move_generator_filter_moves(MOVEBASE_OF_PLY(nbply),&monochrome_is_move_monochrome);

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
    slice_index const prototype = alloc_pipe(STMonochromeRemoveBichromeMoves);
    slice_insertion_insert_contextually(si,st->context,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Initialise solving in Monochrome Chess
 * @param si identifies the root slice of the stipulation
 */
void monochrome_initialise_solving(slice_index si)
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

  stip_instrument_observation_geometry_validation(si,
                                                  nr_sides,
                                                  STMonochromeRemoveBichromeMoves);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
