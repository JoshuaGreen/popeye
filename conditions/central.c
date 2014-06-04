#include "conditions/central.h"
#include "solving/move_generator.h"
#include "solving/observation.h"
#include "debugging/trace.h"
#include "pieces/pieces.h"
#include "position/position.h"

#include "debugging/assert.h"

/* avoid stack overflow in case of cycles */
static boolean is_in_chain[maxsquare];

static boolean is_mover_supported_recursive(void)
{
  boolean result;
  Flags const mask = BIT(trait[nbply])|BIT(Royal);

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  TraceSquare(move_generation_stack[CURRMOVE_OF_PLY(nbply)].capture);
  TraceEOL();

  if (TSTFULLFLAGMASK(being_solved.spec[move_generation_stack[CURRMOVE_OF_PLY(nbply)].capture],mask))
    result = true;
  else
    result = is_square_observed(EVALUATE(observation));

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

static boolean is_mover_supported(numecoup n)
{
  square const sq_departure = move_generation_stack[n].departure;
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  if (is_in_chain[sq_departure])
    result = false;
  else
  {
    is_in_chain[sq_departure] = true;

    siblingply(trait[nbply]);
    push_observation_target(sq_departure);

    result = is_mover_supported_recursive();

    finply();

    is_in_chain[sq_departure] = false;
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Validate an observation according to Central Chess
 * @return true iff the observation is valid
 */
boolean central_validate_observation(slice_index si)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  result = (is_mover_supported(CURRMOVE_OF_PLY(nbply))
            && validate_observation_recursive(slices[si].next1));

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Generate moves for a single piece
 * @param identifies generator slice
 */
void central_generate_moves_for_piece(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (is_mover_supported(current_generation))
    generate_moves_delegate(slices[si].next1);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Inialise the solving machinery with Central Chess
 * @param si identifies root slice of solving machinery
 */
void central_initialise_solving(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  solving_instrument_move_generation(si,nr_sides,STCentralMovesForPieceGenerator);

  stip_instrument_observation_validation(si,nr_sides,STCentralObservationValidator);
  stip_instrument_check_validation(si,nr_sides,STCentralObservationValidator);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
