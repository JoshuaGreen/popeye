#include "conditions/beamten.h"
#include "solving/move_generator.h"
#include "solving/observation.h"
#include "stipulation/stipulation.h"
#include "debugging/trace.h"
#include "pydata.h"

static boolean is_observed(square sq_departure)
{
  boolean result;

  TraceFunctionEntry(__func__);
  TraceSquare(sq_departure);
  TraceFunctionParamListEnd();

  siblingply(advers(trait[nbply]));
  current_move[nbply] = current_move[nbply-1]+1;
  move_generation_stack[current_move[nbply]].capture = sq_departure;
  result = is_square_observed(&validate_observer);
  finply();

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Validate an observation according to Beamten Chess
 * @return true iff the observation is valid
 */
boolean beamten_validate_observation(slice_index si)
{
  square const sq_observer = move_generation_stack[current_move[nbply]].departure;
  boolean result;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (TSTFLAG(spec[sq_observer],Beamtet) && !is_observed(sq_observer))
    result = false;
  else
    result = validate_observation_recursive(slices[si].next1);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Generate moves for a single piece
 * @param identifies generator slice
 * @param sq_departure departure square of generated moves
 * @param p walk to be used for generating
 */
void beamten_generate_moves_for_piece(slice_index si,
                                      square sq_departure,
                                      PieNam p)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceSquare(sq_departure);
  TracePiece(p);
  TraceFunctionParamListEnd();

  if (!TSTFLAG(spec[sq_departure],Beamtet) || is_observed(sq_departure))
    generate_moves_for_piece(slices[si].next1,sq_departure,p);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Inialise the solving machinery with Beamten Chess
 * @param si identifies root slice of solving machinery
 */
void beamten_initialise_solving(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  solving_instrument_move_generation(si,nr_sides,STBeamtenMovesForPieceGenerator);

  stip_instrument_observation_validation(si,nr_sides,STValidatingObservationBeamten);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
