#if !defined(SOLVING_OBSERVATION_H)
#define SOLVING_OBSERVATION_H

#include "stipulation/stipulation.h"
#include "pieces/walks/vectors.h"
#include "solving/ply.h"

/* This module provides supports observation as used by many conditions and
 * piece attributes. This includes
 * - 1st degree: the observation
 *   * check (observation of the enemy king)
 *   * Madrasi paralysis
 *   * Patrol Chess observation
 *   * ...
 * - 2nd degree: the observer's observer
 *   * Madrasi paralysis of a Patrol chess observer
 *   * ...
 * - 3rd degree: the observation geometry
 *   * observation in Monochrome Chess and the like
 *   * ...
 */

typedef struct
{
    vec_index_type vector_index1;
    vec_index_type vector_index2;
    int auxiliary;
} interceptable_observation_type;
extern interceptable_observation_type interceptable_observation[maxply+1];
extern unsigned int observation_context;

/* Continue validating an observation (or observer or observation geometry)
 * @param si identifies the slice with which to continue
 * @return rue iff the observation is valid
 */
boolean validate_observation_recursive(slice_index si);

/* Validate an observation
 * @return true iff the observation is valid
 */
boolean validate_observation_geometry(void);

/* Instrument observation geometry validation with a slice type
 * @param identifies where to start instrumentation
 * @param side for which side (pass nr_sides to indicate both sides)
 * @param type type of slice with which to instrument moves
 */
void stip_instrument_observation_geometry_validation(slice_index si,
                                                     Side side,
                                                     slice_type type);

/* Validate an observer
 * @return true iff the observation is valid
 */
boolean validate_observer(void);


/* Instrument observer validation with a slice type
 * @param identifies where to start instrumentation
 * @param side for which side (pass nr_sides to indicate both sides)
 * @param type type of slice with which to instrument moves
 */
void stip_instrument_observer_validation(slice_index si,
                                         Side side,
                                         slice_type type);

/* Validate an observation
 * @return true iff the observation is valid
 */
boolean validate_observation(void);

/* Instrumenvalidationvation validation with a slice type
 * @param identifies where to start instrumentation
 * @param side for which side (pass nr_sides to indicate both sides)
 * @param type type of slice with which to instrument moves
 */
void stip_instrument_observation_validation(slice_index si,
                                            Side side,
                                            slice_type type);

/* Validate a check
 * @param sq_observer position of the observer
 * @param sq_landing landing square of the observer (normally==sq_observee)
 * @return true iff the observation is valid
 */
boolean validate_check(void);

/* Instrument observation validation with a slice type
 * @param identifies where to start instrumentation
 * @param side for which side (pass nr_sides to indicate both sides)
 * @param type type of slice with which to instrument moves
 */
void stip_instrument_check_validation(slice_index si,
                                      Side side,
                                      slice_type type);

/* Cause observations to be validated by playing the move representing the
 * observation.
 * @param si root slice of solving machinery
 * @param side for which side (pass nr_sides to indicate both sides)
 */
void observation_play_move_to_validate(slice_index si, Side side);

/* version with function pointers
typedef boolean (*validator_id)(void);
#define EVALUATE(key) (&validate_##key)
#define INVOKE_EVALUATE(validator) ((*validator)())
*/

/* version with slice indices */
#include "stipulation/temporary_hacks.h"
typedef slice_index validator_id;
#define EVALUATE(key) (temporary_hack_##key##_validator[trait[nbply]])
#define INVOKE_EVALUATE(validator) (validate_observation_recursive(slices[validator].next2))

#define EVALUATE_OBSERVATION(evaluate,sq_departure,sq_arrival) \
  ( move_generation_stack[CURRMOVE_OF_PLY(nbply)].departure = (sq_departure), \
    move_generation_stack[CURRMOVE_OF_PLY(nbply)].arrival = (sq_arrival), \
    INVOKE_EVALUATE(evaluate) \
  )

/* Determine whether a square is observed be the side at the move; recursive
 * implementation over various slices
 * @param si identifies next slice
 * @return true iff sq_target is observed by the side at the move
 */
boolean is_square_observed_recursive(slice_index si,
                                     validator_id evaluate);

/* Determine whether a square is observed be the side at the move
 * @return true iff sq_target is observed by the side at the move
 */
boolean is_square_observed(validator_id evaluate);

/* Instrument a particular square observation validation branch with a slice type
 * @param testing identifies STTestingIfSquareIsObserved at entrance of branch
 * @param type type of slice to insert
 */
void is_square_observed_insert_slice(slice_index testing,
                                     slice_type type);

/* Instrument square observation validation with a slice type
 * @param identifies where to start instrumentation
 * @param side for which side (pass nr_sides to indicate both sides)
 * @param type type of slice with which to instrument moves
 */
void stip_instrument_is_square_observed_testing(slice_index si,
                                                Side side,
                                                slice_type type);

#endif
