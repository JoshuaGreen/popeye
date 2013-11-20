#if !defined(CONDITIONS_CIRCE_DOUBLE_AGENTS_H)
#define CONDITIONS_CIRCE_DOUBLE_AGENTS_H

/* This module implements Double Agents Circe */

#include "solving/solve.h"

/* Try to solve in n half-moves.
 * @param si slice index
 * @param n maximum number of half moves
 * @return length of solution found and written, i.e.:
 *            previous_move_is_illegal the move just played is illegal
 *            this_move_is_illegal     the move being played is illegal
 *            immobility_on_next_move  the moves just played led to an
 *                                     unintended immobility on the next move
 *            <=n+1 length of shortest solution found (n+1 only if in next
 *                                     branch)
 *            n+2 no solution found in this branch
 *            n+3 no solution found in next branch
 */
stip_length_type circe_doubleagents_adapt_reborn_piece_solve(slice_index si,
                                                             stip_length_type n);

/* Override the Circe instrumentation of the solving machinery with Double Agens
 * @param si identifies root slice of stipulation
 */
void circe_double_agents_initialise_solving(slice_index si);

#endif
