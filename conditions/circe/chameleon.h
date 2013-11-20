#if !defined(CONDITIONS_CIRCE_CHAMELEON_H)
#define CONDITIONS_CIRCE_CHAMELEON_H

/* This module implements Chameleon Circe */

#include "pieces/pieces.h"
#include "solving/solve.h"

/* Reset the mapping from captured to reborn walks
 */
void chameleon_circe_reset_reborn_walks(void);

/* Initialise one mapping captured->reborn from an explicit indication
 * @param captured captured walk
 * @param reborn type of reborn walk if a piece with walk captured is captured
 */
void chameleon_circe_set_reborn_walk_explicit(PieNam from, PieNam to);

/* Initialise the reborn pieces if they haven't been already initialised
 * from explicit indications
 */
void chameleon_circe_init_implicit(void);

/* What kind of piece is to be reborn if a certain piece is captured?
 * @param captured kind of captured piece
 * @return kind of piece to be reborn
 */
PieNam chameleon_circe_get_reborn_walk(PieNam captured);

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
stip_length_type chameleon_circe_adapt_reborn_walk_solve(slice_index si,
                                                         stip_length_type n);

/* Override the Circe instrumentation of the solving machinery with
 * Chameleon Circe
 * @param si identifies root slice of stipulation
 */
void chameleon_circe_initialise_solving(slice_index si);

#endif
