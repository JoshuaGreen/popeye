#if !defined(OUTPUT_LATEX_TWINNING_H)
#define OUTPUT_LATEX_TWINNING_H

#include "stipulation/stipulation.h"

#include <stdio.h>

void LaTeXWriteOptions(void);

void LaTeXFlushTwinning(FILE *file);

/* Allocate a STOutputLaTeXTwinningWriter slice.
 * @return index of allocated slice
 */
slice_index alloc_output_latex_twinning_writer(FILE *file);

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
void output_latex_write_twinning(slice_index si);

#endif
