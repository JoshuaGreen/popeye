#if !defined(SOLVING_SOLVE_H)
#define SOLVING_SOLVE_H

/* Interface for dynamically dispatching solve operations to slices depending
 * on their type
 */

#include "stipulation/stipulation.h"
#include "solving/machinery/dispatch.h"
#include "debugging/trace.h"

extern stip_length_type solve_nr_remaining;

stip_length_type solve_result_min(void);
stip_length_type solve_result_max(void);
void set_solve_result(stip_length_type r);
void set_solve_result_range(stip_length_type min_result, stip_length_type max_result);
void set_solve_result_min(stip_length_type min_result);
void set_solve_result_max(stip_length_type max_result);
void increment_solve_result(void);
void decrement_solve_result(void);

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
#if defined(DOTRACE)
#define solve(si) \
  TraceValue("%u",solve_nr_remaining), TraceEOL(), \
  dispatch(si), \
  TraceValue("%u",solve_nr_remaining), TraceValue("%u",solve_result), TraceEOL()
#else
#define solve(si) dispatch(si)
#endif

/* Detect whether solve_result indicates that solving has succeeded
 * @return true iff solving has succeeded
 */
boolean move_has_solved(void);

#define MOVE_HAS_SOLVED_LENGTH() solve_nr_remaining
#define MOVE_HAS_NOT_SOLVED_LENGTH() (solve_nr_remaining+2)

#endif
