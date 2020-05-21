#include "options/stoponshortsolutions/filter.h"
#include "stipulation/stipulation.h"
#include "options/stoponshortsolutions/stoponshortsolutions.h"
#include "stipulation/branch.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

#include "debugging/assert.h"

/* Allocate a STStopOnShortSolutionsFilter slice.
 * @param length full length
 * @param length minimum length
 * @return allocated slice
 */
slice_index alloc_stoponshortsolutions_filter(stip_length_type length,
                                              stip_length_type min_length)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_branch(STStopOnShortSolutionsFilter,length,min_length);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
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
void stoponshortsolutions_solve(slice_index si)
{
  slice_index const initialiser = SLICE_NEXT2(si);

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (has_short_solution_been_found_in_phase(initialiser))
    set_solve_result(MOVE_HAS_NOT_SOLVED_LENGTH());
  else
  {
    pipe_solve_delegate(si);
    if (solve_result_max()<=MOVE_HAS_SOLVED_LENGTH()
        && solve_nr_remaining<SLICE_U(si).branch.length)
      short_solution_found(initialiser);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
