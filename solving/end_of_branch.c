#include "solving/end_of_branch.h"
#include "solving/has_solution_type.h"
#include "solving/conditional_pipe.h"
#include "solving/pipe.h"
#include "debugging/trace.h"
#include "debugging/assert.h"

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
void end_of_branch_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  assert(solve_nr_remaining>=previous_move_has_solved);

  boolean found_matching_case = false;
  conditional_pipe_solve_return_type const result = conditional_pipe_solve_delegate(si);
  if ((result.result_min<=previous_move_has_not_solved && result.result_max>=previous_move_has_not_solved) ||
      (result.result_min<=immobility_on_next_move && result.result_max>=immobility_on_next_move))
  {
    found_matching_case = true;
    pipe_solve_delegate(si);
  }
  if (result.result_min<=previous_move_has_solved && result.result_max>=previous_move_has_solved)
  {
    if (found_matching_case)
      add_solve_result_possibility(previous_move_has_solved);
    else
    {
      found_matching_case = true;
      set_solve_result(previous_move_has_solved);
    }
  }
  if (!found_matching_case)
  {
    assert(0);
    set_solve_result(previous_move_is_illegal);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
