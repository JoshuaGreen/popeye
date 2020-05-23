#include "solving/move_inverter.h"
#include "solving/machinery/solve.h"
#include "solving/has_solution_type.h"
#include "solving/pipe.h"
#include "debugging/trace.h"
#include "debugging/assert.h"
#ifdef _SE_
#include <se.h>
#endif

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
void move_inverter_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  pipe_solve_delegate(si);
  
  boolean found_match = false;
  if (solve_result_might_equal(immobility_on_next_move) ||
      solve_result_might_equal(previous_move_has_not_solved))
  {
    found_match = true;
    set_solve_result(MOVE_HAS_NOT_SOLVED_LENGTH());
  }
  if (solve_result_might_equal(previous_move_has_solved))
    if (found_match)
      add_solve_result_possibility(MOVE_HAS_SOLVED_LENGTH());
    else
    {
      found_match = true;
      set_solve_result(MOVE_HAS_SOLVED_LENGTH());
    }
  if (solve_result_might_equal(previous_move_is_illegal))
    if (found_match)
      add_solve_result_possibility(immobility_on_next_move);
    else
    {
      found_match = true;
      set_solve_result(immobility_on_next_move);
    }
  if (!found_match)
  {
    assert(0);
    set_solve_result(immobility_on_next_move);
  }

#ifdef _SE_DECORATE_SOLUTION_
  se_end_set_play();
#endif

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
