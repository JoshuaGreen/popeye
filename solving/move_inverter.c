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
  
  boolean const prev_illegal = solve_result_might_equal(previous_move_is_illegal);
  boolean const immob_next = solve_result_might_equal(immobility_on_next_move);
  boolean const prev_not_solved = solve_result_might_equal(previous_move_has_not_solved);
  boolean const prev_solved = solve_result_might_equal(previous_move_has_solved);
  
  assert(prev_illegal || immob_next || prev_not_solved || prev_solved);
  
  stip_length_type result_min;
  stip_length_type result_max;
  
  if (immob_next || prev_not_solved)
  {
    if (prev_illegal)
      result_min = immobility_on_next_move;
    else if (prev_solved)
      result_min = MOVE_HAS_SOLVED_LENGTH();
    else
      result_min = MOVE_HAS_NOT_SOLVED_LENGTH();
    result_max = MOVE_HAS_NOT_SOLVED_LENGTH();
  }
  else if (prev_solved)
  {
    if (prev_illegal)
      result_min = immobility_on_next_move;
    else
      result_min = MOVE_HAS_SOLVED_LENGTH();
    result_max = MOVE_HAS_SOLVED_LENGTH();
  }
  else
  {
    result_min = immobility_on_next_move;
    result_max = immobility_on_next_move;
  }
  
  set_solve_result_range(result_min, result_max);

#ifdef _SE_DECORATE_SOLUTION_
  se_end_set_play();
#endif

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
