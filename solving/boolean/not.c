#include "solving/boolean/not.h"
#include "stipulation/stipulation.h"
#include "stipulation/pipe.h"
#include "solving/has_solution_type.h"
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
void not_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  pipe_solve_delegate(si);

  stip_length_type const result_min = solve_result_min();
  stip_length_type const result_max = solve_result_max();
  if (result_min>MOVE_HAS_SOLVED_LENGTH())
    set_solve_result(MOVE_HAS_SOLVED_LENGTH());
  else if (result_min<previous_move_has_solved)
    if (result_max>MOVE_HAS_SOLVED_LENGTH())
    {
      add_solve_result_possibility(MOVE_HAS_SOLVED_LENGTH());
      if (previous_move_has_solved<=MOVE_HAS_SOLVED_LENGTH())
        add_solve_result_possibility(MOVE_HAS_NOT_SOLVED_LENGTH());
    }
    else if (result_max>=previous_move_has_solved)
      add_solve_result_possibility(MOVE_HAS_NOT_SOLVED_LENGTH());
  else
  {
    set_solve_result(MOVE_HAS_NOT_SOLVED_LENGTH());
    if (result_max>MOVE_HAS_SOLVED_LENGTH())
      add_solve_result_possibility(MOVE_HAS_SOLVED_LENGTH());
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
