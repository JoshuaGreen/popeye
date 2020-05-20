#include "solving/machinery/solve.h"
#include "solving/machinery/slack_length.h"
#include "solving/has_solution_type.h"
#include "debugging/trace.h"
#include "debugging/measure.h"
#include "debugging/assert.h"

stip_length_type solve_nr_remaining = length_unspecified;
static stip_length_type solve_result_min = MOVE_HAS_NOT_SOLVED_LENGTH();
static stip_length_type solve_result_max = MOVE_HAS_NOT_SOLVED_LENGTH();

stip_length_type get_solve_result_min(void)
{
  return solve_result_min;
}
stip_length_type get_solve_result_max(void)
{
  return solve_result_max;
}
void set_solve_result(stip_length_type const r)
{
  solve_result_min = r;
  solve_result_max = r;
}
void set_solve_result_range(stip_length_type const min_result, stip_length_type const max_result)
{
  assert(min_result <= max_result);
  solve_result_min = min_result;
  solve_result_max = max_result;
}
void set_solve_result_min(stip_length_type const min_result)
{
  solve_result_min = min_result;
  if (solve_result_max < min_result)
    solve_result_max = min_result;
}
void set_solve_result_max(stip_length_type const max_result)
{
  solve_result_max = max_result;
  if (solve_result_min > max_result)
    solve_result_min = max_result;
}
void increment_solve_result(void)
{
  ++solve_result_min;
  ++solve_result_max;
}
void decrement_solve_result(void)
{
  --solve_result_min;
  --solve_result_max;
}

/* Detect whether solve_result indicates that solving has succeeded
 * @return true iff solving has succeeded
 */
boolean move_has_solved(void)
{
  return slack_length<=solve_result_min && solve_result_max<=MOVE_HAS_SOLVED_LENGTH();
}
