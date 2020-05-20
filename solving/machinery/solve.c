#include "solving/machinery/solve.h"
#include "solving/machinery/slack_length.h"
#include "solving/has_solution_type.h"
#include "debugging/trace.h"
#include "debugging/measure.h"
#include "debugging/assert.h"

stip_length_type solve_nr_remaining = length_unspecified;
static stip_length_type solve_result_min_stored;
static stip_length_type solve_result_max_stored;

stip_length_type solve_result_min(void)
{
  return solve_result_min_stored;
}
stip_length_type solve_result_max(void)
{
  return solve_result_max_stored;
}
boolean solve_result_must_equal(stip_length_type const r)
{
  return ((solve_result_min_stored == r) && (solve_result_max_stored == r));
}
boolean solve_result_might_equal(stip_length_type const r)
{
  return ((solve_result_min_stored <= r) && (solve_result_max_stored >= r));
}
void set_solve_result(stip_length_type const r)
{
  solve_result_min_stored = r;
  solve_result_max_stored = r;
}
void set_solve_result_range(stip_length_type const min_result, stip_length_type const max_result)
{
  assert(min_result <= max_result);
  solve_result_min_stored = min_result;
  solve_result_max_stored = max_result;
}
void set_solve_result_min(stip_length_type const min_result)
{
  solve_result_min_stored = min_result;
  if (solve_result_max_stored < min_result)
    solve_result_max_stored = min_result;
}
void set_solve_result_max(stip_length_type const max_result)
{
  solve_result_max_stored = max_result;
  if (solve_result_min_stored > max_result)
    solve_result_min_stored = max_result;
}
void increment_solve_result(void)
{
  ++solve_result_min_stored;
  ++solve_result_max_stored;
}
void decrement_solve_result(void)
{
  --solve_result_min_stored;
  --solve_result_max_stored;
}

/* Detect whether solve_result indicates that solving has succeeded
 * @return true iff solving has succeeded
 */
boolean move_has_solved(void)
{
  return slack_length<=solve_result_min_stored && solve_result_max_stored<=MOVE_HAS_SOLVED_LENGTH();
}
