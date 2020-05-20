#include "output/latex/tree/zugzwang_writer.h"
#include "output/latex/message.h"
#include "stipulation/stipulation.h"
#include "stipulation/pipe.h"
#include "solving/has_solution_type.h"
#include "solving/machinery/solve.h"
#include "solving/ply.h"
#include "solving/pipe.h"
#include "debugging/trace.h"

/* Allocate a STOutputLaTeXZugzwangByDummyMoveCheckWriter slice.
 * @return index of allocated slice
 */
slice_index alloc_output_latex_tree_zugzwang_by_dummy_move_check_writer_slice(FILE *file)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STOutputLaTeXZugzwangByDummyMoveCheckWriter);
  SLICE_U(result).writer.file = file;

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Allocate a STOutputLaTeXZugzwangWriter slice.
 * @return index of allocated slice
 */
slice_index alloc_output_latex_tree_zugzwang_writer_slice(FILE *file)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STOutputLaTeXZugzwangWriter);
  SLICE_U(result).writer.file = file;

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
void output_latex_tree_zugzwang_by_dummy_move_check_writer_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  pipe_solve_delegate(si);


  if (solve_result_must_equal(previous_move_is_illegal))
    /* the dummy move has effects that causes check to be delivered to the
     * defending side: no threat attempt can therefore be meaningfully played
     * -> signal Zugzwang
     */
    output_latex_message(SLICE_U(si).writer.file,Zugzwang);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
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
void output_latex_tree_zugzwang_writer_solve(slice_index si)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (parent_ply[nbply]==ply_retro_move)
    /* option postkey is set - write "threat:" or "zugzwang" on a new line
     */
    output_latex_message(SLICE_U(si).writer.file,NewLine);

  pipe_solve_delegate(si);

  /* We don't signal "Zugzwang" after the last attacking move of a
   * self play variation */
  if (solve_nr_remaining>=next_move_has_solution
      && solve_result_must_equal(MOVE_HAS_NOT_SOLVED_LENGTH()))
    output_latex_message(SLICE_U(si).writer.file,Zugzwang);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
