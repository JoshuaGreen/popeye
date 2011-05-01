#include "output/plaintext/tree/variation_writer.h"
#include "pyoutput.h"
#include "pydata.h"
#include "pypipe.h"
#include "output/plaintext/tree/tree.h"
#include "output/plaintext/tree/check_writer.h"
#include "trace.h"

/* Used by STContinuationWriter and STKeyWriter to
 * inform STVariationWriter about the maximum length of variations
 * after the attack just played. STVariationWriter uses this
 * information to suppress the output of variations that are deemed
 * too short to be interesting.
 */
stip_length_type max_variation_length[maxply+1];

/* Allocate a STVariationWriter slice.
 * @return index of allocated slice
 */
slice_index alloc_variation_writer_slice(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STVariationWriter);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Determine whether there is a solution in n half moves.
 * @param si slice index
 * @param n maximum number of half moves until goal
 * @param n_max_unsolvable maximum number of half-moves that we
 *                         know have no solution
 * @return length of solution found, i.e.:
 *            slack_length_battle-2 defense has turned out to be illegal
 *            <=n length of shortest solution found
 *            n+2 no solution found
 */
stip_length_type
variation_writer_can_attack(slice_index si,
                            stip_length_type n,
                            stip_length_type n_max_unsolvable)
{
  stip_length_type result;
  slice_index const next = slices[si].u.pipe.next;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParam("%u",n_max_unsolvable);
  TraceFunctionParamListEnd();

  result = can_attack(next,n,n_max_unsolvable);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Try to solve in n half-moves after a defense.
 * @param si slice index
 * @param n maximum number of half moves until goal
 * @param n_max_unsolvable maximum number of half-moves that we
 *                         know have no solution
 * @note n==n_max_unsolvable means that we are solving refutations
 * @return length of solution found and written, i.e.:
 *            slack_length_battle-2 defense has turned out to be illegal
 *            <=n length of shortest solution found
 *            n+2 no solution found
 */
stip_length_type variation_writer_attack(slice_index si,
                                         stip_length_type n,
                                         stip_length_type n_max_unsolvable)
{
  stip_length_type result;
  slice_index const next = slices[si].u.pipe.next;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParam("%u",n_max_unsolvable);
  TraceFunctionParamListEnd();

  if (n==slack_length_battle
      && max_variation_length[nbply]>slack_length_battle+1)
    /* variation is too short to be interesting - just determine the
     * result
     */
    result = can_attack(next,n,n_max_unsolvable);
  else
  {
    output_plaintext_tree_write_move();
    result = attack(next,n,n_max_unsolvable);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}
