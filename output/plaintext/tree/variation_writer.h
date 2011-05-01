#if !defined(OUTPUT_PLAINTEXT_TREE_VARIATION_WRITER_H)
#define OUTPUT_PLAINTEXT_TREE_VARIATION_WRITER_H

#include "stipulation/battle_play/attack_play.h"

/* Used by STContinuationWriter and STKeyWriter to
 * inform STVariationWriter about the maximum length of variations
 * after the attack just played. STVariationWriter uses this
 * information to suppress the output of variations that are deemed
 * too short to be interesting.
 */
extern stip_length_type max_variation_length[maxply+1];

/* Allocate a STVariationWriter slice.
 * @return index of allocated slice
 */
slice_index alloc_variation_writer_slice(void);

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
                            stip_length_type n_max_unsolvable);

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
                                         stip_length_type n_max_unsolvable);

#endif
