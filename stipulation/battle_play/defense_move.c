#include "stipulation/battle_play/defense_move.h"
#include "pydata.h"
#include "pypipe.h"
#include "stipulation/battle_play/attack_play.h"
#include "trace.h"

#include <assert.h>

/* Allocate a STDefenseMove defender slice.
 * @return index of allocated slice
 */
slice_index alloc_defense_move_slice(void)
{
  slice_index result;

  TraceFunctionEntry(__func__);
  TraceFunctionParamListEnd();

  result = alloc_pipe(STDefenseMove);

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Detect starter field with the starting side if possible.
 * @param si identifies slice being traversed
 * @param st status of traversal
 */
void defense_move_detect_starter(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (slices[si].starter==no_side)
  {
    stip_traverse_structure_pipe(si,st);
    slices[si].starter = advers(slices[slices[si].u.pipe.next].starter);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Try to defend after an attacking move
 * When invoked with some n, the function assumes that the key doesn't
 * solve in less than n half moves.
 * @param si slice index
 * @param n maximum number of half moves until end state has to be reached
 * @param n_max_unsolvable maximum number of half-moves that we
 *                         know have no solution
 * @note n==n_max_unsolvable means that we are solving refutations
 * @return <slack_length_battle - no legal defense found
 *         <=n solved  - return value is maximum number of moves
 *                       (incl. defense) needed
 *         n+2 refuted - acceptable number of refutations found
 *         n+4 refuted - >acceptable number of refutations found
 */
stip_length_type defense_move_defend(slice_index si,
                                     stip_length_type n,
                                     stip_length_type n_max_unsolvable)
{
  stip_length_type result = slack_length_battle-2;
  slice_index const next = slices[si].u.pipe.next;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParam("%u",n_max_unsolvable);
  TraceFunctionParamListEnd();

  assert(n>slack_length_battle);

  n_max_unsolvable = slack_length_battle;

  while(encore())
  {
    if (jouecoup(nbply,first_play) && TraceCurrentMove(nbply))
    {
      stip_length_type const nr_moves_needed
          = attack(next,n-1,n_max_unsolvable-1)+1;
      if (nr_moves_needed>result)
        result = nr_moves_needed;
    }

    repcoup();
  }

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}

/* Determine whether there are defenses after an attacking move
 * @param si slice index
 * @param n maximum number of half moves until end state has to be reached
 * @param n_max_unsolvable maximum number of half-moves that we
 *                         know have no solution
 * @return <slack_length_battle - no legal defense found
 *         <=n solved  - return value is maximum number of moves
 *                       (incl. defense) needed
 *         n+2 refuted - <=acceptable number of refutations found
 *         n+4 refuted - >acceptable number of refutations found
 */
stip_length_type defense_move_can_defend(slice_index si,
                                         stip_length_type n,
                                         stip_length_type n_max_unsolvable)
{
  stip_length_type result;
  slice_index const next = slices[si].u.pipe.next;
  stip_length_type max_len_continuation = slack_length_battle-1;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParam("%u",n);
  TraceFunctionParam("%u",n_max_unsolvable);
  TraceFunctionParamListEnd();

  assert(n>slack_length_battle);

  n_max_unsolvable = slack_length_battle;

  while (max_len_continuation<=n && encore())
  {
    if (jouecoup(nbply,first_play) && TraceCurrentMove(nbply))
    {
      stip_length_type const
          length_sol = can_attack(next,n-1,n_max_unsolvable-1)+1;
      if (max_len_continuation<length_sol)
        max_len_continuation = length_sol;
    }

    repcoup();
  }

  if (max_len_continuation>n) /* refuted */
    result = n+4;
  else
    result = max_len_continuation;

  TraceFunctionExit(__func__);
  TraceFunctionResult("%u",result);
  TraceFunctionResultEnd();
  return result;
}
