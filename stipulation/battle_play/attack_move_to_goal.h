#if !defined(STIPULATION_BATTLE_PLAY_ATTACK_MOVE_TO_GOAL_H)
#define STIPULATION_BATTLE_PLAY_ATTACK_MOVE_TO_GOAL_H

#include "boolean.h"
#include "pystip.h"
#include "pyslice.h"

/* This module provides functionality dealing with the attacking side
 * in STAttackMoveToGoal stipulation slices.
 */

/* Allocate a STAttackMoveToGoal slice.
 * @param length maximum number of half-moves of slice (+ slack)
 * @param min_length minimum number of half-moves of slice (+ slack)
 * @return index of allocated slice
 */
slice_index alloc_attack_move_to_goal_slice(stip_length_type length,
                                            stip_length_type min_length);

/* Determine whether there is a solution in n half moves, by trying
 * n_min, n_min+2 ... n half-moves.
 * @param si slice index
 * @param n maximal number of moves
 * @param n_min minimal number of half moves to try
 * @param n_max_unsolvable maximum number of half-moves that we
 *                         know have no solution
 * @return length of solution found, i.e.:
 *            slack_length_battle-2 defense has turned out to be illegal
 *            <=n length of shortest solution found
 *            n+2 no solution found
 */
stip_length_type
attack_move_to_goal_has_solution_in_n(slice_index si,
                                      stip_length_type n,
                                      stip_length_type n_min,
                                      stip_length_type n_max_unsolvable);

/* Solve a slice, by trying n_min, n_min+2 ... n half-moves.
 * @param si slice index
 * @param n maximum number of half moves until goal
 * @param n_max_unsolvable maximum number of half-moves that we
 *                         know have no solution
 * @return length of solution found and written, i.e.:
 *            slack_length_battle-2 defense has turned out to be illegal
 *            <=n length of shortest solution found
 *            n+2 no solution found
 */
stip_length_type
attack_move_to_goal_solve_in_n(slice_index si,
                               stip_length_type n,
                               stip_length_type n_max_unsolvable);

/* Detect starter field with the starting side if possible.
 * @param si identifies slice being traversed
 * @param st status of traversal
 */
void attack_move_to_goal_detect_starter(slice_index si,
                                        stip_structure_traversal *st);

#endif
