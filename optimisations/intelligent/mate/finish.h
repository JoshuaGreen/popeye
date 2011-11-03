#if !defined(OPTIMISATION_INTELLIGENT_MATE_FINISH_H)
#define OPTIMISATION_INTELLIGENT_MATE_FINISH_H

/* Test the position created by the taken operations; if the position is a
 * solvable target position: solve it; otherwise: improve it
 */
void intelligent_mate_test_target_position(void);

#endif
