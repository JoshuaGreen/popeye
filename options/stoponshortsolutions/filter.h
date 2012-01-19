#if !defined(OPTIONS_STOPONSHORTSOLUTIONS_FILTER_H)
#define OPTIONS_STOPONSHORTSOLUTIONS_FILTER_H

#include "stipulation/help_play/play.h"

/* This module provides functionality dealing with
 * STStopOnShortSolutionsFilter stipulation slice type.
 * Slices of this type make sure that solving stops after a short solution
 * solution has been found
 */

/* Allocate a STStopOnShortSolutionsFilter slice.
 * @param length full length
 * @param length minimum length
 * @return allocated slice
 */
slice_index alloc_stoponshortsolutions_filter(stip_length_type length,
                                              stip_length_type min_length);

/* Determine and write the solution(s) in a help stipulation
 * @param si slice index of slice being solved
 * @param n exact number of half moves until end state has to be reached
 * @return length of solution found, i.e.:
 *         n+4 the move leading to the current position has turned out
 *             to be illegal
 *         n+2 no solution found
 *         n   solution found
 */
stip_length_type stoponshortsolutions_help(slice_index si, stip_length_type n);

#endif
