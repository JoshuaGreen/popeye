#if !defined(OPTIMISATIONS_INTELLIGENT_SERIES_FILTER_H)
#define OPTIMISATIONS_INTELLIGENT_SERIES_FILTER_H

#include "py.h"
#include "pystip.h"

/* This module provides functionality dealing with STIntelligentSeriesFilter
 * stipulation slice type.
 * Slices of this type make solve series stipulations in intelligent mode
 */

/* Allocate a STIntelligentSeriesFilter slice.
 * @return allocated slice
 */
slice_index alloc_intelligent_series_filter(void);

/* Determine and write the solution(s) in a series stipulation
 * @param si slice index of slice being solved
 * @param n exact number of half moves until end state has to be reached
 * @return length of solution found, i.e.:
 *         n+2 the move leading to the current position has turned out
 *             to be illegal
 *         n+1 no solution found
 *         n   solution found
 */
stip_length_type intelligent_series_filter_series(slice_index si,
                                                  stip_length_type n);

/* Determine whether the slice has a solution in n half moves.
 * @param si slice index of slice being solved
 * @param n number of half moves until end state has to be reached
 * @return length of solution found, i.e.:
 *         n+2 the move leading to the current position has turned out
 *             to be illegal
 *         n+1 no solution found
 *         n   solution found
 */
stip_length_type
intelligent_series_filter_has_solution_in_n(slice_index si,
                                            stip_length_type n);

#endif
