#if !defined(DEBUGGING_TRACE_H)
#define DEBUGGING_TRACE_H

/* some trace functions
 * - write useful trace output to standard out
 * - activate by #defining DOTRACE
 * - no overhead if not active
 */

#if defined(_MSC_VER)
/* MSVC compilers before VC7 don't have __func__ at all; later ones
 * call it __FUNCTION__. */
#  if _MSC_VER < 1300
#    define __func__ "???"
#  else
#    define __func__ __FUNCTION__
#  endif
#endif


typedef unsigned long trace_level;


#if defined(DOTRACE)

#include <stddef.h>
#include <stdio.h>

#include "pieces/pieces.h"
#include "solving/ply.h"
#include "stipulation/stipulation.h"

/* Set the maximal level of trace messages to be produced.
* @param max_level maximal level of trace messages to be produced;
*                  pass 0 to suppress all trace messages
*/
void TraceSetMaxLevel(trace_level max_level);

/* Trace function entry
 * e.g. > #17 func
 * (where 17 is the current trace recursion level)
 * NOTE: recursion level tracing only provides useful output if every
 * function that has TraceFunctionEntry() also has TraceFunctionExit()
 * (on every exit!)
 */
void TraceFunctionEntry(char const *name);

/* Trace function exit
 * e.g. < #17 func
 */
void TraceFunctionExit(char const *name);

/* Trace a function parameter
 */
#define TraceFunctionParam(format,name) \
  TraceValueImpl(" ->" #name ":" format, (size_t)name)

/* Trace end of function parameter list
 */
void TraceFunctionParamListEnd(void);

/* Trace the value of some expression
 */
#define TraceValue(format,name) \
  TraceValueImpl(" " #name ":" format, (size_t)name)

/* Trace the value of some expression
 */
#define TracePointerValue(format,name) \
  TracePointerValueImpl(" " #name ":" format, (void *)name)

/* Trace arbitrary text
 */
void TraceText(char const *text);

void TraceSquareImpl(char const *prefix, square s);

/* Trace a square name
 */
#define TraceSquare(name) \
  TraceSquareImpl(" " #name ":", name)

void TracePieceImpl(char const *prefix, PieNam p);

/* Trace a piece
 */
#define TracePiece(name) \
  TracePieceImpl(" " #name ":", name)

/* Trace the notation of the current position
 */
void TracePosition(echiquier e, Flags flags[maxsquare+4]);

/* Trace the content of the hashbuffer of ply nbply
 */
void TraceCurrentHashBuffer(void);

/* Trace a function result.
 * Works best in SESE style functions.
 */
#define TraceFunctionResult(format,name) \
  TraceFunctionResultImpl(" <- " #name ":" format, (size_t)name)

/* Trace a function result of pointer type
 * Works best in SESE style functions.
 */
#define TracePointerFunctionResult(format,name) \
  TracePointerValueImpl(" <- " #name ":" format, (void*)name)

/* Trace end of function return value (if any)
 */
void TraceFunctionResultEnd(void);

/* Trace an enumerator value in both string and numerical form
 * The enumeration type defining type_name must have been generated
 * using utilities/enumeration.h
 */
#define TraceEnumerator(type_name,name,suffix) \
  TraceEnumeratorImpl(" " #name ":%s(%u)" suffix, \
                      type_name##_names[name], \
                      name)

/* Trace the current stipulation structure
 * @param start_slice identifies slice where to start tracing
 */
void TraceStipulation(slice_index start_slice);

/* Write the call stack
 * @param file where to write the call stack
 */
void TraceCallStack(FILE *file);

/* Helper functions
 */
void TraceValueImpl(char const *format, size_t value);
void TraceFunctionResultImpl(char const *format, size_t value);
void TracePointerValueImpl(char const *format, void const *value);
void TraceEnumeratorImpl(char const *format,
                         char const *enumerator_name,
                         unsigned int value);

/* Try to solve in n half-moves.
 * @param si slice index
 * @param n maximum number of half moves
 * @return length of solution found and written, i.e.:
 *            previous_move_is_illegal the move just played is illegal
 *            this_move_is_illegal     the move being played is illegal
 *            immobility_on_next_move  the moves just played led to an
 *                                     unintended immobility on the next move
 *            <=n+1 length of shortest solution found (n+1 only if in next
 *                                     branch)
 *            n+2 no solution found in this branch
 *            n+3 no solution found in next branch
 */
stip_length_type move_tracer_solve(slice_index si, stip_length_type n);

/* Instrument slices with move tracers
 */
void stip_insert_move_tracers(slice_index si);

#else

#define TraceDeactivate()
#define TraceFunctionEntry(name)
#define TraceFunctionParam(format,name)
#define TraceFunctionParamListEnd()
#define TraceValue(format,name)
#define TracePointerValue(format,name)
#define TraceText(text)
#define TraceSquare(name)
#define TracePiece(name)
#define TracePosition(echiquier,flags)
#define TraceFunctionExit(name)
#define TraceFunctionResult(format,name)
#define TracePointerFunctionResult(format,name)
#define TraceFunctionResultEnd()
#define TraceCurrentHashBuffer()
#define TraceEnumerator(type_name,value,suffix)
#define TraceStipulation(start_slice)
#define TraceCallStack(file)

#endif

#endif
