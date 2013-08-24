#include "conditions/alphabetic.h"
#include "solving/move_generator.h"

#include <assert.h>

/* Determine the length of a move for the Alphabetic Chess; the higher
 * the value the more likely the move is going to be played.
 * @return a value expressing the precedence of this move
 */
int alphabetic_measure_length(void)
{
  square const sq_departure = move_generation_stack[current_move[nbply]-1].departure;

  return -((sq_departure/onerow) + onerow*(sq_departure%onerow));
}
