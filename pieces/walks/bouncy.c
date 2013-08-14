#include "pieces/walks/bouncy.h"
#include "solving/move_generator.h"
#include "debugging/trace.h"
#include "pydata.h"
#include "pyproc.h"

#include <assert.h>

static void bouncy_knight_generate_moves_recursive(square step_departure, int x)
{
  vec_index_type k;

  /* ATTENTION:   first call of grefcn: x must be 2 !!   */

  for (k = vec_knight_start; k<=vec_knight_end; ++k)
  {
    curr_generation->arrival = step_departure+vec[k];
    if (is_square_empty(curr_generation->arrival))
    {
      push_move();
      if (x>0 && !NoEdge(curr_generation->arrival))
        bouncy_knight_generate_moves_recursive(curr_generation->arrival,x-1);
    }
    else if (piece_belongs_to_opponent(curr_generation->arrival))
      push_move();
  }
}

/* Generate moves for a bouncy night
 */
void bouncy_knight_generate_moves(void)
{
  numecoup const save_current_move = current_move[nbply]-1;
  bouncy_knight_generate_moves_recursive(curr_generation->departure,2);
  remove_duplicate_moves_of_single_piece(save_current_move);
  return;
}

enum
{
  nr_edge_squares_row = nr_files_on_board,
  nr_edge_squares_file = nr_rows_on_board-2, /* count corners once only */

  nr_edge_squares = 2*nr_edge_squares_row + 2*nr_edge_squares_file
};

typedef square edge_square_index;

/* remember edge traversals by reflecting pieces
 */
static boolean edgestraversed[nr_edge_squares];

/* clear edge traversal memory
 */
void clearedgestraversed(void)
{
  int i;
  for (i=0; i<nr_edge_squares; i++)
    edgestraversed[i] = false;
}

/* map edge squares to indices into edgestraversed
 * the mapping occurs in the order
 * - bottom row
 * - top row
 * - left file
 * - right file
 * @param edge_square square on board edge
 * @return index into edgestraversed where to remember traversal of
 *         edge_square
 */
static edge_square_index square_2_edge_square_index(square edge_square)
{
  int const row =  edge_square/onerow;
  int const file = edge_square%onerow;
  edge_square_index result;

  assert(row==bottom_row || row==top_row
         || file==left_file || file==right_file);
  if (row==bottom_row)
    result = file-left_file;
  else if (row==top_row)
    result = file-left_file + nr_edge_squares_row;
  else if (file==left_file)
    result = row-bottom_row-1 + 2*nr_edge_squares_row;
  else
    result = row-bottom_row-1 + 2*nr_edge_squares_row + nr_edge_squares_file;

  assert(result<nr_edge_squares);
  return result;
}

/* query traversal of an edge square
 * @param edge_square square on board edge
 * @return has edge_square been traversed?
 */
boolean traversed(square edge_square)
{
  return edgestraversed[square_2_edge_square_index(edge_square)];
}

/* remember traversal of an edge square
 * @param edge_square square on board edge
 */
void settraversed(square edge_square)
{
  edgestraversed[square_2_edge_square_index(edge_square)] = true;
}

static void bouncy_nightrider_generate_moves_recursive(square step_departure)
{
  vec_index_type k;

  if (!NoEdge(step_departure))
    settraversed(step_departure);

  for (k= vec_knight_start; k<=vec_knight_end; k++)
  {
    curr_generation->arrival = step_departure+vec[k];

    while (is_square_empty(curr_generation->arrival))
    {
      push_move();
      if (!NoEdge(curr_generation->arrival) && !traversed(curr_generation->arrival))
      {
        bouncy_nightrider_generate_moves_recursive(curr_generation->arrival);
        break;
      }
      else
        curr_generation->arrival += vec[k];
    }

    if (piece_belongs_to_opponent(curr_generation->arrival))
      push_move();
  }
}

/* Generate moves for a bouncy nightrider
 */
void bouncy_nightrider_generate_moves(void)
{
  numecoup const save_current_move = current_move[nbply]-1;
  clearedgestraversed();
  bouncy_nightrider_generate_moves_recursive(curr_generation->departure);
  remove_duplicate_moves_of_single_piece(save_current_move);
}

static boolean rrefcech(square i1, int x, evalfunction_t *evaluate)
{
  square const sq_target = move_generation_stack[current_move[nbply]-1].capture;
  vec_index_type k;

  /* ATTENTION:   first call of rrefech: x must be 2 !!   */

  square sq_departure;

  for (k= vec_knight_start; k <= vec_knight_end; k++)
    if (x) {
      sq_departure= i1+vec[k];
      if (is_square_empty(sq_departure)) {
        if (!NoEdge(sq_departure)) {
          if (rrefcech(sq_departure,x-1,evaluate))
            return true;
        }
      }
      else if (INVOKE_EVAL(evaluate,sq_departure,sq_target))
        return true;
    }
    else
      for (k= vec_knight_start; k <= vec_knight_end; k++) {
        sq_departure= i1+vec[k];
        if (INVOKE_EVAL(evaluate,sq_departure,sq_target))
          return true;
      }

  return false;
}

boolean bouncy_knight_check(evalfunction_t *evaluate)
{
  square const sq_target = move_generation_stack[current_move[nbply]-1].capture;
  return rrefcech(sq_target, 2, evaluate);
}

static boolean rrefnech(square i1, evalfunction_t *evaluate)
{
  square const sq_target = move_generation_stack[current_move[nbply]-1].capture;
  vec_index_type k;

  if (!NoEdge(i1))
    settraversed(i1);

  for (k= vec_knight_start; k<=vec_knight_end; k++) {
    square sq_departure = i1+vec[k];

    while (is_square_empty(sq_departure))
    {
      if (!NoEdge(sq_departure) &&
          !traversed(sq_departure)) {
        if (rrefnech(sq_departure,evaluate))
          return true;
        break;
      }
      sq_departure += vec[k];
    }

    if (INVOKE_EVAL(evaluate,sq_departure,sq_target))
      return true;
  }
  return false;
}

boolean bouncy_nightrider_check(evalfunction_t *evaluate)
{
  square const sq_target = move_generation_stack[current_move[nbply]-1].capture;
  clearedgestraversed();
  return rrefnech(sq_target, evaluate);
}
