#include "stipulation/operators/binary.h"
#include "stipulation/proxy.h"
#include "trace.h"

/* Substitute links to proxy slices by the proxy's target
 * @param si root of sub-tree where to resolve proxies
 * @param st address of structure representing the traversal
 */
void binary_resolve_proxies(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children(si,st);
  proxy_slice_resolve(&slices[si].u.binary.op1);
  proxy_slice_resolve(&slices[si].u.binary.op2);
  
  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Traversal of the moves of an operand of a binary operator
 * @param op identifies operand
 * @param st address of structure representing traversal
 */
void stip_traverse_moves_binary_operand(slice_index op,
                                        stip_move_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",op);
  TraceFunctionParamListEnd();

  st->remaining = 0;
  stip_traverse_moves(op,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Traversal of the moves of a binary operator
 * @param si identifies root of subtree
 * @param st address of structure representing traversal
 */
void stip_traverse_moves_binary(slice_index si, stip_move_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_moves_binary_operand(slices[si].u.binary.op1,st);
  stip_traverse_moves_binary_operand(slices[si].u.binary.op2,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
