#include "output/latex/tree/tree.h"
#include "stipulation/pipe.h"
#include "stipulation/fork.h"
#include "stipulation/slice_insertion.h"
#include "stipulation/move.h"
#include "stipulation/battle_play/branch.h"
#include "stipulation/help_play/branch.h"
#include "solving/trivial_end_filter.h"
#include "output/latex/latex.h"
#include "output/latex/goal_writer.h"
#include "output/latex/tree/end_of_solution_writer.h"
#include "output/latex/tree/check_writer.h"
#include "output/latex/tree/threat_writer.h"
#include "output/latex/tree/move_writer.h"
#include "output/latex/tree/zugzwang_writer.h"
#include "output/latex/tree/key_writer.h"
#include "output/latex/tree/try_writer.h"
#include "output/latex/tree/refuting_variation_writer.h"
#include "output/latex/tree/refutation_writer.h"
#include "options/options.h"
#include "conditions/conditions.h"
#include "debugging/assert.h"
#include "debugging/trace.h"

static void insert_zugzwang_writer(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children(si,st);

  {
    FILE * const file = st->param;
    slice_index const prototypes[] =
    {
      alloc_output_latex_tree_zugzwang_writer_slice(file),
      alloc_output_latex_tree_threat_writer_slice(file),
      alloc_output_latex_tree_move_writer_slice(file)
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    defense_branch_insert_slices_behind_proxy(slices[si].next2,prototypes,nr_prototypes,si);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_writer_for_move_in_parent(slice_index si,
                                             stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (st->level==structure_traversal_level_nested)
  {
    FILE * const file = st->param;
    slice_index const prototypes[] =
    {
      alloc_output_latex_tree_move_writer_slice(file),
      alloc_output_latex_tree_check_writer_slice(file)
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    slice_insertion_insert(si,prototypes,nr_prototypes);
  }

  stip_traverse_structure_children_pipe(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_move_writer(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (st->context==stip_traversal_context_defense
      || st->context==stip_traversal_context_attack)
  {
    FILE * const file = st->param;
    slice_index const prototypes[] =
    {
      alloc_output_latex_tree_move_writer_slice(file),
      alloc_output_latex_tree_check_writer_slice(file)
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    slice_insertion_insert_contextually(si,st->context,prototypes,nr_prototypes);
  }

  stip_traverse_structure_children_pipe(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_goal_writer(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (slices[si].u.goal_handler.goal.type!=no_goal)
  {
    FILE *file = st->param;
    slice_index const prototype = alloc_output_latex_goal_writer_slice(slices[si].u.goal_handler.goal,
                                                                       file);
    slice_insertion_insert_contextually(si,st->context,&prototype,1);
  }

  stip_traverse_structure_children(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor const regular_writer_inserters[] =
{
  { STDefenseAdapter,    &insert_writer_for_move_in_parent },
  { STHelpAdapter,       &stip_structure_visitor_noop      },
  { STThreatSolver,      &insert_zugzwang_writer           },
  { STPlaySuppressor,    &stip_structure_visitor_noop      },
  { STMove,              &insert_move_writer               },
  { STGoalReachedTester, &insert_goal_writer               }
};

enum
{
  nr_regular_writer_inserters
  = sizeof regular_writer_inserters / sizeof regular_writer_inserters[0]
};

/* Insert the writer slices
 * @param si identifies slice where to start
 */
static void insert_regular_writer_slices(slice_index si, FILE *file)
{
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_structure_traversal_init(&st,file);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_testing_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_conditional_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override(&st,
                                    regular_writer_inserters,
                                    nr_regular_writer_inserters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void substitute_try_writer(slice_index si,
                                          stip_structure_traversal *st)
{
  FILE *file = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  pipe_substitute(si,alloc_output_latex_tree_try_writer(file));

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_refutation_writer(slice_index si,
                                     stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  {
    FILE *file = st->param;
    slice_index const prototype = alloc_output_latex_tree_refutation_writer_slice(file);
    defense_branch_insert_slices(si,&prototype,1);
  }

  stip_traverse_structure_children_pipe(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor const try_writer_inserters[] =
{
  { STOutputPlainTextKeyWriter,              &substitute_try_writer                 },
  { STOutputPlainTextRefutationsIntroWriter, &insert_refutation_writer              },
  { STEndOfBranchGoal,                       &stip_traverse_structure_children_pipe }
};

enum
{
  nr_try_writer_inserters
  = sizeof try_writer_inserters / sizeof try_writer_inserters[0]
};

static void insert_try_writers(slice_index si, FILE *file)
{
  stip_structure_traversal st;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_structure_traversal_init(&st,file);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_testing_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_conditional_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override(&st,
                                    try_writer_inserters,
                                    nr_try_writer_inserters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

typedef struct
{
    boolean is_postkey_play;
    FILE *file;
} insertion_state_type;

static void insert_end_of_solution_writer(slice_index si,
                                          stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  if (st->level==structure_traversal_level_top)
  {
    insertion_state_type *state = st->param;
    slice_index const prototype = alloc_output_latex_tree_end_of_solution_writer_slice(state->file);
    slice_insertion_insert(si,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void remember_postkey_play(slice_index si, stip_structure_traversal *st)
{
  insertion_state_type * const state = st->param;
  boolean const save_is_postkey_play = state->is_postkey_play;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  state->is_postkey_play = st->level==structure_traversal_level_top;
  stip_traverse_structure_children_pipe(si,st);
  state->is_postkey_play = save_is_postkey_play;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_key_writer(slice_index si, stip_structure_traversal *st)
{
  boolean const * const is_postkey_play = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (!*is_postkey_play)
  {
    insertion_state_type *state = st->param;
    slice_index const prototype = alloc_output_latex_tree_key_writer(state->file);
    defense_branch_insert_slices(si,&prototype,1);
  }

  stip_traverse_structure_children_pipe(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_postkey_writers(slice_index si, stip_structure_traversal *st)
{
  boolean const * const is_postkey_play = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (*is_postkey_play && st->context==stip_traversal_context_defense)
  {
    FILE * const file = st->param;
    slice_index const prototypes[] =
    {
      alloc_output_latex_tree_check_writer_slice(file)
    };
    enum { nr_prototypes = sizeof prototypes / sizeof prototypes[0] };
    defense_branch_insert_slices(si,prototypes,nr_prototypes);
  }

  stip_traverse_structure_children_pipe(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_refuting_variation_writer(slice_index si,
                                             stip_structure_traversal *st)
{
  boolean const * const is_postkey_play = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (st->context==stip_traversal_context_defense)
    stip_traverse_structure_children_pipe(si,st);
  else if (*is_postkey_play)
  {
    insertion_state_type *state = st->param;
    slice_index const prototype = alloc_output_latex_tree_refuting_variation_writer_slice(state->file);
    attack_branch_insert_slices(si,&prototype,1);
  }

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void insert_key_writer_goal(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (st->context==stip_traversal_context_defense)
  {
    insertion_state_type *state = st->param;
    slice_index const prototype = alloc_output_latex_tree_key_writer(state->file);
    defense_branch_insert_slices_behind_proxy(slices[si].next2,
                                              &prototype,1,
                                              si);
  }

  stip_traverse_structure_children(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static void get_fork_of_my_own(slice_index si, stip_structure_traversal *st)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (st->context==stip_traversal_context_defense)
    slices[si].next2 = stip_deep_copy(slices[si].next2);

  stip_traverse_structure_children(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor const root_writer_inserters[] =
{
  { STSetplayFork,        &stip_traverse_structure_children_pipe },
  { STHelpAdapter,        &stip_structure_visitor_noop           },
  { STAttackAdapter,      &insert_end_of_solution_writer         },
  { STDefenseAdapter,     &remember_postkey_play                 },
  { STEndOfBranchGoal,    &insert_key_writer_goal                },
  { STNotEndOfBranchGoal, &insert_refuting_variation_writer      },
  { STEndOfBranch,        &get_fork_of_my_own                    }, /* saves some moves in capzug stipulations*/
  { STNotEndOfBranch,     &insert_postkey_writers                },
  { STReadyForDefense,    &insert_key_writer                     }
};

enum
{
  nr_root_writer_inserters = (sizeof root_writer_inserters
                              / sizeof root_writer_inserters[0])
};

/* Insert the writer slices
 * @param si identifies slice where to start
 */
static void insert_root_writer_slices(slice_index si, FILE *file)
{
  stip_structure_traversal st;

  insertion_state_type state = { false, file };

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_structure_traversal_init(&st,&state);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_testing_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_conditional_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_binary,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_end_of_branch,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override(&st,
                                    root_writer_inserters,
                                    nr_root_writer_inserters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

typedef struct
{
  Goal goal;
  boolean branch_has_key_writer;
} leaf_optimisation_state_structure;

/* Remember that we are about to deal with a goal (and which one)
 */
static void remember_goal(slice_index si, stip_structure_traversal *st)
{
  leaf_optimisation_state_structure * const state = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  assert(state->goal.type==no_goal);

  state->goal = slices[si].u.goal_handler.goal;
  stip_traverse_structure_children(si,st);
  state->goal.type = no_goal;

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Remember that the current branch has a key writer
 */
static void remember_key_writer(slice_index si, stip_structure_traversal *st)
{
  leaf_optimisation_state_structure * const state = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  if (state->goal.type!=no_goal)
  {
    state->branch_has_key_writer = true;
    stip_traverse_structure_children_pipe(si,st);
    state->branch_has_key_writer = false;
  }
  else
    stip_traverse_structure_children_pipe(si,st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Remove an unused slice dealing with a check that we don't intend to write
 */
static void remove_check_handler_if_unused(slice_index si, stip_structure_traversal *st)
{
  leaf_optimisation_state_structure const * const state = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  if (state->goal.type!=no_goal
      && output_goal_preempts_check(state->goal.type))
    pipe_remove(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Remove a continuation writer in a leaf branch where we already have a key
 * writer
 */
static void remove_continuation_writer_if_unused(slice_index si,
                                                 stip_structure_traversal *st)
{
  leaf_optimisation_state_structure const * const state = st->param;

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_traverse_structure_children_pipe(si,st);

  if (state->branch_has_key_writer)
    pipe_remove(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

static structure_traversers_visitor const goal_writer_slice_inserters[] =
{
  { STGoalReachedTester,          &remember_goal                        },
  { STOutputLaTeXKeyWriter,       &remember_key_writer                  },
  { STOutputLaTeXMoveWriter,      &remove_continuation_writer_if_unused },
  { STOutputLaTeXTreeCheckWriter, &remove_check_handler_if_unused       }
};

enum
{
  nr_goal_writer_slice_inserters = (sizeof goal_writer_slice_inserters
                                    / sizeof goal_writer_slice_inserters[0])
};

/* Optimise away superfluous slices in leaf branches
 * @param si identifies slice where to start
 */
static void optimise_leaf_slices(slice_index si)
{
  stip_structure_traversal st;
  leaf_optimisation_state_structure state = { { no_goal, initsquare }, false };

  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  stip_structure_traversal_init(&st,&state);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_testing_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override_by_contextual(&st,
                                                  slice_contextual_conditional_pipe,
                                                  &stip_traverse_structure_children_pipe);
  stip_structure_traversal_override(&st,
                                    goal_writer_slice_inserters,
                                    nr_goal_writer_slice_inserters);
  stip_traverse_structure(si,&st);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}

/* Instrument the stipulation structure with slices that implement
 * plaintext tree mode output.
 * @param si identifies slice where to start
 * @param is_setplay is si part of set play?
 */
void solving_insert_output_latex_tree_slices(slice_index si,
                                             boolean is_setplay,
                                             FILE *file)
{
  TraceFunctionEntry(__func__);
  TraceFunctionParam("%u",si);
  TraceFunctionParamListEnd();

  TraceStipulation(si);

  insert_regular_writer_slices(si,file);
  insert_root_writer_slices(si,file);
  if (!is_setplay && OptFlag[soltout]) /* this includes OptFlag[solessais] */
    insert_try_writers(si,file);
  optimise_leaf_slices(si);

  TraceFunctionExit(__func__);
  TraceFunctionResultEnd();
}
