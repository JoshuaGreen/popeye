typedef enum
{
 has_solution_type_0, previous_move_is_illegal, immobility_on_next_move, previous_move_has_solved, next_move_has_solution, previous_move_has_not_solved, next_move_has_no_solution, length_unspecified=previous_move_has_solved, this_move_is_illegal=previous_move_is_illegal+1
} has_solution_type;
extern char const *has_solution_type_names[];
