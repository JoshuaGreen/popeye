typedef enum
{
 piece_is_unused, piece_pins, piece_is_fixed_to_diagram_square, piece_intercepts, piece_intercepts_check_from_guard, piece_blocks, piece_guards, piece_gives_check, piece_is_missing, piece_is_captured, piece_is_king,
} piece_usage;
extern char const *piece_usage_names[];
