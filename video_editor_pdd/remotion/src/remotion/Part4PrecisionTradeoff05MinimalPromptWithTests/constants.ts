// === Colors ===
export const BG_COLOR = "#0A0F1A";
export const WINDOW_FRAME_COLOR = "#1E293B";
export const TITLE_BAR_COLOR = "#151B28";
export const FILENAME_COLOR = "#E2E8F0";
export const PROMPT_TEXT_COLOR = "#CBD5E1";
export const BLUE_ACCENT = "#4A90D9";
export const GREEN_ACCENT = "#5AAA6E";
export const LABEL_COLOR = "#4A90D9";

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const EDITOR_X = 360;
export const EDITOR_Y = 80;
export const EDITOR_WIDTH = 600;
export const EDITOR_HEIGHT = 280;

export const TERMINAL_X = 360;
export const TERMINAL_Y = 420;
export const TERMINAL_WIDTH = 600;
export const TERMINAL_HEIGHT = 520;

export const TITLE_BAR_HEIGHT = 36;
export const WINDOW_BORDER_RADIUS = 8;

// === Timing (frames) ===
export const FPS = 30;
export const TOTAL_FRAMES = 240;

export const EDITOR_FADE_START = 0;
export const EDITOR_FADE_DURATION = 30;

export const TERMINAL_FADE_START = 60;
export const TERMINAL_FADE_DURATION = 30;

export const TYPEWRITER_START = 60; // relative to component start
export const TYPEWRITER_CHAR_FRAMES = 1;

export const TEST_CASCADE_START = 90; // absolute: 60 + 30
export const TEST_CASCADE_RATE = 3; // tests per frame

export const WALLS_START = 120;
export const WALL_DRAW_DURATION = 15;
export const WALL_STAGGER = 5;
export const WALL_COUNT = 10;

export const SUMMARY_START = 150; // 60 + 90
export const SUMMARY_FADE_DURATION = 15;

export const LABEL_START = 165;
export const LABEL_FADE_DURATION = 20;

export const FADEOUT_START = 210;
export const FADEOUT_DURATION = 30;

// === Data ===
export const PROMPT_FILENAME = "parser_v2.prompt";
export const PROMPT_LINE_COUNT = 10;
export const TEST_COUNT = 47;
export const TERMINAL_COMMAND = "$ pdd test parser";

export const PROMPT_LINES: string[] = [
  "# Parser V2 — Intent-Only Prompt",
  "",
  "Parse the input into a structured AST.",
  "Preserve source locations on each node.",
  "Handle UTF-8 encoded strings correctly.",
  "Return errors as a list, not exceptions.",
  "Support nested expressions up to depth 64.",
  "Emit warnings for deprecated syntax.",
  "Output must be JSON-serializable.",
  "Maintain backwards compat with v1 output.",
];

export const TEST_NAMES: string[] = [
  "test_basic_parsing",
  "test_edge_case_empty_input",
  "test_nested_expression_depth",
  "test_utf8_string_handling",
  "test_error_list_format",
  "test_source_location_accuracy",
  "test_deprecated_syntax_warning",
  "test_json_serialization",
  "test_backwards_compat_v1",
  "test_whitespace_handling",
  "test_comment_stripping",
  "test_multiline_strings",
  "test_escape_sequences",
  "test_integer_overflow",
  "test_float_precision",
  "test_boolean_literals",
  "test_null_handling",
  "test_array_parsing",
  "test_object_parsing",
  "test_deeply_nested_objects",
  "test_duplicate_keys",
  "test_trailing_commas",
  "test_unicode_escapes",
  "test_surrogate_pairs",
  "test_control_characters",
  "test_max_string_length",
  "test_recursive_descent",
  "test_operator_precedence",
  "test_parenthesized_exprs",
  "test_function_calls",
  "test_method_chaining",
  "test_ternary_operator",
  "test_assignment_ops",
  "test_comparison_ops",
  "test_logical_operators",
  "test_bitwise_operators",
  "test_unary_operators",
  "test_postfix_operators",
  "test_spread_syntax",
  "test_destructuring",
  "test_template_literals",
  "test_regex_literals",
  "test_optional_chaining",
  "test_nullish_coalescing",
  "test_pipeline_operator",
  "test_partial_application",
  "test_pattern_matching",
];
