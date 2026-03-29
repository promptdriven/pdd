// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const WINDOW_FRAME_COLOR = '#1E293B';
export const TITLE_BAR_COLOR = '#151B28';
export const FILENAME_COLOR = '#E2E8F0';
export const PROMPT_TEXT_COLOR = '#CBD5E1';
export const BLUE_ACCENT = '#4A90D9';
export const GREEN_ACCENT = '#5AAA6E';

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

// === Animation Timing (frames) ===
export const TOTAL_FRAMES = 240;

// Phase 1: Editor fade-in (0-30)
export const EDITOR_FADE_START = 0;
export const EDITOR_FADE_DURATION = 30;

// Phase 2: Lines visible (30-60) — already visible, breathing room

// Phase 3: Terminal appears (60-120)
export const TERMINAL_FADE_START = 60;
export const TERMINAL_FADE_DURATION = 30;
export const TYPEWRITER_START = 60;
export const TEST_CASCADE_START = 90; // 60 + 30 frames for typewriter
export const TEST_COUNT = 47;
export const TESTS_PER_FRAME = 3;

// Phase 4: Walls + summary (120-165)
export const WALLS_START = 120;
export const WALL_COUNT = 10;
export const WALL_STAGGER = 5;
export const WALL_DRAW_DURATION = 15;
export const SUMMARY_START = 150; // 60 + 90 frames into terminal sequence

// Phase 5: Label (165-210)
export const LABEL_FADE_START = 165;
export const LABEL_FADE_DURATION = 20;

// Phase 6: Fade out (210-240)
export const FADEOUT_START = 210;
export const FADEOUT_DURATION = 30;

// === Prompt Content ===
export const PROMPT_LINES = [
  'You are a code parser.',
  'Parse the input into an AST.',
  'Return valid JSON output.',
  'Handle nested structures.',
  'Preserve source positions.',
  'Support all token types.',
  'Use the provided schema.',
  'Keep output deterministic.',
  'Respect max depth limits.',
  'Return errors as objects.',
];

// === Test Names ===
export const TEST_NAMES = [
  'test_basic_parsing',
  'test_edge_case_empty_input',
  'test_nested_structures_depth_3',
  'test_unicode_identifiers',
  'test_position_tracking',
  'test_error_recovery_mode',
  'test_json_output_schema',
  'test_deterministic_output',
  'test_max_depth_limit',
  'test_error_as_object',
  'test_multiline_strings',
  'test_comment_preservation',
  'test_array_literals',
  'test_object_destructuring',
  'test_arrow_functions',
  'test_template_literals',
  'test_spread_operator',
  'test_optional_chaining',
  'test_nullish_coalescing',
  'test_async_await',
  'test_generator_functions',
  'test_class_declarations',
  'test_import_statements',
  'test_export_statements',
  'test_type_annotations',
  'test_interface_parsing',
  'test_enum_declarations',
  'test_tuple_types',
  'test_union_types',
  'test_intersection_types',
  'test_conditional_types',
  'test_mapped_types',
  'test_index_signatures',
  'test_decorators',
  'test_jsx_elements',
  'test_fragment_syntax',
  'test_namespace_imports',
  'test_dynamic_imports',
  'test_regex_literals',
  'test_bigint_literals',
  'test_private_fields',
  'test_static_methods',
  'test_computed_properties',
  'test_rest_parameters',
  'test_default_parameters',
  'test_tagged_templates',
  'test_symbol_properties',
];

// === Typography ===
export const FONT_MONO = 'JetBrains Mono, monospace';
export const FONT_SANS = 'Inter, sans-serif';
