// Colors
export const COLORS = {
  background: '#000000',
  leftPanelBg: '#0F172A',
  rightPanelBg: '#0A0F1A',
  splitLine: '#334155',
  fileHeaderBg: '#1E293B',
  fileNameColor: '#4A90D9',
  lineNumberColor: '#64748B',
  codeColor: '#CBD5E1',
  leftAccent: '#D9944A',
  rightAccent: '#5AAA6E',
  testColor: '#5AAA6E',
  commandColor: '#94A3B8',
  outputCodeColor: '#94A3B8',
  bottomLabel: '#E2E8F0',
  terminalBg: '#0F172A',
} as const;

// Dimensions
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const SPLIT_X = 960;
export const LEFT_WIDTH = 958;
export const RIGHT_WIDTH = 958;
export const FILE_HEADER_HEIGHT = 30;
export const LINE_HEIGHT = 16;
export const GUTTER_WIDTH = 40;

// Fonts
export const MONO_FONT = 'JetBrains Mono, Menlo, Monaco, Consolas, monospace';
export const SANS_FONT = 'Inter, -apple-system, BlinkMacSystemFont, sans-serif';

// Dense prompt lines (left panel - 50 lines)
export const DENSE_PROMPT_LINES: string[] = [
  '# parser_v1.prompt',
  '# Full specification with all edge cases',
  '',
  'Parse user IDs from untrusted input.',
  'Input is a string that may contain one or more IDs.',
  '',
  '## Null/Empty Handling',
  'Handle null input by returning None.',
  'Handle empty string by returning None.',
  'Handle whitespace-only input by returning None.',
  'Handle undefined by returning None.',
  '',
  '## Format Validation',
  'IDs must match pattern: [A-Za-z0-9_-]{3,64}',
  'Reject IDs shorter than 3 characters.',
  'Reject IDs longer than 64 characters.',
  '',
  '## Unicode Edge Cases',
  'For unicode characters, normalize to NFC form.',
  'Strip zero-width joiners and BOM markers.',
  'Reject RTL override characters.',
  'Handle combining diacritical marks.',
  'Normalize fullwidth ASCII to halfwidth.',
  '',
  '## Delimiter Handling',
  'Split on comma, semicolon, pipe, or newline.',
  'Trim whitespace around each ID.',
  'Ignore empty segments between delimiters.',
  '',
  '## Error Conditions',
  'ValueError for malformed ID strings.',
  'TypeError for non-string input types.',
  'Log warning for IDs that almost match.',
  'Return partial results on recoverable errors.',
  'Never raise on production input.',
  '',
  '## Security',
  'Sanitize against injection patterns.',
  'Reject IDs containing SQL keywords.',
  'Escape special regex characters.',
  'Cap total input length at 1MB.',
  '',
  '## Performance Constraints',
  'Must process 10k IDs in < 100ms.',
  'Use streaming for inputs > 10MB.',
  'Cache compiled regex patterns.',
  '',
  '## Return Contract',
  'Return type: Optional[List[str]].',
  'Never throw exceptions.',
  'Return None on unrecoverable failure.',
  'Return empty list for valid but empty input.',
];

// Minimal prompt lines (right panel - 10 lines)
export const MINIMAL_PROMPT_LINES: string[] = [
  '# parser_v2.prompt',
  '',
  'Parse user IDs from untrusted input.',
  '',
  'Return None on failure, never throw.',
  '',
  'Handle unicode normalization (NFC).',
  '',
  'Latency < 100ms for batch of 10k.',
  '',
];

// Test results (47 tests)
export const TEST_RESULTS: string[] = [
  'test_null_input',
  'test_empty_string',
  'test_whitespace_only',
  'test_undefined_input',
  'test_single_valid_id',
  'test_multiple_ids_comma',
  'test_multiple_ids_semicolon',
  'test_multiple_ids_pipe',
  'test_multiple_ids_newline',
  'test_trim_whitespace',
  'test_empty_segments',
  'test_id_min_length',
  'test_id_max_length',
  'test_id_too_short',
  'test_id_too_long',
  'test_valid_pattern',
  'test_invalid_pattern',
  'test_unicode_nfc',
  'test_zero_width_joiner',
  'test_bom_marker',
  'test_rtl_override',
  'test_combining_marks',
  'test_fullwidth_ascii',
  'test_sql_injection',
  'test_regex_escape',
  'test_input_size_limit',
  'test_malformed_valueerror',
  'test_type_error_int',
  'test_type_error_list',
  'test_partial_recovery',
  'test_warning_logging',
  'test_10k_ids_under_100ms',
  'test_streaming_large_input',
  'test_regex_cache',
  'test_return_none_failure',
  'test_return_empty_list',
  'test_optional_list_type',
  'test_no_exceptions_raised',
  'test_delimiter_precedence',
  'test_nested_delimiters',
  'test_consecutive_delimiters',
  'test_trailing_delimiter',
  'test_leading_delimiter',
  'test_mixed_valid_invalid',
  'test_idempotent_parse',
  'test_thread_safety',
  'test_memory_bounded',
];

// Generated code (shown at bottom of both panels)
export const GENERATED_CODE_LINES: string[] = [
  'def parse_user_ids(raw: str) -> Optional[List[str]]:',
  '    if not raw or not raw.strip():',
  '        return None',
  '    normalized = unicodedata.normalize("NFC", raw)',
  '    return [id for id in re.split(DELIMS, normalized) if valid(id)]',
];
