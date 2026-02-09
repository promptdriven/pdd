import { z } from "zod";

// Video specs
export const RATCHET_FPS = 30;
export const RATCHET_DURATION_SECONDS = 25;
export const RATCHET_DURATION_FRAMES =
  RATCHET_FPS * RATCHET_DURATION_SECONDS;
export const RATCHET_WIDTH = 1920;
export const RATCHET_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  INITIAL_WALLS_START: 0,
  INITIAL_WALLS_END: 60,
  TIMELAPSE_START: 90,
  TIMELAPSE_END: 540,
  COUNTER_START: 120,
  TERMINAL_START: 150,
  INSIGHT_START: 600,
  HOLD_START: 720,
};

// Wall addition schedule with accelerating tempo
// First wave (3 walls): 60 frames per wall
// Accelerated wave (5 walls): 30 frames per wall
// Final accumulation (4 walls): ~22 frames per wall
export const WALL_SCHEDULE = [
  { frame: 60, label: "empty array → []" },
  { frame: 90, label: "negative → error" },
  { frame: 120, label: "overflow → clamp" },
  { frame: 180, label: "special chars" },
  { frame: 210, label: "concurrent access" },
  { frame: 240, label: "timeout handling" },
  { frame: 270, label: "retry logic" },
  { frame: 300, label: "cache invalidation" },
  { frame: 360, label: "unicode normalization" },
  { frame: 390, label: "boundary conditions" },
  { frame: 420, label: "state transitions" },
  { frame: 450, label: "error recovery" },
];

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  COUNTER_BLUE: "#4A90D9",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Test wall labels that accumulate over time
export const ACCUMULATING_TESTS = [
  "null → None",
  "empty → None",
  '"abc" → "abc"',
  '" abc " → "abc"',
  '"a1b2" → "a1b2"',
  '"a@b" → None',
  '"" → None',
  '" " → None',
  '"ABC" → "ABC"',
  '"123" → "123"',
  '"a_b" → None',
  '"a-b" → None',
  '"a.b" → None',
  '"very_long_id" → None',
  '"id123" → "id123"',
];

// Terminal test output for scrolling display
export const TERMINAL_TESTS = [
  "test_null_returns_none",
  "test_empty_string_returns_empty",
  "test_unicode_handling",
  "test_latency_under_100ms",
  "test_whitespace_returns_none",
  "test_empty_array_returns_empty",
  "test_negative_raises_error",
  "test_overflow_clamps",
  "test_special_chars_filtered",
  "test_concurrent_access",
  "test_timeout_handling",
  "test_retry_logic",
  "test_cache_invalidation",
  "test_unicode_normalization",
  "test_boundary_conditions",
  "test_state_transitions",
  "test_error_recovery",
];

// Props schema
export const RatchetTimelapseProps = z.object({
  maxWalls: z.number().default(15),
});

export const defaultRatchetTimelapseProps: z.infer<typeof RatchetTimelapseProps> = {
  maxWalls: 15,
};

export type RatchetTimelapsePropsType = z.infer<typeof RatchetTimelapseProps>;
