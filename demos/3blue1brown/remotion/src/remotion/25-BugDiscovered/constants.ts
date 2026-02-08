import { z } from "zod";

// Video specs
export const BUG_DISCOVERED_FPS = 30;
export const BUG_DISCOVERED_DURATION_SECONDS = 20;
export const BUG_DISCOVERED_DURATION_FRAMES =
  BUG_DISCOVERED_FPS * BUG_DISCOVERED_DURATION_SECONDS;
export const BUG_DISCOVERED_WIDTH = 1920;
export const BUG_DISCOVERED_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  CODE_START: 0,
  CODE_END: 60,
  BUG_HIGHLIGHT_START: 60,
  BUG_HIGHLIGHT_END: 120,
  RED_FLASH_START: 120,
  RED_FLASH_END: 150,
  TEST_FAILURE_START: 150,
  TEST_FAILURE_END: 210,
  EXPLANATION_START: 240,
  HOLD_START: 480,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BUG_RED: "#D94A4A",
  CODE_GRAY: "#8a9caf",
  WALLS_AMBER: "#D9944A",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Buggy code example
export const BUGGY_CODE = `def parse_user_id(input_str):
    if not input_str:
        return None
    # BUG: missing .strip() call!
    cleaned = input_str
    if not cleaned.isalnum():
        return None
    return cleaned`;

// The failing test case
export const FAILING_TEST = {
  input: '" abc "',
  expected: '"abc"',
  actual: 'None',
};

// Props schema
export const BugDiscoveredProps = z.object({
  showOverlay: z.boolean().default(true),
});

export const defaultBugDiscoveredProps: z.infer<typeof BugDiscoveredProps> = {
  showOverlay: true,
};

export type BugDiscoveredPropsType = z.infer<typeof BugDiscoveredProps>;
