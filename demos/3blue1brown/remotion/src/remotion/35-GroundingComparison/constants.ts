import { z } from "zod";

// Video specs
export const GROUNDING_COMPARISON_FPS = 30;
export const GROUNDING_COMPARISON_DURATION_SECONDS = 20;
export const GROUNDING_COMPARISON_DURATION_FRAMES =
  GROUNDING_COMPARISON_FPS * GROUNDING_COMPARISON_DURATION_SECONDS;
export const GROUNDING_COMPARISON_WIDTH = 1920;
export const GROUNDING_COMPARISON_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  SOURCE_START: 0,
  SOURCE_END: 60,
  GROUNDING_START: 90,
  GROUNDING_END: 140,
  OOP_CODE_START: 180,
  OOP_CODE_END: 240,
  FUNC_CODE_START: 200,
  FUNC_CODE_END: 260,
  CHECKMARKS_START: 300,
  CHECKMARKS_END: 340,
  INSIGHT_START: 420,
  INSIGHT_END: 460,
  HOLD_START: 540,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  GROUNDING_GREEN: "#5AAA6E",
  SUCCESS_GREEN: "#4CAF50",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  CODE_GRAY: "#8a9caf",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// OOP code output
export const OOP_CODE = `class UserParser:
    def __init__(self):
        self._validators = [...]

    def parse(self, input_str):
        if not input_str:
            return None
        cleaned = self._sanitize(input_str)
        return cleaned if self._validate(cleaned) else None

    def _sanitize(self, value):
        return value.strip()

    def _validate(self, value):
        return bool(value) and value.isalnum()`;

// Functional code output
export const FUNCTIONAL_CODE = `def parse_user_id(input_str):
    return pipe(
        input_str,
        sanitize,
        validate,
        lambda x: x if x else None
    )

def sanitize(value):
    return (value or "").strip()

def validate(value):
    return value if value and value.isalnum() else None`;

// Props schema
export const GroundingComparisonProps = z.object({
  showBothStyles: z.boolean().default(true),
});

export const defaultGroundingComparisonProps: z.infer<typeof GroundingComparisonProps> = {
  showBothStyles: true,
};

export type GroundingComparisonPropsType = z.infer<typeof GroundingComparisonProps>;
