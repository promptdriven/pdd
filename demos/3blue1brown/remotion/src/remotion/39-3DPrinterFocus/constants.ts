import { z } from "zod";

// Video specs - 15 seconds at 30fps
export const PRINTER_FOCUS_FPS = 30;
export const PRINTER_FOCUS_DURATION_SECONDS = 15;
export const PRINTER_FOCUS_DURATION_FRAMES =
  PRINTER_FOCUS_FPS * PRINTER_FOCUS_DURATION_SECONDS;
export const PRINTER_FOCUS_WIDTH = 1920;
export const PRINTER_FOCUS_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Based on spec: Frame 0-90 (0-3s), 90-180 (3-6s), 180-300 (6-10s), 300-450 (10-15s)
export const BEATS = {
  // Phase 1: Grid fades in (0-3s)
  GRID_FADE_START: 0,
  GRID_FADE_END: 90,
  AXIS_LABELS_START: 30,
  AXIS_LABELS_END: 90,

  // Phase 2: Position tracking begins (3-6s)
  TRACKING_START: 90,
  TRACKING_ACTIVE: 180,

  // Phase 3: Continue tracking with visual complexity (6-10s)
  TRACKING_CONTINUE: 180,
  TRACKING_COMPLEX: 300,

  // Phase 4: Label appears (10-15s)
  LABEL_START: 300,
  LABEL_END: 360,
  HOLD_START: 360,
};

// Color palette from spec
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  GRID_BLUE: "#5A9FE9", // Light blue at 30% opacity for grid
  AXIS_WHITE: "#ffffff",
  POSITION_CYAN: "#00E5FF",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
  GLOW_BLUE: "rgba(90, 159, 233, 0.5)",
};

// Props schema
export const PrinterFocusProps = z.object({
  showLabel: z.boolean().default(true),
  gridOpacityMax: z.number().default(0.3),
});

export const defaultPrinterFocusProps: z.infer<typeof PrinterFocusProps> = {
  showLabel: true,
  gridOpacityMax: 0.3,
};

export type PrinterFocusPropsType = z.infer<typeof PrinterFocusProps>;
