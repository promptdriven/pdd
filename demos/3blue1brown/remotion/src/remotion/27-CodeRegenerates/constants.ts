import { z } from "zod";

// Video specs
export const CODE_REGEN_FPS = 30;
export const CODE_REGEN_DURATION_SECONDS = 20;
export const CODE_REGEN_DURATION_FRAMES =
  CODE_REGEN_FPS * CODE_REGEN_DURATION_SECONDS;
export const CODE_REGEN_WIDTH = 1920;
export const CODE_REGEN_HEIGHT = 1080;

// Beat timings (in frames at 30fps) aligned with spec
// Frame 0-60 (0-2s): Old code dissolves
// Frame 60-90 (2-3s): Terminal command appears
// Frame 90-180 (3-6s): New injection flows
// Frame 180-270 (6-9s): Wall interactions
// Frame 270-360 (9-12s): Cavity fills
// Frame 360-450 (12-15s): Success indicator
export const BEATS = {
  OLD_CODE_START: 0,
  OLD_CODE_END: 60,
  DISSOLVE_START: 0,
  DISSOLVE_END: 60,
  TERMINAL_START: 60,
  TERMINAL_END: 90,
  INJECTION_START: 90,
  INJECTION_END: 180,
  WALL_INTERACTION_START: 180,
  WALL_INTERACTION_END: 270,
  CAVITY_FILL_START: 270,
  CAVITY_FILL_END: 360,
  SUCCESS_START: 360,
  SUCCESS_END: 450,
  HOLD_START: 450,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  CODE_GRAY: "#8a9caf",
  SUCCESS_GREEN: "#5AAA6E",
  DISSOLVE_ORANGE: "#D9944A",
  LABEL_WHITE: "#ffffff",
  LIQUID_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  MOLD_DARK: "#16161f",
};

// Old buggy code
export const OLD_CODE = `def parse_user_id(input_str):
    if not input_str:
        return None
    cleaned = input_str  # Missing .strip()!
    if not cleaned.isalnum():
        return None
    return cleaned`;

// New fixed code
export const NEW_CODE = `def parse_user_id(input_str):
    if not input_str or not input_str.strip():
        return None
    cleaned = input_str.strip()
    if not cleaned.isalnum():
        return None
    return cleaned`;

// Mold cavity and walls (cross-section view)
export const MOLD_CAVITY = {
  x: 660,
  y: 240,
  width: 600,
  height: 600,
};

// Test wall definitions (including the NEW wall)
export interface WallDef {
  label: string;
  x: number;
  y: number;
  width: number;
  height: number;
  isNew: boolean;
}

export const WALLS: WallDef[] = [
  // Top wall
  { label: "empty → None", x: 660, y: 240, width: 600, height: 12, isNew: false },
  // Right wall
  { label: "valid format", x: 1248, y: 240, width: 12, height: 600, isNew: false },
  // Bottom wall
  { label: "no exceptions", x: 660, y: 828, width: 600, height: 12, isNew: false },
  // Left wall
  { label: "whitespace → None", x: 660, y: 240, width: 12, height: 600, isNew: true },
];

// Contact points for wall interactions
export const CONTACT_POINTS = [
  { wallIndex: 0, frame: 180 }, // Top wall
  { wallIndex: 3, frame: 210 }, // New left wall
  { wallIndex: 1, frame: 240 }, // Right wall
  { wallIndex: 2, frame: 270 }, // Bottom wall
];

// Props schema
export const CodeRegeneratesProps = z.object({
  showTransition: z.boolean().default(true),
});

export const defaultCodeRegeneratesProps: z.infer<typeof CodeRegeneratesProps> = {
  showTransition: true,
};

export type CodeRegeneratesPropsType = z.infer<typeof CodeRegeneratesProps>;
