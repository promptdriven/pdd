import { z } from "zod";

// Video specs
export const Z3_SMT_SIDEBAR_FPS = 30;
export const Z3_SMT_SIDEBAR_DURATION_SECONDS = 20;
export const Z3_SMT_SIDEBAR_DURATION_FRAMES =
  Z3_SMT_SIDEBAR_FPS * Z3_SMT_SIDEBAR_DURATION_SECONDS;
export const Z3_SMT_SIDEBAR_WIDTH = 1920;
export const Z3_SMT_SIDEBAR_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  SYNOPSYS_START: 0,
  SYNOPSYS_END: 60,
  Z3_START: 60,
  Z3_END: 120,
  BRIDGE_START: 120,
  BRIDGE_END: 180,
  LINE1_START: 180,
  LINE1_END: 220,
  LINE2_START: 220,
  LINE2_END: 260,
  LINE3_START: 260,
  LINE3_END: 300,
  PULSE_START: 300,
  HOLD_START: 420,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  TEAL: "#2AA198",
  TEAL_DIM: "#1a7a75",
  MUTED_WHITE: "#B0B0C0",
  BRIGHT_WHITE: "#FFFFFF",
};

// Text content
export const TEXT = {
  SYNOPSYS_LABEL: "Synopsys Formality",
  Z3_LABEL: "Z3 (Microsoft Research)",
  LINE1: "Hardware: SMT-based formal proof",
  LINE2: "PDD: SMT-based formal proof",
  LINE3: "Same math.",
};

// Layout positions
export const LAYOUT = {
  LOGO_Y: 320,
  LOGO_GAP: 200,
  SYNOPSYS_X: 660,
  Z3_X: 1260,
  BRIDGE_WIDTH: 200,
  TEXT_BOTTOM: 280,
};

// Props schema
export const Z3SmtSidebarProps = z.object({
  showOverlay: z.boolean().default(true),
});

export const defaultZ3SmtSidebarProps: z.infer<typeof Z3SmtSidebarProps> = {
  showOverlay: true,
};

export type Z3SmtSidebarPropsType = z.infer<typeof Z3SmtSidebarProps>;
