import { z } from "zod";

// Video specs - 15 seconds at 30fps (450 frames)
export const SOCK_METAPHOR_FPS = 30;
export const SOCK_METAPHOR_DURATION_SECONDS = 15;
export const SOCK_METAPHOR_DURATION_FRAMES =
  SOCK_METAPHOR_FPS * SOCK_METAPHOR_DURATION_SECONDS;
export const SOCK_METAPHOR_WIDTH = 1920;
export const SOCK_METAPHOR_HEIGHT = 1080;

// Beat timings (in frames at 30fps) - matched to spec
export const BEATS = {
  // Phase 1: Sock examination (0-2s, frames 0-60)
  EXAMINATION_START: 0,
  EXAMINATION_END: 60,
  COST_LABEL_FADE_IN: 15, // 0.5s in
  COST_LABEL_FADE_OUT: 90, // 3s

  // Phase 2: Decision moment (2-4s, frames 60-120)
  DECISION_START: 60,
  DECISION_END: 120,

  // Phase 3: Discard (4-8s, frames 120-240)
  DISCARD_START: 120,
  DISCARD_END: 240,
  PARTICLE_START: 120,
  PARTICLE_END: 180,

  // Phase 4: Grab fresh (8-12s, frames 240-360)
  GRAB_FRESH_START: 240,
  GRAB_FRESH_END: 360,
  FRESH_GLOW_START: 260,
  FRESH_GLOW_END: 320,

  // Phase 5: Hold satisfied (12-15s, frames 360-450)
  HOLD_START: 360,
  HOLD_END: 450,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#2A2520", // Warm neutral background
  SOCK_OLD: "#C4956A", // Worn beige sock
  SOCK_BORDER: "#8B6914", // Darker border
  SOCK_FRESH: "#E8D4B8", // Fresh, brighter sock
  COST_LABEL: "rgba(255, 255, 255, 0.6)",
  PARTICLE_GRAY: "#888888",
  GLOW_AMBER: "rgba(255, 240, 220, 0.3)",
};

// Props schema
export const SockMetaphorFinalProps = z.object({
  showCostLabel: z.boolean().default(true),
  showParticles: z.boolean().default(true),
  showGlow: z.boolean().default(true),
});

export const defaultSockMetaphorFinalProps: z.infer<typeof SockMetaphorFinalProps> = {
  showCostLabel: true,
  showParticles: true,
  showGlow: true,
};

export type SockMetaphorFinalPropsType = z.infer<typeof SockMetaphorFinalProps>;
