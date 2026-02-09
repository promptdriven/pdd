import { z } from "zod";

// Video specs
export const FORMAL_VERIFICATION_FPS = 30;
export const FORMAL_VERIFICATION_DURATION_SECONDS = 25;
export const FORMAL_VERIFICATION_DURATION_FRAMES =
  FORMAL_VERIFICATION_FPS * FORMAL_VERIFICATION_DURATION_SECONDS;
export const FORMAL_VERIFICATION_WIDTH = 1920;
export const FORMAL_VERIFICATION_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  DIVIDER_START: 0,
  DIVIDER_END: 60,
  LEFT_HEADER_START: 0,
  LEFT_HEADER_END: 45,
  LEFT_TEXT_START: 90,
  LEFT_TEXT_END: 180,
  RIGHT_HEADER_START: 180,
  RIGHT_HEADER_END: 225,
  RIGHT_TEXT_START: 270,
  RIGHT_TEXT_END: 360,
  MATH_START: 360,
  MATH_END: 450,
  LABEL_START: 450,
  LABEL_END: 540,
  PULSE_START: 510,
  HOLD_START: 540,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  TEAL: "#2AA198",
  TEAL_DIM: "#1a7a75",
  MUTED_WHITE: "#B0B0C0",
  BRIGHT_WHITE: "#FFFFFF",
  GREEN_CHECK: "#5AAA6E",
  MATH_GRAY: "#8090A0",
};

// Text content
export const TEXT = {
  LEFT_HEADER: "Synopsys Formality",
  RIGHT_HEADER: "PDD + Z3",
  LEFT_PREFIX: "SMT solver proves",
  LEFT_RELATION: "RTL ≡ gates",
  LEFT_QUALIFIER: "for all inputs",
  RIGHT_PREFIX: "SMT solver proves",
  RIGHT_RELATION: "code satisfies spec",
  RIGHT_QUALIFIER: "for all inputs",
  BOTTOM_LABEL: "Mathematical proof, not testing.",
  LEFT_MATH: "∀x ∈ Inputs: Synth(RTL, x) ≡ Impl(gates, x)",
  RIGHT_MATH: "∀x ∈ Inputs: Code(x) ⊨ Spec(x)",
};

// Layout positions
export const LAYOUT = {
  DIVIDER_TOP: 80,
  DIVIDER_HEIGHT: 700,
  PANEL_PADDING_H: 80,
  PANEL_PADDING_V: 100,
  ICON_SIZE: 80,
  BOTTOM_LABEL_Y: 100,
};

// Props schema
export const FormalVerificationProps = z.object({
  showOverlay: z.boolean().default(true),
});

export const defaultFormalVerificationProps: z.infer<typeof FormalVerificationProps> = {
  showOverlay: true,
};

export type FormalVerificationPropsType = z.infer<typeof FormalVerificationProps>;
