import { z } from "zod";

// Video specs
export const FADE_TO_BLACK_FPS = 30;
export const FADE_TO_BLACK_DURATION_SECONDS = 5;
export const FADE_TO_BLACK_DURATION_FRAMES =
  FADE_TO_BLACK_FPS * FADE_TO_BLACK_DURATION_SECONDS;
export const FADE_TO_BLACK_WIDTH = 1920;
export const FADE_TO_BLACK_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Fade to black
  FADE_START: 0,
  FADE_END: 45,

  // Title appears
  TITLE_START: 45,
  TITLE_END: 80,

  // URL appears
  URL_START: 85,
  URL_END: 110,

  // Install command appears
  INSTALL_START: 100,
  INSTALL_END: 125,

  // Hold
  HOLD_START: 125,
};

// Color palette
export const COLORS = {
  SCENE_BG: "#1a1a2e",
  BLACK: "#000000",
};

// Props schema
export const FadeToBlackProps = z.object({
  showInstall: z.boolean().default(true),
});

export const defaultFadeToBlackProps: z.infer<typeof FadeToBlackProps> = {
  showInstall: true,
};

export type FadeToBlackPropsType = z.infer<typeof FadeToBlackProps>;
