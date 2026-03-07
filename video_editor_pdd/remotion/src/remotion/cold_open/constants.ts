import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 15.68;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(4.0),
  VISUAL_01_START: s2f(0.0),
  VISUAL_01_END: s2f(15.68),
  VISUAL_02_START: s2f(8.0),
  VISUAL_02_END: s2f(8.67),
  VISUAL_03_START: s2f(0.0),
  VISUAL_03_END: s2f(15.68),
  VISUAL_04_START: s2f(0.0),
  VISUAL_04_END: s2f(15.68),
  VISUAL_05_START: s2f(12.68),
  VISUAL_05_END: s2f(15.68),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "01_title_card",
    desc: "Title card with 'Why You're Still Darning Socks'",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "03_subtitle_track",
    desc: "Word-by-word subtitle track for cold open narration",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "05_crossfade_transition",
    desc: "Crossfade transition between wide and close-up shots",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "06_fade_bookends",
    desc: "Fade-in from black and fade-out to black over background video",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "07_monitor_glow_overlay",
    desc: "Animated monitor glow overlay with oscillating edge lights",
  },
  {
    start: BEATS.VISUAL_05_START,
    end: BEATS.VISUAL_05_END,
    id: "08_closing_question_card",
    desc: "Split-panel closing question: 'Why are we still patching?'",
  },
];

export const ColdOpenSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultColdOpenSectionProps: z.infer<typeof ColdOpenSectionProps> =
  {
    showTitle: true,
  };

export type ColdOpenSectionPropsType = z.infer<typeof ColdOpenSectionProps>;
