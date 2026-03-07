import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 21.0;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(5.0),
  VISUAL_01_START: s2f(5.0),
  VISUAL_01_END: s2f(11.0),
  VISUAL_02_START: s2f(11.0),
  VISUAL_02_END: s2f(15.0),
  VISUAL_03_START: s2f(15.0),
  VISUAL_03_END: s2f(21.0),
  VISUAL_04_START: s2f(0.0),
  VISUAL_04_END: s2f(21.0),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "01_title_card",
    desc: "Closing title card with section header",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "03_stat_callout_roi",
    desc: "ROI stat callout — 3–5× faster iteration with generation",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "05_split_darning_vs_molding",
    desc: "Split view comparing darning cost growth vs molding flat cost",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "07_cta_card",
    desc: "Call-to-action card with PDD logo and URL",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "08_subtitle_track",
    desc: "Word-by-word subtitle track for closing narration",
  },
];

export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
