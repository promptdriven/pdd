import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 21.0;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(8.0),
  VISUAL_01_START: s2f(8.0),
  VISUAL_01_END: s2f(14.0),
  VISUAL_02_START: s2f(17.0),
  VISUAL_02_END: s2f(21.0),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "closing_split_darning_vs_molding",
    desc: "Split view comparing darning cost growth vs molding flat cost",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "closing_stat_callout_roi",
    desc: "3-5x faster iteration with generation, zero residual debt",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "closing_title_card",
    desc: "Title card introducing the closing section",
  },
];

export const ClosingSectionProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultClosingSectionProps: z.infer<typeof ClosingSectionProps> = {
  showTitle: true,
};

export type ClosingSectionPropsType = z.infer<typeof ClosingSectionProps>;
