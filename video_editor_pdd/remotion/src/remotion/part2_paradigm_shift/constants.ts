import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 195.79;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(195.79),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "part2_paradigm_shift_main",
    desc: "Paradigm shift section with background video, narration audio, and subtitles",
  },
];

export const Part2ParadigmShiftProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart2ParadigmShiftProps: z.infer<
  typeof Part2ParadigmShiftProps
> = {
  showTitle: true,
};

export type Part2ParadigmShiftPropsType = z.infer<
  typeof Part2ParadigmShiftProps
>;
