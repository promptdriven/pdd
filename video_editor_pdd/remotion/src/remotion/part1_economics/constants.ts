import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 382.176;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(68.64),
  VISUAL_00_END: s2f(73.64),
  VISUAL_01_START: s2f(83.82),
  VISUAL_01_END: s2f(88.82),
  VISUAL_02_START: s2f(115.58),
  VISUAL_02_END: s2f(120.58),
  VISUAL_03_START: s2f(255.68),
  VISUAL_03_END: s2f(265.68),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "Part1EconomicsStatCalloutGithub",
    desc: "GitHub reports developers using Copilot accept nearly 30% of suggestions",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "Part1EconomicsStatCalloutUplevel",
    desc: "Uplevel found AI-assisted engineers write 26% more code per week",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "Part1EconomicsStatCalloutGitclear",
    desc: "GitClear analysis of 150M lines shows code churn has doubled",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "Part1EconomicsSplitPerceptionVsReality",
    desc: "Developers feel 30% more productive but quality metrics tell opposite story",
  },
];

export const Part1EconomicsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart1EconomicsProps: z.infer<typeof Part1EconomicsProps> = {
  showTitle: true,
};

export type Part1EconomicsPropsType = z.infer<typeof Part1EconomicsProps>;
