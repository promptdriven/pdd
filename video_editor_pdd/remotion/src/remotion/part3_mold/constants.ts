import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 280.73;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(5.0),
  VISUAL_01_START: s2f(21.0),
  VISUAL_01_END: s2f(26.0),
  VISUAL_02_START: s2f(25.72),
  VISUAL_02_END: s2f(30.72),
  VISUAL_03_START: s2f(40.82),
  VISUAL_03_END: s2f(45.82),
  VISUAL_04_START: s2f(207.3),
  VISUAL_04_END: s2f(212.3),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "Part3MoldTitleCard",
    desc: "Title card introducing Part 3: The Mold Has Three Parts",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "Part3MoldSplitPromptVsCode",
    desc: "Split view comparing prompt specification to generated code",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "Part3MoldStatCalloutCoderabbit",
    desc: "CodeRabbit stat: 1.7x more issues in AI-generated code",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "Part3MoldStatCalloutDora",
    desc: "DORA metrics: AI with tests yields delivery amplification",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "Part3MoldStatCalloutNlContext",
    desc: "41% improved code generation with natural language context",
  },
];

export const Part3MoldThreePartsProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPart3MoldThreePartsProps: z.infer<
  typeof Part3MoldThreePartsProps
> = {
  showTitle: true,
};

export type Part3MoldThreePartsPropsType = z.infer<
  typeof Part3MoldThreePartsProps
>;
