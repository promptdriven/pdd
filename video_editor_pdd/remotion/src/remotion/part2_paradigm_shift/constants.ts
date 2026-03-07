import { z } from "zod";

export const SECTION_FPS = 30;
export const SECTION_DURATION_SECONDS = 195.79;
export const SECTION_DURATION_FRAMES = Math.round(
  SECTION_FPS * SECTION_DURATION_SECONDS,
);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
  VISUAL_00_START: s2f(0.0),
  VISUAL_00_END: s2f(8.0),
  VISUAL_01_START: s2f(8.0),
  VISUAL_01_END: s2f(55.0),
  VISUAL_02_START: s2f(55.0),
  VISUAL_02_END: s2f(85.0),
  VISUAL_03_START: s2f(85.0),
  VISUAL_03_END: s2f(115.0),
  VISUAL_04_START: s2f(115.0),
  VISUAL_04_END: s2f(145.0),
  VISUAL_05_START: s2f(145.0),
  VISUAL_05_END: s2f(195.79),
  VISUAL_06_START: s2f(0.0),
  VISUAL_06_END: s2f(195.79),
};

export const VISUAL_SEQUENCE = [
  {
    start: BEATS.VISUAL_00_START,
    end: BEATS.VISUAL_00_END,
    id: "01_title_card",
    desc: "Part 2 Paradigm Shift title card",
  },
  {
    start: BEATS.VISUAL_01_START,
    end: BEATS.VISUAL_01_END,
    id: "03_mold_production_infographic",
    desc: "Mold production infographic showing conveyor belt with part stream and defect traceback",
  },
  {
    start: BEATS.VISUAL_02_START,
    end: BEATS.VISUAL_02_END,
    id: "05_value_migration_diagram",
    desc: "Value migration diagram illustrating shift from manual to specification-driven development",
  },
  {
    start: BEATS.VISUAL_03_START,
    end: BEATS.VISUAL_03_END,
    id: "07_hdl_timeline",
    desc: "HDL timeline showing evolution of hardware description languages as specification paradigm",
  },
  {
    start: BEATS.VISUAL_04_START,
    end: BEATS.VISUAL_04_END,
    id: "08_split_manual_vs_specification",
    desc: "Split view comparing manual construction vs specification across textiles, plastics, semiconductors",
  },
  {
    start: BEATS.VISUAL_05_START,
    end: BEATS.VISUAL_05_END,
    id: "10_prompt_mold_visualization",
    desc: "Prompt mold visualization showing how prompts shape generated output",
  },
  {
    start: BEATS.VISUAL_06_START,
    end: BEATS.VISUAL_06_END,
    id: "11_subtitle_track",
    desc: "Word-by-word subtitle track spanning full Part 2 narration",
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
