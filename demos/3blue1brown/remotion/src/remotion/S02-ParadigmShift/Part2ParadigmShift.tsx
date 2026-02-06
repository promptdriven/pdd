import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part2ParadigmShiftPropsType } from "./constants";
import { AddTestWall, defaultAddTestWallProps } from "../26-AddTestWall";
import { CrossSectionIntro, defaultCrossSectionIntroProps } from "../21-CrossSectionIntro";
import { MoldToPrompt, defaultMoldToPromptProps } from "../19-MoldToPrompt";
import { PromptGeneratesCode, defaultPromptGeneratesCodeProps } from "../20-PromptGeneratesCode";
import { RatchetTimelapse, defaultRatchetTimelapseProps } from "../28-RatchetTimelapse";
import { TraditionalVsPdd, defaultTraditionalVsPddProps } from "../29-TraditionalVsPdd";

export const Part2ParadigmShift: React.FC<Part2ParadigmShiftPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      {/* Narration audio */}
      <Audio src={staticFile("part2_paradigm_shift_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: Veo clip - Crafting vs molding: value in object vs specificat */}
      {activeVisual === 0 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("01_factory_floor.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 1: MoldToPrompt - PDD: prompt is your mold, code is plastic */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <MoldToPrompt {...defaultMoldToPromptProps} />
        </Sequence>
      )}

      {/* Visual 2: PromptGeneratesCode - Three components intro: precise → mold has three p */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <PromptGeneratesCode {...defaultPromptGeneratesCodeProps} />
        </Sequence>
      )}

      {/* Visual 3: CrossSectionIntro - Test capital: tests are walls → constraint → sees  */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <CrossSectionIntro {...defaultCrossSectionIntroProps} />
        </Sequence>
      )}

      {/* Visual 4: AddTestWall - Bug found: don't patch → add wall → permanent */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <AddTestWall {...defaultAddTestWallProps} />
        </Sequence>
      )}

      {/* Visual 5: RatchetTimelapse - Ratchet effect: tests accumulate → constrains all  */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START} durationInFrames={BEATS.VISUAL_05_END - BEATS.VISUAL_05_START}>
          <RatchetTimelapse {...defaultRatchetTimelapseProps} />
        </Sequence>
      )}

      {/* Visual 6: TraditionalVsPdd - Traditional vs PDD: bug fix one place vs everywher */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START} durationInFrames={BEATS.VISUAL_06_END - BEATS.VISUAL_06_START}>
          <TraditionalVsPdd {...defaultTraditionalVsPddProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
