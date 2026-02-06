import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part4PrecisionTradeoffPropsType } from "./constants";
import { BothGenerateFinal, defaultBothGenerateFinalProps } from "../45-BothGenerateFinal";
import { CrossSectionIntro, defaultCrossSectionIntroProps } from "../21-CrossSectionIntro";
import { GraphAnimateCurve, defaultGraphAnimateCurveProps } from "../42-GraphAnimateCurve";
import { PromptGovernsCode, defaultPromptGovernsCodeProps } from "../33-PromptGovernsCode";

export const Part4PrecisionTradeoff: React.FC<Part4PrecisionTradeoffPropsType> = () => {
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
      <Audio src={staticFile("part4_precision_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: Veo clip - Grandmother: not stupid → economics rational */}
      {activeVisual === 0 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 1: GraphAnimateCurve - You: not stupid → economics changed → became darni */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <GraphAnimateCurve {...defaultGraphAnimateCurveProps} />
        </Sequence>
      )}

      {/* Visual 2: BothGenerateFinal - Transition beat */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <BothGenerateFinal {...defaultBothGenerateFinalProps} />
        </Sequence>
      )}

      {/* Visual 3: CrossSectionIntro - Doesn't eliminate → elevates → mold designers → ma */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <CrossSectionIntro {...defaultCrossSectionIntroProps} />
        </Sequence>
      )}

      {/* Visual 4: PromptGovernsCode - PDD developers → specification level → not writing */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <PromptGovernsCode {...defaultPromptGovernsCodeProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
