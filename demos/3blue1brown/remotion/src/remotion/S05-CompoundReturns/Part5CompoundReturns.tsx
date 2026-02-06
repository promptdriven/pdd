import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part5CompoundReturnsPropsType } from "./constants";
import { BothGenerateFinal, defaultBothGenerateFinalProps } from "../45-BothGenerateFinal";
import { CodeOutputMoldGlows, defaultCodeOutputMoldGlowsProps } from "../38-CodeOutputMoldGlows";
import { GraphAnimateCurve, defaultGraphAnimateCurveProps } from "../42-GraphAnimateCurve";
import { ShortPromptTests, defaultShortPromptTestsProps } from "../44-ShortPromptTests";

export const Part5CompoundReturns: React.FC<Part5CompoundReturnsPropsType> = () => {
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
      <Audio src={staticFile("part5_compound_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: GraphAnimateCurve - Patch returns: local, linear, sub-linear */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <GraphAnimateCurve {...defaultGraphAnimateCurveProps} />
        </Sequence>
      )}

      {/* Visual 1: ShortPromptTests - PDD returns: test constrains all future, permanent */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <ShortPromptTests {...defaultShortPromptTestsProps} />
        </Sequence>
      )}

      {/* Visual 2: BothGenerateFinal - Compound vs diminishing returns */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <BothGenerateFinal {...defaultBothGenerateFinalProps} />
        </Sequence>
      )}

      {/* Visual 3: Veo clip - Great-grandmother/you: economics was rational */}
      {activeVisual === 3 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 4: CodeOutputMoldGlows - Economics changed, darning socks */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
