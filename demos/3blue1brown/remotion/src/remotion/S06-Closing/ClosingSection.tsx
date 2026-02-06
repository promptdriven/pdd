import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, ClosingSectionPropsType } from "./constants";
import { CodeOutputMoldGlows, defaultCodeOutputMoldGlowsProps } from "../38-CodeOutputMoldGlows";
import { ThreeComponents, defaultThreeComponentsProps } from "../37-ThreeComponents";

export const ClosingSection: React.FC<ClosingSectionPropsType> = () => {
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
      <Audio src={staticFile("closing_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: CodeOutputMoldGlows - Mental shift: socks cheap, code cheap */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 1: ThreeComponents - Prompts encode intent, tests, grounding */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <ThreeComponents {...defaultThreeComponentsProps} />
        </Sequence>
      )}

      {/* Visual 2: CodeOutputMoldGlows - Code disposable, mold is what matters */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
