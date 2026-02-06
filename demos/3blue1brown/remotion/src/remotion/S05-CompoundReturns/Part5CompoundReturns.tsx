import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part5CompoundReturnsPropsType } from "./constants";
import { CodeOutputMoldGlows, defaultCodeOutputMoldGlowsProps } from "../38-CodeOutputMoldGlows";
import { ThreeComponents, defaultThreeComponentsProps } from "../37-ThreeComponents";

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
      
      {/* Visual 0: CodeOutputMoldGlows - Code still there → live in specification → verifie */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 1: CodeOutputMoldGlows - Transition */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 2: CodeOutputMoldGlows - Mental shift: don't patch socks → cheap → prompts  */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 3: ThreeComponents - Tests preserve behavior → grounding maintains styl */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <ThreeComponents {...defaultThreeComponentsProps} />
        </Sequence>
      )}

      {/* Visual 4: CodeOutputMoldGlows - Code generated, verified, disposable */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
