import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
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
      
      {/* Visual 0: CodeOutputMoldGlows - So here's the mental shift */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 1: Veo clip - Don't patch socks, socks got cheap, irrational */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <AbsoluteFill>
            <OffthreadVideo
              src={staticFile("07_split_screen_sepia.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 2: CodeOutputMoldGlows - Code just got that cheap */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 3: ThreeComponents - Prompts encode intent, tests preserve, grounding m */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <ThreeComponents {...defaultThreeComponentsProps} />
        </Sequence>
      )}

      {/* Visual 4: CodeOutputMoldGlows - Code is generated verified and disposable */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 5: CodeOutputMoldGlows - The code is just plastic, the mold is what matters */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
