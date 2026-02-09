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
import { CompleteSystem, defaultCompleteSystemProps } from "../48-CompleteSystem";
import { DeveloperRegenerates, defaultDeveloperRegeneratesProps } from "../49-DeveloperRegenerates";
import { FadeToBlack, defaultFadeToBlackProps } from "../50-FadeToBlack";
import { SockMetaphorFinal, defaultSockMetaphorFinalProps } from "../51-SockMetaphorFinal";

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
    <AbsoluteFill style={{ backgroundColor: "#1a1a2e" }}>
      {/* Narration audio */}
      <Audio src={staticFile("closing_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}

      {/* Visual 0: CompleteSystem — "So here's the mental shift" */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <CompleteSystem {...defaultCompleteSystemProps} />
        </Sequence>
      )}

      {/* Visual 1: Sock Metaphor Final - "You don't patch socks because socks got cheap" */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <SockMetaphorFinal {...defaultSockMetaphorFinalProps} />
        </Sequence>
      )}

      {/* Visual 2: DeveloperRegenerates — "Code just got that cheap" */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <DeveloperRegenerates {...defaultDeveloperRegeneratesProps} />
        </Sequence>
      )}

      {/* Visual 3: ThreeComponents (triangle) — "Prompts encode intent..." */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <ThreeComponents {...defaultThreeComponentsProps} />
        </Sequence>
      )}

      {/* Visual 4: CodeOutputMoldGlows — "Code is generated verified and disposable" */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 5: CodeOutputMoldGlows — "The code is just plastic, the mold is what matters" */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}

      {/* Visual 6: FadeToBlack — title card */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <FadeToBlack {...defaultFadeToBlackProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
