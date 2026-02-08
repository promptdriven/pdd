import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, ClosingSectionPropsType } from "./constants";
import { CodeOutputMoldGlows, defaultCodeOutputMoldGlowsProps } from "../38-CodeOutputMoldGlows";
import { ThreeComponents, defaultThreeComponentsProps } from "../37-ThreeComponents";
import { CompleteSystem, defaultCompleteSystemProps } from "../48-CompleteSystem";
import { DeveloperRegenerates, defaultDeveloperRegeneratesProps } from "../49-DeveloperRegenerates";
import { FadeToBlack, defaultFadeToBlackProps } from "../50-FadeToBlack";

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

  // Cost label for sock video overlay (spec 6.2)
  // Fades in at ~1s into the veo clip, fades out at ~3s
  const costLabelLocalFrame = frame - BEATS.VISUAL_01_START;
  const costLabelOpacity = interpolate(
    costLabelLocalFrame,
    [15, 30, 60, 90],
    [0, 0.6, 0.6, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

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

      {/* Visual 1: Veo clip + "$0.50" cost label overlay */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("07_split_screen_sepia.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
            {/* Cost label overlay (spec 6.2) */}
            <div
              style={{
                position: "absolute",
                right: 280,
                top: 200,
                opacity: costLabelOpacity,
                fontFamily: "JetBrains Mono, monospace",
                fontSize: 18,
                color: "rgba(255, 255, 255, 0.6)",
              }}
            >
              $0.50
            </div>
          </AbsoluteFill>
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
