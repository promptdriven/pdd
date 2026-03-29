import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BACKGROUND_COLOR,
  DURATION_FRAMES,
  CROSSFADE_START,
  CROSSFADE_DUR,
} from "./constants";
import { PromptBlock } from "./PromptBlock";
import { CodeBlockDisplay } from "./CodeBlockDisplay";
import { RatioLabel } from "./RatioLabel";
import { ContextWindowComparison } from "./ContextWindow";

export const defaultPart3MoldParts13PromptRatioProps = {};

export const Part3MoldParts13PromptRatio: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 fades out as phase 2 fades in
  const phase1Opacity = interpolate(
    frame,
    [CROSSFADE_START, CROSSFADE_START + CROSSFADE_DUR],
    [1, 0],
    {
      easing: Easing.inOut(Easing.cubic),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* ── Phase 1: Prompt vs Code Size ── */}
      <Sequence from={0} durationInFrames={CROSSFADE_START + CROSSFADE_DUR}>
        <AbsoluteFill style={{ opacity: phase1Opacity }}>
          {/* Prompt block - fades in at frame 0 */}
          <PromptBlock />

          {/* Code block - fades in at frame 30 */}
          <CodeBlockDisplay />

          {/* Ratio label - animates in at frame 90 */}
          <RatioLabel />
        </AbsoluteFill>
      </Sequence>

      {/* ── Phase 2: Context Window Comparison ── */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <ContextWindowComparison />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldParts13PromptRatio;
