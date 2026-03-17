import React from "react";
import { AbsoluteFill, Sequence, useCurrentFrame, interpolate } from "remotion";
import { BG_COLOR, TOTAL_FRAMES, FADE_IN_START, FADE_IN_END } from "./constants";
import { CodebaseGrid } from "./CodebaseGrid";
import { ContextWindow } from "./ContextWindow";
import { CoverageCounter } from "./CoverageCounter";
import { BlockHighlights } from "./BlockHighlights";
import { InsetGraph } from "./InsetGraph";

export const defaultPart1Economics05ContextWindowShrinkProps = {};

/**
 * Part1Economics05ContextWindowShrink — The AI Blindspot
 *
 * A spatial visualization showing how a fixed-size context window
 * becomes increasingly inadequate as a codebase grows.
 *
 * Animation sequence:
 * - Frame 0-30: Fade in from black
 * - Frame 30-90: 4x4 grid appears with context window covering ~80%
 * - Frame 90-310: Grid morphs through 8x8, 16x16, 32x32 while window stays fixed
 * - Frame 360-480: Red/green highlights show irrelevant vs needed code
 * - Frame 480-600: Inset performance degradation graph draws in
 * - Frame 600-900: Hold with subtle pulse effects
 *
 * 900 frames (30s at 30fps)
 */
export const Part1Economics05ContextWindowShrink: React.FC = () => {
  const frame = useCurrentFrame();

  // Initial fade-in from dark
  const sceneOpacity = interpolate(
    frame,
    [FADE_IN_START, FADE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          opacity: sceneOpacity,
        }}
      >
        {/* Codebase grid — morphs from 4x4 to 32x32 */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <CodebaseGrid />
        </Sequence>

        {/* Fixed-size context window overlay */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <ContextWindow />
        </Sequence>

        {/* Coverage percentage counter */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <CoverageCounter />
        </Sequence>

        {/* Red/green block highlights */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <BlockHighlights />
        </Sequence>

        {/* Inset performance degradation graph */}
        <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
          <InsetGraph />
        </Sequence>
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics05ContextWindowShrink;
