import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { BlueprintGrid } from "./BlueprintGrid";
import { TypeWriterLine } from "./TypeWriterLine";
import { ConnectingLines } from "./ConnectingLines";
import {
  BG_COLOR,
  FONT_FAMILY,
  SUBTITLE_FONT_SIZE,
  SUBTITLE_COLOR,
  SUBTITLE_OPACITY,
  SUBTITLE_Y,
  CENTER_X,
  LINE1_Y,
  LINE2_Y,
  LINE1_SEGMENTS,
  LINE2_SEGMENTS,
  LINE1_START,
  LINE2_START,
  CONNECTING_START,
  SUBTITLE_START,
  SUBTITLE_FADE_DURATION,
  FADEOUT_START,
  FADEOUT_DURATION,
} from "./constants";

export const defaultPart2ParadigmShift14SynopsysPddEquivalenceProps = {};

export const Part2ParadigmShift14SynopsysPddEquivalence: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Global fade out (frames 330-390) ───────────────────────────────
  const globalOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // ── Subtitle fade in (relative to SUBTITLE_START) ──────────────────
  const subtitleOpacity = interpolate(
    frame,
    [SUBTITLE_START, SUBTITLE_START + SUBTITLE_FADE_DURATION],
    [0, SUBTITLE_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: globalOpacity,
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Line 1: Synopsys — types in from frame 0 */}
      <TypeWriterLine
        segments={LINE1_SEGMENTS}
        y={LINE1_Y}
        startFrame={LINE1_START}
      />

      {/* Line 2: PDD — types in from frame 60 */}
      <TypeWriterLine
        segments={LINE2_SEGMENTS}
        y={LINE2_Y}
        startFrame={LINE2_START}
      />

      {/* Connecting dashed lines — draw from frame 120 over 30 frames */}
      <ConnectingLines startFrame={CONNECTING_START} drawDuration={30} />

      {/* Subtitle: "Same architecture." — fades in from frame 180 */}
      <div
        style={{
          position: "absolute",
          top: SUBTITLE_Y,
          left: 0,
          width: CENTER_X * 2,
          textAlign: "center",
          fontFamily: FONT_FAMILY,
          fontSize: SUBTITLE_FONT_SIZE,
          fontStyle: "italic",
          color: SUBTITLE_COLOR,
          opacity: subtitleOpacity,
          lineHeight: 1.4,
        }}
      >
        Same architecture.
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift14SynopsysPddEquivalence;
