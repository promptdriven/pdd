import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  Sequence,
  useCurrentFrame,
  interpolate,
  spring,
  useVideoConfig,
  Easing,
} from "remotion";
import { AccentBar } from "./AccentBar";
import { PrimaryStat } from "./PrimaryStat";
import { SecondaryStat } from "./SecondaryStat";
import { SourceAttribution } from "./SourceAttribution";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  CARD_X,
  CARD_Y,
  CARD_WIDTH,
  CARD_HEIGHT,
  CARD_BG,
  CARD_BORDER_RADIUS,
  ACCENT_RED,
  ACCENT_BAR_WIDTH,
  SLIDE_DISTANCE,
  CARD_SLIDE_IN_END,
  CARD_SLIDE_OUT_START,
  CARD_SLIDE_OUT_END,
  BORDER_PULSE_SPEED,
  BORDER_PULSE_MIN,
  BORDER_PULSE_MAX,
} from "./constants";

export const defaultPart1Economics06StatCalloutUplevelProps = {};

export const Part1Economics06StatCalloutUplevel: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card slide in: spring animation
  const slideInProgress = spring({
    frame,
    fps,
    config: { damping: 14, stiffness: 170 },
    durationInFrames: CARD_SLIDE_IN_END,
  });

  // Card slide out: easeInCubic
  const slideOutProgress = interpolate(
    frame,
    [CARD_SLIDE_OUT_START, CARD_SLIDE_OUT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  // Combine slide: in from left, hold, out to left
  const translateX =
    frame < CARD_SLIDE_OUT_START
      ? interpolate(slideInProgress, [0, 1], [-SLIDE_DISTANCE, 0])
      : interpolate(slideOutProgress, [0, 1], [0, -SLIDE_DISTANCE]);

  // Opacity: fade in then fade out
  const opacity =
    frame < CARD_SLIDE_OUT_START
      ? interpolate(slideInProgress, [0, 1], [0, 1])
      : interpolate(slideOutProgress, [0, 1], [1, 0]);

  // Border pulse: sinusoidal red glow
  const borderAlpha = interpolate(
    Math.sin(frame * BORDER_PULSE_SPEED),
    [-1, 1],
    [BORDER_PULSE_MIN, BORDER_PULSE_MAX]
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      </AbsoluteFill>

      {/* Stat callout card */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div
          style={{
            position: "absolute",
            left: CARD_X,
            top: CARD_Y,
            width: CARD_WIDTH,
            height: CARD_HEIGHT,
            backgroundColor: CARD_BG,
            backdropFilter: "blur(12px)",
            WebkitBackdropFilter: "blur(12px)",
            borderRadius: CARD_BORDER_RADIUS,
            border: `1px solid rgba(239, 68, 68, ${borderAlpha})`,
            boxShadow: `0 0 20px rgba(239, 68, 68, ${borderAlpha * 0.3}), 0 8px 32px rgba(0, 0, 0, 0.4)`,
            transform: `translateX(${translateX}px)`,
            opacity,
            overflow: "hidden",
          }}
        >
          {/* Red accent bar */}
          <AccentBar />

          {/* Card content */}
          <div
            style={{
              position: "absolute",
              left: ACCENT_BAR_WIDTH + 40,
              top: 40,
              right: 40,
              bottom: 40,
              display: "flex",
              flexDirection: "column",
              justifyContent: "center",
            }}
          >
            <PrimaryStat />
            <SecondaryStat />
            <SourceAttribution />
          </div>
        </div>
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics06StatCalloutUplevel;
