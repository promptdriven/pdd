import React from "react";
import { useCurrentFrame, interpolate, spring, Easing } from "remotion";
import {
  CALLOUT_BG,
  CALLOUT_BORDER_RADIUS,
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  CONNECTING_LINE_COLOR,
  FADE_TO_BLACK_START,
  FADE_TO_BLACK_END,
} from "./constants";

interface CalloutPillProps {
  text: string;
  textColor: string;
  fontSize: number;
  /** Frame at which this callout starts (relative to parent Sequence) */
  appearFrame: number;
  animDuration: number;
  /** Position offset from crossover point */
  offsetX: number;
  offsetY: number;
  /** Slide direction: positive = from right, negative = from left */
  slideFromX: number;
}

export const CalloutPill: React.FC<CalloutPillProps> = ({
  text,
  textColor,
  fontSize,
  appearFrame,
  animDuration,
  offsetX,
  offsetY,
  slideFromX,
}) => {
  const frame = useCurrentFrame();

  if (frame < appearFrame) return null;

  const localFrame = frame - appearFrame;

  // Spring-based slide animation
  const springProgress = spring({
    frame: localFrame,
    fps: 30,
    config: { damping: 14, stiffness: 160 },
  });

  // Opacity fade in
  const opacity = interpolate(localFrame, [0, animDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Fade out before black
  const fadeOut = interpolate(
    frame,
    [FADE_TO_BLACK_START, FADE_TO_BLACK_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  const translateX = slideFromX * (1 - springProgress);

  // Pill position (relative to crossover)
  const pillX = CROSSOVER_PX_X + offsetX;
  const pillY = CROSSOVER_PX_Y + offsetY;

  // Connecting dotted line — draws from pill toward crossover
  const lineProgress = interpolate(
    localFrame,
    [animDuration * 0.5, animDuration * 1.2],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  // Line endpoint: from pill edge toward crossover
  const lineStartX = pillX + (offsetX > 0 ? -20 : 20);
  const lineStartY = pillY;
  const lineEndX =
    lineStartX + (CROSSOVER_PX_X - lineStartX) * lineProgress;
  const lineEndY =
    lineStartY + (CROSSOVER_PX_Y - lineStartY) * lineProgress;

  return (
    <>
      {/* Connecting dotted line */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          opacity: opacity * fadeOut,
        }}
      >
        <line
          x1={lineStartX}
          y1={lineStartY}
          x2={lineEndX}
          y2={lineEndY}
          stroke={CONNECTING_LINE_COLOR}
          strokeWidth={1.5}
          strokeDasharray="4 4"
          opacity={0.5}
        />
      </svg>

      {/* Frosted glass pill */}
      <div
        style={{
          position: "absolute",
          left: pillX - (offsetX > 0 ? 0 : 480),
          top: pillY - 24,
          transform: `translateX(${translateX}px)`,
          opacity: opacity * fadeOut,
          background: CALLOUT_BG,
          backdropFilter: "blur(8px)",
          WebkitBackdropFilter: "blur(8px)",
          borderRadius: CALLOUT_BORDER_RADIUS,
          padding: "16px 24px",
          border: `1px solid rgba(148, 163, 184, 0.2)`,
          whiteSpace: "nowrap",
        }}
      >
        <span
          style={{
            color: textColor,
            fontSize,
            fontFamily: "Inter, sans-serif",
            fontWeight: 700,
            lineHeight: 1,
          }}
        >
          {text}
        </span>
      </div>
    </>
  );
};

export default CalloutPill;
