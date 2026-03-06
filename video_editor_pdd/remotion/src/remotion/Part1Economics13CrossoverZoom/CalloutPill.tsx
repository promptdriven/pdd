import React from "react";
import { useCurrentFrame, interpolate, spring } from "remotion";
import {
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  CALLOUT_BG,
  CONNECTING_LINE_COLOR,
  CALLOUT_A_SIZE,
  CALLOUT_B_SIZE,
  FADE_START,
  FADE_END,
} from "./constants";

interface CalloutPillProps {
  text: string;
  textColor: string;
  position: "top-right" | "bottom-left";
  appearFrame: number;
  slideDuration: number;
}

export const CalloutPill: React.FC<CalloutPillProps> = ({
  text,
  textColor,
  position,
  appearFrame,
  slideDuration,
}) => {
  const frame = useCurrentFrame();

  if (frame < appearFrame) return null;

  const localFrame = frame - appearFrame;

  // Spring-based slide
  const slideProgress = spring({
    frame: localFrame,
    fps: 30,
    config: { damping: 14, stiffness: 160 },
  });

  // Opacity: fade in over slideDuration, then hold, then fade with black overlay
  const opacity = interpolate(
    frame,
    [appearFrame, appearFrame + slideDuration, FADE_START, FADE_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const isTopRight = position === "top-right";
  const fontSize = isTopRight ? CALLOUT_A_SIZE : CALLOUT_B_SIZE;

  // Position callouts relative to crossover point
  const offsetX = isTopRight ? 180 : -180;
  const offsetY = isTopRight ? -160 : 160;
  const slideFromX = isTopRight ? 60 : -60;

  const pillX = CROSSOVER_PX_X + offsetX;
  const pillY = CROSSOVER_PX_Y + offsetY;

  const translateX = interpolate(slideProgress, [0, 1], [slideFromX, 0]);

  // Connecting dotted line from pill to crossover point
  const lineProgress = interpolate(
    frame,
    [appearFrame + slideDuration * 0.6, appearFrame + slideDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Anchor point on the pill closest to the crossover
  const lineStartX = isTopRight ? pillX - 20 : pillX + 320;
  const lineStartY = isTopRight ? pillY + 24 : pillY - 4;

  // Interpolated end point toward crossover
  const lineEndX = lineStartX + (CROSSOVER_PX_X - lineStartX) * lineProgress;
  const lineEndY = lineStartY + (CROSSOVER_PX_Y - lineStartY) * lineProgress;

  return (
    <>
      {/* Connecting dotted line */}
      {lineProgress > 0 && (
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            opacity: opacity * 0.5,
          }}
        >
          <line
            x1={lineStartX}
            y1={lineStartY}
            x2={lineEndX}
            y2={lineEndY}
            stroke={CONNECTING_LINE_COLOR}
            strokeWidth={1.5}
            strokeDasharray="6 4"
          />
        </svg>
      )}

      {/* Frosted glass pill */}
      <div
        style={{
          position: "absolute",
          left: pillX - (isTopRight ? 0 : 300),
          top: pillY - 20,
          transform: `translateX(${translateX}px)`,
          opacity,
          background: CALLOUT_BG,
          backdropFilter: "blur(8px)",
          WebkitBackdropFilter: "blur(8px)",
          borderRadius: 12,
          padding: "16px 24px",
          maxWidth: 420,
          border: `1px solid rgba(148, 163, 184, 0.2)`,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 700,
            fontSize,
            color: textColor,
            lineHeight: 1.3,
          }}
        >
          {text}
        </span>
      </div>
    </>
  );
};

export default CalloutPill;
