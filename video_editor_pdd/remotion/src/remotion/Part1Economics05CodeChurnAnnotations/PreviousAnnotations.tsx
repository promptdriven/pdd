import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

/**
 * Placeholder "previous annotations" (GitHub / Uplevel) that were on screen
 * before this section begins. They fade to 30% opacity over the first 60 frames.
 */

const PREV_FADE_END = 60;
const COLOR_PREV_BORDER = "#3B82F6";

interface PrevAnnotationBoxProps {
  posX: number;
  posY: number;
  label: string;
  subLabel: string;
  opacity: number;
}

const PrevAnnotationBox: React.FC<PrevAnnotationBoxProps> = ({
  posX,
  posY,
  label,
  subLabel,
  opacity,
}) => (
  <div
    style={{
      position: "absolute",
      left: posX,
      top: posY,
      width: 320,
      background: "#1E293B",
      border: `1.5px solid ${COLOR_PREV_BORDER}`,
      borderRadius: 8,
      padding: "10px 16px",
      opacity,
    }}
  >
    <div
      style={{
        fontFamily: "Inter, sans-serif",
        fontSize: 16,
        fontWeight: 700,
        color: COLOR_PREV_BORDER,
        lineHeight: 1.3,
      }}
    >
      {label}
    </div>
    <div
      style={{
        fontFamily: "Inter, sans-serif",
        fontSize: 11,
        fontWeight: 400,
        color: "#94A3B8",
        marginTop: 2,
        lineHeight: 1.3,
      }}
    >
      {subLabel}
    </div>
  </div>
);

export const PreviousAnnotations: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, PREV_FADE_END], [1.0, 0.3], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.quad),
  });

  return (
    <>
      {/* Connector lines for previous annotations */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none", opacity }}
      >
        <line x1={1320} y1={230} x2={1050} y2={350} stroke={COLOR_PREV_BORDER} strokeWidth={1} opacity={0.4} />
        <line x1={1320} y1={310} x2={1080} y2={420} stroke={COLOR_PREV_BORDER} strokeWidth={1} opacity={0.4} />
      </svg>

      <PrevAnnotationBox
        posX={1320}
        posY={200}
        label="GitHub survey: 'more code'"
        subLabel="(Uplevel, 2024)"
        opacity={opacity}
      />
      <PrevAnnotationBox
        posX={1320}
        posY={280}
        label="PR volume: +25%"
        subLabel="(GitHub, 2024)"
        opacity={opacity}
      />
    </>
  );
};

export default PreviousAnnotations;
