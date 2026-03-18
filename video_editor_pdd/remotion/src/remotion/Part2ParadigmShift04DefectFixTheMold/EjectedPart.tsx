import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  PART_W,
  PART_H,
  PART_COLOR,
  DEFECT_RED,
  EJECT_START,
  DISSOLVE_START,
  DISSOLVE_END,
} from "./constants";

/**
 * A plastic part that ejects from the mold cavity.
 * Shows a notched rectangular part sliding downward.
 * At DISSOLVE_START it fades out with red particle scatter.
 */
export const EjectedPart: React.FC<{
  fromY: number;
  toY: number;
  showDefect?: boolean;
  id?: string;
}> = ({ fromY, toY, showDefect = true }) => {
  const frame = useCurrentFrame();

  // Ejection slide
  const ejectY = interpolate(
    frame,
    [EJECT_START, EJECT_START + 20],
    [fromY, toY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Dissolve at DISSOLVE_START
  const dissolveOpacity = showDefect
    ? interpolate(
        frame,
        [DISSOLVE_START, DISSOLVE_END],
        [1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
      )
    : 1;

  // Only show after ejection starts
  if (frame < EJECT_START) return null;

  const x = MOLD_CENTER_X - PART_W / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: ejectY,
        width: PART_W,
        height: PART_H,
        opacity: dissolveOpacity,
      }}
    >
      <svg width={PART_W} height={PART_H} viewBox={`0 0 ${PART_W} ${PART_H}`}>
        {/* Main part body with notch */}
        <path
          d={`M 0 0 L ${PART_W - 12} 0 L ${PART_W} 8 L ${PART_W} ${PART_H} L 0 ${PART_H} Z`}
          fill={PART_COLOR}
          fillOpacity={0.5}
        />
        {/* Defective edge highlight */}
        {showDefect && frame >= 60 && (
          <line
            x1={PART_W - 12}
            y1={0}
            x2={PART_W}
            y2={8}
            stroke={DEFECT_RED}
            strokeWidth={3}
            strokeOpacity={
              0.4 +
              0.3 * Math.sin(((frame - 60) / 10) * Math.PI * 2)
            }
          />
        )}
      </svg>

      {/* Red particle scatter during dissolve */}
      {showDefect && frame >= DISSOLVE_START && frame <= DISSOLVE_END + 10 && (
        <DissolveParticles
          frame={frame}
          startFrame={DISSOLVE_START}
          width={PART_W}
          height={PART_H}
        />
      )}
    </div>
  );
};

const DissolveParticles: React.FC<{
  frame: number;
  startFrame: number;
  width: number;
  height: number;
}> = ({ frame, startFrame, width, height }) => {
  const progress = Math.min(1, (frame - startFrame) / 30);
  const particles = Array.from({ length: 12 }, (_, i) => {
    const angle = (i / 12) * Math.PI * 2 + i * 0.5;
    const dist = progress * (30 + (i % 3) * 20);
    const px = width / 2 + Math.cos(angle) * dist;
    const py = height / 2 + Math.sin(angle) * dist;
    const opacity = Math.max(0, 1 - progress * 1.3);
    const size = 3 + (i % 3);
    return (
      <div
        key={i}
        style={{
          position: "absolute",
          left: px - size / 2,
          top: py - size / 2,
          width: size,
          height: size,
          borderRadius: "50%",
          backgroundColor: DEFECT_RED,
          opacity: opacity * 0.6,
        }}
      />
    );
  });
  return <>{particles}</>;
};

export default EjectedPart;
