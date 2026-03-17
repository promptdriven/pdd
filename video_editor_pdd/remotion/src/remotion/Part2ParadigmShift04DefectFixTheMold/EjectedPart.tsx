import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PART_WIDTH,
  PART_HEIGHT,
  PART_COLOR,
  PART_OPACITY,
  MOLD_CENTER_X,
  PART_EJECT_FROM_Y,
  PART_EJECT_TO_Y,
  PART_EJECT_START,
  PART_EJECT_END,
  DEFECT_COLOR,
  DISSOLVE_START,
  DISSOLVE_END,
} from "./constants";

interface EjectedPartProps {
  showDefect: boolean;
  dissolve: boolean;
}

export const EjectedPart: React.FC<EjectedPartProps> = ({ showDefect, dissolve }) => {
  const frame = useCurrentFrame();

  // Eject animation
  const ejectY = interpolate(
    frame,
    [PART_EJECT_START, PART_EJECT_END],
    [PART_EJECT_FROM_Y, PART_EJECT_TO_Y],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Dissolve animation
  const dissolveOpacity = dissolve
    ? interpolate(
        frame,
        [DISSOLVE_START, DISSOLVE_END],
        [1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
      )
    : 1;

  // Dissolve scale (shrink slightly)
  const dissolveScale = dissolve
    ? interpolate(
        frame,
        [DISSOLVE_START, DISSOLVE_END],
        [1, 0.6],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
      )
    : 1;

  // Don't render after fully dissolved
  if (dissolve && frame >= DISSOLVE_END) return null;

  const partX = MOLD_CENTER_X - PART_WIDTH / 2;
  const notchWidth = 12;
  const notchHeight = 15;

  return (
    <div
      style={{
        position: "absolute",
        left: partX - 10,
        top: ejectY - PART_HEIGHT / 2 - 10,
        width: PART_WIDTH + 20,
        height: PART_HEIGHT + 20,
        opacity: dissolveOpacity,
        transform: `scale(${dissolveScale})`,
        transformOrigin: "center center",
      }}
    >
      <svg
        width={PART_WIDTH + 20}
        height={PART_HEIGHT + 20}
        viewBox={`0 0 ${PART_WIDTH + 20} ${PART_HEIGHT + 20}`}
      >
        {/* Part shape with notch on right edge */}
        <path
          d={`
            M 10 10
            L ${PART_WIDTH + 10} 10
            L ${PART_WIDTH + 10} ${10 + (PART_HEIGHT - notchHeight) / 2}
            L ${PART_WIDTH + 10 - notchWidth} ${10 + PART_HEIGHT / 2}
            L ${PART_WIDTH + 10} ${10 + (PART_HEIGHT + notchHeight) / 2}
            L ${PART_WIDTH + 10} ${PART_HEIGHT + 10}
            L 10 ${PART_HEIGHT + 10}
            Z
          `}
          fill={PART_COLOR}
          fillOpacity={PART_OPACITY}
          stroke={PART_COLOR}
          strokeWidth={1}
          strokeOpacity={0.3}
        />

        {/* Defect highlight on right edge */}
        {showDefect && frame >= PART_EJECT_END && (
          <line
            x1={PART_WIDTH + 10 - notchWidth}
            y1={10 + (PART_HEIGHT - notchHeight) / 2 - 5}
            x2={PART_WIDTH + 10 - notchWidth}
            y2={10 + (PART_HEIGHT + notchHeight) / 2 + 5}
            stroke={DEFECT_COLOR}
            strokeWidth={3}
            strokeOpacity={0.8}
          />
        )}

        {/* Dissolve particles */}
        {dissolve && frame >= DISSOLVE_START && (
          <>
            {Array.from({ length: 8 }).map((_, i) => {
              const progress = interpolate(
                frame,
                [DISSOLVE_START, DISSOLVE_END],
                [0, 1],
                { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
              );
              const angle = (i / 8) * Math.PI * 2;
              const dist = progress * 30;
              const px = PART_WIDTH / 2 + 10 + Math.cos(angle) * dist;
              const py = PART_HEIGHT / 2 + 10 + Math.sin(angle) * dist;
              return (
                <circle
                  key={`particle-${i}`}
                  cx={px}
                  cy={py}
                  r={3 * (1 - progress)}
                  fill={DEFECT_COLOR}
                  fillOpacity={0.6 * (1 - progress)}
                />
              );
            })}
          </>
        )}
      </svg>
    </div>
  );
};
