import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  PART_W,
  PART_H,
  PART_COLOR,
  FIXED_GREEN,
  FIXED_PARTS_START,
  COUNTER_START,
} from "./constants";

const PART_COUNT = 5;
const PART_INTERVAL = 25; // frames between each part ejection
const EJECT_DURATION = 20;

// Stacking positions — parts fan out below the mold
const getStackPosition = (index: number) => {
  const baseX = MOLD_CENTER_X - PART_W / 2;
  const baseY = 710;
  const xOffset = (index - 2) * (PART_W + 15); // fan out horizontally
  const yOffset = index * 6; // slight vertical stagger
  return { x: baseX + xOffset, y: baseY + yOffset };
};

/**
 * Fixed parts ejecting from the corrected mold with green checkmarks.
 */
export const FixedParts: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < FIXED_PARTS_START) return null;

  const localFrame = frame - FIXED_PARTS_START;

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: "100%", height: "100%" }}>
      {Array.from({ length: PART_COUNT }, (_, i) => {
        const partStartFrame = i * PART_INTERVAL;
        const partLocalFrame = localFrame - partStartFrame;

        if (partLocalFrame < 0) return null;

        const stack = getStackPosition(i);

        // Eject from mold center down to stack position
        const ejectFromY = 650;
        const ejectY = interpolate(
          partLocalFrame,
          [0, EJECT_DURATION],
          [ejectFromY, stack.y],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        const ejectX = interpolate(
          partLocalFrame,
          [0, EJECT_DURATION],
          [MOLD_CENTER_X - PART_W / 2, stack.x],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        // Checkmark pops in after landing
        const checkScale = interpolate(
          partLocalFrame,
          [EJECT_DURATION, EJECT_DURATION + 10],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.back(1.5)),
          }
        );

        const partOpacity = interpolate(
          partLocalFrame,
          [0, 5],
          [0, 0.85],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );

        return (
          <div
            key={i}
            style={{
              position: "absolute",
              left: ejectX,
              top: ejectY,
              width: PART_W,
              height: PART_H,
            }}
          >
            {/* Part body */}
            <svg
              width={PART_W}
              height={PART_H}
              viewBox={`0 0 ${PART_W} ${PART_H}`}
            >
              <path
                d={`M 0 0 L ${PART_W - 12} 0 L ${PART_W} 8 L ${PART_W} ${PART_H} L 0 ${PART_H} Z`}
                fill={PART_COLOR}
                fillOpacity={partOpacity}
              />
            </svg>

            {/* Green checkmark */}
            {partLocalFrame >= EJECT_DURATION && (
              <svg
                width={24}
                height={24}
                viewBox="0 0 24 24"
                style={{
                  position: "absolute",
                  left: PART_W / 2 - 12,
                  top: PART_H / 2 - 12,
                  transform: `scale(${checkScale})`,
                  transformOrigin: "center center",
                }}
              >
                <circle
                  cx={12}
                  cy={12}
                  r={10}
                  fill={FIXED_GREEN}
                  fillOpacity={0.5}
                />
                <polyline
                  points="7,12 10,16 17,9"
                  fill="none"
                  stroke="#FFFFFF"
                  strokeWidth={2.5}
                  strokeLinecap="round"
                  strokeLinejoin="round"
                  strokeOpacity={1}
                />
              </svg>
            )}
          </div>
        );
      })}

      {/* "All future parts: fixed" counter label */}
      {frame >= COUNTER_START && (
        <CounterLabel frame={frame} />
      )}
    </div>
  );
};

const CounterLabel: React.FC<{ frame: number }> = ({ frame }) => {
  const localFrame = frame - COUNTER_START;

  const opacity = interpolate(localFrame, [0, 20], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Count of parts visible
  const partsVisible = Math.min(
    PART_COUNT,
    Math.floor((frame - FIXED_PARTS_START) / PART_INTERVAL) + 1
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 1400,
        top: 880,
        opacity,
        display: "flex",
        alignItems: "center",
        gap: 8,
      }}
    >
      {/* Small green checkmark icons */}
      {Array.from({ length: Math.min(partsVisible, 5) }, (_, i) => (
        <svg key={i} width={14} height={14} viewBox="0 0 14 14">
          <polyline
            points="3,7 5.5,10 11,4"
            fill="none"
            stroke={FIXED_GREEN}
            strokeWidth={1.5}
            strokeLinecap="round"
            strokeLinejoin="round"
            opacity={0.7}
          />
        </svg>
      ))}
      <span
        style={{
          fontSize: 14,
          fontFamily: "Inter, sans-serif",
          color: FIXED_GREEN,
          marginLeft: 4,
          whiteSpace: "nowrap",
        }}
      >
        All future parts: fixed
      </span>
    </div>
  );
};

export default FixedParts;
