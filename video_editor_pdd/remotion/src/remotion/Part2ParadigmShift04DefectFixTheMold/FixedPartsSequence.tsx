import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  PART_WIDTH,
  PART_HEIGHT,
  PART_COLOR,
  PART_OPACITY,
  PART_EJECT_FROM_Y,
  CHECKMARK_COLOR,
  FIXED_PARTS_START,
  FIXED_PART_INTERVAL,
  FIXED_PART_COUNT,
  CHECKMARK_POP_DURATION,
  COUNTER_LABEL_X,
  COUNTER_LABEL_Y,
  COUNTER_LABEL_SIZE,
  COUNTER_FADE_START,
  COUNTER_FADE_END,
  FONT_FAMILY,
  FIXED_COLOR,
} from "./constants";

interface FixedPartProps {
  index: number;
  startFrame: number;
}

const FixedPart: React.FC<FixedPartProps> = ({ index, startFrame }) => {
  const frame = useCurrentFrame();

  if (frame < startFrame) return null;

  const localFrame = frame - startFrame;

  // Part ejects downward and stacks
  const stackY = PART_EJECT_FROM_Y + 130 + index * (PART_HEIGHT + 8);
  const ejectY = interpolate(
    localFrame,
    [0, 20],
    [PART_EJECT_FROM_Y, stackY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Checkmark pops in after part lands
  const checkScale = interpolate(
    localFrame,
    [20, 20 + CHECKMARK_POP_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.5)) }
  );

  const partX = MOLD_CENTER_X - PART_WIDTH / 2;
  const notchWidth = 12;
  const notchHeight = 15;

  return (
    <div
      style={{
        position: "absolute",
        left: partX - 10,
        top: ejectY - PART_HEIGHT / 2 - 10,
        width: PART_WIDTH + 40,
        height: PART_HEIGHT + 20,
      }}
    >
      <svg
        width={PART_WIDTH + 40}
        height={PART_HEIGHT + 20}
        viewBox={`0 0 ${PART_WIDTH + 40} ${PART_HEIGHT + 20}`}
      >
        {/* Part shape (no notch defect — it's fixed!) */}
        <path
          d={`
            M 10 10
            L ${PART_WIDTH + 10} 10
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

        {/* Green checkmark */}
        {localFrame >= 20 && (
          <g
            transform={`translate(${PART_WIDTH + 18}, ${PART_HEIGHT / 2 + 10}) scale(${checkScale})`}
          >
            <circle
              cx={0}
              cy={0}
              r={8}
              fill={CHECKMARK_COLOR}
              fillOpacity={0.15}
            />
            <polyline
              points="-5,0 -1,4 6,-4"
              fill="none"
              stroke={CHECKMARK_COLOR}
              strokeWidth={2}
              strokeLinecap="round"
              strokeLinejoin="round"
            />
          </g>
        )}
      </svg>
    </div>
  );
};

export const FixedPartsSequence: React.FC = () => {
  const frame = useCurrentFrame();

  // Counter label
  const counterOpacity = interpolate(
    frame,
    [COUNTER_FADE_START, COUNTER_FADE_END],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Count of visible fixed parts
  const visibleCount = Math.min(
    FIXED_PART_COUNT,
    Math.max(0, Math.floor((frame - FIXED_PARTS_START) / FIXED_PART_INTERVAL) + 1)
  );

  return (
    <>
      {/* Fixed parts ejecting one by one */}
      {Array.from({ length: FIXED_PART_COUNT }).map((_, i) => (
        <FixedPart
          key={`fixed-part-${i}`}
          index={i}
          startFrame={FIXED_PARTS_START + i * FIXED_PART_INTERVAL}
        />
      ))}

      {/* "All future parts: fixed" counter label */}
      {frame >= COUNTER_FADE_START && (
        <div
          style={{
            position: "absolute",
            left: COUNTER_LABEL_X,
            top: COUNTER_LABEL_Y,
            fontFamily: FONT_FAMILY,
            fontSize: COUNTER_LABEL_SIZE,
            color: FIXED_COLOR,
            opacity: counterOpacity,
            whiteSpace: "nowrap" as const,
            display: "flex",
            alignItems: "center",
            gap: 8,
          }}
        >
          {/* Small checkmark icons */}
          <svg width={16} height={16} viewBox="0 0 16 16">
            <circle cx={8} cy={8} r={7} fill={CHECKMARK_COLOR} fillOpacity={0.2} />
            <polyline
              points="4,8 7,11 12,5"
              fill="none"
              stroke={CHECKMARK_COLOR}
              strokeWidth={2}
              strokeLinecap="round"
              strokeLinejoin="round"
            />
          </svg>
          All future parts: fixed
        </div>
      )}
    </>
  );
};
