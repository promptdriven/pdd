import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CHECKMARK_COLOR,
  CHECKMARK_SIZE,
  EQUIV_LABEL_COLOR,
  EQUIV_LABEL_OPACITY,
  EQUIV_LINE_OPACITY,
  UI_FONT,
  UI_FONT_SIZE,
  COL_1_X,
  COL_2_X,
  COL_3_X,
  CHECKMARK_Y,
  CHECKMARK_POP_START,
  CHECKMARK_POP_DURATION,
  CHECKMARK_STAGGER,
  EQUIV_LABEL_START,
  EQUIV_LABEL_END,
  DASHED_LINE_START,
  DASHED_LINE_END,
} from "./constants";

const COLUMNS = [COL_1_X, COL_2_X, COL_3_X];

export const EquivalenceOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < CHECKMARK_POP_START) return null;

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [EQUIV_LABEL_START, EQUIV_LABEL_END],
    [0, EQUIV_LABEL_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Dashed line progress
  const lineProgress = interpolate(
    frame,
    [DASHED_LINE_START, DASHED_LINE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  return (
    <>
      {/* Checkmarks */}
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
        style={{ position: "absolute", left: 0, top: 0, pointerEvents: "none" }}
      >
        {COLUMNS.map((cx, i) => {
          const popStart = CHECKMARK_POP_START + i * CHECKMARK_STAGGER;
          const popEnd = popStart + CHECKMARK_POP_DURATION;

          // Back easing approximation: overshoot then settle
          const rawScale = interpolate(
            frame,
            [popStart, popEnd],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          // Manual back easing: overshoot to ~1.15 then settle to 1
          const t = rawScale;
          const overshoot = 1.5;
          const scale = t < 1
            ? t * t * ((overshoot + 1) * t - overshoot)
            : 1;
          const finalScale = Math.max(0, scale);

          return (
            <g
              key={`check-${i}`}
              transform={`translate(${cx}, ${CHECKMARK_Y}) scale(${finalScale})`}
            >
              {/* Circle background */}
              <circle
                cx={0}
                cy={0}
                r={CHECKMARK_SIZE / 2}
                fill={CHECKMARK_COLOR}
                opacity={0.15}
              />
              {/* Checkmark path */}
              <path
                d={`M ${-CHECKMARK_SIZE * 0.25} ${0} L ${-CHECKMARK_SIZE * 0.05} ${CHECKMARK_SIZE * 0.2} L ${CHECKMARK_SIZE * 0.3} ${-CHECKMARK_SIZE * 0.2}`}
                fill="none"
                stroke={CHECKMARK_COLOR}
                strokeWidth={2.5}
                strokeLinecap="round"
                strokeLinejoin="round"
              />
            </g>
          );
        })}

        {/* Dashed connecting line */}
        {lineProgress > 0 && (
          <line
            x1={COL_1_X}
            y1={CHECKMARK_Y}
            x2={COL_1_X + (COL_3_X - COL_1_X) * lineProgress}
            y2={CHECKMARK_Y}
            stroke={CHECKMARK_COLOR}
            strokeWidth={1}
            strokeDasharray="6 4"
            opacity={EQUIV_LINE_OPACITY}
          />
        )}
      </svg>

      {/* "Functionally equivalent" label */}
      {labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: CHECKMARK_Y + CHECKMARK_SIZE / 2 + 8,
            width: CANVAS_WIDTH,
            textAlign: "center",
            fontFamily: UI_FONT,
            fontSize: UI_FONT_SIZE,
            color: EQUIV_LABEL_COLOR,
            opacity: labelOpacity,
            letterSpacing: "1px",
            pointerEvents: "none",
          }}
        >
          Functionally equivalent
        </div>
      )}
    </>
  );
};

export default EquivalenceOverlay;
