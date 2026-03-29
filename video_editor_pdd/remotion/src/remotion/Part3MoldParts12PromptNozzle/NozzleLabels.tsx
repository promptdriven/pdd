import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  NOZZLE_COLOR,
  MOLD_CENTER_X,
  NOZZLE_Y,
  NOZZLE_HEIGHT,
  NOZZLE_LABELS,
  PHASE_LABELS_START,
} from "./constants";

interface LabelEntry {
  text: string;
  direction: "left" | "right" | "top";
  dx: number;
  dy: number;
}

const LABEL_STAGGER = 15; // frames between each label
const LABEL_ANIM_DURATION = 20;
const FLOAT_DISTANCE = 40;

export const NozzleLabels: React.FC = () => {
  const frame = useCurrentFrame();

  const anchorX = MOLD_CENTER_X;
  const anchorY = NOZZLE_Y + NOZZLE_HEIGHT / 2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {NOZZLE_LABELS.map((label: LabelEntry, i: number) => {
        const labelStart = PHASE_LABELS_START + i * LABEL_STAGGER;
        const progress = interpolate(
          frame,
          [labelStart, labelStart + LABEL_ANIM_DURATION],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
        );

        const targetX = anchorX + label.dx;
        const targetY = anchorY + label.dy;

        // Float in from the label's direction
        let startOffsetX = 0;
        let startOffsetY = 0;
        if (label.direction === "left") startOffsetX = -FLOAT_DISTANCE;
        if (label.direction === "right") startOffsetX = FLOAT_DISTANCE;
        if (label.direction === "top") startOffsetY = -FLOAT_DISTANCE;

        const currentX = targetX + startOffsetX * (1 - progress);
        const currentY = targetY + startOffsetY * (1 - progress);

        // Connector line from label to nozzle anchor
        const lineOpacity = progress * 0.3;

        return (
          <g key={label.text} opacity={progress}>
            {/* Connector line */}
            <line
              x1={anchorX}
              y1={anchorY}
              x2={currentX}
              y2={currentY}
              stroke={NOZZLE_COLOR}
              strokeWidth={1}
              opacity={lineOpacity}
            />
            {/* Small dot at line end */}
            <circle
              cx={currentX}
              cy={currentY}
              r={3}
              fill={NOZZLE_COLOR}
              opacity={lineOpacity}
            />
            {/* Label text */}
            <text
              x={currentX}
              y={currentY - 10}
              fill={NOZZLE_COLOR}
              fontSize={16}
              fontFamily="Inter, sans-serif"
              fontWeight={600}
              textAnchor="middle"
              dominantBaseline="auto"
            >
              {label.text}
            </text>
          </g>
        );
      })}
    </svg>
  );
};
