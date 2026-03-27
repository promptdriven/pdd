import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  AMBER,
  NOZZLE_LABELS,
  MOLD_CENTER_X,
  NOZZLE_TIP_Y,
  PHASE_LABELS_START,
  PHASE_LABELS_STAGGER,
} from "./constants";

export const NozzleLabels: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {NOZZLE_LABELS.map((label, i) => {
        const labelStart = PHASE_LABELS_START + i * PHASE_LABELS_STAGGER;
        const labelEnd = labelStart + 20;

        const progress = interpolate(frame, [labelStart, labelEnd], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        });

        // Float-in offsets based on direction
        let offsetX = 0;
        let offsetY = 0;
        if (label.direction === "left") offsetX = -40;
        if (label.direction === "right") offsetX = 40;
        if (label.direction === "top") offsetY = -40;

        const currentX = label.x + offsetX * (1 - progress);
        const currentY = label.y + offsetY * (1 - progress);

        // Connector line endpoints: from label to nozzle center-top
        const nozzleConnectX = MOLD_CENTER_X;
        const nozzleConnectY = NOZZLE_TIP_Y - 10;

        // Line draw progress (starts slightly after label appears)
        const lineProgress = interpolate(
          frame,
          [labelStart + 5, labelEnd + 5],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        // Compute the line end point based on lineProgress
        const lineEndX =
          currentX +
          (nozzleConnectX - currentX) * lineProgress;
        const lineEndY =
          currentY +
          18 +
          (nozzleConnectY - (currentY + 18)) * lineProgress;

        return (
          <g key={label.text} opacity={progress}>
            {/* Connector line */}
            <line
              x1={currentX + (label.direction === "right" ? 0 : label.text.length * 8)}
              y1={currentY + 18}
              x2={lineEndX}
              y2={lineEndY}
              stroke={AMBER}
              strokeWidth={1}
              opacity={0.3}
            />
            {/* Label text */}
            <text
              x={currentX}
              y={currentY}
              fill={AMBER}
              fontFamily="Inter, sans-serif"
              fontSize={16}
              fontWeight={600}
              dominantBaseline="hanging"
            >
              {label.text}
            </text>
          </g>
        );
      })}
    </svg>
  );
};
