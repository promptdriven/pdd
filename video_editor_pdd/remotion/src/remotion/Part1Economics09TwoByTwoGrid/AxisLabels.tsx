import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface AxisLabelsProps {
  gridLeft: number;
  gridTop: number;
  gridSize: number;
  cellSize: number;
  xLabels: readonly [string, string];
  yLabels: readonly [string, string];
  labelColor: string;
  labelSize: number;
  fadeStart: number;
  fadeEnd: number;
}

export const AxisLabels: React.FC<AxisLabelsProps> = ({
  gridLeft,
  gridTop,
  gridSize,
  cellSize,
  xLabels,
  yLabels,
  labelColor,
  labelSize,
  fadeStart,
  fadeEnd,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const gridRight = gridLeft + gridSize;
  const gridBottom = gridTop + gridSize;
  const gridCenterX = gridLeft + gridSize / 2;
  const gridCenterY = gridTop + gridSize / 2;

  const arrowLength = 60;

  return (
    <div style={{ position: "absolute", top: 0, left: 0, width: 1920, height: 1080, opacity }}>
      {/* X-axis: left label (Greenfield) */}
      <div
        style={{
          position: "absolute",
          left: gridLeft + cellSize / 2,
          top: gridBottom + 24,
          transform: "translateX(-50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: labelSize,
          fontWeight: 400,
          color: labelColor,
          whiteSpace: "nowrap",
        }}
      >
        {xLabels[0]}
      </div>

      {/* X-axis: right label (Brownfield) */}
      <div
        style={{
          position: "absolute",
          left: gridLeft + cellSize + cellSize / 2,
          top: gridBottom + 24,
          transform: "translateX(-50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: labelSize,
          fontWeight: 400,
          color: labelColor,
          whiteSpace: "nowrap",
        }}
      >
        {xLabels[1]}
      </div>

      {/* X-axis arrow */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          <linearGradient id="xArrowGrad" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={labelColor} stopOpacity={0.1} />
            <stop offset="100%" stopColor={labelColor} stopOpacity={0.5} />
          </linearGradient>
          <marker
            id="xArrowHead"
            markerWidth="8"
            markerHeight="6"
            refX="8"
            refY="3"
            orient="auto"
          >
            <polygon points="0 0, 8 3, 0 6" fill={labelColor} opacity={0.5} />
          </marker>
        </defs>
        <line
          x1={gridCenterX - arrowLength}
          y1={gridBottom + 14}
          x2={gridCenterX + arrowLength}
          y2={gridBottom + 14}
          stroke="url(#xArrowGrad)"
          strokeWidth={1.5}
          markerEnd="url(#xArrowHead)"
        />
      </svg>

      {/* Y-axis: top label (In-Distribution) */}
      <div
        style={{
          position: "absolute",
          left: gridLeft - 24,
          top: gridTop + cellSize / 2,
          transform: "translate(-100%, -50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: labelSize,
          fontWeight: 400,
          color: labelColor,
          whiteSpace: "nowrap",
        }}
      >
        {yLabels[0]}
      </div>

      {/* Y-axis: bottom label (Out-of-Distribution) */}
      <div
        style={{
          position: "absolute",
          left: gridLeft - 24,
          top: gridTop + cellSize + cellSize / 2,
          transform: "translate(-100%, -50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: labelSize,
          fontWeight: 400,
          color: labelColor,
          whiteSpace: "nowrap",
        }}
      >
        {yLabels[1]}
      </div>

      {/* Y-axis arrow */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          <linearGradient id="yArrowGrad" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor={labelColor} stopOpacity={0.1} />
            <stop offset="100%" stopColor={labelColor} stopOpacity={0.5} />
          </linearGradient>
          <marker
            id="yArrowHead"
            markerWidth="6"
            markerHeight="8"
            refX="3"
            refY="8"
            orient="auto"
          >
            <polygon points="0 0, 6 0, 3 8" fill={labelColor} opacity={0.5} />
          </marker>
        </defs>
        <line
          x1={gridLeft - 14}
          y1={gridCenterY - arrowLength}
          x2={gridLeft - 14}
          y2={gridCenterY + arrowLength}
          stroke="url(#yArrowGrad)"
          strokeWidth={1.5}
          markerEnd="url(#yArrowHead)"
        />
      </svg>
    </div>
  );
};

export default AxisLabels;
