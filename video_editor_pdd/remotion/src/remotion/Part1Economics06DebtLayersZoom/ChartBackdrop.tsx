import React from "react";

/**
 * Renders a simplified version of the code cost chart backdrop that the camera
 * zooms into. Shows grid lines, axes, year labels, and a shaded debt trapezoid.
 * This fades out as the zoom progresses.
 */

interface ChartBackdropProps {
  /** Overall opacity for the chart (fades as zoom progresses) */
  opacity: number;
  /** Chart region bounds */
  chartLeft: number;
  chartTop: number;
  chartWidth: number;
  chartHeight: number;
  /** Debt area shape params */
  debtAreaX: number;
  debtAreaWidth: number;
  debtAreaYTop: number;
  debtAreaYBottom: number;
  /** Colors */
  debtColor: string;
  debtOpacity: number;
  axisColor: string;
  axisOpacity: number;
  gridLineOpacity: number;
  /** Year labels */
  yearLabels: string[];
  fontFamily: string;
}

const ChartBackdrop: React.FC<ChartBackdropProps> = ({
  opacity,
  chartLeft,
  chartTop,
  chartWidth,
  chartHeight,
  debtAreaX,
  debtAreaWidth,
  debtAreaYTop,
  debtAreaYBottom,
  debtColor,
  debtOpacity,
  axisColor,
  axisOpacity,
  gridLineOpacity,
  yearLabels,
  fontFamily,
}) => {
  const chartRight = chartLeft + chartWidth;
  const chartBottom = chartTop + chartHeight;

  // Generate vertical grid lines for each year
  const gridLines = yearLabels.map((_, i) => {
    const x = chartLeft + (i / (yearLabels.length - 1)) * chartWidth;
    return x;
  });

  // Generate the debt area as a polygon (trapezoid shape)
  // It starts narrow on the left (earlier years, less debt) and widens to the right
  const debtPath = [
    `${debtAreaX},${debtAreaYBottom}`, // bottom-left
    `${debtAreaX},${debtAreaYBottom - 40}`, // top-left (thin)
    `${debtAreaX + debtAreaWidth * 0.3},${debtAreaYTop + 180}`, // mid-top
    `${debtAreaX + debtAreaWidth * 0.6},${debtAreaYTop + 80}`, // growing
    `${debtAreaX + debtAreaWidth},${debtAreaYTop}`, // top-right (thickest)
    `${debtAreaX + debtAreaWidth},${debtAreaYBottom}`, // bottom-right
  ].join(" ");

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        opacity,
      }}
    >
      <svg width={1920} height={1080}>
        {/* Grid lines */}
        {gridLines.map((x, i) => (
          <line
            key={`grid-${i}`}
            x1={x}
            y1={chartTop}
            x2={x}
            y2={chartBottom}
            stroke={axisColor}
            strokeOpacity={gridLineOpacity}
            strokeWidth={1}
          />
        ))}

        {/* Horizontal grid lines */}
        {[0, 0.25, 0.5, 0.75, 1].map((frac, i) => {
          const y = chartTop + frac * chartHeight;
          return (
            <line
              key={`hgrid-${i}`}
              x1={chartLeft}
              y1={y}
              x2={chartRight}
              y2={y}
              stroke={axisColor}
              strokeOpacity={gridLineOpacity}
              strokeWidth={1}
            />
          );
        })}

        {/* Axes */}
        <line
          x1={chartLeft}
          y1={chartBottom}
          x2={chartRight}
          y2={chartBottom}
          stroke={axisColor}
          strokeOpacity={axisOpacity}
          strokeWidth={2}
        />
        <line
          x1={chartLeft}
          y1={chartTop}
          x2={chartLeft}
          y2={chartBottom}
          stroke={axisColor}
          strokeOpacity={axisOpacity}
          strokeWidth={2}
        />

        {/* Debt area (shaded trapezoid) */}
        <polygon
          points={debtPath}
          fill={debtColor}
          fillOpacity={debtOpacity}
        />

        {/* Simulated "generate" curve (upper boundary of debt) */}
        <polyline
          points={`${debtAreaX},${debtAreaYBottom - 40} ${debtAreaX + debtAreaWidth * 0.3},${debtAreaYTop + 180} ${debtAreaX + debtAreaWidth * 0.6},${debtAreaYTop + 80} ${debtAreaX + debtAreaWidth},${debtAreaYTop}`}
          fill="none"
          stroke="#3B82F6"
          strokeOpacity={0.4}
          strokeWidth={2}
        />

        {/* Simulated "patch" curve (lower boundary) */}
        <line
          x1={debtAreaX}
          y1={debtAreaYBottom}
          x2={debtAreaX + debtAreaWidth}
          y2={debtAreaYBottom}
          stroke="#22C55E"
          strokeOpacity={0.3}
          strokeWidth={2}
        />
      </svg>

      {/* Year labels */}
      {yearLabels.map((label, i) => {
        const x = chartLeft + (i / (yearLabels.length - 1)) * chartWidth;
        return (
          <div
            key={label}
            style={{
              position: "absolute",
              left: x,
              top: chartBottom + 12,
              transform: "translateX(-50%)",
              fontFamily,
              fontSize: 12,
              color: axisColor,
              opacity: axisOpacity,
            }}
          >
            {label}
          </div>
        );
      })}

      {/* Chart title */}
      <div
        style={{
          position: "absolute",
          left: chartLeft,
          top: chartTop - 40,
          fontFamily,
          fontSize: 14,
          color: "#FFFFFF",
          opacity: 0.5,
          letterSpacing: "0.05em",
        }}
      >
        CODE COST: GENERATE vs. PATCH
      </div>
    </div>
  );
};

export default ChartBackdrop;
