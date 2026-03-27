import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART_TOP,
  CHART_BOTTOM,
  MARKER_LINE_COLOR,
  LABEL_COLOR,
  BLUE_LINE_COLOR,
  DATE_MARKERS,
  GENERATE_COST_DATA,
  dataToPixelX,
  dataToPixelY,
  type DataPoint,
} from './constants';

/** Linearly interpolate the Y value for a given X from a data series */
function interpolateY(data: DataPoint[], xVal: number): number {
  if (xVal <= data[0].x) return data[0].y;
  if (xVal >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    if (xVal >= data[i].x && xVal <= data[i + 1].x) {
      const t = (xVal - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
}

interface DateMarkersProps {
  /** Frame at which blue line begins drawing (markers appear as line passes) */
  blueLineStart: number;
  /** Frame at which blue line finishes drawing */
  blueLineEnd: number;
}

export const DateMarkers: React.FC<DateMarkersProps> = ({
  blueLineStart,
  blueLineEnd,
}) => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {DATE_MARKERS.map((marker) => {
        const px = dataToPixelX(marker.year);
        const yVal = interpolateY(GENERATE_COST_DATA, marker.year);
        const py = dataToPixelY(yVal);

        // Figure out what fraction through the blue line draw this marker's year appears
        const xFrac =
          (marker.year - GENERATE_COST_DATA[0].x) /
          (GENERATE_COST_DATA[GENERATE_COST_DATA.length - 1].x -
            GENERATE_COST_DATA[0].x);
        const markerAppearFrame =
          blueLineStart + xFrac * (blueLineEnd - blueLineStart);

        const markerOpacity = interpolate(
          frame,
          [markerAppearFrame, markerAppearFrame + 20],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) },
        );

        if (markerOpacity <= 0) return null;

        return (
          <g key={marker.label} opacity={markerOpacity}>
            {/* Vertical dashed line */}
            <line
              x1={px}
              y1={CHART_TOP}
              x2={px}
              y2={CHART_BOTTOM}
              stroke={MARKER_LINE_COLOR}
              strokeWidth={1}
              strokeDasharray="6 4"
              opacity={0.5}
            />

            {/* Dot on the blue line */}
            <circle cx={px} cy={py} r={4} fill={BLUE_LINE_COLOR} />

            {/* Label above */}
            <text
              x={px}
              y={CHART_TOP - 12}
              fill={LABEL_COLOR}
              fontSize={12}
              fontFamily="Inter, sans-serif"
              fontWeight={400}
              opacity={0.8}
              textAnchor="middle"
            >
              {marker.label}
            </text>

            {/* Year below label */}
            <text
              x={px}
              y={CHART_TOP - 0}
              fill={LABEL_COLOR}
              fontSize={10}
              fontFamily="Inter, sans-serif"
              fontWeight={400}
              opacity={0.5}
              textAnchor="middle"
            >
              ({Math.floor(marker.year)})
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export default DateMarkers;
