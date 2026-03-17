// ShadedAreas.tsx — Green (pre-crossing) and red (post-crossing) shaded zones
import React from 'react';
import { CHART, COLORS, OPACITIES, Y_RANGE } from './constants';

interface DataPoint {
  x: number;
  y: number;
}

interface ShadedAreasProps {
  /** Rising line data points */
  risingData: DataPoint[];
  /** Falling line data points */
  fallingData: DataPoint[];
  /** X-axis range */
  xRange: [number, number];
  /** Crossing year (x position of intersection) */
  crossingYear: number;
  /** Post-crossing area label */
  postLabel: string;
  /** Opacity of the entire group */
  opacity: number;
}

const mapX = (x: number, xRange: [number, number]): number => {
  const frac = (x - xRange[0]) / (xRange[1] - xRange[0]);
  return CHART.left + frac * CHART.width;
};

const mapY = (y: number): number => {
  return CHART.top + CHART.height - (y / Y_RANGE.max) * CHART.height;
};

/**
 * Interpolate y value at a given x between two data arrays.
 */
const interpY = (data: DataPoint[], x: number): number => {
  for (let i = 0; i < data.length - 1; i++) {
    if (x >= data[i].x && x <= data[i + 1].x) {
      const t = (x - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
};

export const ShadedAreas: React.FC<ShadedAreasProps> = ({
  risingData,
  fallingData,
  xRange,
  crossingYear,
  postLabel,
  opacity,
}) => {
  // Build polygon for the area between the two lines
  // Pre-crossing: green zone (falling > rising → sock cost > labor cost)
  // Post-crossing: red zone (rising > falling → labor cost > sock cost)

  const crossX = mapX(crossingYear, xRange);
  const crossYRising = interpY(risingData, crossingYear);
  const crossYPx = mapY(crossYRising);

  // Sample x positions for the shaded areas
  const preSamples: number[] = [];
  for (
    let x = xRange[0];
    x <= crossingYear;
    x += (xRange[1] - xRange[0]) / 80
  ) {
    preSamples.push(x);
  }
  preSamples.push(crossingYear);

  const postSamples: number[] = [crossingYear];
  for (
    let x = crossingYear + (xRange[1] - xRange[0]) / 80;
    x <= xRange[1];
    x += (xRange[1] - xRange[0]) / 80
  ) {
    postSamples.push(x);
  }
  postSamples.push(xRange[1]);

  // Pre-crossing polygon: top = falling line, bottom = rising line
  const preTop = preSamples.map(
    (x) => `${mapX(x, xRange)},${mapY(interpY(fallingData, x))}`,
  );
  const preBottom = [...preSamples]
    .reverse()
    .map((x) => `${mapX(x, xRange)},${mapY(interpY(risingData, x))}`);
  const prePoly = [...preTop, ...preBottom].join(' ');

  // Post-crossing polygon: top = rising line, bottom = falling line
  const postTop = postSamples.map(
    (x) => `${mapX(x, xRange)},${mapY(interpY(risingData, x))}`,
  );
  const postBottom = [...postSamples]
    .reverse()
    .map((x) => `${mapX(x, xRange)},${mapY(interpY(fallingData, x))}`);
  const postPoly = [...postTop, ...postBottom].join(' ');

  // Position for the post-crossing label: midpoint of post-crossing zone
  const postMidX = (crossX + mapX(xRange[1], xRange)) / 2;
  const postMidY = crossYPx + 60;

  return (
    <div style={{ position: 'absolute', inset: 0, opacity }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Green pre-crossing zone */}
        <polygon
          points={prePoly}
          fill={COLORS.greenZone}
          fillOpacity={OPACITIES.greenZone}
        />
        {/* Red post-crossing zone */}
        <polygon
          points={postPoly}
          fill={COLORS.redZone}
          fillOpacity={OPACITIES.redZone}
        />
      </svg>

      {/* Post-crossing label */}
      <div
        style={{
          position: 'absolute',
          left: postMidX,
          top: postMidY,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          color: COLORS.redZone,
          opacity: 0.6,
          whiteSpace: 'nowrap',
          fontStyle: 'italic',
        }}
      >
        {postLabel}
      </div>
    </div>
  );
};

export default ShadedAreas;
