import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  BLUE,
  LABEL_COLOR,
  ANNOTATION_LABEL_SIZE,
  LABOR_COST_DATA,
  SOCK_COST_DATA,
  CROSSING_X,
  SHADED_AREA_START,
  SHADED_AREA_END,
  ANNOTATION_FADE_START,
  ANNOTATION_FADE_END,
} from "./constants";

const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

const yToPixel = (y: number): number =>
  MARGIN_TOP + CHART_HEIGHT - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

/** Linearly interpolate a data series */
const lerpData = (
  data: { x: number; y: number }[],
  targetX: number
): number => {
  if (targetX <= data[0].x) return data[0].y;
  if (targetX >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    if (targetX >= data[i].x && targetX <= data[i + 1].x) {
      const t = (targetX - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
};

export const ShadedArea: React.FC = () => {
  const frame = useCurrentFrame();

  const areaOpacity = interpolate(
    frame,
    [SHADED_AREA_START, SHADED_AREA_END],
    [0, 0.06],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const annotationOpacity = interpolate(
    frame,
    [ANNOTATION_FADE_START, ANNOTATION_FADE_END],
    [0, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < SHADED_AREA_START) return null;

  // Build the shaded polygon between the two lines, from crossing to X_MAX
  // Upper line = labor cost (higher y value after crossing), lower = sock cost
  const step = 0.5;
  const upperPoints: string[] = [];
  const lowerPoints: string[] = [];

  for (let x = CROSSING_X; x <= X_MAX; x += step) {
    const laborY = lerpData(LABOR_COST_DATA, x);
    const sockY = lerpData(SOCK_COST_DATA, x);
    upperPoints.push(`${xToPixel(x)},${yToPixel(laborY)}`);
    lowerPoints.push(`${xToPixel(x)},${yToPixel(sockY)}`);
  }
  // Final point at X_MAX
  upperPoints.push(`${xToPixel(X_MAX)},${yToPixel(lerpData(LABOR_COST_DATA, X_MAX))}`);
  lowerPoints.push(`${xToPixel(X_MAX)},${yToPixel(lerpData(SOCK_COST_DATA, X_MAX))}`);

  // Polygon: upper points left-to-right, then lower points right-to-left
  const polygonPoints = [
    ...upperPoints,
    ...lowerPoints.reverse(),
  ].join(" ");

  // Center of shaded area for annotation placement
  const midX = (CROSSING_X + X_MAX) / 2;
  const midLaborY = lerpData(LABOR_COST_DATA, midX);
  const midSockY = lerpData(SOCK_COST_DATA, midX);
  const centerPx = xToPixel(midX);
  const centerPy = (yToPixel(midLaborY) + yToPixel(midSockY)) / 2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Shaded area between lines */}
      <polygon
        points={polygonPoints}
        fill={BLUE}
        fillOpacity={areaOpacity}
      />

      {/* "Darning is irrational" annotation */}
      {annotationOpacity > 0 && (
        <text
          x={centerPx}
          y={centerPy}
          textAnchor="middle"
          fill={LABEL_COLOR}
          fillOpacity={annotationOpacity}
          fontSize={ANNOTATION_LABEL_SIZE}
          fontStyle="italic"
          fontFamily="'Inter', sans-serif"
        >
          Darning is irrational
        </text>
      )}
    </svg>
  );
};

export default ShadedArea;
