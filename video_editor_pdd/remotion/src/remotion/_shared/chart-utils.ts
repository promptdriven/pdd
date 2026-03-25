export type SeriesEntry = {
  label: string;
  color: string;
  points: { x: number; y: number }[];
  style?: string | null;
};

export type ChartBounds = {
  minX: number;
  maxX: number;
  minY: number;
  maxY: number;
};

export const computeSeriesBounds = (series: SeriesEntry[]): ChartBounds => {
  const points = series.flatMap((entry) => entry.points);
  if (points.length === 0) {
    return {
      minX: 0,
      maxX: 1,
      minY: 0,
      maxY: 1,
    };
  }

  return {
    minX: Math.min(...points.map((point) => point.x)),
    maxX: Math.max(...points.map((point) => point.x)),
    minY: Math.min(...points.map((point) => point.y)),
    maxY: Math.max(...points.map((point) => point.y)),
  };
};

export const buildChartPath = (
  points: { x: number; y: number }[],
  width: number,
  height: number,
  bounds?: ChartBounds
): string => {
  const resolvedBounds =
    bounds && Number.isFinite(bounds.minX) && Number.isFinite(bounds.maxX)
      ? bounds
      : computeSeriesBounds([
          {
            label: "Series",
            color: "#000000",
            points,
          },
        ]);
  const minX = resolvedBounds.minX;
  const maxX = resolvedBounds.maxX;
  const minY = resolvedBounds.minY;
  const maxY = resolvedBounds.maxY;
  const spanX = Math.max(1, maxX - minX);
  const spanY = Math.max(1, maxY - minY);

  return points
    .map((point, index) => {
      const x = ((point.x - minX) / spanX) * width;
      const y = height - ((point.y - minY) / spanY) * height;
      return `${index === 0 ? "M" : "L"} ${x.toFixed(1)} ${y.toFixed(1)}`;
    })
    .join(" ");
};
