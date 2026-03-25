import {
  buildChartPath,
  computeSeriesBounds,
  type SeriesEntry,
} from "../remotion/src/remotion/_shared/chart-utils";

describe("GeneratedContractVisual chart helpers", () => {
  it("uses shared bounds across chart series instead of normalizing each line independently", () => {
    const series: SeriesEntry[] = [
      {
        label: "Flat",
        color: "#EF4444",
        points: [
          { x: 2020, y: 35 },
          { x: 2021, y: 35 },
          { x: 2022, y: 34 },
          { x: 2023, y: 34 },
          { x: 2024, y: 33 },
          { x: 2025, y: 32 },
        ],
      },
      {
        label: "Declining",
        color: "#4ADE80",
        points: [
          { x: 2020, y: 35 },
          { x: 2021, y: 28 },
          { x: 2022, y: 22 },
          { x: 2023, y: 15 },
          { x: 2024, y: 12 },
          { x: 2025, y: 10 },
        ],
      },
    ];

    const bounds = computeSeriesBounds(series);
    expect(bounds).toEqual({
      minX: 2020,
      maxX: 2025,
      minY: 10,
      maxY: 35,
    });

    const flatPath = buildChartPath(series[0].points, 1000, 500, bounds);
    const yValues = flatPath
      .split(/[ML]/)
      .map((segment) => segment.trim())
      .filter(Boolean)
      .map((segment) => Number(segment.split(/\s+/)[1]));

    expect(yValues[0]).toBeCloseTo(0, 3);
    expect(yValues[yValues.length - 1]).toBeCloseTo(60, 3);
  });
});
