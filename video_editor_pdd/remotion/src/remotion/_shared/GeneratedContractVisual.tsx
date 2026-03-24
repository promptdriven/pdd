import React from "react";
import {
  AbsoluteFill,
  interpolate,
  spring,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";

import { useVisualContractData } from "./visual-runtime";

const asRecord = (value: unknown): Record<string, unknown> | null => {
  return value && typeof value === "object" && !Array.isArray(value)
    ? (value as Record<string, unknown>)
    : null;
};

const asString = (value: unknown): string | null => {
  return typeof value === "string" && value.trim() ? value.trim() : null;
};

const asNumber = (value: unknown): number | null => {
  return typeof value === "number" && Number.isFinite(value) ? value : null;
};

const asStringArray = (value: unknown): string[] => {
  return Array.isArray(value)
    ? value.map(asString).filter((item): item is string => Boolean(item))
    : [];
};

const titleCase = (value: string): string => {
  return value
    .replace(/[_-]+/g, " ")
    .replace(/\s+/g, " ")
    .trim()
    .replace(/\b\w/g, (match) => match.toUpperCase());
};

const resolveBackgroundColor = (data: Record<string, unknown>): string => {
  return (
    asString(data.backgroundColor) ??
    asString(asRecord(data.colors)?.background) ??
    "#0A0F1A"
  );
};

const resolveTitle = (data: Record<string, unknown>): string => {
  const title = asString(data.title);
  if (title) return title;

  const quote = asString(data.quote);
  if (quote) return quote;

  const line1 = asString(data.titleLine1);
  const line2 = asString(data.titleLine2);
  if (line1 || line2) {
    return [line1, line2].filter(Boolean).join(" ");
  }

  const challenge = asString(data.challenge);
  if (challenge) return challenge;

  const sectionLabel = asString(data.sectionLabel);
  if (sectionLabel) return sectionLabel;

  return (
    asString(data.chartId) ??
    asString(data.diagramId) ??
    asString(data.tableId) ??
    asString(data.cardId) ??
    asString(data.transitionId) ??
    titleCase(asString(data.type) ?? "Generated Visual")
  );
};

const resolveSubtitleLines = (data: Record<string, unknown>): string[] => {
  const candidates = [
    asString(data.subtitle),
    asString(data.tagline),
    asString(data.summary),
    asString(data.bottomLabel),
    asString(asRecord(data.bottomLabel)?.line1),
    asString(asRecord(data.bottomLabel)?.line2),
    asString(data.subtext),
    asString(data.url),
    asString(data.attribution),
  ].filter((line): line is string => Boolean(line));

  return [...candidates, ...asStringArray(data.supportingText)].slice(0, 4);
};

const extractSeries = (data: Record<string, unknown>) => {
  const series = Array.isArray(data.series) ? data.series : [];
  const curves = Array.isArray(data.curves) ? data.curves : [];
  const forks = Array.isArray(data.forks) ? data.forks : [];

  const fromSeries = series
    .map((entry) => {
      const record = asRecord(entry);
      if (!record) return null;
      const points = Array.isArray(record.dataPoints)
        ? record.dataPoints
            .map((point) => {
              const item = asRecord(point);
              const x = asNumber(item?.x);
              const y = asNumber(item?.y);
              return x === null || y === null ? null : { x, y };
            })
            .filter((point): point is { x: number; y: number } => Boolean(point))
        : [];
      return points.length > 1
        ? {
            label: asString(record.label) ?? asString(record.id) ?? "Series",
            color: asString(record.color) ?? "#60A5FA",
            points,
          }
        : null;
    })
    .filter(
      (entry): entry is { label: string; color: string; points: { x: number; y: number }[] } =>
        Boolean(entry)
    );

  if (fromSeries.length > 0) return fromSeries;

  const fromForks = forks
    .map((entry) => {
      const record = asRecord(entry);
      if (!record) return null;
      const points = Array.isArray(record.dataPoints)
        ? record.dataPoints
            .map((point) => {
              const item = asRecord(point);
              const x = asNumber(item?.x);
              const y = asNumber(item?.y);
              return x === null || y === null ? null : { x, y };
            })
            .filter((point): point is { x: number; y: number } => Boolean(point))
        : [];
      return points.length > 1
        ? {
            label: asString(record.label) ?? asString(record.id) ?? "Series",
            color: asString(record.color) ?? "#60A5FA",
            points,
          }
        : null;
    })
    .filter(
      (entry): entry is { label: string; color: string; points: { x: number; y: number }[] } =>
        Boolean(entry)
    );

  if (fromForks.length > 0) return fromForks;

  return curves
    .map((entry, index) => {
      const record = asRecord(entry);
      if (!record) return null;
      const curveType = asString(record.type) ?? "curve";
      const points = Array.from({ length: 6 }, (_, pointIndex) => {
        const x = pointIndex;
        if (curveType === "flat") {
          return { x, y: 45 };
        }
        if (curveType === "exponential" || curveType === "up") {
          return { x, y: 18 + pointIndex * pointIndex * 2.2 };
        }
        return { x, y: 80 - pointIndex * pointIndex * 2.3 };
      });
      return {
        label: asString(record.label) ?? `Series ${index + 1}`,
        color: asString(record.color) ?? "#60A5FA",
        points,
      };
    })
    .filter(
      (entry): entry is { label: string; color: string; points: { x: number; y: number }[] } =>
        Boolean(entry)
    );
};

const buildPath = (
  points: { x: number; y: number }[],
  width: number,
  height: number
): string => {
  const xs = points.map((point) => point.x);
  const ys = points.map((point) => point.y);
  const minX = Math.min(...xs);
  const maxX = Math.max(...xs);
  const minY = Math.min(...ys);
  const maxY = Math.max(...ys);
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

const ChartVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
  frame: number;
}> = ({ data, width, height, frame }) => {
  const series = extractSeries(data);
  const chartWidth = width * 0.7;
  const chartHeight = height * 0.48;
  const reveal = interpolate(frame, [0, 24], [0.25, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  if (series.length === 0) {
    return (
      <div
        style={{
          width: chartWidth,
          height: chartHeight,
          border: "1px solid rgba(148, 163, 184, 0.32)",
          borderRadius: 28,
          backgroundColor: "rgba(15, 23, 42, 0.82)",
        }}
      />
    );
  }

  return (
    <div
      style={{
        position: "relative",
        width: chartWidth,
        height: chartHeight,
        borderRadius: 28,
        backgroundColor: "rgba(15, 23, 42, 0.82)",
        border: "1px solid rgba(148, 163, 184, 0.28)",
        overflow: "hidden",
      }}
    >
      <svg
        width={chartWidth}
        height={chartHeight}
        viewBox={`0 0 ${chartWidth} ${chartHeight}`}
      >
        {Array.from({ length: 4 }).map((_, index) => {
          const y = ((index + 1) / 5) * chartHeight;
          return (
            <line
              key={`grid-${index}`}
              x1={0}
              y1={y}
              x2={chartWidth}
              y2={y}
              stroke="rgba(148, 163, 184, 0.12)"
              strokeWidth={1}
            />
          );
        })}
        {series.map((entry) => {
          return (
            <path
              key={entry.label}
              d={buildPath(entry.points, chartWidth, chartHeight)}
              fill="none"
              stroke={entry.color}
              strokeWidth={4}
              strokeLinecap="round"
              strokeLinejoin="round"
              opacity={reveal}
            />
          );
        })}
      </svg>
      <div
        style={{
          position: "absolute",
          left: 24,
          top: 18,
          display: "flex",
          flexDirection: "column",
          gap: 10,
        }}
      >
        {series.slice(0, 3).map((entry) => (
          <div
            key={`legend-${entry.label}`}
            style={{
              display: "flex",
              alignItems: "center",
              gap: 10,
              color: "#E2E8F0",
              fontFamily: "'Inter', sans-serif",
              fontSize: 18,
              fontWeight: 600,
            }}
          >
            <div
              style={{
                width: 18,
                height: 4,
                borderRadius: 999,
                backgroundColor: entry.color,
              }}
            />
            {entry.label}
          </div>
        ))}
      </div>
    </div>
  );
};

const SplitVisual: React.FC<{ data: Record<string, unknown>; width: number; height: number }> = ({
  data,
  width,
  height,
}) => {
  const left = asRecord(data.leftPanel) ?? asRecord(data.left) ?? {};
  const right = asRecord(data.rightPanel) ?? asRecord(data.right) ?? {};

  const renderPanel = (panel: Record<string, unknown>, accent: string) => (
    <div
      style={{
        flex: 1,
        display: "flex",
        flexDirection: "column",
        justifyContent: "space-between",
        padding: 36,
        borderRadius: 24,
        backgroundColor: "rgba(15, 23, 42, 0.88)",
        border: `1px solid ${accent}55`,
      }}
    >
      <div
        style={{
          color: accent,
          fontFamily: "'Inter', sans-serif",
          fontSize: 24,
          fontWeight: 700,
          letterSpacing: 1.5,
        }}
      >
        {asString(panel.header) ?? asString(panel.label) ?? "Panel"}
      </div>
      <div
        style={{
          color: "#E2E8F0",
          fontFamily: "'Inter', sans-serif",
          fontSize: 26,
          fontWeight: 600,
          lineHeight: 1.25,
          textAlign: "center",
        }}
      >
        {asString(panel.caption) ??
          asString(panel.content) ??
          asString(panel.thematicRole) ??
          "Rendered from visual contract"}
      </div>
      <div
        style={{
          height: 140,
          borderRadius: 18,
          background: `linear-gradient(135deg, ${accent}33, rgba(15, 23, 42, 0.25))`,
        }}
      />
    </div>
  );

  return (
    <div
      style={{
        width: width * 0.82,
        height: height * 0.52,
        display: "flex",
        gap: 28,
      }}
    >
      {renderPanel(left, "#60A5FA")}
      {renderPanel(right, "#D9944A")}
    </div>
  );
};

const TableVisual: React.FC<{ data: Record<string, unknown>; width: number }> = ({
  data,
  width,
}) => {
  const columns = asStringArray(data.columns);
  const rows = Array.isArray(data.rows)
    ? data.rows.map((row) => asRecord(row)).filter((row): row is Record<string, unknown> => Boolean(row))
    : [];

  return (
    <div
      style={{
        width: width * 0.76,
        borderRadius: 24,
        overflow: "hidden",
        border: "1px solid rgba(148, 163, 184, 0.24)",
        backgroundColor: "rgba(15, 23, 42, 0.82)",
      }}
    >
      {columns.length > 0 ? (
        <div
          style={{
            display: "grid",
            gridTemplateColumns: `repeat(${columns.length}, minmax(0, 1fr))`,
            backgroundColor: "rgba(30, 41, 59, 0.9)",
          }}
        >
          {columns.map((column) => (
            <div
              key={column}
              style={{
                padding: "18px 20px",
                color: "#E2E8F0",
                fontFamily: "'Inter', sans-serif",
                fontSize: 20,
                fontWeight: 700,
              }}
            >
              {column}
            </div>
          ))}
        </div>
      ) : null}
      {rows.slice(0, 6).map((row, rowIndex) => {
        const values = columns.length
          ? columns.map((column) => asString(row[column.toLowerCase()]) ?? asString(row[column]) ?? "—")
          : Object.values(row).map((value) => asString(value) ?? "—");
        return (
          <div
            key={`row-${rowIndex}`}
            style={{
              display: "grid",
              gridTemplateColumns: `repeat(${Math.max(1, values.length)}, minmax(0, 1fr))`,
              borderTop: rowIndex === 0 && columns.length === 0 ? "none" : "1px solid rgba(148, 163, 184, 0.12)",
            }}
          >
            {values.map((value, valueIndex) => (
              <div
                key={`cell-${rowIndex}-${valueIndex}`}
                style={{
                  padding: "16px 20px",
                  color: "#CBD5E1",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 18,
                  lineHeight: 1.35,
                }}
              >
                {value}
              </div>
            ))}
          </div>
        );
      })}
    </div>
  );
};

const DiagramVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  frame: number;
}> = ({ data, width, frame }) => {
  const items = [
    ...asStringArray(data.causalChain),
    ...asStringArray(data.fileNames),
    ...asStringArray(data.warningComments),
    ...asStringArray(asRecord(data.takeaway)?.line1 ? [asRecord(data.takeaway)?.line1, asRecord(data.takeaway)?.line2] : []),
  ]
    .filter((item): item is string => Boolean(item))
    .slice(0, 6);

  const emphasis = spring({
    fps: 30,
    frame,
    config: { damping: 14, stiffness: 120 },
  });

  return (
    <div
      style={{
        width: width * 0.74,
        display: "grid",
        gridTemplateColumns: items.length >= 4 ? "repeat(2, minmax(0, 1fr))" : "1fr",
        gap: 18,
      }}
    >
      {items.length > 0 ? (
        items.map((item, index) => (
          <div
            key={`${item}-${index}`}
            style={{
              padding: "22px 24px",
              borderRadius: 22,
              backgroundColor: "rgba(15, 23, 42, 0.82)",
              border: "1px solid rgba(148, 163, 184, 0.22)",
              transform: `scale(${0.98 + emphasis * 0.02})`,
              color: "#E2E8F0",
              fontFamily: "'Inter', sans-serif",
              fontSize: 22,
              fontWeight: 600,
              lineHeight: 1.3,
            }}
          >
            {item}
          </div>
        ))
      ) : (
        <div
          style={{
            padding: "26px 28px",
            borderRadius: 24,
            backgroundColor: "rgba(15, 23, 42, 0.82)",
            border: "1px solid rgba(148, 163, 184, 0.24)",
            color: "#CBD5E1",
            fontFamily: "'Inter', sans-serif",
            fontSize: 24,
            fontWeight: 500,
            textAlign: "center",
          }}
        >
          Generated from visual contract
        </div>
      )}
    </div>
  );
};

export const GeneratedContractVisual: React.FC = () => {
  const data = useVisualContractData<Record<string, unknown>>() ?? {};
  const frame = useCurrentFrame();
  const { width, height, fps } = useVideoConfig();
  const backgroundColor = resolveBackgroundColor(data);
  const visualType = asString(data.type) ?? "generated_visual";
  const title = resolveTitle(data);
  const subtitleLines = resolveSubtitleLines(data);
  const introOpacity = interpolate(frame, [0, 12], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const accent = asString(data.accentColor) ?? "#60A5FA";

  let body: React.ReactNode = null;
  if (
    visualType === "animated_chart" ||
    visualType === "inset_chart" ||
    visualType === "pie_chart" ||
    visualType === "forking_chart" ||
    visualType === "chart_event" ||
    visualType === "chart_callback"
  ) {
    body = <ChartVisual data={data} width={width} height={height} frame={frame} />;
  } else if (visualType === "split_screen") {
    body = <SplitVisual data={data} width={width} height={height} />;
  } else if (visualType === "comparison_table") {
    body = <TableVisual data={data} width={width} />;
  } else {
    body = <DiagramVisual data={data} width={width} frame={frame} />;
  }

  return (
    <AbsoluteFill
      style={{
        backgroundColor,
        color: "#F8FAFC",
        padding: "72px 88px",
        fontFamily: "'Inter', sans-serif",
        justifyContent: "space-between",
      }}
    >
      <div
        style={{
          display: "flex",
          flexDirection: "column",
          gap: 18,
          opacity: introOpacity,
        }}
      >
        <div
          style={{
            color: `${accent}CC`,
            fontSize: 18,
            fontWeight: 700,
            letterSpacing: 2.2,
            textTransform: "uppercase",
          }}
        >
          {titleCase(visualType)}
        </div>
        <div
          style={{
            fontSize: visualType === "quote_card" ? 54 : 46,
            fontWeight: 700,
            lineHeight: 1.08,
            maxWidth: width * 0.74,
          }}
        >
          {title}
        </div>
        {subtitleLines.length > 0 ? (
          <div
            style={{
              display: "flex",
              flexDirection: "column",
              gap: 8,
              maxWidth: width * 0.68,
              color: "#CBD5E1",
              fontSize: 22,
              fontWeight: 500,
              lineHeight: 1.35,
            }}
          >
            {subtitleLines.map((line, index) => (
              <div key={`${line}-${index}`}>{line}</div>
            ))}
          </div>
        ) : null}
      </div>

      <div
        style={{
          flex: 1,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        {body}
      </div>

      <div
        style={{
          display: "flex",
          justifyContent: "space-between",
          alignItems: "center",
          color: "#94A3B8",
          fontSize: 16,
          letterSpacing: 1.4,
          textTransform: "uppercase",
          opacity: interpolate(frame, [fps * 2, fps * 2 + 12], [0, 0.85], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
        }}
      >
        <div>{asString(data.sectionId) ?? asString(data.chartId) ?? ""}</div>
        <div>{subtitleLines.length > 0 ? subtitleLines[0] : ""}</div>
      </div>
    </AbsoluteFill>
  );
};

export default GeneratedContractVisual;
