import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  interpolate,
  spring,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";

import {
  useVisualContractData,
  useVisualMediaAssetSrc,
} from "./visual-runtime";

type SeriesEntry = {
  label: string;
  color: string;
  points: { x: number; y: number }[];
  style?: string | null;
};

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
    .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
    .replace(/[_-]+/g, " ")
    .replace(/\s+/g, " ")
    .trim()
    .replace(/\b\w/g, (match) => match.toUpperCase());
};

const subtleSurface = "rgba(15, 23, 42, 0.84)";
const subtleBorder = "1px solid rgba(148, 163, 184, 0.24)";

const resolveBackgroundColor = (data: Record<string, unknown>): string => {
  return (
    asString(data.backgroundColor) ??
    asString(asRecord(data.colors)?.background) ??
    "#0A0F1A"
  );
};

const resolveAccentColor = (data: Record<string, unknown>): string => {
  return (
    asString(data.titleColor) ??
    asString(data.accentColor) ??
    asString(asRecord(data.colors)?.primary) ??
    "#60A5FA"
  );
};

const resolveTitle = (data: Record<string, unknown>): string => {
  const title = asString(data.title);
  if (title) return title;

  const quote = asString(data.quote);
  if (quote) return quote;

  const challenge = asString(data.challenge);
  if (challenge) return challenge;

  const line1 = asString(data.titleLine1);
  const line2 = asString(data.titleLine2);
  if (line1 || line2) {
    return [line1, line2].filter(Boolean).join("\n");
  }

  return (
    asString(data.chartId) ??
    asString(data.diagramId) ??
    asString(data.cardId) ??
    asString(data.transitionId) ??
    titleCase(asString(data.type) ?? "Generated Visual")
  );
};

const resolveTitleLines = (data: Record<string, unknown>): string[] => {
  const line1 = asString(data.titleLine1);
  const line2 = asString(data.titleLine2);
  if (line1 || line2) {
    return [line1, line2].filter((line): line is string => Boolean(line));
  }

  const title = asString(data.title);
  if (!title) {
    return [resolveTitle(data)];
  }

  if (title.length > 18 && title.includes(" ")) {
    const words = title.split(/\s+/).filter(Boolean);
    const midpoint = Math.ceil(words.length / 2);
    return [words.slice(0, midpoint).join(" "), words.slice(midpoint).join(" ")];
  }

  return [title];
};

const resolveSubtitleLines = (data: Record<string, unknown>): string[] => {
  const candidates = [
    asString(data.subtitle),
    asString(data.tagline),
    asString(data.summary),
    asString(data.subtext),
    asString(data.url),
    asString(data.attribution),
    asString(data.challengeText),
    asString(data.insightText),
    asString(data.sharedLabel),
    asString(data.priorityRule),
  ].filter((line): line is string => Boolean(line));

  return [...candidates, ...asStringArray(data.supportingText)].slice(0, 5);
};

const resolveEyebrow = (data: Record<string, unknown>): string => {
  const sectionLabel = asString(data.sectionLabel);
  const sectionNumber = data.sectionNumber;
  const sectionNumberText =
    typeof sectionNumber === "number" || typeof sectionNumber === "string"
      ? String(sectionNumber)
      : null;
  if (sectionLabel && sectionNumberText && !sectionLabel.includes(sectionNumberText)) {
    return `${sectionLabel}`;
  }
  return (
    sectionLabel ??
    asString(data.sectionId) ??
    titleCase(asString(data.type) ?? "Generated Visual")
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

const normalizeSeries = (data: Record<string, unknown>): SeriesEntry[] => {
  const series = Array.isArray(data.series) ? data.series : [];
  const curves = Array.isArray(data.curves) ? data.curves : [];
  const forks = Array.isArray(data.forks) ? data.forks : [];

  const fromCollections = [series, forks]
    .flat()
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
      if (points.length < 2) return null;
      return {
        label: asString(record.label) ?? asString(record.id) ?? "Series",
        color: asString(record.color) ?? "#60A5FA",
        points,
        style: asString(record.style),
      } satisfies SeriesEntry;
    })
    .filter((entry): entry is SeriesEntry => Boolean(entry));

  if (fromCollections.length > 0) {
    return fromCollections;
  }

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
        style: asString(record.style),
      } satisfies SeriesEntry;
    })
    .filter((entry): entry is SeriesEntry => Boolean(entry));
};

const HeaderBlock: React.FC<{
  data: Record<string, unknown>;
  accent: string;
  title: string;
}> = ({ data, accent, title }) => {
  const subtitleLines = resolveSubtitleLines(data);
  const eyebrow = resolveEyebrow(data);

  return (
    <div
      style={{
        position: "absolute",
        left: 72,
        top: 64,
        display: "flex",
        flexDirection: "column",
        gap: 14,
        maxWidth: 1180,
        zIndex: 10,
      }}
    >
      <div
        style={{
          color: `${accent}D9`,
          fontFamily: "'Inter', sans-serif",
          fontSize: 18,
          fontWeight: 700,
          letterSpacing: 2,
          textTransform: "uppercase",
        }}
      >
        {eyebrow}
      </div>
      <div
        style={{
          color: "#F8FAFC",
          fontFamily: "'Inter', sans-serif",
          fontSize: 48,
          fontWeight: 700,
          lineHeight: 1.05,
          whiteSpace: "pre-wrap",
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
            color: "#CBD5E1",
            fontFamily: "'Inter', sans-serif",
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
  );
};

const GhostElements: React.FC<{ data: Record<string, unknown> }> = ({ data }) => {
  const ghosts = Array.isArray(data.ghostElements)
    ? data.ghostElements.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];

  return (
    <>
      {ghosts.slice(0, 4).map((ghost, index) => {
        const color = asString(ghost.color) ?? "#334155";
        const size = 180 + index * 80;
        return (
          <div
            key={`ghost-${index}`}
            style={{
              position: "absolute",
              right: 100 + index * 80,
              top: 120 + index * 60,
              width: size,
              height: size,
              borderRadius: 999,
              border: `1px solid ${color}33`,
              boxShadow: `0 0 80px ${color}22 inset`,
              opacity: 0.45 - index * 0.08,
              transform: `rotate(${index * 12}deg)`,
            }}
          />
        );
      })}
    </>
  );
};

const TitleCardVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
}> = ({ data, width, height }) => {
  const accent = resolveAccentColor(data);
  const titleLines = resolveTitleLines(data);
  const subtitleLines = resolveSubtitleLines(data);
  const commands = asStringArray(data.commands);
  const style = asString(data.style);
  const isStillnessBeat = style === "stillness_beat";
  const eyebrow = resolveEyebrow(data);
  const titleColor = asString(data.titleColor) ?? "#E2E8F0";
  const ruleColor = "rgba(51, 65, 85, 0.4)";

  return (
    <AbsoluteFill
      style={{
        padding: "80px 96px",
        justifyContent: "center",
        overflow: "hidden",
      }}
    >
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundImage:
            "linear-gradient(rgba(30, 41, 59, 0.08) 1px, transparent 1px), linear-gradient(90deg, rgba(30, 41, 59, 0.08) 1px, transparent 1px)",
          backgroundSize: "60px 60px",
          opacity: isStillnessBeat ? 0.3 : 0.45,
        }}
      />
      <GhostElements data={data} />
      <div
        style={{
          position: "relative",
          zIndex: 2,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          gap: isStillnessBeat ? 14 : 18,
          textAlign: "center",
        }}
      >
        <div
          style={{
            color: isStillnessBeat ? "#94A3B8" : "#64748B",
            fontFamily: "'Inter', sans-serif",
            fontSize: isStillnessBeat ? 14 : 18,
            fontWeight: 700,
            letterSpacing: isStillnessBeat ? 4 : 2.4,
            textTransform: "uppercase",
          }}
        >
          {eyebrow}
        </div>
        {isStillnessBeat ? (
          <div
            style={{
              width: 300,
              height: 1,
              backgroundColor: ruleColor,
              borderRadius: 999,
            }}
          />
        ) : null}
        <div
          style={{
            color: titleColor,
            fontFamily: "'Inter', sans-serif",
            fontSize: isStillnessBeat ? 18 : width > 1400 ? 76 : 64,
            fontWeight: 700,
            lineHeight: isStillnessBeat ? 1.15 : 1.03,
            letterSpacing: isStillnessBeat ? 4 : 1,
            whiteSpace: "pre-wrap",
            maxWidth: width * 0.76,
            textTransform: isStillnessBeat ? "uppercase" : undefined,
            opacity: isStillnessBeat ? 0.72 : 1,
          }}
        >
          {titleLines.join("\n")}
        </div>
        {subtitleLines.map((line, index) => (
          <div
            key={`${line}-${index}`}
            style={{
              color: index === 0 ? "#CBD5E1" : "#94A3B8",
              fontFamily: "'Inter', sans-serif",
              fontSize: index === 0 ? 26 : 22,
              fontWeight: index === 0 ? 500 : 400,
              lineHeight: 1.35,
              maxWidth: width * 0.62,
            }}
          >
            {line}
          </div>
        ))}
      </div>
      {commands.length > 0 ? (
        <div
          style={{
            position: "absolute",
            left: Math.max(80, width * 0.28),
            right: Math.max(80, width * 0.28),
            bottom: Math.max(80, height * 0.12),
            display: "flex",
            flexDirection: "column",
            gap: 12,
            padding: "20px 24px",
            borderRadius: 20,
            backgroundColor: "rgba(2, 6, 23, 0.66)",
            border: subtleBorder,
          }}
        >
          {commands.slice(0, 2).map((command) => (
            <div
              key={command}
              style={{
                color: "#64748B",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 18,
              }}
            >
              {command}
            </div>
          ))}
        </div>
      ) : null}
    </AbsoluteFill>
  );
};

const QuoteCardVisual: React.FC<{ data: Record<string, unknown> }> = ({ data }) => {
  const accent = resolveAccentColor(data);
  const attribution = asString(data.attribution);

  return (
    <AbsoluteFill
      style={{
        padding: "120px 120px 96px",
        justifyContent: "center",
      }}
    >
      <div
        style={{
          maxWidth: 1320,
          margin: "0 auto",
          padding: "52px 60px",
          borderRadius: 36,
          backgroundColor: subtleSurface,
          border: subtleBorder,
          boxShadow: `0 0 120px ${accent}22 inset`,
          display: "flex",
          flexDirection: "column",
          gap: 28,
        }}
      >
        <div
          style={{
            color: accent,
            fontFamily: "'Inter', sans-serif",
            fontSize: 24,
            fontWeight: 700,
            letterSpacing: 2,
            textTransform: "uppercase",
          }}
        >
          Quote
        </div>
        <div
          style={{
            color: "#F8FAFC",
            fontFamily: "'Inter', sans-serif",
            fontSize: 56,
            fontWeight: 700,
            lineHeight: 1.16,
          }}
        >
          “{resolveTitle(data)}”
        </div>
        {attribution ? (
          <div
            style={{
              color: "#CBD5E1",
              fontFamily: "'Inter', sans-serif",
              fontSize: 24,
            }}
          >
            {attribution}
          </div>
        ) : null}
      </div>
    </AbsoluteFill>
  );
};

const TransitionVisual: React.FC<{ data: Record<string, unknown> }> = ({ data }) => {
  const accent = resolveAccentColor(data);
  const echoes = Array.isArray(data.echoes)
    ? data.echoes.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const title = resolveTitle(data);

  return (
    <AbsoluteFill
      style={{
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      <div
        style={{
          position: "absolute",
          inset: 0,
          background:
            "radial-gradient(circle at center, rgba(15, 23, 42, 0.12) 0%, rgba(10, 15, 26, 0.0) 55%)",
        }}
      />
      {echoes.slice(0, 3).map((echo, index) => (
        <div
          key={`echo-${index}`}
          style={{
            position: "absolute",
            width: 820 - index * 120,
            height: 340 - index * 36,
            borderRadius: 32,
            border: `1px solid ${accent}33`,
            opacity: Number(echo.opacity ?? 0.08) + index * 0.04,
            transform: `translateY(${index * 28}px) scale(${1 - index * 0.06})`,
          }}
        />
      ))}
      <div
        style={{
          position: "absolute",
          width: 640,
          height: 2,
          background: `linear-gradient(90deg, transparent, ${accent}55, transparent)`,
          opacity: 0.4,
        }}
      />
      {title && title !== "Transition" ? (
        <div
          style={{
            position: "absolute",
            bottom: 160,
            color: "#94A3B8",
            fontFamily: "'Inter', sans-serif",
            fontSize: 18,
            fontWeight: 600,
            letterSpacing: 2.4,
            textTransform: "uppercase",
            opacity: 0.6,
          }}
        >
          {title}
        </div>
      ) : null}
    </AbsoluteFill>
  );
};

const ChartVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
  frame: number;
}> = ({ data, width, height, frame }) => {
  const accent = resolveAccentColor(data);
  const title = resolveTitle(data);
  const series = normalizeSeries(data);
  const chartWidth = width * 0.72;
  const chartHeight = height * 0.5;
  const reveal = interpolate(frame, [0, 24], [0.25, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill>
      <HeaderBlock data={data} accent={accent} title={title} />
      <div
        style={{
          position: "absolute",
          left: (width - chartWidth) / 2,
          top: height * 0.28,
          width: chartWidth,
          height: chartHeight,
          borderRadius: 30,
          border: subtleBorder,
          backgroundColor: subtleSurface,
          overflow: "hidden",
        }}
      >
        <svg width={chartWidth} height={chartHeight} viewBox={`0 0 ${chartWidth} ${chartHeight}`}>
          {Array.from({ length: 5 }).map((_, index) => {
            const y = ((index + 1) / 6) * chartHeight;
            return (
              <line
                key={`grid-${index}`}
                x1={0}
                y1={y}
                x2={chartWidth}
                y2={y}
                stroke="rgba(148, 163, 184, 0.14)"
                strokeWidth={1}
              />
            );
          })}
          {series.map((entry) => (
            <path
              key={entry.label}
              d={buildPath(entry.points, chartWidth, chartHeight)}
              fill="none"
              stroke={entry.color}
              strokeWidth={4}
              strokeDasharray={entry.style === "dashed" ? "16 10" : undefined}
              strokeLinecap="round"
              strokeLinejoin="round"
              opacity={reveal}
            />
          ))}
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
          {series.slice(0, 4).map((entry) => (
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
    </AbsoluteFill>
  );
};

const SplitVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
}> = ({ data, width, height }) => {
  const left = asRecord(data.leftPanel) ?? asRecord(data.left) ?? {};
  const right = asRecord(data.rightPanel) ?? asRecord(data.right) ?? {};
  const leftSrc = useVisualMediaAssetSrc("leftSrc");
  const rightSrc = useVisualMediaAssetSrc("rightSrc");
  const multiplier = asString(data.multiplier);

  const renderPanel = (
    panel: Record<string, unknown>,
    accent: string,
    src: string | null
  ) => {
    const header = asString(panel.header) ?? asString(panel.label) ?? "Panel";
    const headerColor = asString(panel.headerColor) ?? accent;
    const caption =
      asString(panel.caption) ??
      asString(panel.content) ??
      asString(panel.thematicRole) ??
      "Rendered from visual contract";
    const tokenCount = panel.tokenCount;
    const scope = asString(panel.scope);
    const codeComments = asStringArray(panel.codeComments);
    const steps = Array.isArray(panel.steps)
      ? panel.steps.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];

    return (
      <div
        style={{
          position: "relative",
          flex: 1,
          overflow: "hidden",
          borderRadius: 28,
          backgroundColor: subtleSurface,
          border: `1px solid ${accent}55`,
        }}
      >
        {src ? (
          <OffthreadVideo
            src={src}
            style={{
              width: "100%",
              height: "100%",
              objectFit: "cover",
              opacity: 0.88,
            }}
          />
        ) : (
          <div
            style={{
              width: "100%",
              height: "100%",
              background: `linear-gradient(135deg, ${accent}22, rgba(15, 23, 42, 0.92))`,
            }}
          />
        )}
        <div
          style={{
            position: "absolute",
            inset: 0,
            background:
              "linear-gradient(180deg, rgba(2, 6, 23, 0.12) 0%, rgba(2, 6, 23, 0.28) 35%, rgba(2, 6, 23, 0.72) 100%)",
          }}
        />
        <div
          style={{
            position: "absolute",
            left: 30,
            right: 30,
            top: 28,
            color: headerColor,
            fontFamily: "'Inter', sans-serif",
            fontSize: 24,
            fontWeight: 700,
            letterSpacing: 1.6,
          }}
        >
          {header}
        </div>
        <div
          style={{
            position: "absolute",
            left: 30,
            right: 30,
            bottom: 28,
            display: "flex",
            flexDirection: "column",
            gap: 10,
          }}
        >
          {codeComments.length > 0 ? (
            <div
              style={{
                display: "flex",
                flexDirection: "column",
                gap: 6,
                color: "#FCA5A5",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 16,
                opacity: 0.84,
              }}
            >
              {codeComments.slice(0, 3).map((comment) => (
                <div key={comment}>{comment}</div>
              ))}
            </div>
          ) : null}
          {steps.length > 0 ? (
            <div
              style={{
                display: "flex",
                flexDirection: "column",
                gap: 6,
                color: "#E2E8F0",
                fontFamily: "'Inter', sans-serif",
                fontSize: 18,
              }}
            >
              {steps.slice(0, 3).map((step, index) => (
                <div key={`step-${index}`}>{asString(step.label) ?? asString(step.text) ?? ""}</div>
              ))}
            </div>
          ) : null}
          <div
            style={{
            color: "#F8FAFC",
            fontFamily: "'Inter', sans-serif",
            fontSize: 26,
            fontWeight: 600,
            lineHeight: 1.2,
          }}
        >
          {caption}
          </div>
          {typeof tokenCount === "number" || typeof tokenCount === "string" ? (
            <div
              style={{
                color: headerColor,
                fontFamily: "'Inter', sans-serif",
                fontSize: 18,
                fontWeight: 700,
              }}
            >
              {`${tokenCount} tokens`}
            </div>
          ) : null}
          {scope ? (
            <div
              style={{
                color: "#CBD5E1",
                fontFamily: "'Inter', sans-serif",
                fontSize: 17,
              }}
            >
              {scope}
            </div>
          ) : null}
        </div>
      </div>
    );
  };

  return (
    <AbsoluteFill style={{ padding: "88px 72px 72px" }}>
      <div
        style={{
          width,
          height,
          display: "flex",
          gap: 20,
        }}
      >
        {renderPanel(left, "#60A5FA", leftSrc)}
        {renderPanel(right, "#D9944A", rightSrc)}
      </div>
      <div
        style={{
          position: "absolute",
          top: 88,
          bottom: 72,
          left: "50%",
          width: 2,
          backgroundColor: "rgba(51, 65, 85, 0.35)",
        }}
      />
      {multiplier ? (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: "50%",
            transform: "translate(-50%, -50%)",
            padding: "10px 18px",
            borderRadius: 999,
            backgroundColor: "rgba(2, 6, 23, 0.8)",
            border: "1px solid rgba(45, 212, 191, 0.35)",
            color: "#2DD4BF",
            fontFamily: "'Inter', sans-serif",
            fontSize: 42,
            fontWeight: 700,
            boxShadow: "0 0 28px rgba(45, 212, 191, 0.16)",
          }}
        >
          {multiplier}
        </div>
      ) : null}
    </AbsoluteFill>
  );
};

const TableVisual: React.FC<{ data: Record<string, unknown>; width: number }> = ({
  data,
  width,
}) => {
  const table = asRecord(data.table) ?? data;
  const tableColumns = asStringArray(table.columns);
  const fallbackColumns = asStringArray(data.columns);
  const columns = tableColumns.length > 0 ? tableColumns : fallbackColumns;
  const rows = Array.isArray(table.rows)
    ? table.rows
        .map((row) => asRecord(row))
        .filter((row): row is Record<string, unknown> => Boolean(row))
    : [];

  return (
    <div
      style={{
        width: width * 0.76,
        borderRadius: 24,
        overflow: "hidden",
        border: subtleBorder,
        backgroundColor: subtleSurface,
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
      {rows.slice(0, 8).map((row, rowIndex) => {
        const values = columns.length
          ? columns.map(
              (column) =>
                asString(row[column.toLowerCase()]) ??
                asString(row[column]) ??
                "—"
            )
          : Object.values(row).map((value) => asString(value) ?? "—");
        return (
          <div
            key={`row-${rowIndex}`}
            style={{
              display: "grid",
              gridTemplateColumns: `repeat(${Math.max(1, values.length)}, minmax(0, 1fr))`,
              borderTop:
                rowIndex === 0 && columns.length === 0
                  ? "none"
                  : "1px solid rgba(148, 163, 184, 0.12)",
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

const DualMeterVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
  frame: number;
}> = ({ data, width, height, frame }) => {
  const title = resolveTitle(data);
  const accent = resolveAccentColor(data);
  const meters = Array.isArray(data.meters)
    ? data.meters
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];

  return (
    <AbsoluteFill>
      <HeaderBlock data={data} accent={accent} title={title} />
      <div
        style={{
          position: "absolute",
          left: width * 0.14,
          right: width * 0.14,
          top: height * 0.28,
          bottom: height * 0.12,
          display: "flex",
          gap: 64,
          alignItems: "flex-end",
        }}
      >
        {meters.slice(0, 2).map((meter, index) => {
          const fillGradient = Array.isArray(meter.fillGradient)
            ? meter.fillGradient.map(asString).filter((value): value is string => Boolean(value))
            : [];
          const progress = interpolate(frame, [0, 60], [0.28, 0.95], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          });
          return (
            <div
              key={`meter-${index}`}
              style={{
                flex: 1,
                height: "100%",
                display: "flex",
                flexDirection: "column",
                gap: 18,
                justifyContent: "flex-end",
              }}
            >
              <div
                style={{
                  color: "#E2E8F0",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 26,
                  fontWeight: 700,
                }}
              >
                {asString(meter.label) ?? `Meter ${index + 1}`}
              </div>
              <div
                style={{
                  position: "relative",
                  flex: 1,
                  minHeight: 360,
                  borderRadius: 32,
                  backgroundColor: subtleSurface,
                  border: subtleBorder,
                  overflow: "hidden",
                }}
              >
                <div
                  style={{
                    position: "absolute",
                    left: 0,
                    right: 0,
                    bottom: 0,
                    height: `${progress * 100}%`,
                    background:
                      fillGradient.length >= 2
                        ? `linear-gradient(180deg, ${fillGradient[0]}, ${fillGradient[1]})`
                        : fillGradient[0] ?? "#60A5FA",
                    opacity: 0.92,
                  }}
                />
              </div>
              <div
                style={{
                  display: "flex",
                  justifyContent: "space-between",
                  color: "#94A3B8",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 18,
                  fontWeight: 600,
                }}
              >
                <div>{asString(meter.scaleMin) ?? asStringArray(meter.scale)?.[0] ?? "Low"}</div>
                <div>{asString(meter.scaleMax) ?? asStringArray(meter.scale)?.slice(-1)[0] ?? "High"}</div>
              </div>
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

const CodeVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
}> = ({ data, width, height }) => {
  const accent = resolveAccentColor(data);
  const title = resolveTitle(data);
  const fileNames = [
    asString(data.highlightedModule),
    asString(data.promptFile),
    ...asStringArray(data.fileNames),
  ].filter((item): item is string => Boolean(item));
  const workflow = asStringArray(data.workflow);
  const terminalLines = [
    asString(data.terminalCommand),
    asString(data.terminalOutput),
    ...workflow,
    ...asStringArray(data.terminalCommands),
  ].filter((item): item is string => Boolean(item));

  return (
    <AbsoluteFill>
      <HeaderBlock data={data} accent={accent} title={title} />
      <div
        style={{
          position: "absolute",
          left: 72,
          right: 72,
          top: height * 0.28,
          bottom: 72,
          display: "grid",
          gridTemplateColumns: "1.15fr 0.85fr",
          gap: 28,
        }}
      >
        <div
          style={{
            position: "relative",
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            overflow: "hidden",
            padding: "22px 24px",
          }}
        >
          <div
            style={{
              display: "flex",
              gap: 12,
              marginBottom: 18,
            }}
          >
            {fileNames.slice(0, 5).map((name, index) => (
              <div
                key={`${name}-${index}`}
                style={{
                  padding: "10px 14px",
                  borderRadius: 14,
                  backgroundColor: index === 0 ? "rgba(96, 165, 250, 0.2)" : "rgba(30, 41, 59, 0.9)",
                  color: index === 0 ? "#E2E8F0" : "#94A3B8",
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 16,
                }}
              >
                {name}
              </div>
            ))}
          </div>
          <div
            style={{
              display: "grid",
              gridTemplateColumns: "56px 1fr",
              rowGap: 8,
            }}
          >
            {Array.from({ length: 14 }).map((_, index) => (
              <React.Fragment key={`code-line-${index}`}>
                <div
                  style={{
                    color: "#475569",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 16,
                  }}
                >
                  {index + 1}
                </div>
                <div
                  style={{
                    color: index % 4 === 0 ? "#93C5FD" : index % 3 === 0 ? "#F8FAFC" : "#CBD5E1",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 18,
                    opacity: index < 3 ? 0.55 : 1,
                  }}
                >
                  {index % 4 === 0
                    ? "def transform_module(input_data):"
                    : index % 3 === 0
                      ? "    return validate_against_prompt(input_data)"
                      : "    # structured contract driven output"}
                </div>
              </React.Fragment>
            ))}
          </div>
        </div>
        <div
          style={{
            display: "flex",
            flexDirection: "column",
            gap: 22,
          }}
        >
          <div
            style={{
              flex: 1,
              borderRadius: 28,
              backgroundColor: subtleSurface,
              border: subtleBorder,
              padding: "26px 28px",
              display: "flex",
              flexDirection: "column",
              gap: 16,
            }}
          >
            <div
              style={{
                color: accent,
                fontFamily: "'Inter', sans-serif",
                fontSize: 22,
                fontWeight: 700,
              }}
            >
              Transformation
            </div>
            {terminalLines.slice(0, 5).map((line, index) => (
              <div
                key={`${line}-${index}`}
                style={{
                  color: index < 2 ? "#E2E8F0" : "#94A3B8",
                  fontFamily:
                    index < 2 ? "'JetBrains Mono', monospace" : "'Inter', sans-serif",
                  fontSize: index < 2 ? 18 : 20,
                  lineHeight: 1.35,
                }}
              >
                {line}
              </div>
            ))}
          </div>
          <div
            style={{
              borderRadius: 28,
              backgroundColor: subtleSurface,
              border: subtleBorder,
              padding: "22px 24px",
              color: "#CBD5E1",
              fontFamily: "'Inter', sans-serif",
              fontSize: 20,
              lineHeight: 1.35,
            }}
          >
            {asString(asRecord(data.transformation)?.prompt?.role) ??
              asString(data.resultLabel) ??
              workflow[0] ??
              "Source of truth shifts from the artifact to the specification."}
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};

const NetworkGraphVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
}> = ({ data, width, height }) => {
  const title = resolveTitle(data);
  const accent = resolveAccentColor(data);
  const sequence = Array.isArray(data.migrationSequence)
    ? data.migrationSequence
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const unmigrated = asStringArray(data.unmigrated);

  return (
    <AbsoluteFill>
      <HeaderBlock data={data} accent={accent} title={title} />
      <div
        style={{
          position: "absolute",
          left: 72,
          right: 72,
          top: height * 0.26,
          bottom: 72,
          display: "grid",
          gridTemplateColumns: "1.2fr 0.8fr",
          gap: 24,
        }}
      >
        <div
          style={{
            position: "relative",
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            overflow: "hidden",
          }}
        >
          {sequence.slice(0, 10).map((entry, index) => {
            const position = Array.isArray(entry.position) ? entry.position : [];
            const left = asNumber(position[0]) ?? 240 + (index % 4) * 160;
            const top = asNumber(position[1]) ?? 180 + Math.floor(index / 4) * 140;
            return (
              <div
                key={`node-${index}`}
                style={{
                  position: "absolute",
                  left,
                  top,
                  padding: "14px 18px",
                  borderRadius: 16,
                  backgroundColor: "rgba(96, 165, 250, 0.2)",
                  border: "1px solid rgba(96, 165, 250, 0.5)",
                  color: "#E2E8F0",
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 16,
                }}
              >
                {asString(entry.name) ?? `module_${index + 1}.py`}
              </div>
            );
          })}
        </div>
        <div
          style={{
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            padding: "24px 28px",
            display: "flex",
            flexDirection: "column",
            gap: 14,
          }}
        >
          <div
            style={{
              color: "#94A3B8",
              fontFamily: "'Inter', sans-serif",
              fontSize: 18,
              fontWeight: 700,
              letterSpacing: 1.4,
              textTransform: "uppercase",
            }}
          >
            Remaining
          </div>
          {unmigrated.slice(0, 8).map((name) => (
            <div
              key={name}
              style={{
                color: "#CBD5E1",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 18,
              }}
            >
              {name}
            </div>
          ))}
        </div>
      </div>
    </AbsoluteFill>
  );
};

const AnnotationVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
}> = ({ data, width, height }) => {
  const title = resolveTitle(data);
  const accent = resolveAccentColor(data);
  const annotations = Array.isArray(data.annotations)
    ? data.annotations
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const comparison = asRecord(data.comparison);
  const emphasisLine = asString(data.emphasisLine);

  return (
    <AbsoluteFill>
      <HeaderBlock data={data} accent={accent} title={title} />
      <div
        style={{
          position: "absolute",
          left: 72,
          right: 72,
          top: height * 0.28,
          bottom: 72,
          display: "flex",
          flexDirection: "column",
          gap: 24,
        }}
      >
        {comparison ? (
          <div
            style={{
              display: "grid",
              gridTemplateColumns: "1fr 180px 1fr",
              gap: 24,
              alignItems: "center",
            }}
          >
            {[comparison.left, comparison.right].map((entry, index) => {
              const side = asRecord(entry);
              const color = asString(side?.color) ?? (index === 0 ? "#60A5FA" : "#4ADE80");
              return (
                <div
                  key={`comparison-${index}`}
                  style={{
                    padding: "28px 30px",
                    borderRadius: 28,
                    backgroundColor: subtleSurface,
                    border: `1px solid ${color}44`,
                    color: "#F8FAFC",
                    fontFamily: "'Inter', sans-serif",
                    fontSize: 30,
                    fontWeight: 700,
                    lineHeight: 1.16,
                  }}
                >
                  <div style={{ color, fontSize: 18, letterSpacing: 1.6, textTransform: "uppercase" }}>
                    {asString(side?.domain) ?? asString(side?.label) ?? "Domain"}
                  </div>
                  <div style={{ marginTop: 16 }}>{asString(side?.input) ?? asString(side?.domain) ?? ""}</div>
                  <div style={{ marginTop: 10, color: "#CBD5E1", fontSize: 22 }}>
                    {asString(side?.output) ?? asString(side?.domain) ?? ""}
                  </div>
                </div>
              );
            })}
            <div
              style={{
                justifySelf: "center",
                color: asString(asRecord(comparison.equivalence)?.color) ?? "#A78BFA",
                fontFamily: "'Inter', sans-serif",
                fontSize: 120,
                fontWeight: 700,
              }}
            >
              {asString(asRecord(comparison.equivalence)?.symbol) ?? "≡"}
            </div>
          </div>
        ) : null}
        {annotations.length > 0 ? (
          <div
            style={{
              display: "grid",
              gridTemplateColumns: "repeat(2, minmax(0, 1fr))",
              gap: 18,
            }}
          >
            {annotations.slice(0, 4).map((annotation, index) => {
              const color = asString(annotation.color) ?? "#60A5FA";
              return (
                <div
                  key={`annotation-${index}`}
                  style={{
                    padding: "22px 24px",
                    borderRadius: 24,
                    backgroundColor: subtleSurface,
                    border: `1px solid ${color}44`,
                    display: "flex",
                    flexDirection: "column",
                    gap: 8,
                  }}
                >
                  <div
                    style={{
                      color,
                      fontFamily: "'Inter', sans-serif",
                      fontSize: 18,
                      fontWeight: 700,
                    }}
                  >
                    {asString(annotation.header) ?? asString(annotation.stat) ?? asString(annotation.text) ?? "Callout"}
                  </div>
                  <div
                    style={{
                      color: "#F8FAFC",
                      fontFamily: "'Inter', sans-serif",
                      fontSize: 24,
                      fontWeight: 600,
                      lineHeight: 1.2,
                    }}
                  >
                    {asString(annotation.text) ?? asString(annotation.detail) ?? ""}
                  </div>
                  <div
                    style={{
                      color: "#94A3B8",
                      fontFamily: "'Inter', sans-serif",
                      fontSize: 18,
                    }}
                  >
                    {asString(annotation.source) ?? ""}
                  </div>
                </div>
              );
            })}
          </div>
        ) : null}
        {emphasisLine ? (
          <div
            style={{
              alignSelf: "center",
              padding: "14px 18px",
              borderRadius: 999,
              backgroundColor: "rgba(167, 139, 250, 0.12)",
              border: "1px solid rgba(167, 139, 250, 0.32)",
              color: "#E9D5FF",
              fontFamily: "'Inter', sans-serif",
              fontSize: 22,
              fontWeight: 700,
            }}
          >
            {emphasisLine}
          </div>
        ) : null}
      </div>
    </AbsoluteFill>
  );
};

const TextMorphVisual: React.FC<{ data: Record<string, unknown> }> = ({ data }) => {
  const accent = resolveAccentColor(data);
  const title = resolveTitle(data);
  const comparisons = Array.isArray(data.comparisons)
    ? data.comparisons
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];

  return (
    <AbsoluteFill>
      <HeaderBlock data={data} accent={accent} title={title} />
      <div
        style={{
          position: "absolute",
          left: 72,
          right: 72,
          top: 280,
          bottom: 72,
          display: "grid",
          gridTemplateColumns: "repeat(2, minmax(0, 1fr))",
          gap: 24,
        }}
      >
        {comparisons.slice(0, 2).map((comparison, index) => {
          const color = asString(comparison.domainColor) ?? (index === 0 ? "#60A5FA" : "#4ADE80");
          return (
            <div
              key={`comparison-${index}`}
              style={{
                padding: "28px 30px",
                borderRadius: 28,
                backgroundColor: subtleSurface,
                border: `1px solid ${color}44`,
                display: "flex",
                flexDirection: "column",
                gap: 14,
              }}
            >
              <div
                style={{
                  color,
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 20,
                  fontWeight: 700,
                  letterSpacing: 1.6,
                  textTransform: "uppercase",
                }}
              >
                {asString(comparison.domain) ?? "Domain"}
              </div>
              <div
                style={{
                  color: "#E2E8F0",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 30,
                  fontWeight: 700,
                }}
              >
                {asString(comparison.input) ?? ""}
              </div>
              <div
                style={{
                  color: "#94A3B8",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 22,
                }}
              >
                {asString(comparison.output) ?? ""}
              </div>
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

const AnimatedDiagramVisual: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
}> = ({ data, width, height }) => {
  const title = resolveTitle(data);
  const accent = resolveAccentColor(data);
  const diagramId = asString(data.diagramId) ?? "";
  const promptNozzle = diagramId === "prompt_nozzle";
  const walls = Array.isArray(data.walls)
    ? data.walls.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const modules = Array.isArray(data.modules)
    ? data.modules.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const promptText = asStringArray(data.promptText);
  const nozzleLabels = asStringArray(data.nozzleLabels);
  const phases = Array.isArray(data.phases)
    ? data.phases.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const branches = Array.isArray(data.branches)
    ? data.branches.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const steps = Array.isArray(data.steps)
    ? data.steps.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const timeline = Array.isArray(data.wallTimeline)
    ? data.wallTimeline.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const limitations = asStringArray(data.limitations);
  const table = asRecord(data.table);
  const embeddedCodeBlocks = Array.isArray(data.embeddedCodeBlocks)
    ? data.embeddedCodeBlocks.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const ratchetMetaphor = asRecord(data.ratchetMetaphor);
  const statusDelay = asNumber(data.statusDelay);
  const takeaways = [
    ...asStringArray(data.causalChain),
    ...asStringArray(data.terminalCommands),
    ...asStringArray(data.hierarchy),
    ...asStringArray(data.priorityRule ? [data.priorityRule] : []),
  ].slice(0, 5);

  let body: React.ReactNode;
  if (diagramId === "prompt_ratio") {
    body = (
      <div
        style={{
          width: width * 0.78,
          display: "grid",
          gridTemplateColumns: "1fr 160px 1fr",
          gap: 24,
          alignItems: "center",
        }}
      >
        <div style={{ padding: "26px 28px", borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder }}>
          <div style={{ color: "#94A3B8", fontSize: 20, fontWeight: 700 }}>PROMPT</div>
          <div style={{ color: "#E2E8F0", fontSize: 42, fontWeight: 700, marginTop: 12 }}>
            {asString(data.promptSize) ?? "~12 lines"}
          </div>
          <div style={{ color: "#CBD5E1", fontSize: 22, marginTop: 12 }}>
            {asString(asRecord(data.analogy)?.prompt) ?? "header file"}
          </div>
        </div>
        <div style={{ color: "#2DD4BF", fontSize: 64, fontWeight: 700, textAlign: "center" }}>
          {asString(data.ratio) ?? "1:5"}
        </div>
        <div style={{ padding: "26px 28px", borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder }}>
          <div style={{ color: "#94A3B8", fontSize: 20, fontWeight: 700 }}>GENERATED CODE</div>
          <div style={{ color: "#E2E8F0", fontSize: 42, fontWeight: 700, marginTop: 12 }}>
            {asString(data.codeSize) ?? "~200 lines"}
          </div>
          <div style={{ color: "#CBD5E1", fontSize: 22, marginTop: 12 }}>
            {asString(asRecord(data.analogy)?.code) ?? "OBJ file"}
          </div>
        </div>
      </div>
    );
  } else if (diagramId === "five_generations") {
    const generations = phases.length > 0 ? phases : steps;
    body = (
      <div
        style={{
          width: width * 0.82,
          display: "flex",
          alignItems: "stretch",
          gap: 16,
        }}
      >
        {generations.slice(0, 5).map((entry, index) => (
          <div
            key={`generation-${index}`}
            style={{
              flex: 1,
              padding: "22px 18px",
              borderRadius: 24,
              backgroundColor: subtleSurface,
              border: `1px solid ${(asString(entry.color) ?? "#60A5FA")}44`,
              display: "flex",
              flexDirection: "column",
              justifyContent: "space-between",
              minHeight: 280,
            }}
          >
            <div style={{ color: asString(entry.color) ?? "#60A5FA", fontSize: 18, fontWeight: 700 }}>
              {asString(entry.label) ?? `Generation ${index + 1}`}
            </div>
            <div style={{ color: "#E2E8F0", fontSize: 24, lineHeight: 1.2 }}>
              {asString(entry.detail) ?? asString(entry.text) ?? asString(entry.status) ?? ""}
            </div>
          </div>
        ))}
      </div>
    );
  } else if (diagramId === "embedded_code_document" && embeddedCodeBlocks.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.78,
          display: "grid",
          gridTemplateColumns: "1.1fr 0.9fr",
          gap: 24,
        }}
      >
        <div style={{ borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder, padding: "24px 28px" }}>
          {embeddedCodeBlocks.slice(0, 3).map((block, index) => (
            <div key={`code-block-${index}`} style={{ marginBottom: 18 }}>
              <div style={{ color: "#2DD4BF", fontSize: 18, fontWeight: 700 }}>{asString(block.title) ?? asString(block.label) ?? `Block ${index + 1}`}</div>
              <div style={{ color: "#CBD5E1", fontFamily: "'JetBrains Mono', monospace", fontSize: 16, marginTop: 8 }}>
                {asString(block.code) ?? asString(block.content) ?? ""}
              </div>
            </div>
          ))}
        </div>
        <div style={{ borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder, padding: "24px 28px" }}>
          {takeaways.slice(0, 4).map((item, index) => (
            <div key={`${item}-${index}`} style={{ color: "#E2E8F0", fontSize: 20, marginBottom: 12 }}>
              {item}
            </div>
          ))}
        </div>
      </div>
    );
  } else if (diagramId === "ratchet_timelapse") {
    body = (
      <div
        style={{
          width: width * 0.78,
          display: "grid",
          gridTemplateColumns: "1.15fr 0.85fr",
          gap: 24,
        }}
      >
        <div style={{ display: "flex", alignItems: "flex-end", gap: 14 }}>
          {(timeline.length > 0 ? timeline : Array.from({ length: 6 }, (_, index) => ({ count: index + 1 }))).slice(0, 6).map((entry, index) => {
            const count = asNumber(asRecord(entry)?.count) ?? index + 1;
            return (
              <div
                key={`ratchet-${index}`}
                style={{
                  flex: 1,
                  height: 120 + count * 22,
                  borderRadius: 18,
                  backgroundColor: "rgba(217, 148, 74, 0.24)",
                  border: "1px solid rgba(217, 148, 74, 0.5)",
                }}
              />
            );
          })}
        </div>
        <div style={{ borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder, padding: "24px 28px" }}>
          <div style={{ color: "#D9944A", fontSize: 18, fontWeight: 700 }}>
            {asString(ratchetMetaphor?.label) ?? "Ratchet effect"}
          </div>
          <div style={{ color: "#E2E8F0", fontSize: 24, marginTop: 12 }}>
            {asString(ratchetMetaphor?.summary) ?? "Walls accumulate. They do not disappear."}
          </div>
          {statusDelay !== null ? (
            <div style={{ color: "#94A3B8", fontSize: 18, marginTop: 16 }}>
              {`Status delay: ${statusDelay} frames`}
            </div>
          ) : null}
        </div>
      </div>
    );
  } else if (table) {
    body = <TableVisual data={data} width={width} />;
  } else if (walls.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.76,
          display: "grid",
          gridTemplateColumns: "repeat(2, minmax(0, 1fr))",
          gap: 18,
        }}
      >
        {walls.slice(0, 8).map((wall, index) => (
          <div
            key={`wall-${index}`}
            style={{
              padding: "20px 22px",
              borderRadius: 22,
              backgroundColor: subtleSurface,
              border: `1px solid ${(asString(data.wallColor) ?? "#D9944A")}55`,
              color: "#E2E8F0",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 18,
              lineHeight: 1.3,
            }}
          >
            {asString(wall.label) ?? asString(wall.id) ?? `Wall ${index + 1}`}
          </div>
        ))}
      </div>
    );
  } else if (modules.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.76,
          display: "grid",
          gridTemplateColumns: "1.3fr 0.7fr",
          gap: 22,
        }}
      >
        <div
          style={{
            display: "grid",
            gridTemplateColumns: "repeat(3, minmax(0, 1fr))",
            gap: 16,
          }}
        >
          {modules.slice(0, 12).map((module, index) => (
            <div
              key={`module-${index}`}
              style={{
                padding: "20px 18px",
                borderRadius: 20,
                backgroundColor: asString(module.highlighted) === "true" || module.highlighted
                  ? "rgba(96, 165, 250, 0.2)"
                  : subtleSurface,
                border:
                  asString(module.highlighted) === "true" || module.highlighted
                    ? "1px solid rgba(96, 165, 250, 0.6)"
                    : subtleBorder,
                color: "#E2E8F0",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 18,
              }}
            >
              {asString(module.label) ?? asString(module.id) ?? `module_${index + 1}`}
            </div>
          ))}
        </div>
        <div
          style={{
            borderRadius: 24,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            padding: "20px 22px",
            display: "flex",
            flexDirection: "column",
            gap: 10,
          }}
        >
          {limitations.slice(0, 5).map((item) => (
            <div
              key={item}
              style={{
                color: "#CBD5E1",
                fontFamily: "'Inter', sans-serif",
                fontSize: 20,
              }}
            >
              {item}
            </div>
          ))}
        </div>
      </div>
    );
  } else if (promptNozzle || promptText.length > 0 || nozzleLabels.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.78,
          display: "grid",
          gridTemplateColumns: "0.85fr 1.15fr",
          gap: 24,
        }}
      >
        <div
          style={{
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            padding: "26px 28px",
            display: "flex",
            flexDirection: "column",
            gap: 12,
          }}
        >
          {nozzleLabels.slice(0, 4).map((label) => (
            <div
              key={label}
              style={{
                padding: "10px 14px",
                borderRadius: 999,
                backgroundColor: "rgba(45, 212, 191, 0.18)",
                color: "#CCFBF1",
                fontFamily: "'Inter', sans-serif",
                fontSize: 18,
                fontWeight: 700,
              }}
            >
              {label}
            </div>
          ))}
        </div>
        <div
          style={{
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            padding: "24px 28px",
            display: "flex",
            flexDirection: "column",
            gap: 10,
          }}
        >
          {promptText.slice(0, 6).map((line, index) => (
            <div
              key={`${line}-${index}`}
              style={{
                color: index === 0 ? "#E2E8F0" : "#CBD5E1",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 19,
                lineHeight: 1.35,
              }}
            >
              {line}
            </div>
          ))}
        </div>
      </div>
    );
  } else if (branches.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.76,
          display: "grid",
          gridTemplateColumns: "1fr 1fr",
          gap: 22,
        }}
      >
        {branches.slice(0, 2).map((branch, index) => (
          <div
            key={`branch-${index}`}
            style={{
              padding: "24px 26px",
              borderRadius: 28,
              backgroundColor: subtleSurface,
              border: `1px solid ${(asString(branch.color) ?? "#60A5FA")}44`,
              display: "flex",
              flexDirection: "column",
              gap: 10,
            }}
          >
            <div
              style={{
                color: asString(branch.color) ?? "#60A5FA",
                fontFamily: "'Inter', sans-serif",
                fontSize: 22,
                fontWeight: 700,
              }}
            >
              {asString(branch.label) ?? `Branch ${index + 1}`}
            </div>
            <div
              style={{
                color: "#CBD5E1",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 18,
              }}
            >
              {asString(branch.file) ?? asString(branch.action) ?? ""}
            </div>
          </div>
        ))}
      </div>
    );
  } else if (steps.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.76,
          display: "flex",
          alignItems: "flex-end",
          gap: 18,
        }}
      >
        {steps.slice(0, 6).map((step, index) => (
          <div
            key={`step-${index}`}
            style={{
              flex: 1,
              height: 160 + index * 48,
              borderRadius: 22,
              backgroundColor: "rgba(15, 23, 42, 0.88)",
              border: `1px solid ${(asString(step.color) ?? "#60A5FA")}44`,
              padding: "18px 16px",
              display: "flex",
              alignItems: "flex-end",
            }}
          >
            <div
              style={{
                color: "#F8FAFC",
                fontFamily: "'Inter', sans-serif",
                fontSize: 20,
                fontWeight: 700,
                lineHeight: 1.15,
              }}
            >
              {asString(step.label) ?? ""}
            </div>
          </div>
        ))}
      </div>
    );
  } else if (timeline.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.76,
          display: "flex",
          alignItems: "flex-end",
          gap: 16,
        }}
      >
        {timeline.slice(0, 7).map((entry, index) => {
          const count = asNumber(entry.count) ?? index + 1;
          return (
            <div
              key={`timeline-${index}`}
              style={{
                flex: 1,
                height: 120 + count * 10,
                borderRadius: 20,
                backgroundColor: "rgba(217, 148, 74, 0.25)",
                border: "1px solid rgba(217, 148, 74, 0.55)",
                display: "flex",
                alignItems: "flex-end",
                justifyContent: "center",
                paddingBottom: 18,
                color: "#F8FAFC",
                fontFamily: "'Inter', sans-serif",
                fontSize: 18,
                fontWeight: 700,
              }}
            >
              {count}
            </div>
          );
        })}
      </div>
    );
  } else {
    body = (
      <div
        style={{
          width: width * 0.76,
          display: "grid",
          gridTemplateColumns: takeaways.length >= 4 ? "repeat(2, minmax(0, 1fr))" : "1fr",
          gap: 18,
        }}
      >
        {(takeaways.length > 0 ? takeaways : ["Structured contract preview"]).map((item, index) => (
          <div
            key={`${item}-${index}`}
            style={{
              padding: "22px 24px",
              borderRadius: 22,
              backgroundColor: subtleSurface,
              border: "1px solid rgba(148, 163, 184, 0.22)",
              color: "#E2E8F0",
              fontFamily: "'Inter', sans-serif",
              fontSize: 22,
              fontWeight: 600,
              lineHeight: 1.3,
            }}
          >
            {item}
          </div>
        ))}
      </div>
    );
  }

  return (
    <AbsoluteFill>
      <HeaderBlock data={data} accent={accent} title={title} />
      <div
        style={{
          position: "absolute",
          left: 0,
          right: 0,
          top: 280,
          bottom: 72,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        {body}
      </div>
    </AbsoluteFill>
  );
};

export const GeneratedContractVisual: React.FC = () => {
  const data = useVisualContractData<Record<string, unknown>>() ?? {};
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const backgroundColor = resolveBackgroundColor(data);
  const visualType = asString(data.type) ?? "generated_visual";

  let body: React.ReactNode;
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
    body = (
      <AbsoluteFill style={{ alignItems: "center", justifyContent: "center" }}>
        <TableVisual data={data} width={width} />
      </AbsoluteFill>
    );
  } else if (visualType === "title_card" || visualType === "beat") {
    body = <TitleCardVisual data={data} width={width} height={height} />;
  } else if (visualType === "quote_card") {
    body = <QuoteCardVisual data={data} />;
  } else if (visualType === "transition") {
    body = <TransitionVisual data={data} />;
  } else if (
    visualType === "code_visualization" ||
    visualType === "code_transformation" ||
    visualType === "code_display" ||
    visualType === "code_regeneration"
  ) {
    body = <CodeVisual data={data} width={width} height={height} />;
  } else if (visualType === "network_graph") {
    body = <NetworkGraphVisual data={data} width={width} height={height} />;
  } else if (visualType === "dual_meter_animation" || visualType === "dual_meter") {
    body = <DualMeterVisual data={data} width={width} height={height} frame={frame} />;
  } else if (visualType === "annotation_overlay") {
    body = <AnnotationVisual data={data} width={width} height={height} />;
  } else if (visualType === "text_overlay_with_morph") {
    body = <TextMorphVisual data={data} />;
  } else if (visualType === "animated_diagram") {
    body = <AnimatedDiagramVisual data={data} width={width} height={height} />;
  } else {
    body = <AnimatedDiagramVisual data={data} width={width} height={height} />;
  }

  return (
    <AbsoluteFill
      style={{
        backgroundColor,
        color: "#F8FAFC",
        overflow: "hidden",
        fontFamily: "'Inter', sans-serif",
      }}
    >
      {body}
    </AbsoluteFill>
  );
};

export default GeneratedContractVisual;
