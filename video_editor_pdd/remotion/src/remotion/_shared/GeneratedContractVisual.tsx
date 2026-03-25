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
import {
  buildChartPath,
  computeSeriesBounds,
  type SeriesEntry,
} from "./chart-utils";

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

const resolveExplicitTitle = (data: Record<string, unknown>): string | null => {
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

  return null;
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
  if (sectionLabel) {
    return sectionLabel;
  }

  const sectionNumber = data.sectionNumber;
  if (typeof sectionNumber === "number" && Number.isFinite(sectionNumber)) {
    return `PART ${sectionNumber}`;
  }

  const sectionNumberText = asString(sectionNumber);
  if (sectionNumberText && /^[0-9]+$/.test(sectionNumberText)) {
    return `PART ${sectionNumberText}`;
  }

  return "";
};

const hasExplicitHeaderCopy = (data: Record<string, unknown>): boolean => {
  return Boolean(
    resolveExplicitTitle(data) ||
      resolveEyebrow(data) ||
      resolveSubtitleLines(data).length > 0
  );
};

const buildDegradationSeries = (
  record: Record<string, unknown>
): SeriesEntry | null => {
  const degradationRange = asRecord(record.degradationRange);
  const minValue = asNumber(degradationRange?.min);
  const maxValue = asNumber(degradationRange?.max);
  if (minValue === null || maxValue === null) {
    return null;
  }

  const points = [
    { x: 0, y: maxValue },
    { x: 1, y: maxValue * 0.92 },
    { x: 2, y: (maxValue + minValue) / 2 },
    { x: 3, y: minValue * 1.18 },
    { x: 4, y: minValue },
  ];

  return {
    label: asString(record.label) ?? asString(record.id) ?? "Series",
    color: asString(record.color) ?? "#EF4444",
    points,
    style: asString(record.style),
  };
};

const buildEventSeries = (data: Record<string, unknown>): SeriesEntry[] => {
  const chartId = asString(data.chartId);
  if (chartId === "code_cost_triple_line") {
    return [
      {
        label: "Cost to generate",
        color: "#4A90D9",
        points: [
          { x: 0, y: 82 },
          { x: 1, y: 78 },
          { x: 2, y: 58 },
          { x: 3, y: 36 },
          { x: 4, y: 18 },
        ],
      },
      {
        label: "Immediate patch cost",
        color: "#D9944A",
        points: [
          { x: 0, y: 42 },
          { x: 1, y: 38 },
          { x: 2, y: 31 },
          { x: 3, y: 24 },
          { x: 4, y: 20 },
        ],
      },
      {
        label: "Total cost (with debt)",
        color: "#FBBF24",
        points: [
          { x: 0, y: 58 },
          { x: 1, y: 59 },
          { x: 2, y: 60 },
          { x: 3, y: 60 },
          { x: 4, y: 61 },
        ],
        style: "dashed",
      },
    ];
  }

  const crossings = Array.isArray(data.crossings)
    ? data.crossings
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  if (crossings.length === 0) {
    return [];
  }

  return [
    {
      label: "Primary trend",
      color: "#60A5FA",
      points: [
        { x: 0, y: 80 },
        { x: 1, y: 60 },
        { x: 2, y: 42 },
        { x: 3, y: 28 },
        { x: 4, y: 18 },
      ],
    },
    {
      label: "Reference line",
      color: "#D9944A",
      points: [
        { x: 0, y: 44 },
        { x: 1, y: 38 },
        { x: 2, y: 31 },
        { x: 3, y: 25 },
        { x: 4, y: 21 },
      ],
    },
  ];
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
          const degradationSeries = buildDegradationSeries(record);
          if (degradationSeries) {
            return degradationSeries;
          }
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

  const eventSeries = buildEventSeries(data);
  if (eventSeries.length > 0) {
    return eventSeries;
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
  const explicitTitle = resolveExplicitTitle(data);

  if (!hasExplicitHeaderCopy(data) || (!eyebrow && !explicitTitle && subtitleLines.length === 0)) {
    return null;
  }

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
      {eyebrow ? (
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
      ) : null}
      {explicitTitle ? (
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
      ) : null}
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
  const explicitTitle = resolveExplicitTitle(data);
  const titleLines = explicitTitle ? resolveTitleLines(data) : [];
  const subtitleLines = resolveSubtitleLines(data);
  const commands = asStringArray(data.commands);
  const style = asString(data.style);
  const isStillnessBeat = style === "stillness_beat";
  const eyebrow = resolveEyebrow(data);
  const titleColor = asString(data.titleColor) ?? "#E2E8F0";
  const ruleColor = "rgba(51, 65, 85, 0.4)";
  const subtitleColor = asString(data.subtitleColor) ?? "#CBD5E1";
  const hasCodeUnderlay = Boolean(data.codeUnderlay);

  const resolvedTitleLines =
    isStillnessBeat && !explicitTitle ? [] : titleLines;

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
          backgroundSize: "80px 80px",
          opacity: isStillnessBeat ? 0.3 : 0.45,
        }}
      />
      {hasCodeUnderlay ? (
        <div
          style={{
            position: "absolute",
            inset: "8% 14% auto 10%",
            color: "rgba(148, 163, 184, 0.14)",
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 20,
            lineHeight: 1.45,
            whiteSpace: "pre-wrap",
            transform: "rotate(-6deg)",
          }}
        >
          {`def regenerate(module):\n    tests = load_accumulated_tests(module)\n    prompt = load_prompt(module)\n    return pdd.generate(prompt, tests)\n\n# prompt-driven development`}
        </div>
      ) : null}
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
        {eyebrow ? (
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
        ) : null}
        {isStillnessBeat || resolvedTitleLines.length > 1 ? (
          <div
            style={{
              width: 300,
              height: 2,
              backgroundColor: ruleColor,
              borderRadius: 999,
              opacity: resolvedTitleLines.length > 1 ? 0.9 : 1,
            }}
          />
        ) : null}
        {resolvedTitleLines.length > 0 ? (
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
            {resolvedTitleLines.join("\n")}
          </div>
        ) : null}
        {subtitleLines.map((line, index) => (
          <div
            key={`${line}-${index}`}
            style={{
              color: index === 0 ? subtitleColor : "#94A3B8",
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
  const threshold = asRecord(data.threshold);
  const debtShading = asRecord(data.debtShading);
  const crossings = Array.isArray(data.crossings)
    ? data.crossings
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const causalChain = asStringArray(data.causalChain);
  const keyDates = Array.isArray(data.keyDates)
    ? data.keyDates
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const debtResetNote = asString(data.debtResetNote);
  const annotations = Array.isArray(data.annotations)
    ? data.annotations
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const trapArrow = asRecord(data.trapArrow);
  const eventLabel = asString(data.label) ?? asString(asRecord(data.takeaway)?.line1);
  const eventSubLabel =
    debtResetNote ??
    asString(data.newAnnotation) ??
    asString(asRecord(data.takeaway)?.line2);
  const showInsetCallout = data.type === "inset_chart" && causalChain.length > 0;
  const chartWidth = width * 0.72;
  const chartHeight = height * 0.5;
  const seriesBounds = computeSeriesBounds(series);
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
          {debtShading ? (
            <rect
              x={chartWidth * 0.18}
              y={chartHeight * 0.22}
              width={chartWidth * 0.56}
              height={chartHeight * 0.5}
              fill="rgba(217, 148, 74, 0.08)"
            />
          ) : null}
          {showInsetCallout ? (
            <rect
              x={chartWidth * 0.52}
              y={chartHeight * 0.18}
              width={chartWidth * 0.34}
              height={chartHeight * 0.58}
              rx={28}
              fill="rgba(2, 6, 23, 0.22)"
              stroke="rgba(148, 163, 184, 0.22)"
              strokeWidth={2}
            />
          ) : null}
          {series.map((entry) => (
            <path
              key={entry.label}
              d={buildChartPath(entry.points, chartWidth, chartHeight, seriesBounds)}
              fill="none"
              stroke={entry.color}
              strokeWidth={4}
              strokeDasharray={entry.style === "dashed" ? "16 10" : undefined}
              strokeLinecap="round"
              strokeLinejoin="round"
              opacity={reveal}
            />
          ))}
          {threshold ? (
            <g>
              <circle
                cx={chartWidth * 0.32}
                cy={chartHeight * 0.54}
                r={10}
                fill="rgba(226, 232, 240, 0.18)"
                stroke="#E2E8F0"
                strokeWidth={3}
              />
              <text
                x={chartWidth * 0.32 + 18}
                y={chartHeight * 0.54 - 14}
                fill="#E2E8F0"
                fontSize="22"
                fontWeight="700"
              >
                {asString(threshold.label) ?? "Threshold"}
              </text>
            </g>
          ) : null}
          {crossings.map((crossing, index) => (
            <g key={`crossing-${index}`}>
              <circle
                cx={chartWidth * (0.58 + index * 0.16)}
                cy={chartHeight * (0.42 + index * 0.1)}
                r={asNumber(crossing.radius) ?? 10}
                fill="rgba(96, 165, 250, 0.18)"
                stroke="#60A5FA"
                strokeWidth={3}
              />
            </g>
          ))}
          {keyDates.slice(0, 4).map((entry, index) => (
            <g key={`key-date-${index}`}>
              <line
                x1={chartWidth * (0.12 + index * 0.17)}
                y1={chartHeight - 32}
                x2={chartWidth * (0.12 + index * 0.17)}
                y2={chartHeight - 14}
                stroke="rgba(148, 163, 184, 0.45)"
                strokeWidth={2}
              />
              <text
                x={chartWidth * (0.12 + index * 0.17)}
                y={chartHeight - 4}
                textAnchor="middle"
                fill="#94A3B8"
                fontSize="16"
              >
                {asString(entry.label) ?? ""}
              </text>
            </g>
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
        {showInsetCallout ? (
          <div
            style={{
              position: "absolute",
              left: chartWidth * 0.56,
              top: chartHeight * 0.24,
              width: chartWidth * 0.26,
              display: "flex",
              flexDirection: "column",
              gap: 10,
            }}
          >
            {causalChain.slice(0, 3).map((item, index) => (
              <div
                key={`${item}-${index}`}
                style={{
                  color: index === 2 ? "#EF4444" : "#E2E8F0",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 22,
                  fontWeight: 700,
                }}
              >
                {item}
              </div>
            ))}
          </div>
        ) : null}
        {eventLabel ? (
          <div
            style={{
              position: "absolute",
              right: 28,
              bottom: 64,
              maxWidth: chartWidth * 0.34,
              color: "#E2E8F0",
              fontFamily: "'Inter', sans-serif",
              fontSize: 24,
              fontWeight: 700,
              textAlign: "right",
            }}
          >
            {eventLabel}
          </div>
        ) : null}
        {eventSubLabel ? (
          <div
            style={{
              position: "absolute",
              right: 28,
              bottom: 30,
              maxWidth: chartWidth * 0.42,
              color: "#94A3B8",
              fontFamily: "'Inter', sans-serif",
              fontSize: 18,
              fontWeight: 500,
              textAlign: "right",
              lineHeight: 1.3,
            }}
          >
            {eventSubLabel}
          </div>
        ) : null}
        {annotations.length > 0 ? (
          <div
            style={{
              position: "absolute",
              left: 28,
              bottom: 28,
              display: "flex",
              flexDirection: "column",
              gap: 10,
              maxWidth: chartWidth * 0.42,
            }}
          >
            {annotations.slice(0, 2).map((entry, index) => (
              <div
                key={`annotation-${index}`}
                style={{
                  padding: "10px 14px",
                  borderRadius: 16,
                  backgroundColor: "rgba(2, 6, 23, 0.8)",
                  border: `1px solid ${(asString(entry.color) ?? "#60A5FA")}44`,
                }}
              >
                <div
                  style={{
                    color: asString(entry.color) ?? "#60A5FA",
                    fontFamily: "'Inter', sans-serif",
                    fontSize: 16,
                    fontWeight: 700,
                  }}
                >
                  {asString(entry.header) ?? asString(entry.text) ?? "Annotation"}
                </div>
                <div
                  style={{
                    color: "#CBD5E1",
                    fontFamily: "'Inter', sans-serif",
                    fontSize: 15,
                    marginTop: 4,
                  }}
                >
                  {asString(entry.source) ?? asString(entry.detail) ?? ""}
                </div>
              </div>
            ))}
          </div>
        ) : null}
        {trapArrow ? (
          <div
            style={{
              position: "absolute",
              left: chartWidth * 0.3,
              top: chartHeight * 0.18,
              transform: "translateX(-50%)",
              display: "flex",
              alignItems: "center",
              gap: 10,
              color: asString(trapArrow.color) ?? "#D9944A",
              fontFamily: "'Inter', sans-serif",
              fontSize: 18,
              fontWeight: 700,
            }}
          >
            <span>{asString(trapArrow.label) ?? "Trap"}</span>
            <span style={{ fontSize: 24 }}>↓</span>
          </div>
        ) : null}
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
  const visualType = asString(data.type);
  const fileNames = [
    asString(data.highlightedModule),
    asString(data.promptFile),
    ...asStringArray(data.fileNames),
  ].filter((item): item is string => Boolean(item));
  const workflow = asStringArray(data.workflow);
  const warningComments = asStringArray(data.warningComments);
  const lineCount = asString(data.lineCount);
  const terminalLines = [
    asString(data.terminalCommand),
    asString(data.terminalOutput),
    ...workflow,
    ...asStringArray(data.terminalCommands),
  ].filter((item): item is string => Boolean(item));

  if (visualType === "code_visualization") {
    const panels = Math.max(3, asNumber(data.panels) ?? fileNames.length ?? 5);
    const panelNames =
      fileNames.length > 0
        ? fileNames
        : Array.from({ length: panels }, (_, index) => `module_${index + 1}.py`);

    return (
      <AbsoluteFill style={{ padding: "92px 96px 80px" }}>
        <div
          style={{
            position: "absolute",
            inset: 0,
            background:
              "radial-gradient(circle at center, rgba(15, 23, 42, 0.18) 0%, rgba(10, 15, 26, 0) 60%)",
          }}
        />
        <div
          style={{
            position: "relative",
            width,
            height,
          }}
        >
          {panelNames.slice(0, panels).map((name, index) => (
            <div
              key={`${name}-${index}`}
              style={{
                position: "absolute",
                left: 120 + index * 90,
                top: 60 + (index % 2) * 24,
                width: 520,
                height: 680,
                borderRadius: 24,
                backgroundColor: "rgba(2, 6, 23, 0.9)",
                border: "1px solid rgba(71, 85, 105, 0.44)",
                boxShadow: "0 24px 80px rgba(2, 6, 23, 0.36)",
                overflow: "hidden",
                transform: `rotate(${(index - 2) * 1.6}deg)`,
              }}
            >
              <div
                style={{
                  height: 48,
                  display: "flex",
                  alignItems: "center",
                  padding: "0 18px",
                  backgroundColor: "rgba(15, 23, 42, 0.96)",
                  color: "#CBD5E1",
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 15,
                }}
              >
                {name}
              </div>
              <div
                style={{
                  display: "grid",
                  gridTemplateColumns: "52px 1fr",
                  rowGap: 8,
                  padding: "18px 18px 20px",
                }}
              >
                {Array.from({ length: 16 }).map((_, lineIndex) => {
                  const comment =
                    warningComments[(lineIndex + index) % Math.max(1, warningComments.length)];
                  const showComment = Boolean(comment) && [2, 6, 11].includes(lineIndex);
                  return (
                    <React.Fragment key={`viz-line-${index}-${lineIndex}`}>
                      <div
                        style={{
                          color: "rgba(148, 163, 184, 0.55)",
                          fontFamily: "'JetBrains Mono', monospace",
                          fontSize: 14,
                        }}
                      >
                        {lineIndex + 1}
                      </div>
                      <div
                        style={{
                          color: showComment ? "#FCA5A5" : "#94A3B8",
                          fontFamily: "'JetBrains Mono', monospace",
                          fontSize: 15,
                          whiteSpace: "pre",
                        }}
                      >
                        {showComment
                          ? comment
                          : lineIndex % 4 === 0
                            ? "def legacy_handler(user, state):"
                            : lineIndex % 4 === 1
                              ? "    payload = adapter.load(state)"
                              : lineIndex % 4 === 2
                                ? "    if payload is None: return cache_fallback()"
                                : "    return transform(payload, user)"}
                      </div>
                    </React.Fragment>
                  );
                })}
              </div>
            </div>
          ))}
          {lineCount ? (
            <div
              style={{
                position: "absolute",
                right: 120,
                bottom: 68,
                padding: "12px 18px",
                borderRadius: 999,
                backgroundColor: "rgba(2, 6, 23, 0.82)",
                border: subtleBorder,
                color: accent,
                fontFamily: "'Inter', sans-serif",
                fontSize: 22,
                fontWeight: 700,
              }}
            >
              {lineCount}
            </div>
          ) : null}
        </div>
      </AbsoluteFill>
    );
  }

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
  const panels = Array.isArray(data.panels)
    ? data.panels.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const scenarios = Array.isArray(data.scenarios)
    ? data.scenarios.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
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
  const document = asRecord(data.document);
  const codeBlock = asRecord(data.codeBlock);
  const annotations = asRecord(data.annotations);
  const embeddedCodeBlocks = Array.isArray(data.embeddedCodeBlocks)
    ? data.embeddedCodeBlocks.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const ratchetMetaphor = asRecord(data.ratchetMetaphor);
  const statusDelay = asNumber(data.statusDelay);
  const bottomLabel = asString(data.bottomLabel);
  const promptDocument = asRecord(data.promptDocument);
  const testSuite = asRecord(data.testSuite);
  const reviewLabel = asString(data.reviewLabel);
  const moldAnimation = asRecord(data.moldAnimation);
  const netlists = Array.isArray(data.netlists)
    ? data.netlists.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const equivalenceLabel = asString(data.equivalenceLabel);
  const takeaways = [
    ...asStringArray(data.causalChain),
    ...asStringArray(data.terminalCommands),
    ...asStringArray(data.hierarchy),
    ...asStringArray(data.priorityRule ? [data.priorityRule] : []),
  ].slice(0, 5);

  let body: React.ReactNode;
  if (diagramId === "code_generation_comparison" && scenarios.length > 0) {
    const takeaway = asRecord(data.takeaway);
    body = (
      <div
        style={{
          width: width * 0.82,
          display: "grid",
          gridTemplateColumns: "1fr 1fr",
          gap: 24,
        }}
      >
        {scenarios.slice(0, 2).map((scenario, index) => {
          const preferred = Boolean(scenario.preferred);
          const promptLines = asNumber(scenario.promptLines) ?? 0;
          const testCount = asNumber(scenario.testCount) ?? 0;
          return (
            <div
              key={`scenario-${index}`}
              style={{
                borderRadius: 28,
                backgroundColor: subtleSurface,
                border: preferred ? "1px solid rgba(74, 222, 128, 0.55)" : subtleBorder,
                padding: "26px 28px",
                display: "flex",
                flexDirection: "column",
                gap: 18,
              }}
            >
              <div style={{ color: preferred ? "#4ADE80" : "#94A3B8", fontSize: 18, fontWeight: 700 }}>
                {asString(scenario.side)?.toUpperCase() ?? `SIDE ${index + 1}`}
              </div>
              <div style={{ color: "#E2E8F0", fontFamily: "'JetBrains Mono', monospace", fontSize: 18 }}>
                {asString(scenario.promptFile) ?? `prompt_v${index + 1}.md`}
              </div>
              <div style={{ display: "flex", gap: 14 }}>
                <div style={{ flex: 1, padding: "14px 16px", borderRadius: 18, backgroundColor: "rgba(96, 165, 250, 0.14)" }}>
                  <div style={{ color: "#60A5FA", fontSize: 16, fontWeight: 700 }}>Prompt</div>
                  <div style={{ color: "#F8FAFC", fontSize: 34, fontWeight: 700 }}>{promptLines}</div>
                </div>
                <div style={{ flex: 1, padding: "14px 16px", borderRadius: 18, backgroundColor: "rgba(217, 148, 74, 0.14)" }}>
                  <div style={{ color: "#D9944A", fontSize: 16, fontWeight: 700 }}>Tests</div>
                  <div style={{ color: "#F8FAFC", fontSize: 34, fontWeight: 700 }}>{testCount}</div>
                </div>
              </div>
              <div style={{ color: preferred ? "#4ADE80" : "#CBD5E1", fontSize: 22, fontWeight: 700 }}>
                {asString(scenario.result) ?? "correct"}
              </div>
            </div>
          );
        })}
        <div
          style={{
            gridColumn: "1 / -1",
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            gap: 8,
            marginTop: 8,
          }}
        >
          <div style={{ color: "#E2E8F0", fontSize: 34, fontWeight: 700 }}>
            {asString(takeaway?.line1) ?? "More tests, less prompt."}
          </div>
          <div style={{ color: "#94A3B8", fontSize: 24, fontWeight: 600 }}>
            {asString(takeaway?.line2) ?? "The walls do the precision work."}
          </div>
        </div>
      </div>
    );
  } else if (diagramId === "prompt_ratio") {
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
  } else if (diagramId === "verilog_synthesis_triple" && netlists.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.84,
          display: "grid",
          gridTemplateColumns: "repeat(3, minmax(0, 1fr))",
          gap: 18,
        }}
      >
        {netlists.slice(0, 3).map((netlist, index) => (
          <div
            key={`netlist-${index}`}
            style={{
              borderRadius: 24,
              backgroundColor: subtleSurface,
              border: `1px solid ${(asString(netlist.color) ?? "#60A5FA")}66`,
              padding: "22px 20px",
              display: "flex",
              flexDirection: "column",
              gap: 14,
            }}
          >
            <div style={{ color: "#94A3B8", fontSize: 16, fontWeight: 700 }}>
              {`RUN ${index + 1}`}
            </div>
            <div style={{ color: "#E2E8F0", fontFamily: "'JetBrains Mono', monospace", fontSize: 15, whiteSpace: "pre-wrap" }}>
              {`module chip_${index + 1}(...);\n  assign y = a & b;\nendmodule`}
            </div>
            <div
              style={{
                height: 170,
                borderRadius: 18,
                background: `linear-gradient(135deg, ${(asString(netlist.color) ?? "#60A5FA")}22, rgba(15, 23, 42, 0.92))`,
                border: `1px solid ${(asString(netlist.color) ?? "#60A5FA")}44`,
              }}
            />
            <div style={{ color: asString(netlist.color) ?? "#4ADE80", fontSize: 18, fontWeight: 700 }}>
              {equivalenceLabel ?? "Functionally equivalent"}
            </div>
          </div>
        ))}
      </div>
    );
  } else if (diagramId === "five_generations") {
    const generations = panels.length > 0 ? panels : phases.length > 0 ? phases : steps;
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
              minHeight: 320,
            }}
          >
            <div style={{ color: asString(entry.color) ?? "#60A5FA", fontSize: 18, fontWeight: 700 }}>
              {asString(entry.label) ?? `Generation ${index + 1}`}
            </div>
            <div
              style={{
                flex: 1,
                borderRadius: 16,
                backgroundColor: "rgba(2, 6, 23, 0.72)",
                border: "1px solid rgba(71, 85, 105, 0.24)",
                padding: "14px 16px",
                color: "#94A3B8",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 14,
                lineHeight: 1.45,
              }}
            >
              {`def candidate_${index + 1}(user_id):\n    return normalize(user_id)\n\n# ${asString(entry.status) ?? "candidate"}`}
            </div>
            <div style={{ color: "#E2E8F0", fontSize: 24, lineHeight: 1.2, marginTop: 14 }}>
              {asString(entry.detail) ?? asString(entry.text) ?? asString(entry.status) ?? ""}
            </div>
          </div>
        ))}
      </div>
    );
  } else if (
    diagramId === "embedded_code_document" &&
    (embeddedCodeBlocks.length > 0 || document || codeBlock || annotations || bottomLabel)
  ) {
    const nlLabel = asString(annotations?.nlLabel) ?? "Natural language";
    const codeLabel = asString(annotations?.codeLabel) ?? "Critical algorithm";
    body = (
      <div
        style={{
          width: width * 0.78,
          display: "grid",
          gridTemplateColumns: "1.1fr 0.9fr",
          gap: 24,
        }}
      >
        <div style={{ borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder, padding: "24px 28px", display: "flex", flexDirection: "column", gap: 18 }}>
          <div style={{ padding: "14px 18px", borderRadius: 18, backgroundColor: "rgba(45, 212, 191, 0.12)", borderLeft: "4px solid #2DD4BF", color: "#CCFBF1", fontSize: 18 }}>
            {`${nlLabel}\n\nIntent, constraints, and architecture live here.`}
          </div>
          <div style={{ padding: "16px 18px", borderRadius: 18, backgroundColor: "rgba(96, 165, 250, 0.12)", borderLeft: "4px solid #60A5FA" }}>
            <div style={{ color: "#60A5FA", fontSize: 18, fontWeight: 700 }}>{codeLabel}</div>
            <div style={{ color: "#CBD5E1", fontFamily: "'JetBrains Mono', monospace", fontSize: 16, marginTop: 8, whiteSpace: "pre-wrap" }}>
              {`def ${asString(codeBlock?.function) ?? "hash_id"}(user_id):\n    return sha256(user_id.encode()).hexdigest()[:12]`}
            </div>
          </div>
          {embeddedCodeBlocks.slice(0, 2).map((block, index) => (
            <div key={`code-block-${index}`} style={{ marginBottom: 8 }}>
              <div style={{ color: "#2DD4BF", fontSize: 18, fontWeight: 700 }}>{asString(block.title) ?? asString(block.label) ?? `Block ${index + 1}`}</div>
              <div style={{ color: "#CBD5E1", fontFamily: "'JetBrains Mono', monospace", fontSize: 16, marginTop: 8, whiteSpace: "pre-wrap" }}>
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
          {document ? (
            <div style={{ color: "#94A3B8", fontSize: 18, marginTop: 10 }}>
              {`${asNumber(document.totalLines) ?? 18} total lines • ${asNumber(document.codeLines) ?? 4} code`}
            </div>
          ) : null}
          {bottomLabel ? (
            <div style={{ color: "#E2E8F0", fontSize: 22, fontWeight: 700, marginTop: 18 }}>
              {bottomLabel}
            </div>
          ) : null}
        </div>
      </div>
    );
  } else if (diagramId === "context_compression") {
    const moduleCount = Math.max(8, asNumber(data.moduleCount) ?? 20);
    const overflowCount = Math.max(0, asNumber(data.overflowCount) ?? 0);
    const ratio = asString(data.compressionRatio) ?? "5-10×";
    body = (
      <div
        style={{
          width: width * 0.84,
          display: "grid",
          gridTemplateColumns: "1.05fr 0.95fr",
          gap: 24,
          alignItems: "center",
        }}
      >
        <div
          style={{
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            padding: "28px 30px",
            display: "grid",
            gridTemplateColumns: "repeat(5, minmax(0, 1fr))",
            gap: 14,
            minHeight: 420,
          }}
        >
          {Array.from({ length: moduleCount }).map((_, index) => (
            <div
              key={`module-${index}`}
              style={{
                height: 82,
                borderRadius: 16,
                backgroundColor: index < moduleCount - overflowCount ? "rgba(74, 144, 217, 0.16)" : "rgba(239, 68, 68, 0.16)",
                border: `1px solid ${index < moduleCount - overflowCount ? "rgba(74, 144, 217, 0.44)" : "rgba(239, 68, 68, 0.44)"}`,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                color: index < moduleCount - overflowCount ? "#BFDBFE" : "#FCA5A5",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 14,
              }}
            >
              {`mod_${index + 1}`}
            </div>
          ))}
        </div>
        <div
          style={{
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            padding: "28px 30px",
            minHeight: 420,
            position: "relative",
          }}
        >
          <div
            style={{
              width: asNumber(asRecord(data.contextWindow)?.width) ?? 600,
              maxWidth: "100%",
              height: asNumber(asRecord(data.contextWindow)?.height) ?? 500,
              maxHeight: 320,
              margin: "0 auto",
              borderRadius: 24,
              border: "2px solid rgba(74, 144, 217, 0.65)",
              boxShadow: "0 0 0 1px rgba(74, 144, 217, 0.18) inset",
              padding: 22,
              display: "grid",
              gridTemplateColumns: "repeat(5, minmax(0, 1fr))",
              gap: 10,
            }}
          >
            {Array.from({ length: Math.max(8, moduleCount - overflowCount) }).map((_, index) => (
              <div
                key={`prompt-${index}`}
                style={{
                  height: 34,
                  borderRadius: 12,
                  backgroundColor: "rgba(45, 212, 191, 0.18)",
                  border: "1px solid rgba(45, 212, 191, 0.4)",
                }}
              />
            ))}
          </div>
          <div
            style={{
              position: "absolute",
              right: 34,
              top: 34,
              padding: "10px 16px",
              borderRadius: 999,
              backgroundColor: "rgba(45, 212, 191, 0.14)",
              color: "#2DD4BF",
              fontSize: 28,
              fontWeight: 700,
            }}
          >
            {ratio}
          </div>
          <div
            style={{
              position: "absolute",
              left: 34,
              bottom: 30,
              color: "#E2E8F0",
              fontSize: 24,
              fontWeight: 700,
            }}
          >
            {asString(data.resultLabel) ?? "Same system. More fits."}
          </div>
        </div>
      </div>
    );
  } else if (diagramId === "mold_defect_fix") {
    const elements = asRecord(data.elements);
    const counter = asRecord(elements?.counter);
    body = (
      <div
        style={{
          width: width * 0.84,
          display: "grid",
          gridTemplateColumns: "1.2fr 0.8fr",
          gap: 24,
          alignItems: "center",
        }}
      >
        <div
          style={{
            position: "relative",
            minHeight: 420,
            borderRadius: 32,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            overflow: "hidden",
          }}
        >
          <div style={{ position: "absolute", left: 60, right: 60, top: 220, height: 10, backgroundColor: "rgba(148, 163, 184, 0.35)" }} />
          <div style={{ position: "absolute", left: 120, top: 100, width: 320, height: 180, borderRadius: 28, border: "2px solid rgba(217, 148, 74, 0.7)" }} />
          {Array.from({ length: 5 }).map((_, index) => (
            <div
              key={`part-${index}`}
              style={{
                position: "absolute",
                left: 560 + index * 72,
                top: index === 1 ? 196 : 176,
                width: 52,
                height: 52,
                borderRadius: 16,
                backgroundColor: index === 1 ? "#EF4444" : "#4A90D9",
                boxShadow: index === 1 ? "0 0 18px rgba(239, 68, 68, 0.4)" : undefined,
              }}
            />
          ))}
          <div
            style={{
              position: "absolute",
              left: 380,
              top: 76,
              width: 64,
              height: 64,
              borderRadius: 999,
              border: "3px solid rgba(251, 191, 36, 0.8)",
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              color: "#FBBF24",
              fontSize: 28,
              fontWeight: 700,
            }}
          >
            🔧
          </div>
        </div>
        <div
          style={{
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            padding: "28px 30px",
            display: "flex",
            flexDirection: "column",
            gap: 16,
          }}
        >
          <div style={{ color: "#4ADE80", fontSize: 48, fontWeight: 800 }}>
            {asString(counter?.maxValue) ?? "10000+"}
          </div>
          <div style={{ color: "#E2E8F0", fontSize: 28, fontWeight: 700 }}>
            All future parts inherit the fix
          </div>
          <div style={{ color: "#94A3B8", fontSize: 20, lineHeight: 1.4 }}>
            defect found → fix mold → every new part is correct
          </div>
        </div>
      </div>
    );
  } else if (diagramId === "bug_add_wall") {
    body = (
      <div
        style={{
          width: width * 0.84,
          display: "grid",
          gridTemplateColumns: "1.05fr 0.95fr",
          gap: 24,
        }}
      >
        <div style={{ borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder, padding: "24px 26px" }}>
          <div style={{ color: "#94A3B8", fontSize: 18, fontWeight: 700, letterSpacing: 1.6 }}>CODE</div>
          <div style={{ marginTop: 16, display: "grid", gridTemplateColumns: "48px 1fr", rowGap: 8 }}>
            {Array.from({ length: 10 }).map((_, index) => (
              <React.Fragment key={`bug-line-${index}`}>
                <div style={{ color: "#475569", fontFamily: "'JetBrains Mono', monospace", fontSize: 14 }}>{index + 1}</div>
                <div style={{ color: index === 4 ? "#FCA5A5" : "#CBD5E1", fontFamily: "'JetBrains Mono', monospace", fontSize: 16 }}>
                  {index === 4 ? "if user_id is None: return None" : "normalize_user(user_id)"}
                </div>
              </React.Fragment>
            ))}
          </div>
        </div>
        <div style={{ display: "flex", flexDirection: "column", gap: 20 }}>
          <div style={{ borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder, minHeight: 240, position: "relative" }}>
            <div style={{ position: "absolute", left: 44, right: 44, top: 52, height: 18, borderRadius: 999, backgroundColor: "rgba(45, 212, 191, 0.4)" }} />
            <div style={{ position: "absolute", left: 44, right: 44, bottom: 52, height: 18, borderRadius: 999, backgroundColor: "rgba(217, 148, 74, 0.7)" }} />
            <div style={{ position: "absolute", right: 120, top: 84, bottom: 84, width: 16, borderRadius: 999, backgroundColor: "#D9944A", boxShadow: "0 0 18px rgba(217, 148, 74, 0.4)" }} />
          </div>
          <div style={{ borderRadius: 24, backgroundColor: "rgba(2, 6, 23, 0.82)", border: subtleBorder, padding: "20px 22px" }}>
            {asStringArray(data.terminalCommands).slice(0, 3).map((line, index) => (
              <div key={`${line}-${index}`} style={{ color: index === 0 ? "#E2E8F0" : "#4ADE80", fontFamily: "'JetBrains Mono', monospace", fontSize: 16, marginTop: index === 0 ? 0 : 8 }}>
                {index === 0 ? `$ ${line}` : `✓ ${line}`}
              </div>
            ))}
          </div>
        </div>
      </div>
    );
  } else if (diagramId === "ratchet_timelapse") {
    body = (
      <div
        style={{
          width: width * 0.84,
          display: "grid",
          gridTemplateColumns: "1.1fr 0.9fr",
          gap: 24,
        }}
      >
        <div
          style={{
            position: "relative",
            minHeight: 420,
            borderRadius: 28,
            backgroundColor: subtleSurface,
            border: subtleBorder,
            overflow: "hidden",
          }}
        >
          <div style={{ position: "absolute", left: 110, right: 110, top: 70, bottom: 70, border: "2px solid rgba(148, 163, 184, 0.28)", borderRadius: 28 }} />
          {Array.from({ length: 25 }).map((_, index) => (
            <div
              key={`wall-${index}`}
              style={{
                position: "absolute",
                left: 150 + (index % 5) * 72,
                top: 120 + Math.floor(index / 5) * 44,
                width: 20,
                height: 34,
                borderRadius: 999,
                backgroundColor: "rgba(217, 148, 74, 0.92)",
                boxShadow: "0 0 12px rgba(217, 148, 74, 0.5)",
              }}
            />
          ))}
          <div style={{ position: "absolute", right: 42, top: 36, color: "#D9944A", fontSize: 64, fontWeight: 800 }}>25</div>
          <div style={{ position: "absolute", left: 46, bottom: 36, right: 46, color: "#E2E8F0", fontSize: 22, fontWeight: 700 }}>
            Tests only accumulate. The mold only gets more precise.
          </div>
        </div>
        <div style={{ display: "flex", flexDirection: "column", gap: 18 }}>
          <div style={{ borderRadius: 28, backgroundColor: subtleSurface, border: subtleBorder, padding: "24px 28px" }}>
            <div style={{ color: "#D9944A", fontSize: 18, fontWeight: 700 }}>
              Ratchet effect
            </div>
            <div style={{ color: "#E2E8F0", fontSize: 24, marginTop: 12 }}>
              Walls accumulate. They do not disappear.
            </div>
          </div>
          <div style={{ borderRadius: 24, backgroundColor: "rgba(2, 6, 23, 0.82)", border: subtleBorder, padding: "20px 22px" }}>
            {Array.from({ length: 5 }).map((_, index) => (
              <div key={`test-${index}`} style={{ color: "#4ADE80", fontFamily: "'JetBrains Mono', monospace", fontSize: 16, marginTop: index === 0 ? 0 : 8 }}>
                {`✓ test_case_${index + 21}`}
              </div>
            ))}
          </div>
        </div>
      </div>
    );
  } else if (diagramId === "grounding_feedback_loop") {
    const pipeline = phases.find((phase) => asString(phase.id) === "pipeline");
    const stages = asStringArray(pipeline?.stages);
    const pathPhase = phases.find((phase) => asString(phase.id) === "dual_grounding");
    const paths = Array.isArray(pathPhase?.paths)
      ? pathPhase.paths.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];
    body = (
      <div
        style={{
          width: width * 0.84,
          display: "grid",
          gridTemplateColumns: "1fr 1fr",
          gap: 24,
          alignItems: "center",
        }}
      >
        <div style={{ display: "flex", flexDirection: "column", gap: 18 }}>
          {paths.slice(0, 2).map((entry, index) => (
            <div
              key={`path-${index}`}
              style={{
                padding: "24px 26px",
                borderRadius: 24,
                backgroundColor: subtleSurface,
                border: `1px solid ${(asString(entry.color) ?? (index === 0 ? "#4A90D9" : "#4ADE80"))}55`,
              }}
            >
              <div style={{ color: asString(entry.color) ?? (index === 0 ? "#4A90D9" : "#4ADE80"), fontSize: 20, fontWeight: 700 }}>
                {asString(entry.label) ?? `Path ${index + 1}`}
              </div>
              <div style={{ color: "#CBD5E1", fontSize: 18, marginTop: 10 }}>
                {asString(entry.style) ?? "grounding path"}
              </div>
            </div>
          ))}
          <div style={{ padding: "18px 22px", borderRadius: 20, backgroundColor: "rgba(167, 139, 250, 0.12)", border: "1px solid rgba(167, 139, 250, 0.35)", color: "#E9D5FF", fontSize: 20, fontWeight: 700 }}>
            {asString(asRecord(phases.find((phase) => asString(phase.id) === "feedback"))?.flow) ?? "(prompt, code) → Grounding Database"}
          </div>
        </div>
        <div style={{ display: "flex", gap: 14, alignItems: "center", justifyContent: "space-between" }}>
          {(stages.length > 0 ? stages : ["Prompt", "Grounding", "Mold", "Test Walls", "Code"]).slice(0, 5).map((stage, index, allStages) => (
            <React.Fragment key={stage}>
              <div
                style={{
                  flex: 1,
                  padding: "22px 12px",
                  borderRadius: 22,
                  backgroundColor: subtleSurface,
                  border: `1px solid ${index === 0 ? "rgba(45, 212, 191, 0.44)" : index === 1 ? "rgba(167, 139, 250, 0.44)" : index === 2 ? "rgba(96, 165, 250, 0.44)" : index === 3 ? "rgba(217, 148, 74, 0.44)" : "rgba(74, 222, 128, 0.44)"}`,
                  color: "#E2E8F0",
                  fontSize: 18,
                  fontWeight: 700,
                  textAlign: "center",
                }}
              >
                {stage}
              </div>
              {index < allStages.length - 1 ? (
                <div style={{ color: "#94A3B8", fontSize: 28, fontWeight: 700 }}>→</div>
              ) : null}
            </React.Fragment>
          ))}
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
  } else if (diagramId === "prompt_replaces_review" && promptDocument && testSuite) {
    body = (
      <div
        style={{
          width: width * 0.8,
          display: "grid",
          gridTemplateColumns: "0.9fr 1.2fr 0.9fr",
          gap: 18,
          alignItems: "center",
        }}
      >
        <div style={{ borderRadius: 24, backgroundColor: subtleSurface, border: `1px solid ${(asString(promptDocument.glowColor) ?? "#4ADE80")}55`, padding: "22px 24px" }}>
          <div style={{ color: asString(promptDocument.glowColor) ?? "#4ADE80", fontSize: 18, fontWeight: 700 }}>
            {asString(promptDocument.label) ?? "PROMPT"}
          </div>
          <div style={{ color: "#E2E8F0", fontFamily: "'JetBrains Mono', monospace", fontSize: 16, marginTop: 12, whiteSpace: "pre-wrap" }}>
            {`- intent\n- requirements\n- constraints\n- edge cases`}
          </div>
        </div>
        <div style={{ position: "relative", height: 320, borderRadius: 28, backgroundColor: "rgba(2, 6, 23, 0.48)", overflow: "hidden" }}>
          <div style={{ position: "absolute", left: "50%", top: 36, bottom: 36, width: 220, transform: "translateX(-50%)", borderRadius: 120, backgroundColor: "rgba(148, 163, 184, 0.12)" }} />
          <div style={{ position: "absolute", left: 70, right: 70, top: 54, height: 14, borderRadius: 999, backgroundColor: asString(moldAnimation?.wallColor) ?? "#D9944A" }} />
          <div style={{ position: "absolute", left: 70, right: 70, bottom: 54, height: 14, borderRadius: 999, backgroundColor: asString(moldAnimation?.wallColor) ?? "#D9944A" }} />
          {Array.from({ length: 5 }).map((_, index) => (
            <div
              key={`code-stream-${index}`}
              style={{
                position: "absolute",
                left: 320 + index * 48,
                top: 74 + index * 36,
                width: 180,
                height: 16,
                borderRadius: 999,
                backgroundColor: asString(moldAnimation?.codeColor) ?? "#94A3B8",
                opacity: 0.9 - index * 0.12,
              }}
            />
          ))}
        </div>
        <div style={{ borderRadius: 24, backgroundColor: subtleSurface, border: "1px solid rgba(217, 148, 74, 0.55)", padding: "22px 24px" }}>
          <div style={{ color: "#D9944A", fontSize: 18, fontWeight: 700 }}>
            {asString(testSuite.label) ?? "TESTS"}
          </div>
          <div style={{ color: "#E2E8F0", fontFamily: "'JetBrains Mono', monospace", fontSize: 16, marginTop: 12 }}>
            {Array.from({ length: asNumber(testSuite.testCount) ?? 6 }).slice(0, 6).map((_, index) => (
              <div key={`test-${index}`}>{`✓ test_case_${index + 1}`}</div>
            ))}
          </div>
          {reviewLabel ? (
            <div style={{ color: "#CBD5E1", fontSize: 18, marginTop: 16 }}>
              {reviewLabel}
            </div>
          ) : null}
        </div>
      </div>
    );
  } else if (promptNozzle || promptText.length > 0 || nozzleLabels.length > 0) {
    body = (
      <div
        style={{
          width: width * 0.82,
          display: "grid",
          gridTemplateColumns: "0.75fr 1.05fr 0.95fr",
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
            {asString(data.promptFile) ? (
              <div style={{ color: "#94A3B8", fontFamily: "'JetBrains Mono', monospace", fontSize: 16 }}>
                {asString(data.promptFile)}
              </div>
            ) : null}
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
          <div style={{ color: "#2DD4BF", fontSize: 18, fontWeight: 700 }}>Dual generation</div>
          {Boolean(data.dualGeneration)
            ? ["A", "B"].map((variant) => (
                <div key={variant} style={{ padding: "12px 14px", borderRadius: 16, backgroundColor: "rgba(2, 6, 23, 0.72)" }}>
                  <div style={{ color: "#CBD5E1", fontFamily: "'JetBrains Mono', monospace", fontSize: 15 }}>
                    {`$ pdd generate ${asString(data.promptFile) ?? "user_parser.prompt"}`}
                  </div>
                  <div style={{ color: "#4ADE80", fontSize: 16, fontWeight: 700, marginTop: 8 }}>
                    {`✓ All tests passing (${variant})`}
                  </div>
                </div>
              ))
            : null}
          {Boolean(data.dualGeneration) ? (
            <div style={{ color: "#E2E8F0", fontSize: 18, fontWeight: 700, marginTop: 8 }}>
              Same prompt. Different code. Same behavior.
            </div>
          ) : null}
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
