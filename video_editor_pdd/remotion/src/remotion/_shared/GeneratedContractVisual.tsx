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
  useVisualDurationInFrames,
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

const asRecordArray = (value: unknown): Record<string, unknown>[] => {
  return Array.isArray(value)
    ? value
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
};

const extractTextList = (
  value: unknown,
  preferredKeys: string[] = ["text", "label", "name", "title", "comment"]
): string[] => {
  if (!Array.isArray(value)) {
    return [];
  }

  const values: string[] = [];
  for (const entry of value) {
    if (typeof entry === "string" && entry.trim()) {
      values.push(entry.trim());
      continue;
    }
    const record = asRecord(entry);
    if (!record) {
      continue;
    }
    const resolved = preferredKeys
      .map((key) => asString(record[key]))
      .find((item): item is string => Boolean(item));
    if (resolved) {
      values.push(resolved);
    }
  }
  return values;
};

const resolveContractChartId = (data: Record<string, unknown>): string | null => {
  const rawChartId =
    asString(data.chartId) ??
    asString(data.chartRef) ??
    asString(data.editorId);

  if (!rawChartId) {
    return null;
  }

  if (rawChartId === "code_cost_generate_vs_patch") {
    return "code_cost_triple_line";
  }

  if (rawChartId === "maintenance_cost_split") {
    return "maintenance_cost_pie";
  }

  return rawChartId;
};

const formatCompactMetric = (value: number): string => {
  const rounded = Math.round(value);
  if (rounded >= 10000) {
    return `${Math.round(rounded / 1000).toLocaleString()}000+`;
  }
  if (rounded >= 1000) {
    return rounded.toLocaleString();
  }
  return `${rounded}`;
};

const formatApproxTokenCount = (value: unknown): string | null => {
  if (typeof value === "number" && Number.isFinite(value)) {
    return `~${Math.round(value).toLocaleString()} tokens`;
  }

  const raw = asString(value);
  if (!raw) {
    return null;
  }

  const digitsOnly = raw.replace(/[^0-9]/g, "");
  if (!digitsOnly) {
    return raw.toLowerCase().includes("token") ? raw : `${raw} tokens`;
  }

  const numeric = Number(digitsOnly);
  if (!Number.isFinite(numeric)) {
    return raw;
  }

  const prefix = raw.trim().startsWith("~") ? "~" : "~";
  return `${prefix}${numeric.toLocaleString()} tokens`;
};

const formatExactTokenCount = (value: unknown): string | null => {
  if (typeof value === "number" && Number.isFinite(value)) {
    return `${Math.round(value).toLocaleString()} tokens`;
  }

  const raw = asString(value);
  if (!raw) {
    return null;
  }

  const digitsOnly = raw.replace(/[^0-9]/g, "");
  if (!digitsOnly) {
    return raw.toLowerCase().includes("token") ? raw : `${raw} tokens`;
  }

  const numeric = Number(digitsOnly);
  if (!Number.isFinite(numeric)) {
    return raw;
  }

  return `${numeric.toLocaleString()} tokens`;
};

const buildDenseCodePreviewLines = (variant: "dense" | "cluttered" | "clean"): string[] => {
  if (variant === "clean") {
    return [
      "intent: parse user ids from input",
      "constraints: return None on failure",
      "tests: malformed strings, unicode, whitespace",
      "grounding: team style, naming, imports",
      "room_to_think()",
    ];
  }

  const shared = [
    "def normalize_user(raw_input, state, cache):",
    "    parser = resolver.lookup(current_module, raw_input)",
    "    payload = maybe_decode(cache, state, fallback='legacy')",
    "    if payload is None: return try_secondary_path(raw_input)",
    "    return adapter.rebuild(parser, payload, state)",
    "    # temporary fix from 2022",
    "    # copied from webhook_router.py",
    "    # TODO: reconcile cursor patch branch",
  ];

  if (variant === "cluttered") {
    return [...shared, "    if state.flags.get('patched'): return legacy_fork()", "    return nested_callback(user, payload)"];
  }

  return shared;
};

type ContextTokenBlock = {
  left: number;
  top: number;
  width: number;
  height: number;
  tone: "danger" | "success" | "neutral";
  opacity: number;
};

const buildContextWindowTokenBlocks = (
  variant: "cluttered" | "dense"
): ContextTokenBlock[] => {
  if (variant === "cluttered") {
    return [
      { left: 4, top: 6, width: 80, height: 22, tone: "danger", opacity: 0.22 },
      { left: 8, top: 13, width: 68, height: 18, tone: "danger", opacity: 0.18 },
      { left: 18, top: 19, width: 62, height: 18, tone: "neutral", opacity: 0.12 },
      { left: 5, top: 27, width: 84, height: 20, tone: "danger", opacity: 0.2 },
      { left: 28, top: 34, width: 56, height: 17, tone: "danger", opacity: 0.2 },
      { left: 9, top: 40, width: 72, height: 16, tone: "neutral", opacity: 0.12 },
      { left: 12, top: 47, width: 76, height: 20, tone: "danger", opacity: 0.2 },
      { left: 46, top: 54, width: 34, height: 14, tone: "success", opacity: 0.22 },
      { left: 6, top: 59, width: 80, height: 16, tone: "danger", opacity: 0.18 },
      { left: 22, top: 66, width: 61, height: 18, tone: "danger", opacity: 0.2 },
      { left: 11, top: 72, width: 48, height: 13, tone: "success", opacity: 0.24 },
      { left: 42, top: 77, width: 43, height: 14, tone: "danger", opacity: 0.2 },
      { left: 6, top: 83, width: 74, height: 14, tone: "danger", opacity: 0.18 },
      { left: 58, top: 88, width: 17, height: 10, tone: "success", opacity: 0.28 },
    ];
  }

  return [
    { left: 6, top: 8, width: 82, height: 10, tone: "neutral", opacity: 0.14 },
    { left: 11, top: 16, width: 76, height: 9, tone: "neutral", opacity: 0.14 },
    { left: 15, top: 24, width: 70, height: 10, tone: "neutral", opacity: 0.12 },
    { left: 9, top: 32, width: 82, height: 9, tone: "neutral", opacity: 0.14 },
    { left: 18, top: 40, width: 62, height: 10, tone: "neutral", opacity: 0.13 },
    { left: 13, top: 48, width: 78, height: 9, tone: "neutral", opacity: 0.14 },
    { left: 21, top: 56, width: 60, height: 10, tone: "neutral", opacity: 0.12 },
    { left: 8, top: 64, width: 83, height: 9, tone: "neutral", opacity: 0.14 },
    { left: 18, top: 72, width: 68, height: 10, tone: "neutral", opacity: 0.13 },
    { left: 11, top: 80, width: 78, height: 9, tone: "neutral", opacity: 0.14 },
  ];
};

const renderInsetTokenBadge = (tokenCount: string, color: string): React.ReactNode => {
  return (
    <div
      style={{
        position: "absolute",
        top: 18,
        right: 18,
        padding: "6px 10px",
        borderRadius: 999,
        backgroundColor: "rgba(2, 6, 23, 0.86)",
        border: `1px solid ${color}33`,
        color,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 11,
        fontWeight: 700,
        letterSpacing: 0.2,
      }}
    >
      {tokenCount}
    </div>
  );
};

const splitQuoteIntoLines = (quote: string, maxLines = 3): string[] => {
  const trimmed = quote.trim();
  if (!trimmed) {
    return [];
  }

  const punctuationFirst = trimmed
    .split(/(?<=[,.;:])\s+/)
    .map((part) => part.trim())
    .filter(Boolean);

  if (punctuationFirst.length >= 2 && punctuationFirst.length <= maxLines) {
    return punctuationFirst;
  }

  const words = trimmed.split(/\s+/).filter(Boolean);
  if (words.length <= 6) {
    return [trimmed];
  }

  const chunkSize = Math.ceil(words.length / Math.min(maxLines, 3));
  const lines: string[] = [];
  for (let index = 0; index < words.length; index += chunkSize) {
    lines.push(words.slice(index, index + chunkSize).join(" "));
  }
  return lines.slice(0, maxLines);
};

const splitDramaticQuoteLines = (quote: string): string[] => {
  const baseline = splitQuoteIntoLines(quote, 3);
  const words = quote.trim().split(/\s+/).filter(Boolean);
  if (words.length < 8) {
    return baseline;
  }

  const finalWord = words[words.length - 1] ?? "";
  const normalizedFinalWord = finalWord.replace(/[^a-z]/gi, "");
  if (normalizedFinalWord.length < 10) {
    return baseline;
  }

  const leadingWords = words.slice(0, -1);
  const midpoint = Math.ceil(leadingWords.length / 2);
  return [
    leadingWords.slice(0, midpoint).join(" "),
    leadingWords.slice(midpoint).join(" "),
    finalWord,
  ].filter(Boolean);
};

const parsePercentRangeMidpoint = (value: unknown): number | null => {
  const raw = asString(value);
  if (!raw) {
    return null;
  }

  const matches = raw.match(/\d+(?:\.\d+)?/g);
  if (!matches || matches.length === 0) {
    return null;
  }

  const numbers = matches.map(Number).filter((entry) => Number.isFinite(entry));
  if (numbers.length === 0) {
    return null;
  }

  if (numbers.length === 1) {
    return numbers[0];
  }

  return (numbers[0] + numbers[1]) / 2;
};

const polarToCartesian = (
  cx: number,
  cy: number,
  radius: number,
  angleDeg: number
) => {
  const radians = ((angleDeg - 90) * Math.PI) / 180;
  return {
    x: cx + radius * Math.cos(radians),
    y: cy + radius * Math.sin(radians),
  };
};

const describePieSlicePath = (
  cx: number,
  cy: number,
  radius: number,
  startAngle: number,
  endAngle: number
) => {
  const start = polarToCartesian(cx, cy, radius, endAngle);
  const end = polarToCartesian(cx, cy, radius, startAngle);
  const largeArcFlag = endAngle - startAngle <= 180 ? 0 : 1;

  return [
    `M ${cx} ${cy}`,
    `L ${start.x} ${start.y}`,
    `A ${radius} ${radius} 0 ${largeArcFlag} 0 ${end.x} ${end.y}`,
    "Z",
  ].join(" ");
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
  const chartId = resolveContractChartId(data);
  if (chartId === "code_cost_triple_line") {
    return [
      {
        label: "Generate new",
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
        label: "Immediate patch",
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
        label: "Total cost of patching",
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
          const rawPoints = Array.isArray(record.dataPoints)
            ? record.dataPoints
            : Array.isArray(record.data)
              ? record.data
              : [];
          const points = rawPoints.length > 0
            ? rawPoints
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

const GhostElements: React.FC<{
  data: Record<string, unknown>;
  width: number;
  height: number;
}> = ({ data, width, height }) => {
  const ghosts = Array.isArray(data.ghostElements)
    ? data.ghostElements.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const ghostShapes = ghosts
    .map((ghost) => asString(ghost.shape))
    .filter((shape): shape is string => Boolean(shape));
  const hasCodebaseTree = ghostShapes.includes("codebase_tree");
  const hasMoldGhost = ghostShapes.some((shape) =>
    ["mold_shell", "mold_walls", "mold_nozzle", "mold_material"].includes(shape)
  );

  if (hasMoldGhost) {
    const shellGhost = ghosts.find((ghost) => asString(ghost.shape) === "mold_shell");
    const wallGhost = ghosts.find((ghost) => asString(ghost.shape) === "mold_walls");
    const nozzleGhost = ghosts.find((ghost) => asString(ghost.shape) === "mold_nozzle");
    const materialGhost = ghosts.find((ghost) => asString(ghost.shape) === "mold_material");

    return (
      <svg
        width={width}
        height={height}
        viewBox={`0 0 ${width} ${height}`}
        style={{ position: "absolute", inset: 0, opacity: 0.92 }}
      >
        <rect
          x={width / 2 - 250}
          y={height / 2 - 40}
          width={500}
          height={250}
          rx={16}
          fill="none"
          stroke={asString(shellGhost?.color) ?? "#4A90D9"}
          strokeWidth={2}
          opacity={0.16}
        />
        {[0, 1, 2].map((index) => (
          <line
            key={`mold-wall-${index}`}
            x1={width / 2 - 168 + index * 42}
            y1={height / 2 - 24}
            x2={width / 2 - 168 + index * 42}
            y2={height / 2 + 150}
            stroke={asString(wallGhost?.color) ?? "#D9944A"}
            strokeWidth={2}
            opacity={0.18}
          />
        ))}
        <path
          d={`M ${width / 2 - 46} ${height / 2 - 72} L ${width / 2} ${height / 2 - 8} L ${
            width / 2 + 46
          } ${height / 2 - 72} Z`}
          fill="none"
          stroke={asString(nozzleGhost?.color) ?? "#2DD4BF"}
          strokeWidth={2}
          opacity={0.18}
        />
        <path
          d={`M ${width / 2 - 76} ${height / 2 + 74}
              C ${width / 2 - 26} ${height / 2 + 4}, ${width / 2 + 46} ${height / 2 + 24}, ${
                width / 2 + 88
              } ${height / 2 + 92}
              C ${width / 2 + 54} ${height / 2 + 138}, ${width / 2 - 6} ${height / 2 + 150}, ${
                width / 2 - 82
              } ${height / 2 + 118} Z`}
          fill="none"
          stroke={asString(materialGhost?.color) ?? "#A78BFA"}
          strokeWidth={2}
          opacity={0.15}
        />
      </svg>
    );
  }

  if (ghostShapes.includes("quadratic_curve") || ghostShapes.includes("crossing_point")) {
    const descendingGhost = ghosts.find(
      (ghost) =>
        asString(ghost.shape) === "quadratic_curve" &&
        asString(ghost.component) === "descending_cost"
    );
    const ascendingGhost = ghosts.find(
      (ghost) =>
        asString(ghost.shape) === "quadratic_curve" &&
        asString(ghost.component) === "ascending_cost"
    );
    const thresholdGhost = ghosts.find(
      (ghost) => asString(ghost.shape) === "crossing_point"
    );
    const crossingX = width * 0.547;
    const crossingY = height * 0.463;

    return (
      <svg
        width={width}
        height={height}
        viewBox={`0 0 ${width} ${height}`}
        style={{ position: "absolute", inset: 0, opacity: 0.92 }}
      >
        <path
          d={`M ${width * 0.1} ${height * 0.31} Q ${width * 0.31} ${height * 0.44} ${crossingX} ${crossingY}`}
          fill="none"
          stroke={asString(descendingGhost?.color) ?? "#D9944A"}
          strokeWidth={2}
          opacity={0.18}
        />
        <path
          d={`M ${width * 0.1} ${height * 0.68} Q ${width * 0.31} ${height * 0.51} ${crossingX} ${crossingY}`}
          fill="none"
          stroke={asString(ascendingGhost?.color) ?? "#4A90D9"}
          strokeWidth={2}
          opacity={0.18}
        />
        <circle
          cx={crossingX}
          cy={crossingY}
          r={4}
          fill={asString(thresholdGhost?.color) ?? "#E2E8F0"}
          opacity={0.16}
        />
      </svg>
    );
  }

  if (hasCodebaseTree) {
    const treeGhost = ghosts.find((ghost) => asString(ghost.shape) === "codebase_tree");
    const treeColor = asString(treeGhost?.color) ?? "#334155";
    const centerX = width / 2;
    const trunkTop = height * 0.28;
    const trunkBottom = height * 0.74;
    const branchRows = [0.36, 0.44, 0.52, 0.6, 0.68];

    return (
      <svg
        width={width}
        height={height}
        viewBox={`0 0 ${width} ${height}`}
        style={{ position: "absolute", inset: 0, opacity: 0.9 }}
      >
        <line
          x1={centerX}
          y1={trunkTop}
          x2={centerX}
          y2={trunkBottom}
          stroke={treeColor}
          strokeWidth={2}
          opacity={0.18}
        />
        {branchRows.map((row, index) => {
          const y = height * row;
          const isLeft = index % 2 === 0;
          const branchLength = 110 + (index % 3) * 26;
          const branchEnd = centerX + (isLeft ? -branchLength : branchLength);
          const fileX = branchEnd + (isLeft ? -10 : 2);
          return (
            <React.Fragment key={`branch-${index}`}>
              <line
                x1={centerX}
                y1={y}
                x2={branchEnd}
                y2={y}
                stroke={treeColor}
                strokeWidth={2}
                opacity={0.14}
              />
              <rect
                x={fileX}
                y={y - 8}
                width={10}
                height={14}
                rx={2}
                fill="none"
                stroke={treeColor}
                strokeWidth={1.5}
                opacity={0.14}
              />
            </React.Fragment>
          );
        })}
      </svg>
    );
  }

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
  const sectionNumber = asNumber(data.sectionNumber);
  const titleColor = asString(data.titleColor) ?? "#E2E8F0";
  const ruleColor = "rgba(51, 65, 85, 0.4)";
  const subtitleColor = asString(data.subtitleColor) ?? "#CBD5E1";
  const hasCodeUnderlay = Boolean(data.codeUnderlay);
  const hideEyebrow =
    (sectionNumber !== null && sectionNumber <= 0) ||
    eyebrow.trim().toLowerCase() === "cold open";
  const displayedEyebrow = hideEyebrow ? "" : eyebrow;
  const prefersSingleLineTitle =
    hasCodeUnderlay &&
    !isStillnessBeat &&
    explicitTitle !== null &&
    !asString(data.titleLine1) &&
    !asString(data.titleLine2);
  const subtitleFontStyle = hasCodeUnderlay && commands.length === 0 ? "italic" : "normal";

  const resolvedTitleLines =
    isStillnessBeat && !explicitTitle
      ? []
      : prefersSingleLineTitle && explicitTitle
        ? [explicitTitle]
        : titleLines;
  const showSingleTitleRule =
    !isStillnessBeat &&
    resolvedTitleLines.length === 1 &&
    subtitleLines.length > 0;

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
      <GhostElements data={data} width={width} height={height} />
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
        {displayedEyebrow ? (
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
            {displayedEyebrow}
          </div>
        ) : null}
        {isStillnessBeat ? (
          <div
            style={{
              width: 300,
              height: 2,
              backgroundColor: ruleColor,
              borderRadius: 999,
              opacity: 1,
            }}
          />
        ) : null}
        {resolvedTitleLines.length === 2 && !isStillnessBeat ? (
          <div
            style={{
              display: "flex",
              flexDirection: "column",
              alignItems: "center",
              gap: 18,
              maxWidth: width * 0.76,
            }}
          >
            <div
              style={{
                color: titleColor,
                fontFamily: "'Inter', sans-serif",
                fontSize: width > 1400 ? 76 : 64,
                fontWeight: 700,
                lineHeight: 1.03,
                letterSpacing: 1,
                whiteSpace: "pre-wrap",
              }}
            >
              {resolvedTitleLines[0]}
            </div>
            <div
              style={{
                width: 240,
                height: 2,
                backgroundColor: ruleColor,
                borderRadius: 999,
                opacity: 0.9,
              }}
            />
            <div
              style={{
                color: titleColor,
                fontFamily: "'Inter', sans-serif",
                fontSize: width > 1400 ? 76 : 64,
                fontWeight: 700,
                lineHeight: 1.03,
                letterSpacing: 1,
                whiteSpace: "pre-wrap",
                transform: "translateX(15px)",
              }}
            >
              {resolvedTitleLines[1]}
            </div>
          </div>
        ) : resolvedTitleLines.length > 0 ? (
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
        {showSingleTitleRule ? (
          <div
            style={{
              width: 140,
              height: 2,
              backgroundColor: titleColor === "#E2E8F0" ? ruleColor : `${titleColor}44`,
              borderRadius: 999,
              opacity: 0.9,
            }}
          />
        ) : null}
        {subtitleLines.map((line, index) => (
          <div
            key={`${line}-${index}`}
            style={{
              color: index === 0 ? subtitleColor : "#94A3B8",
              fontFamily: "'Inter', sans-serif",
              fontSize: index === 0 ? 26 : 22,
              fontWeight: index === 0 ? 300 : 400,
              fontStyle: subtitleFontStyle,
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
  const quoteLine1 = asString(data.quoteLine1);
  const quoteLine2 = asString(data.quoteLine2);
  const quoteLine2Color = asString(data.quoteLine2Color) ?? accent;
  const secondaryText =
    asString(data.secondaryText) ?? asString(data.summary) ?? asString(data.subtext);
  const attribution = asString(data.attribution);
  const quote = asString(data.quote);
  const primaryLines =
    quoteLine1 || quoteLine2
      ? [quoteLine1, quoteLine2].filter((line): line is string => Boolean(line))
      : quote
        ? splitDramaticQuoteLines(quote)
        : [resolveTitle(data)];
  const usesMinimalQuoteLayout = Boolean(
    quote &&
      attribution &&
      !quoteLine1 &&
      !quoteLine2 &&
      !secondaryText
  );
  const usesMinimalCalloutLayout = Boolean(
    quoteLine1 &&
      quoteLine2 &&
      secondaryText &&
      !attribution
  );

  if (usesMinimalQuoteLayout) {
    return (
      <AbsoluteFill
        style={{
          padding: "120px 140px 120px 180px",
          justifyContent: "center",
        }}
      >
        <div
          style={{
            position: "absolute",
            left: 400,
            top: "50%",
            width: 2,
            height: 120,
            transform: "translateY(-20%)",
            backgroundColor: `${accent}66`,
            borderRadius: 999,
          }}
        />
        <div
          style={{
            position: "absolute",
            left: 840,
            top: 310,
            color: `${accent}33`,
            fontFamily: "'Georgia', serif",
            fontSize: 132,
            lineHeight: 1,
          }}
        >
          "
        </div>
        <div
          style={{
            maxWidth: 960,
            margin: "0 auto",
            display: "flex",
            flexDirection: "column",
            gap: 12,
            alignItems: "center",
            textAlign: "center",
          }}
        >
          {primaryLines.map((line, index) => (
            <div
              key={`${line}-${index}`}
              style={{
                color: "#E2E8F0",
                fontFamily: "'Inter', sans-serif",
                fontSize: 32,
                fontWeight: index === primaryLines.length - 1 ? 700 : 400,
                lineHeight: 1.28,
                maxWidth: 900,
              }}
            >
              {line}
            </div>
          ))}
          <div
            style={{
              color: "rgba(148, 163, 184, 0.78)",
              fontFamily: "'Inter', sans-serif",
              fontSize: 16,
              marginTop: 32,
            }}
          >
            {`— ${attribution}`}
          </div>
        </div>
      </AbsoluteFill>
    );
  }

  if (usesMinimalCalloutLayout) {
    return (
      <AbsoluteFill
        style={{
          padding: "120px 120px 110px",
          justifyContent: "center",
          alignItems: "center",
          textAlign: "center",
        }}
      >
        <div
          style={{
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            gap: 18,
            maxWidth: 1080,
          }}
        >
          <div
            style={{
              color: "#E2E8F0",
              fontFamily: "'Inter', sans-serif",
              fontSize: 44,
              fontWeight: 700,
              lineHeight: 1.15,
            }}
          >
            {quoteLine1}
          </div>
          <div
            style={{
              color: quoteLine2Color,
              fontFamily: "'Inter', sans-serif",
              fontSize: 44,
              fontWeight: 700,
              lineHeight: 1.15,
            }}
          >
            {quoteLine2}
          </div>
          <div
            style={{
              width: 160,
              height: 1.5,
              borderRadius: 999,
              backgroundColor: "rgba(51, 65, 85, 0.4)",
              marginTop: 8,
            }}
          />
          <div
            style={{
              color: "rgba(148, 163, 184, 0.78)",
              fontFamily: "'Inter', sans-serif",
              fontSize: 20,
              fontWeight: 400,
              lineHeight: 1.35,
            }}
          >
            {secondaryText}
          </div>
        </div>
      </AbsoluteFill>
    );
  }

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
            {attribution ? "Quote" : "Key idea"}
          </div>
        <div style={{ display: "flex", flexDirection: "column", gap: 8 }}>
          {primaryLines.map((line, index) => (
            <div
              key={`${line}-${index}`}
              style={{
                color:
                  index === 1 && quoteLine2
                    ? quoteLine2Color
                    : "#F8FAFC",
                fontFamily: "'Inter', sans-serif",
                fontSize: primaryLines.length > 1 ? 60 : 56,
                fontWeight: 700,
                lineHeight: 1.1,
                letterSpacing: -0.4,
              }}
            >
              {quoteLine1 || quoteLine2 ? line : `“${line}”`}
            </div>
          ))}
        </div>
        {secondaryText ? (
          <div
            style={{
              width: 220,
              height: 2,
              borderRadius: 999,
              backgroundColor: "rgba(148, 163, 184, 0.34)",
              marginTop: 4,
              marginBottom: 2,
            }}
          />
        ) : null}
        {secondaryText ? (
          <div
            style={{
              color: "#CBD5E1",
              fontFamily: "'Inter', sans-serif",
              fontSize: 28,
              lineHeight: 1.35,
              maxWidth: 980,
            }}
          >
            {secondaryText}
          </div>
        ) : null}
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
  const frame = useCurrentFrame();
  const accent = resolveAccentColor(data);
  const echoes = Array.isArray(data.echoes)
    ? data.echoes.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const fade = interpolate(frame, [0, 45, 90], [0.22, 0.12, 0.02], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

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
            opacity: (Number(echo.opacity ?? 0.08) + index * 0.04) * (1 - fade * 0.8),
            transform: `translateY(${index * 28}px) scale(${1 - index * 0.06})`,
          }}
        />
      ))}
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
  const durationInFrames = useVisualDurationInFrames();
  const chartId = resolveContractChartId(data);
  const event = asString(data.event);
  const callouts = Array.isArray(data.callouts)
    ? data.callouts
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const stats = Array.isArray(data.stats)
    ? data.stats
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
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
  const annotationRecord = asRecord(data.annotations);
  const annotations = Array.isArray(data.annotations)
    ? data.annotations
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const trapArrow = asRecord(data.trapArrow);
  const isCodeCostCallback =
    chartId === "code_cost_triple_line" &&
    (data.type === "chart_callback" || event === "crossing_reprise");
  const resolvedThreshold =
    threshold ??
    (isCodeCostCallback
      ? {
          label: "We are here.",
        }
      : null);
  const resolvedCrossings =
    crossings.length > 0
      ? crossings
      : isCodeCostCallback
        ? [
            asRecord(data.crossingPoint) ?? {
              radius: 12,
              glowRadius: 24,
            },
          ]
        : [];
  const eventLabel = asString(data.label) ?? asString(asRecord(data.takeaway)?.line1);
  const eventSubLabel =
    debtResetNote ??
    asString(data.reframeText) ??
    asString(data.newAnnotation) ??
    (isCodeCostCallback ? "When economics change, rational behavior changes." : null) ??
    asString(asRecord(data.takeaway)?.line2);
  const showInsetCallout = data.type === "inset_chart" && causalChain.length > 0;
  const chartWidth = width * 0.72;
  const chartHeight = height * 0.5;
  const seriesBounds = computeSeriesBounds(series);
  const reveal = interpolate(frame, [0, 24], [0.25, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  if (chartId === "mold_production_counter") {
    const counter = asRecord(data.counter);
    const moldCycle = asRecord(data.moldCycle);
    const startValue = Math.max(1, asNumber(counter?.start) ?? 1);
    const endValue = Math.max(startValue + 1, asNumber(counter?.end) ?? 10000);
    const milestoneValues = (Array.isArray(counter?.milestones) ? counter?.milestones : [])
      .map((entry) => asNumber(entry))
      .filter((entry): entry is number => entry !== null);
    const holdStart = Math.max(1, Math.floor(durationInFrames * 0.78));
    const productionProgress = interpolate(frame, [0, holdStart], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
    const easedProgress = Math.pow(productionProgress, 0.42);
    const currentValue =
      productionProgress >= 0.96
        ? endValue
        : Math.max(startValue, startValue * Math.pow(endValue / startValue, easedProgress));
    const finalDisplayValue =
      endValue >= 10000 ? "10,000+" : `${Math.round(endValue).toLocaleString()}+`;
    const displayValue =
      productionProgress >= 0.8
        ? finalDisplayValue
        : Math.round(currentValue).toLocaleString();
    const cycleDots = Math.max(4, Math.min(10, Math.round(interpolate(
      frame,
      [0, durationInFrames],
      [asNumber(moldCycle?.startFramesPerCycle) ?? 60, asNumber(moldCycle?.endFramesPerCycle) ?? 6],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) / 8)));

    return (
      <AbsoluteFill style={{ padding: "88px 92px 78px" }}>
        <div
          style={{
            position: "relative",
            flex: 1,
            borderRadius: 32,
            background:
              "radial-gradient(circle at 68% 18%, rgba(96, 165, 250, 0.12), transparent 28%), radial-gradient(circle at 18% 82%, rgba(217, 148, 74, 0.12), transparent 34%), rgba(10, 15, 26, 0.96)",
            border: subtleBorder,
            overflow: "hidden",
          }}
        >
          <div
            style={{
              position: "absolute",
              left: 76,
              top: 54,
              display: "flex",
              gap: 10,
            }}
          >
            {Array.from({ length: cycleDots }).map((_, index) => (
              <div
                key={`cycle-dot-${index}`}
                style={{
                  width: 12,
                  height: 12,
                  borderRadius: 999,
                  backgroundColor: index < Math.round(productionProgress * cycleDots) ? "#F59E0B" : "rgba(148, 163, 184, 0.22)",
                  boxShadow: index < Math.round(productionProgress * cycleDots) ? "0 0 14px rgba(245, 158, 11, 0.35)" : undefined,
                }}
              />
            ))}
          </div>
          <div
            style={{
              position: "absolute",
              left: 120,
              top: 112,
              width: 780,
              height: 468,
              borderRadius: 36,
              backgroundColor: "rgba(15, 23, 42, 0.72)",
              border: "1px solid rgba(148, 163, 184, 0.22)",
              overflow: "hidden",
            }}
          >
            <svg width="100%" height="100%" viewBox="0 0 780 468">
              <rect x={164} y={112} width={452} height={214} rx={44} fill="none" stroke="rgba(148, 163, 184, 0.78)" strokeWidth={14} />
              <rect x={198} y={142} width={384} height={160} rx={26} fill="rgba(2, 6, 23, 0.36)" stroke="rgba(217, 148, 74, 0.72)" strokeWidth={6} />
              <rect x={316} y={84} width={148} height={46} rx={22} fill="rgba(226, 232, 240, 0.16)" />
              <path d="M 390 148 C 350 208, 330 236, 328 270 C 326 308, 358 336, 394 336 C 430 336, 460 306, 458 270 C 456 236, 434 208, 414 172 Z" fill="rgba(217, 148, 74, 0.28)" />
              <path d="M 390 138 L 390 54" stroke="rgba(217, 148, 74, 0.72)" strokeWidth={8} strokeLinecap="round" />
              {Array.from({ length: 12 }).map((_, index) => (
                <rect
                  key={`part-${index}`}
                  x={170 + (index % 4) * 112}
                  y={372 + Math.floor(index / 4) * 38}
                  width={52}
                  height={28}
                  rx={10}
                  fill={index < Math.round(productionProgress * 12) ? "#D9944A" : "rgba(71, 85, 105, 0.55)"}
                />
              ))}
            </svg>
          </div>
          <div
            style={{
              position: "absolute",
              right: 120,
              bottom: 118,
              width: 360,
              display: "flex",
              flexDirection: "column",
              alignItems: "center",
            }}
          >
            <div
              style={{
                color: "#E2E8F0",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 96,
                fontWeight: 700,
                lineHeight: 1,
              }}
            >
              {displayValue}
            </div>
            <div
              style={{
                marginTop: 10,
                color: "rgba(148, 163, 184, 0.6)",
                fontFamily: "'Inter', sans-serif",
                fontSize: 16,
                fontWeight: 400,
              }}
            >
              parts produced
            </div>
            <div
              style={{
                marginTop: 22,
                width: 300,
                height: 4,
                borderRadius: 999,
                backgroundColor: "#1E293B",
                overflow: "hidden",
              }}
            >
              <div
                style={{
                  width: `${Math.max(6, productionProgress * 100)}%`,
                  height: "100%",
                  borderRadius: 999,
                  background: "linear-gradient(90deg, #4A90D9 0%, #5AAA6E 100%)",
                }}
              />
            </div>
            <div
              style={{
                marginTop: 18,
                display: "flex",
                flexWrap: "wrap",
                justifyContent: "center",
                gap: 8,
              }}
            >
              {(milestoneValues.length > 0 ? milestoneValues : [1, 10, 100, 1000, 10000]).map((value) => (
                <div
                  key={`milestone-${value}`}
                  style={{
                    padding: "8px 12px",
                    borderRadius: 999,
                    backgroundColor: "rgba(15, 23, 42, 0.84)",
                    border: `1px solid ${currentValue >= value ? "rgba(74, 222, 128, 0.42)" : "rgba(71, 85, 105, 0.42)"}`,
                    color: currentValue >= value ? "#86EFAC" : "#94A3B8",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 14,
                    fontWeight: 700,
                  }}
                >
                  {value >= endValue ? finalDisplayValue : value.toLocaleString()}
                </div>
              ))}
            </div>
          </div>
        </div>
      </AbsoluteFill>
    );
  }

  if (chartId === "schematic_density_zoom") {
    const counter = asRecord(data.counter);
    const zoom = asRecord(data.zoom);
    const startValue = Math.max(1, asNumber(counter?.start) ?? 20);
    const endValue = Math.max(startValue + 1, asNumber(counter?.end) ?? 50000);
    const zoomProgress = interpolate(frame, [0, Math.max(1, durationInFrames - 60)], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
    const currentValue =
      zoomProgress >= 0.82
        ? endValue
        : Math.max(startValue, startValue * Math.pow(endValue / startValue, Math.pow(zoomProgress, 0.58)));
    const displayValue = zoomProgress >= 0.78 ? `${formatCompactMetric(endValue)}` : `${formatCompactMetric(currentValue)}`;
    const finalScale = asNumber(zoom?.endScale) ?? 0.1;

    return (
      <AbsoluteFill style={{ padding: "82px 88px 78px" }}>
        <div
          style={{
            position: "relative",
            flex: 1,
            borderRadius: 30,
            backgroundColor: "#F5F0E8",
            overflow: "hidden",
            border: "1px solid rgba(148, 163, 184, 0.24)",
          }}
        >
          <div
            style={{
              position: "absolute",
              inset: 0,
              backgroundImage:
                "linear-gradient(rgba(148, 163, 184, 0.08) 1px, transparent 1px), linear-gradient(90deg, rgba(148, 163, 184, 0.08) 1px, transparent 1px)",
              backgroundSize: "38px 38px",
            }}
          />
          <div
            style={{
              position: "absolute",
              inset: "72px 110px 92px 72px",
              display: "grid",
              gridTemplateColumns: "repeat(10, minmax(0, 1fr))",
              gap: 8,
              transform: `scale(${interpolate(zoomProgress, [0, 1], [1.7, Math.max(1, 1 / finalScale) * 0.12], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              })})`,
              transformOrigin: "center center",
            }}
          >
            {Array.from({ length: 120 }).map((_, index) => {
              const wobble = ((index % 5) - 2) * 1.6;
              return (
                <svg
                  key={`schematic-cell-${index}`}
                  viewBox="0 0 82 56"
                  style={{
                    width: "100%",
                    minHeight: 28,
                    overflow: "visible",
                    opacity: 0.18 + (index % 7) * 0.08,
                  }}
                >
                  <line x1="8" y1="28" x2="28" y2="28" stroke="#4A5568" strokeWidth="1" />
                  <line x1="54" y1="28" x2="74" y2="28" stroke="#4A5568" strokeWidth="1" />
                  <line x1="41" y1="12" x2="41" y2="44" stroke="#4A5568" strokeWidth="1" />
                  <path
                    d={`M 28 12 L 54 28 L 28 44`}
                    fill="none"
                    stroke="#2D3748"
                    strokeWidth="1.5"
                    strokeLinecap="round"
                    strokeLinejoin="round"
                  />
                  <path
                    d={`M 16 ${16 + wobble} C 26 ${20 + wobble}, 36 ${18 + wobble}, 44 ${24 + wobble}`}
                    fill="none"
                    stroke="#4A5568"
                    strokeWidth="1"
                    strokeLinecap="round"
                  />
                </svg>
              );
            })}
          </div>
          <div
            style={{
              position: "absolute",
              right: 86,
              bottom: 72,
              display: "flex",
              flexDirection: "column",
              alignItems: "flex-end",
              gap: 6,
            }}
          >
            <div
              style={{
                color: "#4A5568",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 36,
                fontWeight: 400,
                lineHeight: 1,
              }}
            >
              {displayValue}
            </div>
            <div
              style={{
                color: "#94A3B8",
                fontFamily: "'Inter', sans-serif",
                fontSize: 14,
                fontWeight: 400,
              }}
            >
              transistors
            </div>
          </div>
        </div>
      </AbsoluteFill>
    );
  }

  if (chartId === "precision_tradeoff_curve") {
    const axes = asRecord(data.axes);
    const xAxis = asRecord(data.xAxis) ?? asRecord(axes?.x);
    const yAxis = asRecord(data.yAxis) ?? asRecord(axes?.y);
    const calloutAnnotations =
      annotations.length > 0
        ? annotations
        : [asRecord(annotationRecord?.left), asRecord(annotationRecord?.right)].filter(
            (entry): entry is Record<string, unknown> => Boolean(entry)
          );
    const leftAnnotation = calloutAnnotations[0] ?? asRecord(annotationRecord?.left);
    const rightAnnotation = calloutAnnotations[1] ?? asRecord(annotationRecord?.right);
    const chartLeft = width * 0.14;
    const chartTop = height * 0.22;
    const curveWidth = width * 0.66;
    const curveHeight = height * 0.52;
    const chartBottom = chartTop + curveHeight;
    const xTicks = asStringArray(xAxis?.ticks);
    const yTicks = asStringArray(yAxis?.ticks);
    const resolvedXTicks = xTicks.length > 0 ? xTicks : ["0", "10", "20", "30", "40", "50+"];
    const resolvedYTicks = yTicks.length > 0 ? yTicks : ["Low", "Medium", "High"];
    const introText = asString(data.introText) ?? "This maps directly to PDD.";
    const rightTestCount = asNumber(rightAnnotation?.testCount) ?? 50;
    const resolveCalloutCopy = (
      annotation: Record<string, unknown> | null,
      fallbackLabel: string,
      fallbackDescription: string
    ) => {
      const rawText = asString(annotation?.text);
      if (rawText) {
        const [labelLine, ...detailLines] = rawText
          .split(/\n+/)
          .map((line) => line.trim())
          .filter(Boolean);
        return {
          label: labelLine ?? fallbackLabel,
          description: detailLines.join(" ") || fallbackDescription,
        };
      }

      return {
        label: asString(annotation?.label) ?? fallbackLabel,
        description: asString(annotation?.description) ?? fallbackDescription,
      };
    };
    const leftCallout = resolveCalloutCopy(
      leftAnnotation,
      "50-line prompt",
      "Every edge case specified"
    );
    const rightCallout = resolveCalloutCopy(
      rightAnnotation,
      "10-line prompt",
      "Tests handle constraints"
    );
    const leftCalloutColor = asString(leftAnnotation?.color) ?? "#D9944A";
    const rightCalloutColor = asString(rightAnnotation?.color) ?? "#4A90D9";
    const pointForTestCount = (testCount: number) => {
      const clamped = Math.max(0, Math.min(50, testCount));
      const x = chartLeft + (clamped / 50) * curveWidth;
      const normalizedPrecision = 1 / (1 + 0.08 * clamped);
      const y = chartBottom - curveHeight * normalizedPrecision;
      return { x, y };
    };
    const curvePoints = Array.from({ length: 41 }, (_, index) =>
      pointForTestCount((index / 40) * 50)
    );
    const curvePath = curvePoints
      .map((point, index) => `${index === 0 ? "M" : "L"} ${point.x} ${point.y}`)
      .join(" ");
    const areaPath = `${curvePath} L ${chartLeft + curveWidth} ${chartBottom} L ${chartLeft} ${chartBottom} Z`;
    const curveStrokeColor =
      asString(asRecord(series[0])?.color) ?? "#E2E8F0";
    const leftZoneColor =
      asString(
        Array.isArray(data.zones) ? asRecord(data.zones[0])?.color : null
      ) ?? "#D9944A";
    const rightZoneColor =
      asString(
        Array.isArray(data.zones) ? asRecord(data.zones[1])?.color : null
      ) ?? "#4A90D9";
    const dotProgress = interpolate(frame, [300, 450], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
    const dotPoint = pointForTestCount(dotProgress * 50);
    const leftPoint = pointForTestCount(3.5);
    const rightPoint = pointForTestCount(45);
    const leftOpacity = interpolate(frame, [180, 220, 320, 450], [0, 1, 1, 0.42], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
    const rightOpacity = interpolate(frame, [300, 340, 450], [0, 1, 0.64], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });
    const introOpacity =
      frame <= 45
        ? interpolate(frame, [0, 15, 30, 45], [0, 0.85, 0.85, 0], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })
        : 0;
    const leftCalloutX = chartLeft + curveWidth * 0.12;
    const leftCalloutY = chartTop + curveHeight * 0.1;
    const rightCalloutX = chartLeft + curveWidth * 0.72;
    const rightCalloutY = chartTop + curveHeight * 0.54;

    return (
      <AbsoluteFill>
        <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}>
          <defs>
            <linearGradient id="precisionTradeoffFill" x1="0" y1="0" x2="1" y2="0">
              <stop offset="0%" stopColor={leftZoneColor} stopOpacity="0.08" />
              <stop offset="42%" stopColor={leftZoneColor} stopOpacity="0.05" />
              <stop offset="58%" stopColor={rightZoneColor} stopOpacity="0.05" />
              <stop offset="100%" stopColor={rightZoneColor} stopOpacity="0.08" />
            </linearGradient>
          </defs>
          {Array.from({ length: 8 }).map((_, index) => {
            const x = chartLeft + index * (curveWidth / 7);
            return (
              <line
                key={`precision-v-${index}`}
                x1={x}
                y1={chartTop}
                x2={x}
                y2={chartBottom}
                stroke="rgba(30, 41, 59, 0.35)"
                strokeWidth={1}
              />
            );
          })}
          {Array.from({ length: 6 }).map((_, index) => {
            const y = chartTop + index * (curveHeight / 5);
            return (
              <line
                key={`precision-h-${index}`}
                x1={chartLeft}
                y1={y}
                x2={chartLeft + curveWidth}
                y2={y}
                stroke="rgba(30, 41, 59, 0.32)"
                strokeWidth={1}
              />
            );
          })}
          <line
            x1={chartLeft}
            y1={chartBottom}
            x2={chartLeft + curveWidth}
            y2={chartBottom}
            stroke="#334155"
            strokeWidth={2}
          />
          <line
            x1={chartLeft}
            y1={chartTop}
            x2={chartLeft}
            y2={chartBottom}
            stroke="#334155"
            strokeWidth={2}
          />
          <path d={areaPath} fill="url(#precisionTradeoffFill)" opacity={0.9} />
          <path d={curvePath} fill="none" stroke={curveStrokeColor} strokeWidth={4} opacity={0.96} />
          <circle cx={dotPoint.x} cy={dotPoint.y} r={10} fill="#FFFFFF" opacity={0.96} />
          <circle cx={dotPoint.x} cy={dotPoint.y} r={18} fill="rgba(255, 255, 255, 0.18)" />
          <line
            x1={leftPoint.x}
            y1={leftPoint.y}
            x2={leftCalloutX + 12}
            y2={leftCalloutY + 36}
            stroke={leftCalloutColor}
            strokeWidth={1.5}
            opacity={leftOpacity}
          />
          <line
            x1={rightPoint.x}
            y1={rightPoint.y}
            x2={rightCalloutX + 12}
            y2={rightCalloutY + 28}
            stroke={rightCalloutColor}
            strokeWidth={1.5}
            opacity={rightOpacity}
          />
          {resolvedXTicks.map((tick, index) => {
            const x =
              chartLeft +
              (index / Math.max(1, resolvedXTicks.length - 1)) * curveWidth;
            return (
              <g key={`precision-x-tick-${tick}`}>
                <line
                  x1={x}
                  y1={chartBottom}
                  x2={x}
                  y2={chartBottom + 10}
                  stroke="#64748B"
                  strokeWidth={1.5}
                />
                <text
                  x={x}
                  y={chartBottom + 34}
                  fill="#64748B"
                  fontSize={14}
                  textAnchor="middle"
                  fontFamily="'Inter', sans-serif"
                >
                  {tick}
                </text>
              </g>
            );
          })}
          {resolvedYTicks.map((tick, index) => {
            const y =
              chartBottom -
              (index / Math.max(1, resolvedYTicks.length - 1)) * curveHeight;
            return (
              <text
                key={`precision-y-tick-${tick}`}
                x={chartLeft - 18}
                y={y + 5}
                fill="#64748B"
                fontSize={14}
                textAnchor="end"
                fontFamily="'Inter', sans-serif"
              >
                {tick}
              </text>
            );
          })}
          <text
            x={chartLeft + curveWidth / 2}
            y={chartBottom + 72}
            fill="#94A3B8"
            fontSize={18}
            fontWeight={600}
            textAnchor="middle"
            fontFamily="'Inter', sans-serif"
          >
            {`${asString(xAxis?.label) ?? "Number of Tests"} →`}
          </text>
          <text
            x={chartLeft - 92}
            y={chartTop + curveHeight / 2}
            fill="#94A3B8"
            fontSize={18}
            fontWeight={600}
            textAnchor="middle"
            fontFamily="'Inter', sans-serif"
            transform={`rotate(-90 ${chartLeft - 92} ${chartTop + curveHeight / 2})`}
          >
            {`${asString(yAxis?.label) ?? "Required Prompt Precision"} →`}
          </text>
          <text
            x={width / 2}
            y={height * 0.17}
            fill="#E2E8F0"
            fontSize={32}
            fontWeight={700}
            textAnchor="middle"
            fontFamily="'Inter', sans-serif"
            opacity={introOpacity}
          >
            {introText}
          </text>
        </svg>
        <div
          style={{
            position: "absolute",
            left: leftCalloutX,
            top: leftCalloutY,
            width: 260,
            opacity: leftOpacity,
          }}
        >
          <div
            style={{
              color: leftCalloutColor,
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 12,
              fontWeight: 700,
              letterSpacing: 0.18,
            }}
          >
            parser_v1.prompt
          </div>
          <div
            style={{
              color: leftCalloutColor,
              fontFamily: "'Inter', sans-serif",
              fontSize: 14,
              fontWeight: 400,
              lineHeight: 1.35,
              marginTop: 8,
            }}
          >
            {leftCallout.label}
          </div>
          <div
            style={{
              color: leftCalloutColor,
              opacity: 0.92,
              fontSize: 14,
              marginTop: 8,
              lineHeight: 1.35,
            }}
          >
            {leftCallout.description}
          </div>
        </div>
        <div
          style={{
            position: "absolute",
            left: rightCalloutX,
            top: rightCalloutY,
            width: 292,
            opacity: rightOpacity,
          }}
        >
          <div
            style={{
              color: rightCalloutColor,
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 12,
              fontWeight: 700,
              letterSpacing: 0.18,
            }}
          >
            parser_v2.prompt
          </div>
          <div
            style={{
              color: rightCalloutColor,
              fontSize: 14,
              marginTop: 8,
              lineHeight: 1.35,
            }}
          >
            {rightCallout.label}
          </div>
          <div
            style={{
              color: rightCalloutColor,
              opacity: 0.92,
              fontSize: 14,
              marginTop: 8,
              lineHeight: 1.35,
            }}
          >
            {rightCallout.description}
          </div>
          <div
            style={{
              marginTop: 14,
              color: "#86EFAC",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 12,
              lineHeight: 1.4,
            }}
          >
            <div>$ pdd test parser</div>
            <div>{`${rightTestCount} tests passing ✓`}</div>
          </div>
        </div>
      </AbsoluteFill>
    );
  }

  if (chartId === "maintenance_cost_pie") {
    const slices = Array.isArray(data.slices)
      ? data.slices
          .map((entry) => asRecord(entry))
          .filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : Array.isArray(data.segments)
        ? data.segments
          .map((entry) => asRecord(entry))
          .filter((entry): entry is Record<string, unknown> => Boolean(entry))
        : [];
    const statisticEntries = Array.isArray(data.statistics)
      ? data.statistics
          .map((entry) => asRecord(entry))
          .filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];
    const centerX = width * 0.44;
    const centerY = height * 0.5;
    const baseRadius = 220;
    let startAngle = -90;
    const resolvedSlices = slices.map((slice, index) => {
      const percentageRange = asString(slice.range) ?? asString(slice.percentage);
      const degrees = asNumber(slice.degrees);
      const value =
        parsePercentRangeMidpoint(percentageRange) ??
        (degrees !== null ? (degrees / 360) * 100 : null) ??
        (index === 0 ? 85 : 15);
      const sweep = degrees ?? (value / 100) * 360;
      const pullOut = asNumber(slice.pullOut) ?? 0;
      const midAngle = startAngle + sweep / 2;
      const offset = polarToCartesian(0, 0, pullOut, midAngle);
      const segment = {
        path: describePieSlicePath(
          centerX + offset.x,
          centerY + offset.y,
          baseRadius,
          startAngle,
          startAngle + sweep
        ),
        label: asString(slice.label) ?? `Slice ${index + 1}`,
        valueText: percentageRange ?? `${Math.round(value)}%`,
        color: asString(slice.color) ?? (index === 0 ? "#D9944A" : "#4A90D9"),
        midAngle,
        cx: centerX + offset.x,
        cy: centerY + offset.y,
      };
      startAngle += sweep;
      return segment;
    });

    return (
      <AbsoluteFill>
        <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}>
          {resolvedSlices.map((slice) => (
            <path
              key={slice.label}
              d={slice.path}
              fill={slice.color}
              opacity={0.96}
              filter="drop-shadow(0 4px 20px rgba(0,0,0,0.3))"
            />
          ))}
          {resolvedSlices.map((slice, index) => {
            const labelAnchor = polarToCartesian(
              slice.cx,
              slice.cy,
              baseRadius + 72,
              slice.midAngle
            );
            const edgeAnchor = polarToCartesian(
              slice.cx,
              slice.cy,
              baseRadius + 8,
              slice.midAngle
            );
            return (
              <g key={`${slice.label}-label`}>
                <line
                  x1={edgeAnchor.x}
                  y1={edgeAnchor.y}
                  x2={labelAnchor.x}
                  y2={labelAnchor.y}
                  stroke={slice.color}
                  strokeWidth={2}
                  opacity={0.55}
                />
                <text
                  x={labelAnchor.x}
                  y={labelAnchor.y - 10}
                  fill={slice.color}
                  fontSize={14}
                  fontWeight={600}
                  textAnchor={labelAnchor.x > slice.cx ? "start" : "end"}
                >
                  {slice.label}
                </text>
                <text
                  x={labelAnchor.x}
                  y={labelAnchor.y + 18}
                  fill={slice.color}
                  fontSize={index === 0 ? 28 : 20}
                  fontWeight={700}
                  textAnchor={labelAnchor.x > slice.cx ? "start" : "end"}
                >
                  {slice.valueText}
                </text>
              </g>
            );
          })}
        </svg>
        <div
          style={{
            position: "absolute",
            left: width * 0.66,
            top: height * 0.32,
            display: "flex",
            flexDirection: "column",
            gap: 22,
            width: 360,
          }}
        >
          {(callouts.length > 0 ? callouts : statisticEntries).slice(0, 3).map((callout, index) => (
            <div
              key={`callout-${index}`}
              style={{
                display: "flex",
                gap: 14,
                alignItems: "stretch",
              }}
            >
              <div
                style={{
                  width: 3,
                  borderRadius: 999,
                  backgroundColor: `${asString(callout.color) ?? "#F59E0B"}99`,
                }}
              />
              <div style={{ display: "flex", flexDirection: "column", gap: 6 }}>
                <div
                  style={{
                    color: "#E2E8F0",
                    fontFamily: "'Inter', sans-serif",
                    fontSize: 16,
                    fontWeight: 400,
                    lineHeight: 1.35,
                  }}
                >
                  {asString(callout.text) ?? asString(callout.finding) ?? ""}
                </div>
                <div
                  style={{
                    color: "rgba(148, 163, 184, 0.72)",
                    fontFamily: "'Inter', sans-serif",
                    fontSize: 12,
                    fontWeight: 400,
                  }}
                >
                  {`—${asString(callout.source) ?? ""}`}
                </div>
              </div>
            </div>
          ))}
        </div>
      </AbsoluteFill>
    );
  }

  if (
    chartId === "compound_debt_curve" ||
    chartId === "compound_debt_vs_regeneration"
  ) {
    const curveEntries = Array.isArray(data.series)
      ? data.series
      : Array.isArray(data.curves)
        ? data.curves
        : [];
    const resolvedCurves = curveEntries
      .map((entry) => asRecord(entry))
      .filter((entry): entry is Record<string, unknown> => Boolean(entry));
    const debtCurve = resolvedCurves.find(
      (entry) => asString(entry?.id) === "debt_exponential"
    );
    const regenerationCurve = resolvedCurves.find(
      (entry) => asString(entry?.id) === "regeneration_flat"
    );
    const chartLeft = width * 0.14;
    const chartTop = height * 0.24;
    const curveWidth = width * 0.66;
    const curveHeight = height * 0.5;
    const debtColor = asString(debtCurve?.color) ?? "#D9944A";
    const flatColor = asString(regenerationCurve?.color) ?? "#5AAA6E";
    const debtSeries = Array.isArray(debtCurve?.data)
      ? debtCurve.data.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];
    const regenerationSeries = Array.isArray(regenerationCurve?.data)
      ? regenerationCurve.data.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];
    const debtPoints = (debtSeries.length > 0 ? debtSeries : Array.from({ length: 11 }, (_, pointIndex) => {
      const x = pointIndex / 10;
      return {
        x: x * 20,
        y: 0.05 + Math.pow(x, 2.1) * 0.9,
      };
    }))
      .map((point) => {
        const x = asNumber(point.x) ?? 0;
        const y = asNumber(point.y) ?? 0.05;
        return {
          x,
          y,
          px: chartLeft + curveWidth * (x / 20),
          py: chartTop + curveHeight * (1 - y),
        };
      });
    const debtPath = debtPoints
      .map((point, index) => `${index === 0 ? "M" : "L"} ${point.px} ${point.py}`)
      .join(" ");
    const debtAreaPath = `${debtPath} L ${chartLeft + curveWidth} ${chartTop + curveHeight} L ${chartLeft} ${chartTop + curveHeight} Z`;
    const flatYValue = asNumber(regenerationSeries[0]?.y) ?? 0.08;
    const flatY = chartTop + curveHeight * (1 - flatYValue);
    const stat = stats[0] ?? asRecord(annotations[0]);

    return (
      <AbsoluteFill>
        <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}>
          <defs>
            <linearGradient id="compoundDebtFill" x1="0" y1="1" x2="0" y2="0">
              <stop offset="0%" stopColor="#D9944A" stopOpacity="0.16" />
              <stop offset="100%" stopColor="#D9944A" stopOpacity="0.04" />
            </linearGradient>
          </defs>
          {Array.from({ length: 4 }).map((_, index) => {
            const y = chartTop + ((index + 1) / 5) * curveHeight;
            return (
              <line
                key={`grid-${index}`}
                x1={chartLeft}
                y1={y}
                x2={chartLeft + curveWidth}
                y2={y}
                stroke="rgba(26, 37, 64, 0.5)"
                strokeWidth={1}
              />
            );
          })}
          <line
            x1={chartLeft}
            y1={chartTop}
            x2={chartLeft}
            y2={chartTop + curveHeight}
            stroke="#334155"
            strokeWidth={1.5}
          />
          <line
            x1={chartLeft}
            y1={chartTop + curveHeight}
            x2={chartLeft + curveWidth}
            y2={chartTop + curveHeight}
            stroke="#334155"
            strokeWidth={1.5}
          />
          <path d={debtAreaPath} fill="url(#compoundDebtFill)" />
          <path
            d={debtPath}
            fill="none"
            stroke={debtColor}
            strokeWidth={3}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
          <line
            x1={chartLeft}
            y1={flatY}
            x2={chartLeft + curveWidth}
            y2={flatY}
            stroke={flatColor}
            strokeWidth={3}
          />
          {Array.from({ length: 6 }).map((_, index) => {
            const x = chartLeft + (index / 5) * curveWidth;
            return (
              <g key={`reset-arrow-${index}`}>
                <line
                  x1={x}
                  y1={flatY - 4}
                  x2={x}
                  y2={flatY + 18}
                  stroke={flatColor}
                  strokeWidth={1.5}
                  strokeDasharray="3 5"
                  opacity={0.5}
                />
                <path
                  d={`M ${x - 7} ${flatY + 10} L ${x} ${flatY + 18} L ${x + 7} ${flatY + 10}`}
                  fill="none"
                  stroke={flatColor}
                  strokeWidth={1.8}
                  strokeLinecap="round"
                  strokeLinejoin="round"
                  opacity={0.7}
                />
              </g>
            );
          })}
          {Array.from({ length: 5 }).map((_, index) => {
            const x = chartLeft + (index / 4) * curveWidth;
            const tickValue = index * 5;
            return (
              <g key={`compound-x-tick-${tickValue}`}>
                <line
                  x1={x}
                  y1={chartTop + curveHeight}
                  x2={x}
                  y2={chartTop + curveHeight + 10}
                  stroke="#64748B"
                  strokeWidth={1.5}
                />
                <text
                  x={x}
                  y={chartTop + curveHeight + 34}
                  fill="#94A3B8"
                  fontSize={14}
                  textAnchor="middle"
                  fontFamily="'Inter', sans-serif"
                >
                  {tickValue}
                </text>
              </g>
            );
          })}
          <text
            x={chartLeft + curveWidth / 2}
            y={chartTop + curveHeight + 70}
            fill="#94A3B8"
            fontSize={14}
            textAnchor="middle"
            fontFamily="'Inter', sans-serif"
          >
            {asString(asRecord(data.xAxis)?.label) ?? "Time (maintenance cycles)"}
          </text>
          <text
            x={chartLeft - 86}
            y={chartTop + curveHeight / 2}
            fill="#94A3B8"
            fontSize={14}
            textAnchor="middle"
            fontFamily="'Inter', sans-serif"
            transform={`rotate(-90 ${chartLeft - 86} ${chartTop + curveHeight / 2})`}
          >
            {asString(asRecord(data.yAxis)?.label) ?? "Cumulative Cost"}
          </text>
          <text
            x={chartLeft + curveWidth * 0.7}
            y={chartTop + 24}
            fill={debtColor}
            fontSize={18}
            fontFamily="'JetBrains Mono', monospace"
            opacity={0.8}
          >
            {asString(debtCurve?.label) ?? "Debt × (1 + Rate)^Time"}
          </text>
          <text
            x={chartLeft + curveWidth * 0.7}
            y={flatY + 26}
            fill={flatColor}
            fontSize={16}
            fontFamily="'Inter', sans-serif"
            opacity={0.82}
          >
            {asString(regenerationCurve?.label) ?? "Regeneration cost (debt resets each cycle)"}
          </text>
          {stat ? (
            <>
              <text
                x={chartLeft + curveWidth * 0.46}
                y={chartTop + 60}
                fill="#E2E8F0"
                fontSize={22}
                fontWeight={700}
                fontFamily="'Inter', sans-serif"
              >
                {asString(stat.value) ?? asString(stat.text) ?? "$1.52 trillion/year"}
              </text>
              <text
                x={chartLeft + curveWidth * 0.46}
                y={chartTop + 86}
                fill="#94A3B8"
                fontSize={14}
                fontFamily="'Inter', sans-serif"
              >
                {`— ${asString(stat.source) ?? "CISQ"}`}
              </text>
            </>
          ) : null}
        </svg>
      </AbsoluteFill>
    );
  }

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
          {resolvedThreshold ? (
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
                  {asString(resolvedThreshold.label) ?? "Threshold"}
                </text>
              </g>
            ) : null}
          {resolvedCrossings.map((crossing, index) => (
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
  const frame = useCurrentFrame();
  const durationInFrames = useVisualDurationInFrames();
  const splitVisualId = React.useId().replace(/:/g, "");
  const divider = asRecord(data.divider);
  const dividerWidth = Math.max(1, Math.floor(asNumber(divider?.width) ?? 2));
  const dividerColor = asString(divider?.color) ?? "#FFFFFF";
  const dividerOpacity = asNumber(divider?.opacity) ?? 0.6;
  const panelRecord = asRecord(data.panels);
  const left = asRecord(panelRecord?.left) ?? asRecord(data.leftPanel) ?? asRecord(data.left) ?? {};
  const right = asRecord(panelRecord?.right) ?? asRecord(data.rightPanel) ?? asRecord(data.right) ?? {};
  const leftSrc = useVisualMediaAssetSrc("leftSrc");
  const rightSrc = useVisualMediaAssetSrc("rightSrc");
  const leftBaseSrc = useVisualMediaAssetSrc("leftBaseSrc") ?? leftSrc;
  const leftRevealSrc = useVisualMediaAssetSrc("leftRevealSrc");
  const rightBaseSrc = useVisualMediaAssetSrc("rightBaseSrc") ?? rightSrc;
  const rightRevealSrc = useVisualMediaAssetSrc("rightRevealSrc");
  const multiplier = asString(data.multiplier);

  const renderPanelInterior = (
    panel: Record<string, unknown>,
    accent: string,
    panelKey: "left" | "right"
  ) => {
    const animation = asString(panel.animation);
    const content = asString(panel.content);
    const tokenCount = formatApproxTokenCount(panel.tokenCount);
    const elements = Array.isArray(panel.elements)
      ? panel.elements
          .map((entry) => asRecord(entry))
          .filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];
    const elementTypes = new Set(
      elements
        .map((entry) => asString(entry.type))
        .filter((entry): entry is string => Boolean(entry))
    );
    const sections = Array.isArray(panel.sections)
      ? panel.sections.map((entry) => asRecord(entry)).filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];

    if (content === "veo_clip_with_aura") {
      const auraColor =
        asString(asRecord(panel.aura)?.color) ??
        asString(panel.auraColor) ??
        accent;
      return (
        <div
          style={{
            position: "absolute",
            inset: 0,
            pointerEvents: "none",
          }}
        >
          <div
            style={{
              position: "absolute",
              left: "50%",
              top: "50%",
              width: 280,
              height: 280,
              borderRadius: 999,
              transform: "translate(-50%, -50%)",
              boxShadow: `0 0 140px ${auraColor}66`,
              border: `2px solid ${auraColor}66`,
              opacity: 0.34,
            }}
          />
          <div
            style={{
              position: "absolute",
              left: "50%",
              top: "50%",
              width: 180,
              height: 180,
              borderRadius: 999,
              transform: "translate(-50%, -50%)",
              background: `radial-gradient(circle, ${auraColor}24 0%, rgba(2, 6, 23, 0) 72%)`,
              opacity: 0.72,
            }}
          />
        </div>
      );
    }

    if (content === "veo_clip_then_zoom_out") {
      const revealHint = asString(panel.zoomOutReveals);
      return (
        <div
          style={{
            position: "absolute",
            inset: 0,
            pointerEvents: "none",
          }}
        >
          {revealHint?.includes("codebase") ? (
            <div style={{ position: "absolute", inset: "24px 22px 24px 22px" }}>
              {["// TODO", "// legacy", "// patch", "+ spec", "- debt"].map((label, index) => (
                <div
                  key={`${label}-${index}`}
                  style={{
                    position: "absolute",
                    left: `${8 + (index % 2) * 46}%`,
                    top: `${14 + index * 12}%`,
                    padding: "6px 10px",
                    borderRadius: 999,
                    backgroundColor: "rgba(239, 68, 68, 0.16)",
                    border: "1px solid rgba(239, 68, 68, 0.28)",
                    color: "#FCA5A5",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 12,
                    opacity: index < 2 ? 0.28 : 0.42,
                  }}
                >
                  {label}
                </div>
              ))}
              {Array.from({ length: 12 }).map((_, index) => (
                <div
                  key={`code-file-${index}`}
                  style={{
                    position: "absolute",
                    left: `${4 + (index % 4) * 22}%`,
                    top: `${54 + Math.floor(index / 4) * 12}%`,
                    width: 72,
                    height: 34,
                    borderRadius: 10,
                    backgroundColor: "rgba(15, 23, 42, 0.76)",
                    border: "1px solid rgba(148, 163, 184, 0.16)",
                    opacity: 0.38,
                  }}
                />
              ))}
            </div>
          ) : null}
          {revealHint?.includes("drawer_of_mended_garments") ? (
            <div
              style={{
                position: "absolute",
                inset: "56px 36px 48px 36px",
                display: "grid",
                gridTemplateColumns: "repeat(4, minmax(0, 1fr))",
                gap: 14,
              }}
            >
              {Array.from({ length: 12 }).map((_, index) => (
                <div
                  key={`garment-${index}`}
                  style={{
                    borderRadius: 16,
                    backgroundColor:
                      index % 3 === 0
                        ? "rgba(217, 148, 74, 0.22)"
                        : index % 3 === 1
                          ? "rgba(148, 163, 184, 0.18)"
                          : "rgba(120, 113, 108, 0.2)",
                    border: "1px solid rgba(226, 232, 240, 0.14)",
                    opacity: 0.42,
                  }}
                />
              ))}
            </div>
          ) : null}
        </div>
      );
    }

    if (elements.length > 0) {
      const isPrinterPanel =
        elementTypes.has("coordinate_grid") || elementTypes.has("printer_nozzle");
      const isMoldPanel =
        elementTypes.has("mold_walls") ||
        elementTypes.has("liquid_flow") ||
        elementTypes.has("wall_glow_on_impact");
      const hasImpactGlow = elementTypes.has("wall_glow_on_impact");

      if (isPrinterPanel) {
        return (
          <div
            style={{
              position: "absolute",
              inset: "86px 24px 92px",
              borderRadius: 20,
              border: "1px solid rgba(96, 165, 250, 0.22)",
              overflow: "hidden",
            }}
          >
            <svg width="100%" height="100%" viewBox="0 0 420 520" preserveAspectRatio="none">
              {Array.from({ length: 9 }).map((_, index) => (
                <line
                  key={`grid-h-${index}`}
                  x1={36}
                  y1={60 + index * 40}
                  x2={384}
                  y2={60 + index * 40}
                  stroke="rgba(96, 165, 250, 0.14)"
                  strokeDasharray="4 8"
                />
              ))}
              {Array.from({ length: 8 }).map((_, index) => (
                <line
                  key={`grid-v-${index}`}
                  x1={52 + index * 40}
                  y1={44}
                  x2={52 + index * 40}
                  y2={404}
                  stroke="rgba(96, 165, 250, 0.14)"
                  strokeDasharray="4 8"
                />
              ))}
              <path d="M 170 104 L 210 140 L 250 104 Z" fill="rgba(96, 165, 250, 0.82)" />
              {Array.from({ length: 3 }).flatMap((_, layer) =>
                Array.from({ length: 8 }).map((__, point) => (
                  <g key={`print-point-${layer}-${point}`}>
                    <rect
                      x={114 + point * 18}
                      y={254 + layer * 18}
                      width={10}
                      height={6}
                      rx={2}
                      fill="rgba(96, 165, 250, 0.72)"
                    />
                    <text
                      x={110 + point * 18}
                      y={248 + layer * 18}
                      fill="rgba(96, 165, 250, 0.42)"
                      fontSize="7"
                      fontFamily="JetBrains Mono, monospace"
                    >
                      ({point},{layer})
                    </text>
                  </g>
                ))
              )}
            </svg>
          </div>
        );
      }

      if (isMoldPanel) {
        const moldFlowClipId = `${splitVisualId}-${panelKey}-mold-flow-clip`;
        return (
          <div
            style={{
              position: "absolute",
              inset: "86px 24px 92px",
              borderRadius: 20,
              border: "1px solid rgba(217, 148, 74, 0.24)",
              overflow: "hidden",
            }}
          >
            <svg width="100%" height="100%" viewBox="0 0 420 520" preserveAspectRatio="none">
              <defs>
                <clipPath id={moldFlowClipId}>
                  <rect x={108} y={98} width={204} height={278} rx={18} />
                </clipPath>
              </defs>
              <path d="M 180 42 L 210 92 L 240 42 Z" fill="rgba(148, 163, 184, 0.72)" />
              <rect
                x={104}
                y={94}
                width={212}
                height={286}
                rx={20}
                fill="none"
                stroke="rgba(217, 148, 74, 0.72)"
                strokeWidth={4}
              />
              <path
                d="M 138 132 L 170 132 L 170 186 L 204 186 L 204 238 L 256 238 L 256 186 L 292 186 L 292 132"
                fill="none"
                stroke="rgba(217, 148, 74, 0.56)"
                strokeWidth={4}
                strokeLinejoin="round"
              />
              <path
                d="M 208 94
                   C 188 130, 168 176, 172 224
                   C 176 270, 214 306, 252 302
                   C 276 298, 290 272, 286 234
                   C 282 204, 254 178, 236 146
                   C 228 130, 220 112, 208 94 Z"
                fill="rgba(167, 139, 250, 0.36)"
                stroke="rgba(217, 148, 74, 0.32)"
                strokeWidth={2}
                clipPath={`url(#${moldFlowClipId})`}
              />
              <circle
                cx={258}
                cy={238}
                r={36}
                fill="rgba(217, 148, 74, 0.16)"
                clipPath={`url(#${moldFlowClipId})`}
              />
              {hasImpactGlow ? (
                <>
                  <circle
                    cx={258}
                    cy={238}
                    r={48}
                    fill="rgba(250, 204, 21, 0.12)"
                    clipPath={`url(#${moldFlowClipId})`}
                  />
                  <circle
                    cx={258}
                    cy={238}
                    r={22}
                    fill="rgba(250, 204, 21, 0.22)"
                    clipPath={`url(#${moldFlowClipId})`}
                  />
                </>
              ) : null}
            </svg>
          </div>
        );
      }
    }

    if (animation === "printer_nozzle_grid") {
      return renderPanelInterior(
        {
          ...panel,
          elements: [{ type: "coordinate_grid" }, { type: "printer_nozzle" }],
        },
        accent,
        panelKey
      );
    }

    if (animation === "liquid_flow_walls") {
      return renderPanelInterior(
        {
          ...panel,
          elements: [{ type: "mold_walls" }, { type: "liquid_flow" }, { type: "wall_glow_on_impact" }],
        },
        accent,
        panelKey
      );
    }

    if (content === "context_window_cluttered") {
      const blocks = buildContextWindowTokenBlocks("cluttered");
      return (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: 86,
            bottom: 92,
            width: 420,
            maxWidth: "calc(100% - 48px)",
            transform: "translateX(-50%)",
            borderRadius: 20,
            backgroundColor: "rgba(2, 6, 23, 0.8)",
            border: "1px solid rgba(239, 68, 68, 0.22)",
            overflow: "hidden",
            padding: "18px 18px 56px",
          }}
        >
          {tokenCount ? renderInsetTokenBadge(tokenCount, "#EF4444") : null}
          <div
            style={{
              position: "absolute",
              inset: "52px 16px 56px",
            }}
          >
            {blocks.map((block, index) => {
              const blockColor =
                block.tone === "danger"
                  ? "#EF4444"
                  : block.tone === "success"
                    ? "#4ADE80"
                    : "#94A3B8";
              return (
                <div
                  key={`context-block-${index}`}
                  style={{
                    position: "absolute",
                    left: `${block.left}%`,
                    top: `${block.top}%`,
                    width: `${block.width}%`,
                    height: block.height,
                    borderRadius: 10,
                    backgroundColor: `${blockColor}${block.tone === "neutral" ? "14" : "22"}`,
                    border: `1px solid ${blockColor}44`,
                    opacity: block.opacity,
                    overflow: "hidden",
                  }}
                >
                  <div
                    style={{
                      position: "absolute",
                      left: 8,
                      right: "22%",
                      top: "50%",
                      height: 2,
                      transform: "translateY(-50%)",
                      borderRadius: 999,
                      backgroundColor: blockColor,
                      opacity: 0.65,
                    }}
                  />
                </div>
              );
            })}
            <div
              style={{
                position: "absolute",
                inset: 0,
                boxShadow: "inset 0 0 90px rgba(239, 68, 68, 0.16)",
                pointerEvents: "none",
              }}
            />
          </div>
          <div
            style={{
              position: "absolute",
              left: 18,
              bottom: 16,
              display: "flex",
              flexDirection: "column",
              gap: 5,
              fontFamily: "'Inter', sans-serif",
              fontSize: 11,
            }}
          >
            <div style={{ color: "#EF4444", opacity: 0.75 }}>Red = irrelevant code retrieved</div>
            <div style={{ color: "#4ADE80", opacity: 0.82 }}>Green = actually needed</div>
          </div>
        </div>
      );
    }

    if (content === "context_window_clean") {
      return (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: 86,
            bottom: 92,
            width: 420,
            maxWidth: "calc(100% - 48px)",
            transform: "translateX(-50%)",
            borderRadius: 20,
            backgroundColor: "rgba(2, 6, 23, 0.72)",
            border: "1px solid rgba(74, 222, 128, 0.24)",
            padding: "52px 18px 18px",
            display: "flex",
            flexDirection: "column",
            gap: 12,
          }}
        >
          {tokenCount ? renderInsetTokenBadge(tokenCount, "#4ADE80") : null}
          {sections.slice(0, 3).map((section, index) => {
            const color = asString(section.color) ?? (index === 0 ? "#4A90D9" : index === 1 ? "#D9944A" : "#5AAA6E");
            const tokens = formatExactTokenCount(section.tokens);
            const rawLabel = asString(section.label) ?? `Section ${index + 1}`;
            const normalizedLabel = rawLabel.toLowerCase();
            const title =
              normalizedLabel === "grounding"
                ? "Grounding example"
                : tokens && (normalizedLabel === "prompt" || normalizedLabel === "tests")
                  ? `${rawLabel} (${tokens})`
                  : rawLabel;
            return (
              <div
                key={`section-${index}`}
                style={{
                  borderRadius: 14,
                  backgroundColor: `${color}22`,
                  border: `1px solid ${color}44`,
                  padding: "14px 16px",
                }}
              >
                <div style={{ color, fontSize: 14, fontWeight: 800, letterSpacing: 1 }}>
                  {title}
                </div>
                {tokens && normalizedLabel !== "prompt" && normalizedLabel !== "tests" && normalizedLabel !== "grounding" ? (
                  <div style={{ color: "#E2E8F0", fontSize: 12, marginTop: 4 }}>{tokens}</div>
                ) : null}
              </div>
            );
          })}
          <div
            style={{
              flex: 1,
              borderRadius: 14,
              border: "1px dashed rgba(74, 222, 128, 0.28)",
              backgroundColor: "rgba(15, 23, 42, 0.52)",
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              color: "#4ADE80",
              fontSize: 16,
              fontWeight: 700,
            }}
          >
            Room to think
          </div>
        </div>
      );
    }

    if (content === "dense_code") {
      const lines = buildDenseCodePreviewLines("dense");
      const blocks = buildContextWindowTokenBlocks("dense");
      return (
        <div
          style={{
            position: "absolute",
            inset: "86px 24px 92px",
            borderRadius: 20,
            backgroundColor: "rgba(2, 6, 23, 0.82)",
            border: "1px solid rgba(148, 163, 184, 0.22)",
            padding: "50px 18px 16px",
            overflow: "hidden",
          }}
        >
          {tokenCount ? renderInsetTokenBadge(tokenCount, accent) : null}
          <div style={{ position: "absolute", inset: "52px 16px 16px" }}>
            {blocks.map((block, index) => (
              <div
                key={`dense-block-${index}`}
                style={{
                  position: "absolute",
                  left: `${block.left}%`,
                  top: `${block.top}%`,
                  width: `${block.width}%`,
                  height: block.height,
                  borderRadius: 10,
                  backgroundColor: "rgba(148, 163, 184, 0.12)",
                  border: "1px solid rgba(148, 163, 184, 0.14)",
                  opacity: block.opacity,
                }}
              />
            ))}
            <div style={{ display: "grid", gridTemplateColumns: "1fr", rowGap: 5 }}>
              {lines
                .concat(lines)
                .slice(0, 14)
                .map((line, index) => (
                  <div
                    key={`${line}-${index}`}
                    style={{
                      color: index % 4 === 0 ? "#93C5FD" : index % 3 === 0 ? "#E2E8F0" : "#CBD5E1",
                      fontFamily: "'JetBrains Mono', monospace",
                      fontSize: 12,
                      whiteSpace: "pre",
                      opacity: 0.92 - index * 0.035,
                    }}
                  >
                    {line}
                  </div>
                ))}
            </div>
          </div>
        </div>
      );
    }

    if (content === "prompt_blocks") {
      const promptLines = buildDenseCodePreviewLines("clean");
      return (
        <div
          style={{
            position: "absolute",
            inset: "86px 24px 92px",
            borderRadius: 20,
            backgroundColor: "rgba(2, 6, 23, 0.72)",
            border: `1px solid ${accent}33`,
            padding: "52px 18px 16px",
            display: "grid",
            gridTemplateColumns: "1fr 1fr",
            gap: 12,
          }}
        >
          {tokenCount ? renderInsetTokenBadge(tokenCount, accent) : null}
          {Array.from({ length: 10 }).map((_, index) => (
            <div
              key={`prompt-${index}`}
              style={{
                borderRadius: 14,
                backgroundColor: "rgba(45, 212, 191, 0.14)",
                border: "1px solid rgba(45, 212, 191, 0.3)",
                padding: "10px 12px",
                display: "flex",
                flexDirection: "column",
                gap: 4,
                justifyContent: "center",
              }}
            >
              <div style={{ color: "#CCFBF1", fontSize: 11, fontWeight: 800, letterSpacing: 0.6 }}>
                {index === 0 ? "PROMPT" : index === 1 ? "TESTS" : index === 2 ? "GROUNDING" : `MODULE ${index + 1}`}
              </div>
              <div style={{ color: "#E2E8F0", fontSize: 11, lineHeight: 1.3 }}>
                {promptLines[index % promptLines.length]}
              </div>
            </div>
          ))}
        </div>
      );
    }

    return null;
  };

  const renderPanel = (
    panel: Record<string, unknown>,
    accent: string,
    src: string | null,
    baseSrc: string | null,
    revealSrc: string | null,
    panelKey: "left" | "right"
  ) => {
    const panelAccent = asString(panel.accentColor) ?? accent;
    const rawLabel = asString(panel.label);
    const labelLooksLikeHeader =
      Boolean(rawLabel) &&
      rawLabel === rawLabel?.toUpperCase() &&
      rawLabel.length <= 24;
    const header = asString(panel.header) ?? (labelLooksLikeHeader ? rawLabel : null);
    const headerColor = asString(panel.headerColor) ?? asString(panel.color) ?? panelAccent;
    const content = asString(panel.content);
    const caption =
      asString(panel.caption) ??
      asString(panel.description) ??
      asString(panel.subLabel) ??
      asString(panel.summary);
    const tokenCount = formatApproxTokenCount(panel.tokenCount);
    const usesInsetTokenBadge = ["context_window_cluttered", "context_window_clean", "dense_code", "prompt_blocks"].includes(
      content ?? ""
    );
    const scope = asString(panel.scope);
    const codeComments = asStringArray(panel.codeComments);
    const aura = asRecord(panel.aura);
    const revealHint = asString(panel.zoomOutReveals);
    const panelScale = revealHint
      ? interpolate(frame, [0, 180], [1.14, 0.88], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 1;
    const revealOpacity =
      revealSrc && revealSrc !== baseSrc
        ? interpolate(
            frame,
            [
              Math.max(6, Math.floor(durationInFrames * 0.18)),
              Math.max(12, Math.floor(durationInFrames * 0.55)),
            ],
            [0, 1],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }
          )
        : 1;
    const steps = Array.isArray(panel.steps)
      ? panel.steps
          .map((entry) =>
            typeof entry === "string" && entry.trim()
              ? { text: entry.trim() }
              : asRecord(entry)
          )
          .filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];
    const interior = renderPanelInterior(
      panel,
      panelAccent,
      panelKey
    );
    const usagePercent =
      typeof panel.relevantPercent === "number" || typeof panel.relevantPercent === "string"
        ? `Context utilization: ~${panel.relevantPercent}%`
        : null;

    return (
      <div
        style={{
          position: "relative",
          flex: 1,
          overflow: "hidden",
          borderRadius: 28,
          backgroundColor: subtleSurface,
          border: `1px solid ${panelAccent}55`,
        }}
      >
        {baseSrc || src ? (
          <>
            <OffthreadVideo
              src={baseSrc ?? src ?? ""}
              style={{
                width: "100%",
                height: "100%",
                objectFit: "cover",
                opacity: revealSrc && revealSrc !== baseSrc ? 0.88 * (1 - revealOpacity) : 0.88,
                transform: `scale(${panelScale})`,
                transformOrigin: "center center",
              }}
            />
            {revealSrc && revealSrc !== baseSrc ? (
              <OffthreadVideo
                src={revealSrc}
                style={{
                  position: "absolute",
                  inset: 0,
                  width: "100%",
                  height: "100%",
                  objectFit: "cover",
                  opacity: 0.92 * revealOpacity,
                  transform: `scale(${panelScale})`,
                  transformOrigin: "center center",
                }}
              />
            ) : null}
          </>
        ) : (
          <div
            style={{
              width: "100%",
              height: "100%",
              background: `linear-gradient(135deg, ${panelAccent}2b, rgba(15, 23, 42, 0.96))`,
              transform: `scale(${panelScale})`,
              transformOrigin: "center center",
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
        {aura ? (
          <div
            style={{
              position: "absolute",
              left: "50%",
              top: "50%",
              width: 260,
              height: 260,
              borderRadius: 999,
              transform: "translate(-50%, -50%)",
              boxShadow: `0 0 120px ${asString(aura.color) ?? panelAccent}66`,
              border: `2px solid ${asString(aura.color) ?? panelAccent}55`,
              opacity: 0.42,
              pointerEvents: "none",
            }}
          />
        ) : null}
        {header ? (
          <div
            style={{
              position: "absolute",
              left: 24,
              right: 24,
              top: 24,
              color: headerColor,
              fontFamily: "'Inter', sans-serif",
              fontSize: 24,
              fontWeight: 700,
              letterSpacing: 1.6,
              textAlign: "center",
            }}
          >
            {header}
          </div>
        ) : null}
        {tokenCount && !usesInsetTokenBadge ? (
          <div
            style={{
              position: "absolute",
              top: 24,
              right: 24,
              padding: "8px 12px",
              borderRadius: 999,
              backgroundColor: "rgba(2, 6, 23, 0.78)",
              border: `1px solid ${headerColor}33`,
              color: headerColor,
              fontFamily: "'Inter', sans-serif",
              fontSize: 14,
              fontWeight: 800,
            }}
          >
            {tokenCount}
          </div>
        ) : null}
        {interior}
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
          {caption ? (
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
          {usagePercent ? (
            <div
              style={{
                color: headerColor,
                fontFamily: "'Inter', sans-serif",
                fontSize: 15,
                fontWeight: 700,
                opacity: 0.82,
              }}
            >
              {usagePercent}
            </div>
          ) : null}
        </div>
      </div>
    );
  };

  const hasScopeFooter =
    Boolean(asString(left.scope)) &&
    Boolean(asString(right.scope)) &&
    !left.relevantPercent &&
    !right.relevantPercent;
  const usesPromptContextFooter =
    asString(left.content) === "dense_code" &&
    asString(right.content) === "prompt_blocks";

  return (
    <AbsoluteFill style={{ padding: "88px 72px 72px" }}>
      <div
        style={{
          width,
          height,
          display: "flex",
          gap: dividerWidth,
        }}
      >
        {renderPanel(left, "#60A5FA", leftSrc, leftBaseSrc, leftRevealSrc, "left")}
        {renderPanel(right, "#D9944A", rightSrc, rightBaseSrc, rightRevealSrc, "right")}
      </div>
      <div
        style={{
          position: "absolute",
          top: 88,
          bottom: 72,
          left: "50%",
          width: dividerWidth,
          backgroundColor: dividerColor,
          opacity: dividerOpacity,
          transform: "translateX(-50%)",
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
      {usesPromptContextFooter ? (
        <div
          style={{
            position: "absolute",
            left: 120,
            right: 120,
            bottom: 24,
            display: "flex",
            flexDirection: "column",
            gap: 8,
            alignItems: "center",
            textAlign: "center",
          }}
        >
          <div style={{ color: "#E2E8F0", fontSize: 16, opacity: 0.8 }}>
            Every token is author-curated. No retrieval guessing. No wasted space.
          </div>
          <div style={{ color: "#2DD4BF", fontSize: 16, fontWeight: 700, opacity: 0.92 }}>
            The entire context window is devoted to your problem.
          </div>
        </div>
      ) : hasScopeFooter ? (
        <div
          style={{
            position: "absolute",
            left: 120,
            right: 120,
            bottom: 26,
            display: "flex",
            flexDirection: "column",
            gap: 6,
            alignItems: "center",
            textAlign: "center",
          }}
        >
          <div style={{ color: "#E2E8F0", fontSize: 16, opacity: 0.78 }}>
            {`${asString(left.scope)} vs ${asString(right.scope)}`}
          </div>
          <div style={{ color: "#2DD4BF", fontSize: 16, fontWeight: 700, opacity: 0.9 }}>
            The right context is curated for the problem instead of retrieved from raw code.
          </div>
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
  const editorId = asString(data.editorId);
  const functionName = asString(data.functionName);
  const fileNames = [
    asString(data.filename),
    asString(data.highlightedModule),
    asString(data.promptFile),
    ...asStringArray(data.files),
    ...asStringArray(data.fileNames),
  ].filter((item): item is string => Boolean(item));
  const workflow = asStringArray(data.workflow);
  const warningComments = [
    ...asStringArray(data.warningComments),
    ...extractTextList(data.warningComments),
  ].filter((item, index, all) => all.indexOf(item) === index);
  const lineCount =
    asString(data.lineCount) ??
    (typeof data.originalLines === "number" ? `${data.originalLines} lines` : null);
  const regeneratedLines = asNumber(data.regeneratedLines);
  const originalLines = asNumber(data.originalLines);
  const generatedLines = Math.max(8, asNumber(data.generatedLines) ?? regeneratedLines ?? 14);
  const deletedLines = Math.max(
    0,
    asNumber(data.deletedLines) ??
      asNumber(data.patchCommentsRemoved) ??
      (originalLines !== null && regeneratedLines !== null
        ? Math.max(0, originalLines - regeneratedLines)
        : 0)
  );
  const chartId = resolveContractChartId(data);
  const terminal = asRecord(data.terminal);
  const terminalLines = [
    asString(terminal?.command),
    asString(terminal?.result),
    asString(data.terminalCommand),
    asString(data.terminalOutput),
    ...workflow,
    ...asStringArray(data.terminalCommands),
  ].filter((item): item is string => Boolean(item));
  const terminalPosition = asString(terminal?.position) ?? "bottom_right";
  const transformedModules = Array.isArray(data.transformedModules)
    ? data.transformedModules
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const pendingModules = asStringArray(data.pendingModules);

  const derivePromptFileName = (moduleName: string): string =>
    moduleName.replace(/\.[a-z0-9]+$/i, ".prompt.md");

  if (visualType === "code_visualization" || visualType === "code_editor_animation") {
    const prefersDenseEditor = editorId === "legacy_codebase_reveal";
    const panels = Math.max(
      prefersDenseEditor ? 4 : 3,
      asNumber(data.panels) ?? fileNames.length ?? (prefersDenseEditor ? 4 : 5)
    );
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
                  const showComment = Boolean(comment) && [2, 6, 11, 14].includes(lineIndex);
                  const fallbackLine = prefersDenseEditor
                    ? lineIndex % 5 === 0
                      ? "class LegacyAdapter:"
                      : lineIndex % 5 === 1
                        ? "    def route(self, request, env, cache):"
                        : lineIndex % 5 === 2
                          ? "        payload = legacy_utils.maybe_decode(request)"
                          : lineIndex % 5 === 3
                            ? "        return payment_processor.forward(payload, env)"
                            : "        return auth_handler.process(payload)"
                    : lineIndex % 4 === 0
                      ? "def legacy_handler(user, state):"
                      : lineIndex % 4 === 1
                        ? "    payload = adapter.load(state)"
                        : lineIndex % 4 === 2
                          ? "    if payload is None: return cache_fallback()"
                          : "    return transform(payload, user)";
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
                        {showComment ? comment : fallbackLine}
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

  if (visualType === "code_regeneration") {
    const resolvedFunctionName = functionName ?? "regenerate_auth_handler";
    const functionArgs =
      resolvedFunctionName === "process_order" ? "order, ctx" : "user_input: str";
    const fileTabLabel =
      fileNames[0] ?? `${resolvedFunctionName.replace(/[^\w]+/g, "_")}.py`;
    const regenerationLines =
      resolvedFunctionName === "process_order"
        ? [
            "from pricing import apply_discounts",
            "from inventory import reserve_items",
            "from receipts import build_receipt_response",
            "from metrics import emit_order_metrics",
            "",
            `def ${resolvedFunctionName}(${functionArgs}):`,
            "    validated = validate_order(order, ctx)",
            "    if validated is None:",
            "        return error_response('invalid-order')",
            "",
            "    priced = apply_discounts(validated, ctx)",
            "    reserved = reserve_items(priced, ctx)",
            "    if reserved.failed:",
            "        return error_response('inventory-unavailable')",
            "",
            "    receipt = finalize_order(reserved, ctx)",
            "    emit_order_metrics(receipt, ctx)",
            "    notify_fulfillment(receipt, ctx)",
            "    return build_receipt_response(receipt)",
            "",
            "# generated from prompt + tests + grounding",
          ].slice(0, Math.max(generatedLines, 21))
        : [
            "from auth import normalize_user_id",
            "from tests import ensure_user_contract",
            "",
            `def ${resolvedFunctionName}(${functionArgs}):`,
            "    normalized = normalize_user_id(user_input)",
            "    if normalized is None:",
            "        return None",
            "    ensure_user_contract(normalized)",
            "    payload = load_user_payload(normalized)",
            "    if payload is None:",
            "        return None",
            "    return build_auth_response(payload)",
            "",
            "# generated from prompt + tests + grounding",
          ].slice(0, Math.max(generatedLines, 14));
    const terminalCommandText =
      asString(terminal?.command) ??
      asString(data.terminalCommand) ??
      `pdd generate ${resolvedFunctionName}`;
    const terminalDisplay = `${terminalCommandText.startsWith("$") ? terminalCommandText : `$ ${terminalCommandText}`} ✓`;

    return (
      <AbsoluteFill style={{ padding: "76px 88px 78px" }}>
        <div
          style={{
            position: "absolute",
            inset: 0,
            background:
              "radial-gradient(circle at 72% 22%, rgba(74, 222, 128, 0.08), transparent 30%), radial-gradient(circle at 18% 18%, rgba(96, 165, 250, 0.10), transparent 32%)",
          }}
        />
        <div
          style={{
            position: "relative",
            flex: 1,
            borderRadius: 28,
            backgroundColor: "rgba(2, 6, 23, 0.9)",
            border: "1px solid rgba(71, 85, 105, 0.44)",
            boxShadow: "0 28px 90px rgba(2, 6, 23, 0.42)",
            overflow: "hidden",
          }}
        >
          <div
            style={{
              height: 52,
              display: "flex",
              alignItems: "center",
              justifyContent: "space-between",
              padding: "0 20px",
              backgroundColor: "rgba(15, 23, 42, 0.96)",
              color: "#CBD5E1",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 15,
            }}
          >
            <div>{fileTabLabel}</div>
            <div style={{ color: "#4ADE80" }}>{deletedLines > 0 ? `-${deletedLines} / +${generatedLines}` : `+${generatedLines} lines`}</div>
          </div>
          <div
            style={{
              display: "grid",
              gridTemplateColumns: "58px 1fr",
              rowGap: 8,
              padding: "22px 24px 26px",
            }}
          >
            {regenerationLines.map((line, index) => (
              <React.Fragment key={`regen-line-${index}`}>
                <div
                  style={{
                    color: "rgba(148, 163, 184, 0.48)",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 14,
                  }}
                >
                  {index + 1}
                </div>
                <div
                  style={{
                    color:
                      line.startsWith("from")
                        ? "#C4B5FD"
                        : line.startsWith("def")
                          ? "#93C5FD"
                          : line.startsWith("#")
                            ? "#4ADE80"
                            : line.includes("return")
                              ? "#FCD34D"
                              : "#E2E8F0",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 16,
                    whiteSpace: "pre",
                    opacity: 0.96,
                  }}
                >
                  {line}
                </div>
              </React.Fragment>
            ))}
          </div>
          <div
            style={{
              position: "absolute",
              right: terminalPosition === "bottom_right" ? 24 : undefined,
              left: terminalPosition === "bottom_right" ? undefined : 24,
              bottom: 24,
              minWidth: 320,
              padding: "14px 16px",
              borderRadius: 8,
              backgroundColor: "rgba(17, 17, 27, 0.9)",
            }}
          >
            <div
              style={{
                color: "#A6E3A1",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 12,
              }}
            >
              {terminalDisplay}
            </div>
          </div>
        </div>
      </AbsoluteFill>
    );
  }

  const supportsSourceOfTruthShift =
    visualType === "code_transformation" &&
    (chartId === "source_of_truth_shift" ||
      (transformedModules.length >= 2 &&
        pendingModules.length > 0 &&
        workflow.length >= 3));

  if (supportsSourceOfTruthShift) {
    const modulePairs =
      transformedModules.length >= 2
        ? transformedModules.slice(0, 2)
        : [
            { name: "auth_handler.py", state: "complete" },
            { name: "payment_processor.py", state: "animating" },
          ];
    const workflowStages =
      workflow.length > 0
        ? workflow
        : ["module", "prompt", "tests", "regenerate", "compare"];
    const backgroundModuleNames =
      pendingModules.length > 0
        ? pendingModules
        : [
            "user_service.py",
            "legacy_router.py",
            "config.py",
            "db_connector.py",
            "email_sender.py",
            "cache_layer.py",
          ];

    return (
      <AbsoluteFill style={{ padding: "72px 82px 76px" }}>
        <div
          style={{
            position: "absolute",
            inset: 0,
            background:
              "radial-gradient(circle at 78% 22%, rgba(96, 165, 250, 0.08), transparent 28%), radial-gradient(circle at 18% 18%, rgba(45, 212, 191, 0.06), transparent 26%)",
          }}
        />
        {backgroundModuleNames.slice(0, 6).map((moduleName, index) => {
          const column = index % 3;
          const row = Math.floor(index / 3);
          return (
            <div
              key={`background-module-${moduleName}`}
              style={{
                position: "absolute",
                left: 760 + column * 220 + (row % 2) * 28,
                top: 130 + row * 190,
                width: 188,
                height: 106,
                borderRadius: 18,
                backgroundColor: "rgba(17, 24, 39, 0.18)",
                border: "1px solid rgba(71, 85, 105, 0.18)",
                boxShadow: "0 12px 32px rgba(2, 6, 23, 0.18)",
                overflow: "hidden",
              }}
            >
              <div
                style={{
                  height: 26,
                  display: "flex",
                  alignItems: "center",
                  padding: "0 12px",
                  backgroundColor: "rgba(15, 23, 42, 0.35)",
                  color: "rgba(71, 85, 105, 0.7)",
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 10,
                }}
              >
                {moduleName}
              </div>
            </div>
          );
        })}
        {modulePairs.map((moduleEntry, index) => {
          const moduleName = asString(moduleEntry.name) ?? `module_${index + 1}.py`;
          const moduleState = asString(moduleEntry.state) ?? (index === 0 ? "complete" : "animating");
          const codeTop = 178 + index * 242;
          const codeLeft = 220;
          const promptLeft = 452;
          const promptFileName = derivePromptFileName(moduleName);
          const promptGlow =
            moduleState === "animating"
              ? "0 0 26px rgba(96, 165, 250, 0.34)"
              : "0 0 18px rgba(96, 165, 250, 0.24)";

          return (
            <React.Fragment key={`transform-pair-${moduleName}`}>
              <div
                style={{
                  position: "absolute",
                  left: codeLeft,
                  top: codeTop,
                  width: 170,
                  height: 114,
                  borderRadius: 20,
                  backgroundColor:
                    moduleState === "animating"
                      ? "rgba(17, 24, 39, 0.36)"
                      : "rgba(17, 24, 39, 0.28)",
                  border: "1px solid rgba(71, 85, 105, 0.34)",
                  boxShadow: "0 18px 44px rgba(2, 6, 23, 0.22)",
                  overflow: "hidden",
                  filter: "grayscale(0.72)",
                }}
              >
                <div
                  style={{
                    height: 30,
                    display: "flex",
                    alignItems: "center",
                    padding: "0 12px",
                    backgroundColor: "rgba(15, 23, 42, 0.72)",
                    color: "#94A3B8",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 11,
                  }}
                >
                  {moduleName}
                </div>
                <div
                  style={{
                    display: "grid",
                    gridTemplateColumns: "20px 1fr",
                    rowGap: 5,
                    padding: "10px 12px 0",
                  }}
                >
                  {Array.from({ length: 5 }).map((_, lineIndex) => (
                    <React.Fragment key={`${moduleName}-line-${lineIndex}`}>
                      <div
                        style={{
                          color: "rgba(100, 116, 139, 0.55)",
                          fontFamily: "'JetBrains Mono', monospace",
                          fontSize: 9,
                        }}
                      >
                        {lineIndex + 1}
                      </div>
                      <div
                        style={{
                          color: "rgba(148, 163, 184, 0.45)",
                          fontFamily: "'JetBrains Mono', monospace",
                          fontSize: 10,
                        }}
                      >
                        {lineIndex === 0
                          ? "def handle(input):"
                          : lineIndex === 1
                            ? "    return prompt.generate()"
                            : "    # artifact"}
                      </div>
                    </React.Fragment>
                  ))}
                </div>
              </div>
              <div
                style={{
                  position: "absolute",
                  left: promptLeft,
                  top: codeTop + 8,
                  width: 72,
                  height: 92,
                  borderRadius: 18,
                  backgroundColor: "rgba(96, 165, 250, 0.18)",
                  border: "1px solid rgba(96, 165, 250, 0.62)",
                  boxShadow: promptGlow,
                  display: "flex",
                  alignItems: "center",
                  justifyContent: "center",
                }}
              >
                <div
                  style={{
                    width: 46,
                    height: 58,
                    borderRadius: 12,
                    border: "1px solid rgba(96, 165, 250, 0.72)",
                    backgroundColor: "rgba(96, 165, 250, 0.16)",
                    color: "#BFDBFE",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 8,
                    lineHeight: 1.3,
                    display: "flex",
                    alignItems: "flex-end",
                    justifyContent: "center",
                    paddingBottom: 10,
                    textAlign: "center",
                  }}
                >
                  {".prompt.md"}
                </div>
              </div>
              <div
                style={{
                  position: "absolute",
                  left: codeLeft + 170,
                  top: codeTop + 54,
                  width: 62,
                  height: 2,
                  backgroundColor: "rgba(96, 165, 250, 0.28)",
                }}
              />
              <div
                style={{
                  position: "absolute",
                  left: codeLeft + 168,
                  top: codeTop + 49,
                  width: 0,
                  height: 0,
                  borderTop: "6px solid transparent",
                  borderBottom: "6px solid transparent",
                  borderRight: "10px solid rgba(96, 165, 250, 0.34)",
                }}
              />
              <div
                style={{
                  position: "absolute",
                  left: codeLeft + 8,
                  top: codeTop + 124,
                  color: "rgba(100, 116, 139, 0.72)",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 11,
                  letterSpacing: 0.2,
                }}
              >
                artifact
              </div>
              <div
                style={{
                  position: "absolute",
                  left: promptLeft - 8,
                  top: codeTop + 124,
                  color: "rgba(96, 165, 250, 0.84)",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 11,
                  letterSpacing: 0.2,
                }}
              >
                source of truth
              </div>
              <div
                style={{
                  position: "absolute",
                  left: promptLeft - 18,
                  top: codeTop + 108,
                  width: 126,
                  color: "#60A5FA",
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 10,
                  textAlign: "center",
                }}
              >
                {promptFileName}
              </div>
              {moduleState === "animating" ? (
                <div
                  style={{
                    position: "absolute",
                    left: 206,
                    top: codeTop - 44,
                    padding: "8px 12px",
                    borderRadius: 14,
                    backgroundColor: "rgba(2, 6, 23, 0.84)",
                    border: "1px solid rgba(96, 165, 250, 0.3)",
                    color: "#E2E8F0",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 11,
                  }}
                >
                  {`$ pdd update ${moduleName}`}
                </div>
              ) : null}
            </React.Fragment>
          );
        })}
        <div
          style={{
            position: "absolute",
            left: width - 660,
            right: 88,
            bottom: 78,
            display: "grid",
            gridTemplateColumns: "repeat(5, minmax(0, 1fr))",
            alignItems: "center",
            columnGap: 12,
          }}
        >
          {workflowStages.slice(0, 5).map((stage, index) => (
            <React.Fragment key={`workflow-stage-${stage}`}>
              <div
                style={{
                  borderRadius: 999,
                  border: `1px solid ${index === 1 ? "rgba(96, 165, 250, 0.46)" : index === 2 ? "rgba(217, 148, 74, 0.46)" : index === 3 ? "rgba(167, 139, 250, 0.46)" : index === 4 ? "rgba(74, 222, 128, 0.46)" : "rgba(51, 65, 85, 0.56)"}`,
                  backgroundColor:
                    index === 1
                      ? "rgba(96, 165, 250, 0.14)"
                      : index === 2
                        ? "rgba(217, 148, 74, 0.14)"
                        : index === 3
                          ? "rgba(167, 139, 250, 0.14)"
                          : index === 4
                            ? "rgba(74, 222, 128, 0.14)"
                            : "rgba(51, 65, 85, 0.28)",
                  color: "#94A3B8",
                  fontFamily: "'Inter', sans-serif",
                  fontSize: 11,
                  fontWeight: 600,
                  textAlign: "center",
                  padding: "9px 8px",
                }}
              >
                {stage}
              </div>
              {index < workflowStages.slice(0, 5).length - 1 ? (
                <div
                  style={{
                    position: "absolute",
                    left: width - 660 + (index + 0.74) * ((width - 660 - 88) / 5),
                    right: undefined,
                    bottom: 101,
                    width: 34,
                    color: "rgba(71, 85, 105, 0.75)",
                    fontSize: 20,
                    textAlign: "center",
                  }}
                >
                  →
                </div>
              ) : null}
            </React.Fragment>
          ))}
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
  const chartId = asString(data.chartId);
  const diagramId = asString(data.diagramId) ?? "";
  const annotations = Array.isArray(data.annotations)
    ? data.annotations
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const comparison = asRecord(data.comparison);
  const emphasisLine = asString(data.emphasisLine);
  const annotationPositions: Record<
    string,
    { left: number; top: number; targetX: number; targetY: number; anchor: "left" | "right" }
  > = {
    immediate_patch_line: {
      left: width * 0.72,
      top: height * 0.47,
      targetX: width * 0.67,
      targetY: height * 0.58,
      anchor: "left",
    },
    total_cost_line: {
      left: width * 0.72,
      top: height * 0.2,
      targetX: width * 0.66,
      targetY: height * 0.4,
      anchor: "left",
    },
    debt_shading: {
      left: width * 0.72,
      top: height * 0.34,
      targetX: width * 0.58,
      targetY: height * 0.48,
      anchor: "left",
    },
    debt_gap: {
      left: width * 0.12,
      top: height * 0.34,
      targetX: width * 0.5,
      targetY: height * 0.48,
      anchor: "right",
    },
  };

  if (diagramId === "research_annotations") {
    const warning = annotations[0] ?? null;
    const positive = annotations[1] ?? null;
    return (
      <AbsoluteFill>
        <HeaderBlock data={data} accent={accent} title={title} />
        <div
          style={{
            position: "absolute",
            inset: `${height * 0.28}px 72px 72px`,
            overflow: "hidden",
          }}
        >
          <div
            style={{
              position: "absolute",
              inset: 0,
              backgroundImage:
                "linear-gradient(rgba(30,41,59,0.14) 1px, transparent 1px), linear-gradient(90deg, rgba(30,41,59,0.14) 1px, transparent 1px)",
              backgroundSize: "40px 40px",
              opacity: 0.34,
            }}
          />
          <svg
            width="100%"
            height="100%"
            viewBox={`0 0 ${width - 144} ${height * 0.5}`}
            style={{ position: "absolute", inset: 0 }}
          >
            <path d="M 420 54 L 490 112 L 560 54 Z" fill="rgba(148, 163, 184, 0.34)" />
            <rect x="264" y="126" width="420" height="236" rx="24" fill="none" stroke="rgba(217, 148, 74, 0.22)" strokeWidth="3" />
            <path d="M 326 182 L 396 182 L 396 236 L 474 236 L 474 296 L 554 296 L 554 236 L 624 236 L 624 182" fill="none" stroke="rgba(217, 148, 74, 0.44)" strokeWidth="5" strokeLinejoin="round" />
            <path d="M 468 126 C 432 176, 394 242, 414 298 C 436 360, 526 372, 588 334 C 636 306, 644 244, 610 198 C 584 164, 528 144, 494 128 Z" fill="rgba(96, 165, 250, 0.08)" stroke="rgba(167, 139, 250, 0.14)" strokeWidth="2" />
          </svg>
          <div
            style={{
              position: "absolute",
              left: width * 0.58,
              top: height * 0.02,
              width: 400,
              padding: "18px 20px",
              borderRadius: 12,
              backgroundColor: "#1E1015",
              border: "1px solid rgba(239, 68, 68, 0.3)",
              boxShadow: "0 16px 36px rgba(2, 6, 23, 0.28)",
              display: "flex",
              flexDirection: "column",
              gap: 8,
            }}
          >
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <div style={{ color: "#EF4444", fontSize: 18, fontWeight: 700 }}>▲</div>
              <div style={{ color: "#EF4444", fontSize: 20, fontWeight: 700 }}>
                {asString(warning?.text) ?? "AI code: 1.7× more issues"}
              </div>
            </div>
            <div style={{ color: "#94A3B8", fontSize: 12 }}>
              {asString(warning?.source) ?? "CodeRabbit, 2025"}
            </div>
            <div style={{ color: "rgba(239, 68, 68, 0.76)", fontSize: 11 }}>
              {asString(warning?.detail) ?? "75% more logic errors · 8× more perf problems"}
            </div>
          </div>
          <div
            style={{
              position: "absolute",
              left: width * 0.58,
              top: height * 0.19,
              width: 400,
              padding: "18px 20px",
              borderRadius: 12,
              backgroundColor: "#0F1E15",
              border: "1px solid rgba(74, 222, 128, 0.3)",
              boxShadow: "0 16px 36px rgba(2, 6, 23, 0.28)",
              display: "flex",
              flexDirection: "column",
              gap: 8,
            }}
          >
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <div style={{ color: "#4ADE80", fontSize: 18, fontWeight: 700 }}>✓</div>
              <div style={{ color: "#4ADE80", fontSize: 20, fontWeight: 700 }}>
                {asString(positive?.text) ?? "AI + strong tests = amplified delivery"}
              </div>
            </div>
            <div style={{ color: "#94A3B8", fontSize: 12 }}>
              {asString(positive?.source) ?? "DORA, 2025"}
            </div>
          </div>
          <div
            style={{
              position: "absolute",
              right: 46,
              bottom: 42,
              width: 260,
              padding: "16px 18px",
              borderRadius: 18,
              backgroundColor: "rgba(2, 6, 23, 0.78)",
              border: "1px solid rgba(74, 222, 128, 0.24)",
              color: "#4ADE80",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 12,
              lineHeight: 1.45,
            }}
          >
            <div>✓ test_null_handling</div>
            <div>✓ test_unicode</div>
            <div>✓ test_empty_string</div>
            <div>✓ test_latency</div>
          </div>
          <div
            style={{
              position: "absolute",
              left: 0,
              right: 0,
              bottom: 10,
              textAlign: "center",
              color: "#E2E8F0",
              fontSize: 16,
              fontStyle: "italic",
              opacity: 0.66,
            }}
          >
            The walls aren't optional
          </div>
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
        {annotations.length > 0 && chartId === "code_cost_triple_line" ? (
          <div
            style={{
              position: "relative",
              minHeight: 470,
              borderRadius: 28,
              backgroundColor: "rgba(2, 6, 23, 0.42)",
              border: "1px solid rgba(148, 163, 184, 0.14)",
              overflow: "hidden",
            }}
          >
            <svg
              width="100%"
              height="100%"
              viewBox={`0 0 ${width - 144} ${Math.max(470, height * 0.42)}`}
              style={{ position: "absolute", inset: 0 }}
            >
              <path
                d={`M 110 320 C 270 302, 420 286, 700 270 C 860 256, 970 240, 1100 220`}
                fill="none"
                stroke="rgba(74, 144, 217, 0.72)"
                strokeWidth={4}
              />
              <path
                d={`M 110 240 C 280 238, 420 244, 690 256 C 870 262, 990 266, 1100 270`}
                fill="none"
                stroke="rgba(217, 148, 74, 0.72)"
                strokeWidth={4}
              />
              <path
                d={`M 110 208 C 280 210, 430 220, 700 234 C 880 244, 1000 250, 1100 254`}
                fill="none"
                stroke="rgba(217, 148, 74, 0.58)"
                strokeWidth={3}
                strokeDasharray="10 10"
              />
              <path
                d={`M 710 244 C 820 250, 920 256, 1100 264 L 1100 312 C 930 304, 830 296, 710 286 Z`}
                fill="rgba(217, 148, 74, 0.08)"
                stroke="none"
              />
              {annotations.slice(0, 4).map((annotation, index) => {
                const target = asString(annotation.target) ?? `annotation-${index}`;
                const position =
                  annotationPositions[target] ??
                  ({
                    left: width * 0.68,
                    top: height * 0.28 + index * 82,
                    targetX: width * 0.64,
                    targetY: height * 0.34 + index * 36,
                    anchor: "left",
                  } as const);
                const color = asString(annotation.color) ?? "#60A5FA";
                const startX =
                  position.anchor === "left" ? position.left - 24 : position.left + 260;
                const startY = position.top + 58;
                return (
                  <g key={`callout-${index}`}>
                    <line
                      x1={startX}
                      y1={startY}
                      x2={position.targetX}
                      y2={position.targetY}
                      stroke={`${color}66`}
                      strokeWidth={2}
                    />
                    <circle cx={position.targetX} cy={position.targetY} r={5} fill={`${color}AA`} />
                  </g>
                );
              })}
            </svg>
            {annotations.slice(0, 4).map((annotation, index) => {
              const target = asString(annotation.target) ?? `annotation-${index}`;
              const position =
                annotationPositions[target] ??
                ({
                  left: width * 0.68,
                  top: height * 0.28 + index * 82,
                  targetX: width * 0.64,
                  targetY: height * 0.34 + index * 36,
                  anchor: "left",
                } as const);
              const color = asString(annotation.color) ?? "#60A5FA";
              return (
                <div
                  key={`annotation-${index}`}
                  style={{
                    position: "absolute",
                    left: position.left,
                    top: position.top,
                    width: 260,
                    padding: "18px 18px 16px",
                    borderRadius: 18,
                    backgroundColor: "rgba(15, 23, 42, 0.86)",
                    border: `1px solid ${color}44`,
                    display: "flex",
                    flexDirection: "column",
                    gap: 6,
                    boxShadow: "0 10px 30px rgba(2, 6, 23, 0.32)",
                  }}
                >
                  <div style={{ color, fontSize: 18, fontWeight: 700 }}>
                    {asString(annotation.header) ?? asString(annotation.stat) ?? "Callout"}
                  </div>
                  <div style={{ color: "#94A3B8", fontSize: 12 }}>
                    {asString(annotation.source) ?? ""}
                  </div>
                  <div style={{ color: "#64748B", fontSize: 11, lineHeight: 1.35 }}>
                    {asString(annotation.finePrint) ?? asString(annotation.detail) ?? ""}
                  </div>
                </div>
              );
            })}
          </div>
        ) : annotations.length > 0 ? (
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
                  {asString(annotation.finePrint) ? (
                    <div
                      style={{
                        color: "#64748B",
                        fontFamily: "'Inter', sans-serif",
                        fontSize: 15,
                        lineHeight: 1.3,
                      }}
                    >
                      {asString(annotation.finePrint)}
                    </div>
                  ) : null}
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
  const diagramId = asString(data.diagramId) ?? "";
  const comparisons = Array.isArray(data.comparisons)
    ? data.comparisons
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];
  const morphPairs = Array.isArray(data.morphPairs)
    ? data.morphPairs
        .map((entry) => asRecord(entry))
        .filter((entry): entry is Record<string, unknown> => Boolean(entry))
    : [];

  if (diagramId === "synopsys_pdd_equivalence") {
    const pairCards = morphPairs.length > 0 ? morphPairs : [
      { from: "verilog_code", to: "prompt_document" },
      { from: "synopsys_checkmark", to: "test_suite" },
      { from: "gate_netlist", to: "software_code" },
    ];

    return (
      <AbsoluteFill>
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            top: 164,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            gap: 20,
          }}
        >
          {comparisons.slice(0, 2).map((comparison, index) => {
            const color = asString(comparison.domainColor) ?? (index === 0 ? "#4A90D9" : "#4ADE80");
            const domain = asString(comparison.domain) ?? (index === 0 ? "Synopsys" : "PDD");
            const input = asString(comparison.input) ?? "specification";
            const output = asString(comparison.output) ?? "verified artifact";
            return (
              <div
                key={`comparison-line-${index}`}
                style={{
                  color: "#E2E8F0",
                  fontSize: 28,
                  fontWeight: 700,
                  letterSpacing: 0.1,
                }}
              >
                <span style={{ color }}>{domain}</span>
                {`: ${input} in `}
                <span style={{ color: "#64748B", opacity: 0.72 }}>→</span>
                {` ${output} out.`}
              </div>
            );
          })}
          <div
            style={{
              display: "flex",
              alignItems: "center",
              gap: 18,
              marginTop: 8,
            }}
          >
            <div
              style={{
                width: 1,
                height: 64,
                backgroundColor: "rgba(51, 65, 85, 0.7)",
              }}
            />
            <div
              style={{
                color: "#FBBF24",
                fontSize: 16,
                fontStyle: "italic",
                fontWeight: 600,
              }}
            >
              {asString(data.sharedLabel) ?? "Same architecture"}
            </div>
          </div>
        </div>
        <div
          style={{
            position: "absolute",
            left: 120,
            right: 120,
            bottom: 120,
            display: "grid",
            gridTemplateColumns: "repeat(3, minmax(0, 1fr))",
            gap: 24,
          }}
        >
          {pairCards.slice(0, 3).map((pair, index) => {
            const from = asString(pair.from) ?? "source";
            const to = asString(pair.to) ?? "target";
            const cardColor = index === 0 ? "#4A90D9" : index === 1 ? "#4ADE80" : "#A78BFA";
            return (
              <div
                key={`morph-pair-${index}`}
                style={{
                  borderRadius: 28,
                  backgroundColor: subtleSurface,
                  border: `1px solid ${cardColor}44`,
                  padding: "24px 24px 22px",
                  display: "flex",
                  flexDirection: "column",
                  gap: 16,
                  minHeight: 250,
                }}
              >
                <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center" }}>
                  <div style={{ color: "#94A3B8", fontSize: 14, fontWeight: 700, letterSpacing: 1.2 }}>
                    MORPH PAIR
                  </div>
                  <div style={{ color: cardColor, fontSize: 18, fontWeight: 700 }}>
                    {index === 0 ? "← →" : index === 1 ? "✓ → ✓✓✓" : "⊙ → ///"}
                  </div>
                </div>
                <div style={{ display: "grid", gridTemplateColumns: "1fr auto 1fr", gap: 14, alignItems: "center" }}>
                  <div
                    style={{
                      borderRadius: 18,
                      backgroundColor: "rgba(15, 23, 42, 0.92)",
                      border: "1px solid rgba(148, 163, 184, 0.22)",
                      padding: "14px 16px",
                      minHeight: 92,
                    }}
                  >
                    <div style={{ color: "#94A3B8", fontSize: 12, fontWeight: 700, letterSpacing: 0.8 }}>
                      {titleCase(from)}
                    </div>
                    <div
                      style={{
                        color: from === "verilog_code" ? "#C792EA" : from === "gate_netlist" ? "#4ADE80" : "#60A5FA",
                        fontFamily: "'JetBrains Mono', monospace",
                        fontSize: 14,
                        lineHeight: 1.35,
                        marginTop: 10,
                        whiteSpace: "pre-wrap",
                      }}
                    >
                      {from === "verilog_code"
                        ? "module chip(...)\n  assign y = a & b;\nendmodule"
                        : from === "gate_netlist"
                          ? "o─●─o\n  ╲╱\n  ●"
                          : "✓ verified"}
                    </div>
                  </div>
                  <div style={{ color: "#64748B", fontSize: 24, fontWeight: 700 }}>→</div>
                  <div
                    style={{
                      borderRadius: 18,
                      backgroundColor: "rgba(15, 23, 42, 0.92)",
                      border: `1px solid ${cardColor}44`,
                      padding: "14px 16px",
                      minHeight: 92,
                    }}
                  >
                    <div style={{ color: cardColor, fontSize: 12, fontWeight: 700, letterSpacing: 0.8 }}>
                      {titleCase(to)}
                    </div>
                    <div
                      style={{
                        color: "#E2E8F0",
                        fontFamily: to === "software_code" ? "'JetBrains Mono', monospace" : "'Inter', sans-serif",
                        fontSize: 14,
                        lineHeight: 1.35,
                        marginTop: 10,
                        whiteSpace: "pre-wrap",
                      }}
                    >
                      {to === "prompt_document"
                        ? "PROMPT\nintent + constraints"
                        : to === "software_code"
                          ? "def solve(x):\n    return mold(x)"
                          : "Tests\n✓ unit\n✓ property\n✓ integration"}
                    </div>
                  </div>
                </div>
              </div>
            );
          })}
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
  const chartId = asString(data.chartId) ?? "";
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
  if (chartId === "dissolve_regenerate_loop") {
    const cycleTints = asStringArray(data.cycleTints);
    const tintColors =
      cycleTints.length > 0 ? cycleTints : ["#60A5FA", "#4ADE80", "#D9944A"];
    const terminal = asRecord(data.terminal);
    const command = asString(terminal?.command) ?? "pdd generate";
    const successIndicator = asString(terminal?.successIndicator) ?? "✓";
    const codeVariants = [
      [
        "def build_user_parser(prompt, tests):",
        "    grounding = fetch_examples(prompt)",
        "    candidate = synthesize(prompt, grounding)",
        "    return verify(candidate, tests)",
      ],
      [
        "def generate_candidate(spec, tests):",
        "    mold = build_mold(spec, tests)",
        "    draft = regenerate(mold)",
        "    return run_suite(draft, tests)",
      ],
      [
        "def solve(intent, suite):",
        "    grounded = hydrate(intent, suite)",
        "    fresh_code = emit(grounded)",
        "    return assert_valid(fresh_code, suite)",
      ],
    ];
    body = (
      <div
        style={{
          width: width * 0.78,
          minHeight: height * 0.66,
          position: "relative",
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <svg
          width="100%"
          height="100%"
          viewBox={`0 0 ${width * 0.78} ${height * 0.66}`}
          preserveAspectRatio="none"
          style={{ position: "absolute", inset: 0 }}
        >
          <path d={`M ${width * 0.39} 36 L ${width * 0.12} ${height * 0.54} L ${width * 0.66} ${height * 0.54} Z`} fill="none" stroke="rgba(51, 65, 85, 0.8)" strokeWidth={2} />
        </svg>
        {[
          { label: "PROMPT", color: "#60A5FA", left: "50%", top: 28, transform: "translateX(-50%)" },
          { label: "TESTS", color: "#4ADE80", left: 68, bottom: 94 },
          { label: "GROUNDING", color: "#D9944A", right: 68, bottom: 94 },
        ].map((node) => (
          <div
            key={node.label}
            style={{
              position: "absolute",
              padding: "14px 18px",
              borderRadius: 999,
              backgroundColor: "rgba(2, 6, 23, 0.88)",
              border: `1px solid ${node.color}55`,
              color: node.color,
              fontSize: 18,
              fontWeight: 700,
              boxShadow: `0 0 28px ${node.color}22`,
              ...node,
            }}
          >
            {node.label}
          </div>
        ))}
        <div
          style={{
            width: 430,
            height: 230,
            borderRadius: 26,
            backgroundColor: "rgba(15, 23, 42, 0.88)",
            border: "1px solid rgba(51, 65, 85, 0.3)",
            padding: "24px 26px",
            display: "flex",
            flexDirection: "column",
            gap: 12,
            boxShadow: "0 0 0 1px rgba(51, 65, 85, 0.08) inset",
          }}
        >
          {codeVariants.map((variant, index) => (
            <div key={`variant-${index}`} style={{ display: "flex", flexDirection: "column", gap: 5 }}>
              {variant.map((line, lineIndex) => (
                <div
                  key={`${line}-${lineIndex}`}
                  style={{
                    color: "#E2E8F0",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 13,
                    lineHeight: 1.3,
                    opacity: index === codeVariants.length - 1 ? 0.86 : 0.42,
                  }}
                >
                  {line}
                </div>
              ))}
              {index < codeVariants.length - 1 ? (
                <div
                  style={{
                    height: 1,
                    backgroundColor: `${tintColors[index] ?? "#60A5FA"}55`,
                    margin: "4px 0",
                  }}
                />
              ) : null}
            </div>
          ))}
        </div>
        <div
          style={{
            position: "absolute",
            left: 120,
            right: 120,
            bottom: 18,
            display: "flex",
            justifyContent: "center",
            gap: 14,
            color: "#64748B",
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 13,
          }}
        >
          {tintColors.slice(0, 3).map((color, index) => (
            <div key={`ticker-${index}`} style={{ color: index === 2 ? "#4ADE80" : "#64748B" }}>
              {`${command} → ${successIndicator}`}
            </div>
          ))}
        </div>
      </div>
    );
  } else if (diagramId === "test_walls_illuminate") {
    body = (
      <div
        style={{
          width: width * 0.82,
          minHeight: height * 0.62,
          position: "relative",
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <div
          style={{
            position: "absolute",
            inset: "14px 36px 40px",
            backgroundImage:
              "linear-gradient(rgba(30,41,59,0.18) 1px, transparent 1px), linear-gradient(90deg, rgba(30,41,59,0.18) 1px, transparent 1px)",
            backgroundSize: "40px 40px",
            opacity: 0.42,
          }}
        />
        <svg
          width="100%"
          height="100%"
          viewBox="0 0 1200 620"
          preserveAspectRatio="none"
          style={{ position: "absolute", inset: 0 }}
        >
          <path d="M 530 70 L 600 140 L 670 70 Z" fill="rgba(148, 163, 184, 0.72)" />
          <rect x={360} y={150} width={480} height={320} rx={28} fill="none" stroke="rgba(217, 148, 74, 0.78)" strokeWidth={4} />
          <path d="M 430 208 L 510 208 L 510 284 L 600 284 L 600 360 L 690 360 L 690 284 L 770 284 L 770 208" fill="none" stroke="rgba(217, 148, 74, 0.65)" strokeWidth={6} strokeLinejoin="round" />
          <path d="M 590 150 C 544 212, 498 292, 520 360 C 544 432, 650 448, 720 404 C 778 368, 784 286, 736 232 C 702 194, 642 176, 614 154 Z" fill="rgba(96, 165, 250, 0.28)" stroke="rgba(167, 139, 250, 0.36)" strokeWidth={2} />
          <circle cx={684} cy={318} r={56} fill="rgba(217, 148, 74, 0.14)" />
          <circle cx={684} cy={318} r={28} fill="rgba(217, 148, 74, 0.22)" />
        </svg>
        {[
          { label: "null → None", left: 170, top: 182 },
          { label: "empty string → ''", left: 142, top: 266 },
          { label: "handles unicode", left: 154, top: 352 },
          { label: "latency < 100ms", right: 148, top: 182 },
          { label: "no exceptions thrown", right: 114, top: 266 },
          { label: "idempotent", right: 196, top: 352 },
        ].map((wall, index) => (
          <div
            key={`wall-label-${index}`}
            style={{
              position: "absolute",
              padding: "10px 12px",
              borderRadius: 14,
              backgroundColor: "rgba(2, 6, 23, 0.84)",
              border: "1px solid rgba(217, 148, 74, 0.4)",
              color: "#D9944A",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 13,
              boxShadow: "0 0 18px rgba(217, 148, 74, 0.12)",
              ...wall,
            }}
          >
            {wall.label}
          </div>
        ))}
        <div
          style={{
            position: "absolute",
            bottom: 20,
            left: 0,
            right: 0,
            textAlign: "center",
            color: "#94A3B8",
            fontSize: 16,
            fontWeight: 600,
          }}
        >
          Each test is a constraint
        </div>
      </div>
    );
  } else if (diagramId === "three_components_table" && table) {
    const rows = Array.isArray(table.rows)
      ? table.rows
          .map((entry) => asRecord(entry))
          .filter((entry): entry is Record<string, unknown> => Boolean(entry))
      : [];
    const hierarchyEntries =
      asStringArray(data.hierarchy).length > 0
        ? asStringArray(data.hierarchy)
        : ["Tests", "Prompt", "Grounding"];
    body = (
      <div
        style={{
          width: width * 0.82,
          minHeight: height * 0.66,
          position: "relative",
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "flex-start",
        }}
      >
        <div
          style={{
            width: 700,
            borderRadius: 24,
            overflow: "hidden",
            backgroundColor: "rgba(15, 23, 42, 0.88)",
            border: subtleBorder,
            boxShadow: "0 16px 40px rgba(2, 6, 23, 0.22)",
          }}
        >
          <div
            style={{
              display: "grid",
              gridTemplateColumns: "1.1fr 1fr 0.8fr",
              backgroundColor: "#1E293B",
              color: "#94A3B8",
              fontSize: 13,
              fontWeight: 600,
            }}
          >
            {(Array.isArray(table.columns) ? table.columns : ["Component", "Encodes", "Owner"]).map((column, index) => (
              <div key={`header-${index}`} style={{ padding: "16px 20px" }}>
                {asString(column) ?? `Column ${index + 1}`}
              </div>
            ))}
          </div>
          {rows.slice(0, 3).map((row, index) => {
            const color = asString(row.color) ?? (index === 0 ? "#2DD4BF" : index === 1 ? "#A78BFA" : "#D9944A");
            return (
              <div
                key={`row-${index}`}
                style={{
                  display: "grid",
                  gridTemplateColumns: "1.1fr 1fr 0.8fr",
                  borderTop: "1px solid rgba(51, 65, 85, 0.32)",
                  minHeight: 60,
                }}
              >
                <div style={{ padding: "18px 20px", borderLeft: `3px solid ${color}`, color, fontSize: 16, fontWeight: 700 }}>
                  {asString(row.component) ?? `Component ${index + 1}`}
                </div>
                <div style={{ padding: "18px 20px", color: "#E2E8F0", fontSize: 14, opacity: 0.72 }}>
                  {asString(row.encodes) ?? ""}
                </div>
                <div style={{ padding: "18px 20px", color: "#94A3B8", fontSize: 14, opacity: 0.66 }}>
                  {asString(row.owner) ?? ""}
                </div>
              </div>
            );
          })}
        </div>
        <div
          style={{
            marginTop: 34,
            color: "#D9944A",
            fontSize: 22,
            fontWeight: 700,
            textAlign: "center",
            textShadow: "0 0 18px rgba(217, 148, 74, 0.24)",
          }}
        >
          {asString(data.priorityRule) ?? "When these conflict, tests win. Always."}
        </div>
        <div
          style={{
            marginTop: 18,
            display: "flex",
            alignItems: "center",
            gap: 12,
            color: "#64748B",
            fontSize: 11,
            letterSpacing: 0.4,
          }}
        >
          {hierarchyEntries.map((entry, index) => (
            <React.Fragment key={`hierarchy-${entry}`}>
              <div style={{ color: index === 0 ? "#D9944A" : index === 1 ? "#2DD4BF" : "#A78BFA", fontWeight: 700 }}>
                {entry}
              </div>
              {index < hierarchyEntries.length - 1 ? <div>overrides ↓</div> : null}
            </React.Fragment>
          ))}
        </div>
        <div
          style={{
            position: "absolute",
            left: 88,
            bottom: 26,
            display: "flex",
            alignItems: "center",
            gap: 14,
          }}
        >
          <div
            style={{
              width: 58,
              height: 58,
              borderRadius: 18,
              background: "linear-gradient(135deg, rgba(45, 212, 191, 0.26), rgba(167, 139, 250, 0.24) 52%, rgba(217, 148, 74, 0.28))",
              border: "1px solid rgba(226, 232, 240, 0.12)",
              boxShadow: "0 0 24px rgba(217, 148, 74, 0.16)",
            }}
          />
          <div style={{ color: "#E2E8F0", fontSize: 16, opacity: 0.6 }}>
            The mold is what matters.
          </div>
        </div>
        <div
          style={{
            position: "absolute",
            right: 88,
            bottom: 22,
            padding: "14px 16px",
            borderRadius: 18,
            backgroundColor: "rgba(2, 6, 23, 0.68)",
            color: "#64748B",
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 12,
            opacity: 0.34,
          }}
        >
          <div>def candidate(intent, tests):</div>
          <div>    return regenerate(intent, tests)</div>
        </div>
      </div>
    );
  } else if (diagramId === "code_generation_comparison" && scenarios.length > 0) {
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
    const ratio = asString(data.compressionRatio) ?? "5-10×";
    body = (
      <div
        style={{
          width: width * 0.76,
          minHeight: height * 0.62,
          borderRadius: 32,
          backgroundColor: subtleSurface,
          border: subtleBorder,
          padding: "44px 52px 42px",
          position: "relative",
          display: "flex",
          flexDirection: "column",
          justifyContent: "center",
          margin: "0 auto",
        }}
      >
        <div
          style={{
            alignSelf: "center",
            color: "#94A3B8",
            fontSize: 20,
            fontWeight: 700,
            letterSpacing: 1.6,
            textTransform: "uppercase",
            marginBottom: 18,
          }}
        >
          Context Window
        </div>
        <div
          style={{
            width: Math.min(width * 0.54, 760),
            maxWidth: "100%",
            height: Math.min(height * 0.46, 500),
            borderRadius: 28,
            border: "2px solid rgba(74, 144, 217, 0.65)",
            boxShadow: "0 0 0 1px rgba(74, 144, 217, 0.18) inset",
            padding: "22px 24px 22px",
            display: "grid",
            gridTemplateColumns: "repeat(5, minmax(0, 1fr))",
            gap: 12,
            position: "relative",
            margin: "0 auto",
          }}
        >
          {Array.from({ length: moduleCount }).map((_, index) => {
            return (
              <div
                key={`prompt-${index}`}
                style={{
                  height: 42,
                  borderRadius: 12,
                  backgroundColor: index % 3 === 0 ? "rgba(74, 144, 217, 0.24)" : "rgba(96, 165, 250, 0.18)",
                  border: "1px solid rgba(74, 144, 217, 0.42)",
                  boxShadow: index % 5 === 0 ? "0 0 0 1px rgba(125, 211, 252, 0.18) inset" : undefined,
                }}
              />
            );
          })}
          <div
            style={{
              position: "absolute",
              right: -10,
              top: -18,
              padding: "10px 16px",
              borderRadius: 999,
              backgroundColor: "rgba(74, 144, 217, 0.16)",
              color: "#93C5FD",
              fontSize: 28,
              fontWeight: 700,
            }}
          >
            {ratio}
          </div>
          <div
            style={{
              position: "absolute",
              left: 24,
              bottom: 18,
              display: "flex",
              alignItems: "center",
              gap: 14,
            }}
          >
            <div
              style={{
                color: "#4ADE80",
                fontSize: 28,
                fontWeight: 800,
              }}
            >
              ✓
            </div>
            <div
              style={{
                color: "#4ADE80",
                fontSize: 20,
                fontWeight: 700,
              }}
            >
              Headroom
            </div>
          </div>
        </div>
        <div
          style={{
            alignSelf: "center",
            marginTop: 26,
            display: "flex",
            flexDirection: "column",
            gap: 10,
            alignItems: "center",
          }}
        >
          <div
            style={{
              color: "#E2E8F0",
              fontSize: 26,
              fontWeight: 700,
            }}
          >
            {asString(data.resultLabel) ?? "Same system. More fits."}
          </div>
        </div>
      </div>
    );
  } else if (diagramId === "bug_fork") {
    const root = asRecord(data.root);
    const convergence = asRecord(data.convergence);
    body = (
      <div
        style={{
          width: width * 0.82,
          minHeight: height * 0.56,
          position: "relative",
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <div
          style={{
            position: "absolute",
            top: 24,
            left: "50%",
            transform: "translateX(-50%)",
            padding: "14px 22px",
            borderRadius: 999,
            backgroundColor: "rgba(239, 68, 68, 0.16)",
            border: "1px solid rgba(239, 68, 68, 0.4)",
            color: asString(root?.color) ?? "#EF4444",
            fontSize: 24,
            fontWeight: 700,
          }}
        >
          {asString(root?.label) ?? "Bug found"}
        </div>
        <div
          style={{
            position: "absolute",
            top: 88,
            left: "50%",
            width: 2,
            height: 70,
            transform: "translateX(-50%)",
            backgroundColor: "rgba(148, 163, 184, 0.38)",
          }}
        />
        <div
          style={{
            width: "100%",
            display: "grid",
            gridTemplateColumns: "1fr 1fr",
            gap: 28,
            alignItems: "start",
            marginTop: 120,
          }}
        >
          {branches.slice(0, 2).map((branch, index) => {
            const color = asString(branch.color) ?? (index === 0 ? "#D9944A" : "#2DD4BF");
            return (
              <div
                key={`branch-${index}`}
                style={{
                  borderRadius: 28,
                  backgroundColor: subtleSurface,
                  border: `1px solid ${color}55`,
                  padding: "24px 26px",
                  minHeight: 260,
                  display: "flex",
                  flexDirection: "column",
                  gap: 12,
                }}
              >
                <div style={{ color, fontSize: 20, fontWeight: 700 }}>
                  {asString(branch.label) ?? `Branch ${index + 1}`}
                </div>
                <div
                  style={{
                    color: "#94A3B8",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 16,
                  }}
                >
                  {asString(branch.file) ?? ""}
                </div>
                <div
                  style={{
                    marginTop: 6,
                    color: "#E2E8F0",
                    fontSize: 22,
                    fontWeight: 600,
                  }}
                >
                  {asString(branch.action) ?? "fix_specification"}
                </div>
              </div>
            );
          })}
        </div>
        <div
          style={{
            position: "absolute",
            left: width * 0.25,
            top: height * 0.52,
            width: width * 0.25,
            height: 2,
            backgroundColor: "rgba(148, 163, 184, 0.32)",
            transform: "rotate(18deg)",
            transformOrigin: "left center",
          }}
        />
        <div
          style={{
            position: "absolute",
            right: width * 0.25,
            top: height * 0.52,
            width: width * 0.25,
            height: 2,
            backgroundColor: "rgba(148, 163, 184, 0.32)",
            transform: "rotate(-18deg)",
            transformOrigin: "right center",
          }}
        />
        <div
          style={{
            position: "absolute",
            bottom: 26,
            left: "50%",
            transform: "translateX(-50%)",
            padding: "14px 22px",
            borderRadius: 999,
            backgroundColor: "rgba(74, 222, 128, 0.14)",
            border: "1px solid rgba(74, 222, 128, 0.42)",
            color: asString(convergence?.color) ?? "#4ADE80",
            fontSize: 24,
            fontWeight: 700,
          }}
        >
          {asString(convergence?.label) ?? "Regenerate"}
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
    const terminalLines = asStringArray(data.terminalCommands);
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
          <div style={{ marginTop: 16, display: "grid", gridTemplateColumns: "48px 1fr auto", rowGap: 8, columnGap: 10 }}>
            {Array.from({ length: 10 }).map((_, index) => (
              <React.Fragment key={`bug-line-${index}`}>
                <div style={{ color: "#475569", fontFamily: "'JetBrains Mono', monospace", fontSize: 14 }}>{index + 1}</div>
                <div style={{ color: index === 4 ? "#FCA5A5" : "#CBD5E1", fontFamily: "'JetBrains Mono', monospace", fontSize: 16 }}>
                  {index === 4 ? "if user_id is None: return None" : "normalize_user(user_id)"}
                </div>
                <div
                  style={{
                    color: index >= 6 ? "#4ADE80" : "transparent",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 16,
                    fontWeight: 700,
                  }}
                >
                  ✓
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
            <div
              style={{
                position: "absolute",
                right: 82,
                top: "50%",
                transform: "translateY(-50%)",
                padding: "8px 12px",
                borderRadius: 999,
                border: "1px solid rgba(217, 148, 74, 0.55)",
                backgroundColor: "rgba(217, 148, 74, 0.16)",
                color: "#FBBF24",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 13,
                fontWeight: 700,
              }}
            >
              handles_null_userid
            </div>
          </div>
          <div style={{ borderRadius: 24, backgroundColor: "rgba(2, 6, 23, 0.82)", border: subtleBorder, padding: "20px 22px" }}>
            {(terminalLines.length >= 2
              ? [
                  `$ ${terminalLines[0]}`,
                  "Creating failing test... ✓",
                  `$ ${terminalLines[1]}`,
                  "All tests passing ✓",
                ]
              : terminalLines
            ).map((line, index) => {
              const isCommand = line.startsWith("$ ");
              const isSuccess = line.includes("✓");
              return (
                <div
                  key={`${line}-${index}`}
                  style={{
                    color: isCommand ? "#E2E8F0" : isSuccess ? "#4ADE80" : "#94A3B8",
                    fontFamily: "'JetBrains Mono', monospace",
                    fontSize: 16,
                    marginTop: index === 0 ? 0 : 8,
                  }}
                >
                  {line}
                </div>
              );
            })}
          </div>
          <div
            style={{
              borderRadius: 24,
              backgroundColor: "rgba(217, 148, 74, 0.12)",
              border: "1px solid rgba(217, 148, 74, 0.32)",
              padding: "18px 20px",
              color: "#FBBF24",
              fontSize: 20,
              fontWeight: 700,
              lineHeight: 1.3,
            }}
          >
            That wall is permanent. That bug can never occur again.
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
    visualType === "line_chart" ||
    visualType === "counter_animation" ||
    visualType === "schematic_zoom" ||
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
    visualType === "code_editor_animation" ||
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
