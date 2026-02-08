import React from "react";
import {
  AbsoluteFill,
  Audio,
  Easing,
  interpolate,
  staticFile,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";
import {
  COLORS,
  CHART_DATA,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  DataPoint,
} from "../05-CodeCostChart/constants";
import { BEATS, CodeCostChartMiniPropsType } from "./constants";

// ── Inline AnimatedLine with tip-tracking labels ──
const AnimatedLine: React.FC<{
  data: DataPoint[];
  color: string;
  startFrame: number;
  endFrame: number;
  strokeWidth?: number;
  label?: string;
  dashed?: boolean;
  showDot?: boolean;
  lineOpacity?: number;
}> = ({
  data,
  color,
  startFrame,
  endFrame,
  strokeWidth = 4,
  label,
  dashed = false,
  showDot = true,
  lineOpacity = 1,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  const getX = (year: number) =>
    CHART_MARGINS.left +
    ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth;
  const getY = (hours: number) =>
    CHART_MARGINS.top + chartHeight - (hours / HOURS_RANGE.max) * chartHeight;

  const progress = interpolate(frame, [startFrame, endFrame], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  const pts = data.map((d) => ({ x: getX(d.year), y: getY(d.hours) }));
  if (pts.length < 2 || progress <= 0) return null;

  // Build path
  let pathD = "";
  let tipX = pts[0].x;
  let tipY = pts[0].y;

  if (pts.length === 2) {
    const ex = pts[0].x + (pts[1].x - pts[0].x) * progress;
    const ey = pts[0].y + (pts[1].y - pts[0].y) * progress;
    pathD = `M ${pts[0].x} ${pts[0].y} L ${ex} ${ey}`;
    tipX = ex;
    tipY = ey;
  } else {
    const segs: { sx: number; sy: number; ex: number; ey: number; len: number }[] = [];
    let total = 0;
    for (let i = 1; i < pts.length; i++) {
      const dx = pts[i].x - pts[i - 1].x;
      const dy = pts[i].y - pts[i - 1].y;
      const len = Math.sqrt(dx * dx + dy * dy);
      segs.push({ sx: pts[i - 1].x, sy: pts[i - 1].y, ex: pts[i].x, ey: pts[i].y, len });
      total += len;
    }
    let rem = total * progress;
    pathD = `M ${pts[0].x} ${pts[0].y}`;
    for (const s of segs) {
      if (rem <= 0) break;
      if (rem >= s.len) {
        pathD += ` L ${s.ex} ${s.ey}`;
        tipX = s.ex;
        tipY = s.ey;
        rem -= s.len;
      } else {
        const t = rem / s.len;
        tipX = s.sx + t * (s.ex - s.sx);
        tipY = s.sy + t * (s.ey - s.sy);
        pathD += ` L ${tipX} ${tipY}`;
        rem = 0;
      }
    }
  }

  const endPt = pts[pts.length - 1];

  // Label tracks the tip while drawing, settles at endpoint when done
  const labelX = progress >= 1 ? endPt.x : tipX;
  const labelY = progress >= 1 ? endPt.y : tipY;
  const labelOp = interpolate(frame, [startFrame, startFrame + 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <>
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none", opacity: lineOpacity }}
      >
        {progress > 0 && pathD && (
          <path
            d={pathD}
            fill="none"
            stroke={color}
            strokeWidth={strokeWidth}
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeDasharray={dashed ? "12,8" : undefined}
          />
        )}
        {showDot && progress > 0 && progress < 1 && (
          <circle cx={tipX} cy={tipY} r={8} fill={color} />
        )}
      </svg>
      {label && progress > 0 && (
        <div
          style={{
            position: "absolute",
            left: labelX + 15,
            top: labelY,
            transform: "translateY(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 22,
            fontWeight: 600,
            color,
            opacity: labelOp * lineOpacity,
            textShadow: "0 2px 4px rgba(0,0,0,0.5)",
            maxWidth: 200,
            lineHeight: 1.3,
            whiteSpace: "nowrap",
            pointerEvents: "none",
          }}
        >
          {label}
        </div>
      )}
    </>
  );
};

// ── Inline AnimatedArea ──
const AnimatedArea: React.FC<{
  topData: DataPoint[];
  bottomData: DataPoint[];
  fillColor: string;
  startFrame: number;
  endFrame: number;
  extraOpacity?: number;
}> = ({ topData, bottomData, fillColor, startFrame, endFrame, extraOpacity = 1 }) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  const getX = (year: number) =>
    CHART_MARGINS.left +
    ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth;
  const getY = (hours: number) =>
    CHART_MARGINS.top + chartHeight - (hours / HOURS_RANGE.max) * chartHeight;

  const interp = (data: DataPoint[], year: number): number => {
    if (!data.length) return 0;
    if (year <= data[0].year) return data[0].hours;
    if (year >= data[data.length - 1].year) return data[data.length - 1].hours;
    for (let i = 1; i < data.length; i++) {
      if (year <= data[i].year) {
        const t = (year - data[i - 1].year) / (data[i].year - data[i - 1].year);
        return data[i - 1].hours + t * (data[i].hours - data[i - 1].hours);
      }
    }
    return data[data.length - 1].hours;
  };

  const progress = interpolate(frame, [startFrame, endFrame], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });
  if (progress <= 0) return null;

  const minY = Math.min(topData[0].year, bottomData[0].year);
  const maxY = Math.max(topData[topData.length - 1].year, bottomData[bottomData.length - 1].year);
  const curMax = minY + (maxY - minY) * progress;

  const years: number[] = [];
  for (let y = minY; y <= curMax; y += 2) years.push(y);
  if (years[years.length - 1] !== curMax) years.push(curMax);

  let d = "";
  years.forEach((y, i) => {
    const x = getX(y);
    const yPos = getY(interp(bottomData, y));
    d += i === 0 ? `M ${x} ${yPos}` : ` L ${x} ${yPos}`;
  });
  for (let i = years.length - 1; i >= 0; i--) {
    d += ` L ${getX(years[i])} ${getY(interp(topData, years[i]))}`;
  }
  d += " Z";

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none", opacity: extraOpacity }}
    >
      <path d={d} fill={fillColor} stroke="none" />
    </svg>
  );
};

// ══════════════════════════════════════════════════════════════════════
// Main component
// ══════════════════════════════════════════════════════════════════════
export const CodeCostChartMini: React.FC<CodeCostChartMiniPropsType> = ({
  showTitle = true,
  showAudio = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  const getX = (year: number) =>
    CHART_MARGINS.left +
    ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth;
  const getY = (hours: number) =>
    CHART_MARGINS.top + chartHeight - (hours / HOURS_RANGE.max) * chartHeight;

  // Data splits
  const genPhase1 = CHART_DATA.costToGenerate.filter((d) => d.year <= 2020);
  const genPhase2 = CHART_DATA.costToGenerate.filter((d) => d.year >= 2020);

  // Combined bottom boundary for debt area (baseline 2015-2020 + large CB 2020-2025)
  const debtBottomFull: DataPoint[] = [
    ...CHART_DATA.immediateCostBaseline,
    ...CHART_DATA.immediateCostLargeCodebase.filter((d) => d.year > 2020),
  ];

  // ── Opacity animations ──

  const axesOpacity = interpolate(frame, [BEATS.AXES_VISIBLE_START, BEATS.AXES_VISIBLE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const titleOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Phase 1 standalone labels: fade in with their lines, fade out when Phase 2 starts
  const phase1BlueLabelOp = interpolate(
    frame,
    [BEATS.BLUE_LINE_START, BEATS.BLUE_LINE_START + 20, BEATS.PHASE2_START - 15, BEATS.PHASE2_START],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );
  const phase1AmberLabelOp = interpolate(
    frame,
    [BEATS.AMBER_LINE_START, BEATS.AMBER_LINE_START + 20, BEATS.PHASE2_START - 15, BEATS.PHASE2_START],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // "But watch the dashed line" → dim solid lines so dashed stands out
  const revealDim = interpolate(
    frame,
    [BEATS.REVEAL_DASHED_START, BEATS.REVEAL_DASHED_START + 30],
    [1, 0.25],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // After debt highlight starts, restore lines from dim
  const restoreFromDim = interpolate(
    frame,
    [BEATS.DEBT_HIGHLIGHT_START, BEATS.DEBT_HIGHLIGHT_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Combined: lines are dimmed during reveal, then restore
  const nonDashedOpacity = frame >= BEATS.DEBT_HIGHLIGHT_START
    ? 0.25 + restoreFromDim * 0.75
    : frame >= BEATS.REVEAL_DASHED_START
      ? revealDim
      : 1;

  // Debt area pulse during "residue... technical debt"
  const debtPulse = frame >= BEATS.DEBT_HIGHLIGHT_START && frame <= BEATS.DEBT_HIGHLIGHT_END
    ? 0.6 + 0.4 * Math.sin(((frame - BEATS.DEBT_HIGHLIGHT_START) / 30) * Math.PI * 2 * 0.5)
    : 0;
  const debtExtraOpacity = interpolate(
    frame,
    [BEATS.DEBT_HIGHLIGHT_START, BEATS.DEBT_HIGHLIGHT_START + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // "each patch is getting faster" → highlight small-CB line
  const patchHighlight = interpolate(
    frame,
    [BEATS.HIGHLIGHT_PATCH_START, BEATS.HIGHLIGHT_PATCH_START + 20, BEATS.HIGHLIGHT_PATCH_END - 20, BEATS.HIGHLIGHT_PATCH_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Emphasis annotations
  const emphasisOpacity = interpolate(
    frame,
    [BEATS.EMPHASIS_START, BEATS.EMPHASIS_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Crossing point
  const crossingOpacity = interpolate(
    frame,
    [BEATS.CROSSING_START, BEATS.CROSSING_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Legend - appears after Phase 2 completes
  const legendOpacity = interpolate(
    frame,
    [BEATS.PHASE2_END, BEATS.PHASE2_END + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Grid constants
  const yearTicks = [2015, 2020, 2022, 2025];
  const hourTicks = [0, 5, 10, 15, 20, 25, 30, 35];

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Narration audio (suppressed when used in section compositions) */}
      {showAudio && <Audio src={staticFile("codecostchart_narration.wav")} />}

      {/* Title */}
      {showTitle && (
        <div
          style={{
            position: "absolute",
            top: 30,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 42,
            fontWeight: 700,
            color: COLORS.TITLE,
            opacity: titleOpacity,
            textShadow: "0 2px 10px rgba(0,0,0,0.5)",
          }}
        >
          The Economics of Code
        </div>
      )}

      {/* ── Axes & grid ── */}
      <div style={{ position: "absolute", inset: 0, opacity: axesOpacity }}>
        <svg width={width} height={height} style={{ position: "absolute", top: 0, left: 0 }}>
          {hourTicks.map((h) => (
            <line key={`hg-${h}`} x1={CHART_MARGINS.left} y1={getY(h)} x2={width - CHART_MARGINS.right} y2={getY(h)} stroke={COLORS.GRID} strokeWidth={1} strokeDasharray="5,5" opacity={0.5} />
          ))}
          {yearTicks.map((y) => (
            <line key={`vg-${y}`} x1={getX(y)} y1={CHART_MARGINS.top} x2={getX(y)} y2={height - CHART_MARGINS.bottom} stroke={COLORS.GRID} strokeWidth={1} strokeDasharray="5,5" opacity={0.5} />
          ))}
          <line x1={CHART_MARGINS.left} y1={height - CHART_MARGINS.bottom} x2={width - CHART_MARGINS.right} y2={height - CHART_MARGINS.bottom} stroke={COLORS.AXIS} strokeWidth={2} />
          <line x1={CHART_MARGINS.left} y1={CHART_MARGINS.top} x2={CHART_MARGINS.left} y2={height - CHART_MARGINS.bottom} stroke={COLORS.AXIS} strokeWidth={2} />
        </svg>
        {yearTicks.map((y) => (
          <div key={`yl-${y}`} style={{ position: "absolute", left: getX(y), top: height - CHART_MARGINS.bottom + 20, transform: "translateX(-50%)", fontFamily: "Inter, system-ui, sans-serif", fontSize: 28, fontWeight: 500, color: COLORS.AXIS_LABEL }}>{y}</div>
        ))}
        {hourTicks.map((h) => (
          <div key={`hl-${h}`} style={{ position: "absolute", left: CHART_MARGINS.left - 15, top: getY(h), transform: "translate(-100%, -50%)", fontFamily: "Inter, system-ui, sans-serif", fontSize: 28, fontWeight: 500, color: COLORS.AXIS_LABEL, textAlign: "right" }}>{h}</div>
        ))}
        <div style={{ position: "absolute", left: 0, top: 0, width: 70, height: "100%", display: "flex", alignItems: "center", justifyContent: "center" }}>
          <div style={{ transform: "rotate(-90deg)", fontFamily: "Inter, system-ui, sans-serif", fontSize: 26, fontWeight: 600, color: COLORS.AXIS_LABEL, whiteSpace: "nowrap" }}>Cost (Developer Hours)</div>
        </div>
        <div style={{ position: "absolute", left: "50%", bottom: 25, transform: "translateX(-50%)", fontFamily: "Inter, system-ui, sans-serif", fontSize: 26, fontWeight: 600, color: COLORS.AXIS_LABEL }}>Year</div>
      </div>

      {/* ══ SECTION 1: Phase 1 lines (2015-2020) ══ */}
      {/* Only blue + amber. NO dashed line yet. */}

      {/* Blue: Cost to Generate - "For fifty years... expensive... hours, days, weeks" */}
      <AnimatedLine
        data={genPhase1}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.BLUE_LINE_START}
        endFrame={BEATS.BLUE_LINE_END}
        strokeWidth={4}
        label="Cost to Generate"
        lineOpacity={nonDashedOpacity}
      />

      {/* Amber: Patch Cost - "So when something broke, you patched... rational" */}
      <AnimatedLine
        data={CHART_DATA.immediateCostBaseline}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.AMBER_LINE_START}
        endFrame={BEATS.AMBER_LINE_END}
        strokeWidth={4}
        label="Patch Cost"
        lineOpacity={nonDashedOpacity}
      />

      {/* ══ SECTION 2: Phase 2 lines (2020-2025) ══ */}
      {/* Blue plunges, amber forks. Still NO dashed line. */}

      {/* Blue: Cost to Generate - dramatic plunge */}
      <AnimatedLine
        data={genPhase2}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.PHASE2_START}
        endFrame={BEATS.PHASE2_END}
        strokeWidth={4}
        label="Cost to Generate"
        lineOpacity={nonDashedOpacity}
      />

      {/* Amber: Small codebase fork - drops fast */}
      <AnimatedLine
        data={CHART_DATA.immediateCostSmallCodebase}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.PHASE2_START}
        endFrame={BEATS.PHASE2_END}
        strokeWidth={3 + Math.round(patchHighlight * 3)}
        label="Small Codebase"
        lineOpacity={nonDashedOpacity}
      />

      {/* Amber: Large codebase fork - stays flat */}
      <AnimatedLine
        data={CHART_DATA.immediateCostLargeCodebase}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.PHASE2_START}
        endFrame={BEATS.PHASE2_END}
        strokeWidth={2}
        lineOpacity={0.7 * nonDashedOpacity}
        label="Large Codebase"
      />

      {/* ══ SECTION 3: The reveal ══ */}
      {/* "But watch the dashed line" — it draws for the FIRST time here */}

      {/* Dashed: Total Cost - draws across full 2015-2025 range */}
      <AnimatedLine
        data={CHART_DATA.totalCostLargeCodebase}
        color={COLORS.LINE_PATCH_TOTAL}
        startFrame={BEATS.REVEAL_DASHED_START}
        endFrame={BEATS.REVEAL_DASHED_END}
        strokeWidth={4}
        dashed
        showDot
        label="True Cost (with debt)"
      />

      {/* Debt area fills in alongside the dashed line */}
      <AnimatedArea
        topData={CHART_DATA.totalCostLargeCodebase}
        bottomData={debtBottomFull}
        fillColor={COLORS.AREA_TECH_DEBT}
        startFrame={BEATS.REVEAL_DASHED_START}
        endFrame={BEATS.REVEAL_DASHED_END}
      />

      {/* "barely moving" overlay text */}
      {frame >= BEATS.REVEAL_DASHED_END && frame < BEATS.DEBT_HIGHLIGHT_START && (
        <div style={{
          position: "absolute",
          bottom: 160,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: interpolate(frame, [BEATS.REVEAL_DASHED_END, BEATS.REVEAL_DASHED_END + 20], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
          fontFamily: "Georgia, serif",
          fontSize: 32,
          fontStyle: "italic",
          color: "rgba(255,255,255,0.9)",
          textShadow: "0 2px 10px rgba(0,0,0,0.8)",
        }}>
          The total cost is barely moving.
        </div>
      )}

      {/* Debt highlight pulse overlay */}
      {frame >= BEATS.DEBT_HIGHLIGHT_START && frame <= BEATS.DEBT_HIGHLIGHT_END && (
        <AnimatedArea
          topData={CHART_DATA.totalCostLargeCodebase}
          bottomData={debtBottomFull}
          fillColor="rgba(217, 148, 74, 0.5)"
          startFrame={BEATS.REVEAL_DASHED_START}
          endFrame={BEATS.REVEAL_DASHED_END}
          extraOpacity={debtExtraOpacity * (0.5 + debtPulse * 0.5)}
        />
      )}

      {/* "Technical debt" label during debt highlight */}
      {frame >= BEATS.DEBT_HIGHLIGHT_START && frame < BEATS.EMPHASIS_START && (
        <div style={{
          position: "absolute",
          bottom: 160,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: debtExtraOpacity,
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 30,
          fontWeight: 600,
          color: COLORS.LINE_PATCH,
          textShadow: "0 2px 10px rgba(0,0,0,0.8)",
        }}>
          Technical debt accumulates
        </div>
      )}

      {/* ══ SECTION 4: The data ══ */}

      {/* Emphasis annotations (synced to "AI gave you a 60% speed up...") */}
      {frame >= BEATS.EMPHASIS_START && frame < BEATS.CROSSING_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: emphasisOpacity,
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.75)",
            padding: "24px 40px",
            borderRadius: 12,
          }}
        >
          <p style={{ fontFamily: "Inter, system-ui, sans-serif", fontSize: 28, color: COLORS.LINE_PATCH, margin: 0, marginBottom: 8, fontWeight: 600 }}>
            Individual task: -55% faster (Peng et al., 2023)
          </p>
          <p style={{ fontFamily: "Inter, system-ui, sans-serif", fontSize: 28, color: "#ffffff", margin: 0, fontWeight: 500 }}>
            Overall throughput: ~0% change (Uplevel, 2024)
          </p>
          <p style={{ fontFamily: "Inter, system-ui, sans-serif", fontSize: 28, color: COLORS.LINE_PATCH, margin: 0, marginTop: 8, fontWeight: 600 }}>
            Bug rate: +41% (Uplevel, 2024)
          </p>
        </div>
      )}

      {/* Crossing point annotation */}
      {frame >= BEATS.CROSSING_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: crossingOpacity,
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.75)",
            padding: "24px 40px",
            borderRadius: 12,
          }}
        >
          <p style={{ fontFamily: "Inter, system-ui, sans-serif", fontSize: 24, color: "#ffffff", margin: 0, marginBottom: 12, fontWeight: 500 }}>
            Generate: <span style={{ color: COLORS.LINE_GENERATE, fontWeight: 700 }}>3 hrs</span>
            &nbsp;&nbsp;&nbsp;vs&nbsp;&nbsp;&nbsp;
            True Cost: <span style={{ color: COLORS.LINE_PATCH, fontWeight: 700 }}>33 hrs</span>
          </p>
          <p style={{ fontFamily: "Georgia, serif", fontSize: 32, color: "#ffffff", textShadow: "0 2px 10px rgba(0,0,0,0.8)", fontStyle: "italic", margin: 0 }}>
            &ldquo;The debt ate the gains.&rdquo;
          </p>
        </div>
      )}

      {/* Legend */}
      <div style={{ position: "absolute", top: 300, right: 40, opacity: legendOpacity, backgroundColor: "rgba(0,0,0,0.4)", padding: "16px 20px", borderRadius: 8 }}>
        {[
          { color: COLORS.LINE_GENERATE, w: 4, label: "Cost to Generate", op: 1, dash: false },
          { color: COLORS.LINE_PATCH, w: 3, label: "Patch (Small CB)", op: 1, dash: false },
          { color: COLORS.LINE_PATCH, w: 2, label: "Patch (Large CB)", op: 0.7, dash: false },
          { color: COLORS.LINE_PATCH_TOTAL, w: 3, label: "True Cost (with debt)", op: 1, dash: true },
        ].map((item) => (
          <div key={item.label} style={{ display: "flex", alignItems: "center", marginBottom: 10, fontFamily: "Inter, system-ui, sans-serif", fontSize: 18, fontWeight: 500, color: "#ffffff", opacity: item.op }}>
            {item.dash ? (
              <svg width={36} height={4} style={{ marginRight: 12 }}>
                <line x1={0} y1={2} x2={36} y2={2} stroke={item.color} strokeWidth={item.w} strokeDasharray="8,4" />
              </svg>
            ) : (
              <div style={{ width: 36, height: item.w, backgroundColor: item.color, marginRight: 12, borderRadius: 2 }} />
            )}
            {item.label}
          </div>
        ))}
      </div>
    </AbsoluteFill>
  );
};
