import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing, spring } from "remotion";
import {
  COLORS,
  GRAPH,
  PATCH_DOT_COUNT,
  PATCH_DOT_RADIUS,
  PDD_DOT_COUNT,
  PDD_DOT_RADIUS,
  DIP_POSITIONS,
  DIP_LABELS,
  DIP_MAGNITUDES,
  DIP_SPREAD,
  CompoundCurvesGraphPropsType,
} from "./constants";

// ── Curve math ───────────────────────────────────────────────────────

/** Logarithmic patching curve: fast early growth, then flattening. */
const patchingBaseY = (t: number): number => {
  const maxHeight = GRAPH.HEIGHT * 0.7; // ~560px
  return maxHeight * (Math.log(t * 5 + 1) / Math.log(6));
};

/** Patching curve with wobble dips applied. Per-dip activation flags allow
 *  discrete dip appearance matching the spec pseudo-code (frame >= 30, etc). */
const patchingWobblyY = (
  t: number,
  wobbleAmount: number,
  dipActive: readonly boolean[] = [true, true, true],
): number => {
  const base = patchingBaseY(t);
  let dipTotal = 0;
  for (let i = 0; i < DIP_POSITIONS.length; i++) {
    if (!dipActive[i]) continue;
    const pos = DIP_POSITIONS[i];
    const mag = DIP_MAGNITUDES[i];
    dipTotal += -mag * Math.exp(-Math.pow((t - pos) / DIP_SPREAD, 2));
  }
  return base + dipTotal * wobbleAmount;
};

/** Exponential PDD curve: slow start, accelerating growth. */
const pddY = (t: number): number => {
  const maxHeight = GRAPH.HEIGHT * 0.88; // ~700px
  return maxHeight * ((Math.exp(t * 2.5) - 1) / (Math.exp(2.5) - 1));
};

// ── Coordinate helpers ───────────────────────────────────────────────

/** Map normalised t (0-1) to SVG x. */
const toSvgX = (t: number) => GRAPH.LEFT + t * GRAPH.WIDTH;

/** Map curve-space y to SVG y (invert: 0 is bottom). */
const toSvgY = (curveY: number) => GRAPH.BOTTOM - curveY;

// ── Sub-components ───────────────────────────────────────────────────

/** Animated graph axes with arrowheads. */
const Axes: React.FC<{ xProgress: number; yProgress: number }> = ({
  xProgress,
  yProgress,
}) => {
  const yEnd = GRAPH.TOP + (GRAPH.BOTTOM - GRAPH.TOP) * (1 - yProgress);
  const xEnd = GRAPH.LEFT + GRAPH.WIDTH * xProgress;

  return (
    <>
      {/* Y-axis */}
      <line
        x1={GRAPH.LEFT}
        y1={GRAPH.BOTTOM}
        x2={GRAPH.LEFT}
        y2={yEnd}
        stroke={COLORS.AXIS_WHITE}
        strokeWidth={2}
      />
      {/* Y arrowhead */}
      {yProgress > 0.95 && (
        <polygon
          points={`${GRAPH.LEFT},${GRAPH.TOP - 10} ${GRAPH.LEFT - 6},${GRAPH.TOP + 4} ${GRAPH.LEFT + 6},${GRAPH.TOP + 4}`}
          fill={COLORS.AXIS_WHITE}
          opacity={interpolate(yProgress, [0.95, 1], [0, 1])}
        />
      )}
      {/* X-axis */}
      <line
        x1={GRAPH.LEFT}
        y1={GRAPH.BOTTOM}
        x2={xEnd}
        y2={GRAPH.BOTTOM}
        stroke={COLORS.AXIS_WHITE}
        strokeWidth={2}
      />
      {/* X arrowhead */}
      {xProgress > 0.95 && (
        <polygon
          points={`${GRAPH.RIGHT + 10},${GRAPH.BOTTOM} ${GRAPH.RIGHT - 4},${GRAPH.BOTTOM - 6} ${GRAPH.RIGHT - 4},${GRAPH.BOTTOM + 6}`}
          fill={COLORS.AXIS_WHITE}
          opacity={interpolate(xProgress, [0.95, 1], [0, 1])}
        />
      )}
    </>
  );
};

/** Axis labels. */
const AxisLabels: React.FC<{ opacity: number }> = ({ opacity }) => (
  <>
    {/* X-axis label */}
    <text
      x={(GRAPH.LEFT + GRAPH.RIGHT) / 2}
      y={GRAPH.X_LABEL_Y}
      fill={COLORS.LABEL_WHITE}
      fontSize={24}
      fontFamily="system-ui, sans-serif"
      textAnchor="middle"
      opacity={opacity * 0.9}
    >
      Time
    </text>
    {/* Y-axis label (rotated) */}
    <text
      x={GRAPH.Y_LABEL_X}
      y={(GRAPH.TOP + GRAPH.BOTTOM) / 2}
      fill={COLORS.LABEL_WHITE}
      fontSize={22}
      fontFamily="system-ui, sans-serif"
      textAnchor="middle"
      opacity={opacity * 0.9}
      transform={`rotate(-90, ${GRAPH.Y_LABEL_X}, ${(GRAPH.TOP + GRAPH.BOTTOM) / 2})`}
    >
      Cumulative Value of Investment
    </text>
  </>
);

/** Legend box. */
const Legend: React.FC<{ opacity: number }> = ({ opacity }) => (
  <g opacity={opacity}>
    <rect
      x={GRAPH.LEGEND_X}
      y={GRAPH.LEGEND_Y}
      width={200}
      height={80}
      rx={6}
      fill="rgba(26, 26, 46, 0.8)"
      stroke={COLORS.LEGEND_BORDER}
      strokeWidth={1}
    />
    {/* Patching swatch + label */}
    <line
      x1={GRAPH.LEGEND_X + 15}
      y1={GRAPH.LEGEND_Y + 25}
      x2={GRAPH.LEGEND_X + 45}
      y2={GRAPH.LEGEND_Y + 25}
      stroke={COLORS.PATCHING_AMBER}
      strokeWidth={3}
    />
    <text
      x={GRAPH.LEGEND_X + 55}
      y={GRAPH.LEGEND_Y + 30}
      fill={COLORS.LABEL_WHITE}
      fontSize={18}
      fontFamily="system-ui, sans-serif"
    >
      Patching
    </text>
    {/* PDD swatch + label */}
    <line
      x1={GRAPH.LEGEND_X + 15}
      y1={GRAPH.LEGEND_Y + 55}
      x2={GRAPH.LEGEND_X + 45}
      y2={GRAPH.LEGEND_Y + 55}
      stroke={COLORS.PDD_BLUE}
      strokeWidth={3}
    />
    <text
      x={GRAPH.LEGEND_X + 55}
      y={GRAPH.LEGEND_Y + 60}
      fill={COLORS.LABEL_WHITE}
      fontSize={18}
      fontFamily="system-ui, sans-serif"
    >
      PDD
    </text>
  </g>
);

/** Generate SVG path d-string for a curve. */
const buildCurvePath = (
  yFn: (t: number) => number,
  from: number,
  to: number,
  steps = 200,
): string => {
  const pts: string[] = [];
  for (let i = 0; i <= steps; i++) {
    const t = from + (to - from) * (i / steps);
    const x = toSvgX(t);
    const y = toSvgY(yFn(t));
    pts.push(i === 0 ? `M ${x} ${y}` : `L ${x} ${y}`);
  }
  return pts.join(" ");
};

/** A curve drawn as SVG path. */
const CurveLine: React.FC<{
  yFn: (t: number) => number;
  from: number;
  to: number;
  color: string;
  strokeWidth?: number;
  opacity?: number;
  glowId?: string;
  glowStd?: number;
}> = ({
  yFn,
  from,
  to,
  color,
  strokeWidth = 3,
  opacity = 1,
  glowId,
  glowStd,
}) => {
  const d = useMemo(() => buildCurvePath(yFn, from, to), [yFn, from, to]);
  return (
    <>
      {glowId && glowStd && (
        <defs>
          <filter id={glowId} x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur stdDeviation={glowStd} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>
      )}
      <path
        d={d}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        opacity={opacity}
        filter={glowId ? `url(#${glowId})` : undefined}
      />
    </>
  );
};

/** Dots along a curve with spring physics pop-in. */
const CurveDots: React.FC<{
  yFn: (t: number) => number;
  visibleCount: number;
  totalCount: number;
  from?: number;
  to?: number;
  color: string;
  radius?: number;
  frame: number;
  dotStartFrame?: number;
  fps?: number;
}> = ({
  yFn,
  visibleCount,
  totalCount,
  from = 0,
  to = 1,
  color,
  radius = 8,
  frame,
  dotStartFrame = 0,
  fps = 30,
}) => {
  const dots = [];
  for (let i = 0; i < visibleCount; i++) {
    const t = from + ((i + 1) / (totalCount + 1)) * (to - from);
    const x = toSvgX(t);
    const y = toSvgY(yFn(t));
    // Spring physics pop-in: each dot appears at a staggered frame
    const dotFrame = dotStartFrame + i * 8;
    const popScale = spring({
      frame: frame - dotFrame,
      fps,
      config: {
        damping: 12,
        stiffness: 200,
      },
    });
    dots.push(
      <g key={i} transform={`translate(${x}, ${y}) scale(${popScale})`}>
        <circle r={radius} fill={color} stroke="#ffffff" strokeWidth={2} />
      </g>,
    );
  }
  return <>{dots}</>;
};

/** Dip annotation icons. */
const DipIcon: React.FC<{
  type: "arrow-down" | "revert" | "fork";
  x: number;
  y: number;
  color: string;
  size?: number;
}> = ({ type, x, y, color, size = 14 }) => {
  if (type === "arrow-down") {
    return (
      <path
        d={`M ${x} ${y - size / 2} L ${x} ${y + size / 2} M ${x - size / 3} ${y + size / 4} L ${x} ${y + size / 2} L ${x + size / 3} ${y + size / 4}`}
        stroke={color}
        strokeWidth={2}
        fill="none"
      />
    );
  }
  if (type === "revert") {
    return (
      <g>
        <circle cx={x} cy={y} r={size / 2} stroke={color} strokeWidth={2} fill="none" />
        <path
          d={`M ${x - size / 4} ${y - size / 4} L ${x - size / 4} ${y + size / 4} L ${x + size / 4} ${y}`}
          stroke={color}
          strokeWidth={2}
          fill="none"
        />
      </g>
    );
  }
  // fork
  return (
    <path
      d={`M ${x} ${y - size / 2} L ${x} ${y} M ${x} ${y} L ${x - size / 3} ${y + size / 2} M ${x} ${y} L ${x + size / 3} ${y + size / 2}`}
      stroke={color}
      strokeWidth={2}
      fill="none"
    />
  );
};

/** Annotation callout with leader line and optional icon. */
const Annotation: React.FC<{
  text: string;
  x: number;
  y: number;
  opacity: number;
  color?: string;
  offsetY?: number;
  fontSize?: number;
  icon?: "arrow-down" | "revert" | "fork";
}> = ({
  text,
  x,
  y,
  opacity,
  color = "rgba(255,255,255,0.7)",
  offsetY = 50,
  fontSize = 16,
  icon,
}) => (
  <g opacity={opacity}>
    {/* Leader line */}
    <line
      x1={x}
      y1={y}
      x2={x + 10}
      y2={y + offsetY - 5}
      stroke={color}
      strokeWidth={1}
      opacity={0.5}
    />
    {icon && (
      <DipIcon
        type={icon}
        x={x + 12}
        y={y + offsetY - 10}
        color={color}
      />
    )}
    <text
      x={icon ? x + 28 : x + 14}
      y={y + offsetY + 4}
      fill={color}
      fontSize={fontSize}
      fontFamily="system-ui, sans-serif"
      fontStyle="italic"
    >
      {text}
    </text>
  </g>
);

/** Forward radial lines projecting from a PDD dot to the right edge. */
const ForwardRadials: React.FC<{
  dotT: number;
  yFn: (t: number) => number;
  opacity: number;
}> = ({ dotT, yFn, opacity }) => {
  const x1 = toSvgX(dotT);
  const y1 = toSvgY(yFn(dotT));
  // Project 2-3 lines toward the right edge
  const lines = [0, -15, 15];
  return (
    <>
      {lines.map((yOff, i) => (
        <line
          key={i}
          x1={x1}
          y1={y1}
          x2={GRAPH.RIGHT}
          y2={y1 + yOff - 30}
          stroke={COLORS.PDD_GLOW}
          strokeWidth={1}
          opacity={opacity * 0.3}
        />
      ))}
    </>
  );
};

/** Shaded gap region between PDD and patching curves. */
const GapRegion: React.FC<{
  pddFn: (t: number) => number;
  patchFn: (t: number) => number;
  from: number;
  to: number;
  opacity: number;
}> = ({ pddFn, patchFn, from, to, opacity }) => {
  const path = useMemo(() => {
    const steps = 200;
    // Top edge: PDD curve (left to right)
    const topPts: string[] = [];
    for (let i = 0; i <= steps; i++) {
      const t = from + (to - from) * (i / steps);
      const x = toSvgX(t);
      const y = toSvgY(pddFn(t));
      topPts.push(i === 0 ? `M ${x} ${y}` : `L ${x} ${y}`);
    }
    // Bottom edge: patching curve (right to left)
    const bottomPts: string[] = [];
    for (let i = steps; i >= 0; i--) {
      const t = from + (to - from) * (i / steps);
      const x = toSvgX(t);
      const y = toSvgY(patchFn(t));
      bottomPts.push(`L ${x} ${y}`);
    }
    return topPts.join(" ") + " " + bottomPts.join(" ") + " Z";
  }, [pddFn, patchFn, from, to]);

  return (
    <path
      d={path}
      fill="url(#gapGradient)"
      opacity={opacity}
    />
  );
};

/** Cost statistic callout ($1.52T). */
const CostCallout: React.FC<{ opacity: number }> = ({ opacity }) => (
  <g opacity={opacity}>
    <rect
      x={1350}
      y={120}
      width={360}
      height={100}
      rx={8}
      fill="rgba(26, 26, 46, 0.85)"
      stroke="rgba(255,255,255,0.15)"
      strokeWidth={1}
    />
    <text
      x={1530}
      y={168}
      fill={COLORS.DIP_RED}
      fontSize={36}
      fontWeight="bold"
      fontFamily="system-ui, sans-serif"
      textAnchor="middle"
    >
      $1.52T
    </text>
    <text
      x={1530}
      y={200}
      fill={COLORS.LABEL_DIM}
      fontSize={18}
      fontFamily="system-ui, sans-serif"
      textAnchor="middle"
    >
      annual US tech debt cost (CISQ)
    </text>
  </g>
);

// ── Main component ───────────────────────────────────────────────────

export const CompoundCurvesGraph: React.FC<CompoundCurvesGraphPropsType> = ({
  phase = 1,
}) => {
  const frame = useCurrentFrame();

  // ── Phase 1: axes, labels, legend, curve starts ──────────────────
  const axisYProgress =
    phase >= 2
      ? 1 // Phase 2+: axes already fully drawn from phase 1
      : interpolate(
          frame,
          [0, 60],
          [0, 1],
          { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) },
        );
  const axisXProgress =
    phase >= 2
      ? 1 // Phase 2+: axes already fully drawn from phase 1
      : interpolate(
          frame,
          [15, 75],
          [0, 1],
          { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) },
        );
  const labelOpacity =
    phase >= 2
      ? 1 // Phase 2+: labels already fully visible from phase 1
      : interpolate(
          frame,
          [60, 120],
          [0, 1],
          { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
        );
  const curveStartProgress =
    phase >= 3
      ? 0.08 // Phase 3+: PDD starting segment is already fully visible from phase 1
      : interpolate(
          frame,
          [120, 210],
          [0, 0.08],
          { extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) },
        );

  // ── Phase 2: patching curve draws, dots, annotations ─────────────
  const patchCurveProgress =
    phase >= 3
      ? 1 // Phase 3+: patching curve is already fully drawn from phase 2
      : phase >= 2
        ? interpolate(
            frame,
            [0, 450],
            [0.08, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
          )
        : 0;
  const patchVisibleDots =
    phase >= 3
      ? PATCH_DOT_COUNT // Phase 3+: all dots already visible from phase 2
      : phase >= 2
        ? Math.floor(
            interpolate(frame, [0, 450], [1, PATCH_DOT_COUNT], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          )
        : 0;
  const patchAnnot1Opacity =
    phase >= 3
      ? 1 // Phase 3+: annotations fully visible from phase 2
      : phase >= 2
        ? interpolate(frame, [90, 150], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          })
        : 0;
  const patchAnnot2Opacity =
    phase >= 3
      ? 1 // Phase 3+: annotations fully visible from phase 2
      : phase >= 2
        ? interpolate(frame, [150, 330], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          })
        : 0;
  const ceilingOpacity =
    phase >= 3
      ? 0.4 // Phase 3+: ceiling fully visible from phase 2
      : phase >= 2
        ? interpolate(frame, [330, 450], [0, 0.4], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          })
        : 0;

  // ── Phase 3: wobbles, dip annotations, cost callout ──────────────
  const wobbleAmount =
    phase >= 3
      ? interpolate(frame, [0, 270], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.inOut(Easing.quad),
        })
      : 0;

  // Flicker effect for each dip (1-2px lateral shake, 5-8 frames per dip)
  const flickerOffsets = phase >= 3 ? DIP_POSITIONS.map((_, i) => {
    const dipStartFrame = [0, 90, 180][i]; // When each dip starts forming
    const flickerStart = dipStartFrame + 60;
    const flickerEnd = flickerStart + 7;
    if (frame >= flickerStart && frame <= flickerEnd) {
      return Math.sin(frame * 3) * 1.5; // Oscillate ±1.5px
    }
    return 0;
  }) : [0, 0, 0];

  const dipAnnotOpacities =
    phase >= 3
      ? [
          interpolate(frame, [60, 90], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }),
          interpolate(frame, [150, 180], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }),
          interpolate(frame, [240, 270], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }),
        ]
      : [0, 0, 0];
  const costOpacity =
    phase >= 3
      ? interpolate(frame, [270, 360], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        })
      : 0;

  // ── Phase 4: PDD curve draws, test dots, radial lines ────────────
  const pddActivation =
    phase >= 4
      ? interpolate(frame, [0, 30], [0.5, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 0;
  const pddCurveProgress =
    phase >= 4
      ? interpolate(frame, [30, 240], [0.08, 0.5], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.in(Easing.quad),
        })
      : 0;
  const pddVisibleDots4 =
    phase >= 4
      ? Math.floor(
          interpolate(frame, [30, 240], [0, 8], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
        )
      : 0;
  const pddAnnotOpacity =
    phase >= 4
      ? interpolate(frame, [120, 180], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        })
      : 0;
  const patchingDimOpacity =
    phase >= 4
      ? interpolate(frame, [0, 30], [1, 0.6], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 1;

  // ── Phase 5: PDD exponential, gap shading, labels ────────────────
  const pddFullProgress =
    phase >= 5
      ? interpolate(frame, [0, 330], [0.5, 1.0], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.in(Easing.quad),
        })
      : 0;
  const pddVisibleDots5 =
    phase >= 5
      ? Math.floor(
          interpolate(frame, [0, 330], [8, PDD_DOT_COUNT], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
        )
      : 0;
  const gapOpacity =
    phase >= 5
      ? interpolate(frame, [0, 60], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        })
      : 0;
  const advantageLabelOpacity =
    phase >= 5
      ? interpolate(frame, [180, 270], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        })
      : 0;
  const advantageLabelDrift =
    phase >= 5
      ? interpolate(frame, [180, 450], [0, -40], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 0;
  const wallCalloutOpacity =
    phase >= 5
      ? interpolate(frame, [270, 360], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        })
      : 0;
  const glowStd =
    phase >= 5
      ? interpolate(frame, [0, 330], [4, 8], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 4;

  // ── Determine which curve functions and progress to use ──────────

  // Discrete per-dip activation matching spec pseudo-code thresholds
  const dipActive: readonly boolean[] = useMemo(
    () => [frame >= 30, frame >= 120, frame >= 210] as const,
    [frame],
  );

  // The patching curve fn depends on whether wobbles are active
  const patchYFn = useMemo(() => {
    if (phase >= 3) {
      return (t: number) => patchingWobblyY(t, wobbleAmount, dipActive);
    }
    return patchingBaseY;
  }, [phase, wobbleAmount, dipActive]);

  // Effective PDD draw range
  const effectivePddTo =
    phase >= 5
      ? pddFullProgress
      : phase >= 4
        ? pddCurveProgress
        : curveStartProgress;

  // Effective PDD dot count
  const effectivePddDots =
    phase >= 5 ? pddVisibleDots5 : phase >= 4 ? pddVisibleDots4 : 0;

  // Effective patching draw range
  const effectivePatchTo =
    phase >= 2 ? patchCurveProgress : curveStartProgress;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg
        viewBox="0 0 1920 1080"
        style={{
          position: "absolute",
          width: "100%",
          height: "100%",
        }}
      >
        {/* Gradient for gap region */}
        <defs>
          <linearGradient id="gapGradient" x1="0" y1="0" x2="0" y2="1">
            <stop offset="0%" stopColor={COLORS.PDD_BLUE} stopOpacity={0.15} />
            <stop
              offset="100%"
              stopColor={COLORS.PATCHING_AMBER}
              stopOpacity={0.1}
            />
          </linearGradient>
        </defs>

        {/* Axes */}
        <Axes xProgress={axisXProgress} yProgress={axisYProgress} />

        {/* Axis Labels */}
        <AxisLabels opacity={labelOpacity} />

        {/* Legend */}
        <Legend opacity={labelOpacity} />

        {/* ── Patching curve ────────────────────────────────────── */}
        {effectivePatchTo > 0 && (
          <g opacity={patchingDimOpacity}>
            <CurveLine
              yFn={patchYFn}
              from={0}
              to={effectivePatchTo}
              color={COLORS.PATCHING_AMBER}
              strokeWidth={3}
            />

            {/* Patch dots (phase 2+) */}
            {phase >= 2 && (
              <CurveDots
                yFn={patchYFn}
                visibleCount={patchVisibleDots}
                totalCount={PATCH_DOT_COUNT}
                color={COLORS.PATCHING_AMBER}
                radius={PATCH_DOT_RADIUS}
                frame={phase >= 3 ? 9999 : frame} // Phase 3+: force all springs settled (dots fully visible)
                dotStartFrame={10}
                fps={30}
              />
            )}

            {/* Phase 2 annotations */}
            {phase >= 2 && (
              <>
                <Annotation
                  text="one bug fixed"
                  x={toSvgX(3 / (PATCH_DOT_COUNT + 1))}
                  y={toSvgY(patchYFn(3 / (PATCH_DOT_COUNT + 1)))}
                  opacity={patchAnnot1Opacity}
                />
                <Annotation
                  text="local return only"
                  x={toSvgX(6 / (PATCH_DOT_COUNT + 1))}
                  y={toSvgY(patchYFn(6 / (PATCH_DOT_COUNT + 1)))}
                  opacity={patchAnnot2Opacity}
                />
              </>
            )}

            {/* Dashed ceiling (phase 2+) */}
            {phase >= 2 && ceilingOpacity > 0 && (
              <line
                x1={GRAPH.LEFT}
                y1={toSvgY(patchingBaseY(1))}
                x2={GRAPH.RIGHT}
                y2={toSvgY(patchingBaseY(1))}
                stroke={COLORS.CEILING_DASH}
                strokeWidth={1.5}
                strokeDasharray="10 6"
                opacity={ceilingOpacity}
              />
            )}

            {/* Phase 3 dip annotations with icons */}
            {phase >= 3 &&
              DIP_POSITIONS.map((pos, i) => (
                <Annotation
                  key={i}
                  text={DIP_LABELS[i]}
                  x={toSvgX(pos)}
                  y={toSvgY(patchYFn(pos))}
                  opacity={dipAnnotOpacities[i]}
                  color={COLORS.DIP_RED}
                  fontSize={16}
                  icon={["arrow-down", "revert", "fork"][i] as "arrow-down" | "revert" | "fork"}
                />
              ))}

            {/* Phase 3 per-dip flicker: short curve segments near each dip shake laterally */}
            {phase >= 3 &&
              DIP_POSITIONS.map((pos, i) => {
                const offset = flickerOffsets[i];
                if (offset === 0) return null;
                const segFrom = Math.max(0, pos - DIP_SPREAD * 3);
                const segTo = Math.min(1, pos + DIP_SPREAD * 3);
                return (
                  <g key={`flicker-${i}`} transform={`translate(${offset}, 0)`}>
                    <CurveLine
                      yFn={patchYFn}
                      from={segFrom}
                      to={segTo}
                      color={COLORS.PATCHING_AMBER}
                      strokeWidth={3}
                      opacity={0.7}
                    />
                  </g>
                );
              })}
          </g>
        )}

        {/* Phase 3 cost callout */}
        {phase >= 3 && <CostCallout opacity={costOpacity} />}

        {/* ── Gap region (phase 5) ──────────────────────────────── */}
        {phase >= 5 && gapOpacity > 0 && (
          <GapRegion
            pddFn={pddY}
            patchFn={(t) => patchingWobblyY(t, 1, [true, true, true])}
            from={0.1}
            to={pddFullProgress}
            opacity={gapOpacity}
          />
        )}

        {/* ── PDD curve ─────────────────────────────────────────── */}
        {effectivePddTo > 0 && (
          <g opacity={phase >= 4 ? pddActivation : 1}>
            <CurveLine
              yFn={pddY}
              from={0}
              to={effectivePddTo}
              color={COLORS.PDD_BLUE}
              strokeWidth={phase >= 5 ? 4 : 3}
              glowId="pddGlow"
              glowStd={glowStd}
            />

            {/* PDD dots + radial lines (phase 4-5) */}
            {phase >= 4 && effectivePddDots > 0 && (
              <>
                {Array.from({ length: effectivePddDots }).map((_, i) => {
                  const dotT =
                    (i + 1) / (PDD_DOT_COUNT + 1);
                  return (
                    <React.Fragment key={i}>
                      <ForwardRadials
                        dotT={dotT}
                        yFn={pddY}
                        opacity={phase >= 4 ? 1 : 0}
                      />
                    </React.Fragment>
                  );
                })}
                <CurveDots
                  yFn={pddY}
                  visibleCount={effectivePddDots}
                  totalCount={PDD_DOT_COUNT}
                  color={COLORS.PDD_BLUE}
                  radius={PDD_DOT_RADIUS}
                  frame={frame}
                  dotStartFrame={phase >= 5 ? 0 : 40}
                  fps={30}
                />
              </>
            )}

            {/* Phase 4 annotation */}
            {phase === 4 && pddAnnotOpacity > 0 && (
              <Annotation
                text="constrains all future generations"
                x={toSvgX(3 / (PDD_DOT_COUNT + 1))}
                y={toSvgY(pddY(3 / (PDD_DOT_COUNT + 1)))}
                opacity={pddAnnotOpacity}
                color="rgba(255,255,255,0.8)"
                fontSize={17}
              />
            )}
          </g>
        )}

        {/* Phase 1 only: PDD starting segment (just a hint) */}
        {phase === 1 && curveStartProgress > 0 && (
          <CurveLine
            yFn={pddY}
            from={0}
            to={curveStartProgress}
            color={COLORS.PDD_BLUE}
            strokeWidth={3}
          />
        )}
      </svg>

      {/* ── Phase 5 HTML overlays ─────────────────────────────────── */}
      {phase >= 5 && advantageLabelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: `calc(55% + ${advantageLabelDrift}px)`,
            transform: "translateX(-50%)",
            color: COLORS.LABEL_DIM,
            fontSize: 22,
            fontStyle: "italic",
            fontFamily: "system-ui, sans-serif",
            opacity: advantageLabelOpacity,
          }}
        >
          compound advantage
        </div>
      )}

      {phase >= 5 && wallCalloutOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            right: 180,
            top: 260,
            color: COLORS.LABEL_WHITE,
            fontSize: 20,
            fontWeight: "bold",
            fontFamily: "system-ui, sans-serif",
            opacity: wallCalloutOpacity,
          }}
        >
          It's a permanent wall.
        </div>
      )}
    </AbsoluteFill>
  );
};
