import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
  Easing,
} from "remotion";
import {
  COLORS,
  BEATS,
  PatchCyclePropsType,
} from "./constants";

/**
 * Patch Cycle composition — Section 1.9 (spec 10_patch_cycle)
 *
 * Animated diagram showing two fork paths diverging from a common origin:
 *   - Small codebase: curves downward (cost dropping, AI helps here)
 *   - Large codebase: stays flat/rises (cost high, AI struggles)
 *
 * A curved arrow from the small-codebase path arcs upward toward the
 * large-codebase path, with the label "Every patch adds code."
 *
 * This illustrates the catch: patching grows the codebase, pushing you
 * from the world where AI helps into the world where it doesn't.
 */
export const PatchCycle: React.FC<PatchCyclePropsType> = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // ── Chart layout ──────────────────────────────────────────────
  const margins = { top: 160, right: 200, bottom: 120, left: 140 };
  const chartW = width - margins.left - margins.right;
  const chartH = height - margins.top - margins.bottom;

  // X-axis: abstract "time / patches applied" from 0 to 1
  const xScale = (t: number) => margins.left + t * chartW;
  // Y-axis: "effective cost" from 0 (bottom) to 1 (top)
  const yScale = (v: number) => margins.top + chartH - v * chartH;

  // ── Fork origin ───────────────────────────────────────────────
  const forkX = xScale(0.15);
  const forkY = yScale(0.5);

  // ── Path data ─────────────────────────────────────────────────
  // Small codebase: drops from fork point downward (cost decreasing)
  const smallPath = buildCurvePath(
    forkX, forkY,
    xScale(0.85), yScale(0.2),     // endpoint: low cost
    0.4, -0.15                      // control: gentle downward curve
  );

  // Large codebase: rises from fork point upward (cost stays high / increases)
  const largePath = buildCurvePath(
    forkX, forkY,
    xScale(0.85), yScale(0.82),    // endpoint: high cost
    0.4, 0.15                       // control: gentle upward curve
  );

  // ── Common approach path (before the fork) ────────────────────
  const approachPath = `M ${xScale(0.0)} ${yScale(0.48)} L ${forkX} ${forkY}`;

  // ── Draw progress ─────────────────────────────────────────────
  const drawProgress = interpolate(
    frame,
    [BEATS.FORK_DRAW_START, BEATS.FORK_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Approach line draws in first half, fork in second half
  const approachProgress = interpolate(drawProgress, [0, 0.3], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const forkProgress = interpolate(drawProgress, [0.25, 1], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Arrow animation ───────────────────────────────────────────
  // Arrow sits at roughly x=0.55 between the two paths
  const arrowBaseX = xScale(0.55);
  const arrowStartY = yScale(0.32);   // near small codebase path
  const arrowEndY = yScale(0.72);     // near large codebase path

  const arrowDrawProgress = interpolate(
    frame,
    [BEATS.ARROW_DRAW_START, BEATS.ARROW_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Curved arrow SVG path (concave to the right)
  const arrowCurve = `M ${arrowBaseX} ${arrowStartY} C ${arrowBaseX + 100} ${arrowStartY}, ${arrowBaseX + 100} ${arrowEndY}, ${arrowBaseX} ${arrowEndY}`;

  // ── Label animation ───────────────────────────────────────────
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_FADE_START, BEATS.LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const labelScale = interpolate(
    frame,
    [BEATS.LABEL_FADE_START, BEATS.LABEL_FADE_END],
    [0.85, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.5)),
    }
  );

  // ── Zone label animations ─────────────────────────────────────
  const zoneOpacity = interpolate(
    frame,
    [BEATS.ZONES_FADE_START, BEATS.ZONES_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Fork dot pulse ────────────────────────────────────────────
  const dotPulse = interpolate(
    Math.sin(frame * 0.08),
    [-1, 1],
    [0.6, 1.0]
  );

  // Path total length estimate for dashoffset animation
  const pathLen = 1200;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: "50%",
          transform: "translateX(-50%)",
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 42,
          fontWeight: 700,
          color: COLORS.LABEL_WHITE,
          opacity: interpolate(frame, [0, 30], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          textShadow: "0 2px 10px rgba(0,0,0,0.5)",
        }}
      >
        The Patch Cycle Trap
      </div>

      {/* Subtitle */}
      <div
        style={{
          position: "absolute",
          top: 95,
          left: "50%",
          transform: "translateX(-50%)",
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 22,
          fontWeight: 400,
          color: COLORS.LABEL_DIM,
          opacity: interpolate(frame, [15, 45], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
        }}
      >
        Patching grows the codebase. Growth degrades AI assistance.
      </div>

      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          {/* Arrowhead marker */}
          <marker
            id="patchArrowhead"
            markerWidth="12"
            markerHeight="8"
            refX="12"
            refY="4"
            orient="auto"
          >
            <polygon
              points="0 0, 12 4, 0 8"
              fill={COLORS.ARROW}
              opacity={arrowDrawProgress}
            />
          </marker>

          {/* Glow filter */}
          <filter id="lineGlow" x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* ── Background zones ──────────────────────────────── */}

        {/* Green zone (bottom): "AI helps" */}
        <rect
          x={margins.left}
          y={yScale(0.5)}
          width={chartW}
          height={chartH / 2}
          fill={COLORS.GLOW_GREEN}
          opacity={zoneOpacity * 0.6}
          rx={8}
        />

        {/* Red zone (top): "AI struggles" */}
        <rect
          x={margins.left}
          y={margins.top}
          width={chartW}
          height={chartH / 2}
          fill={COLORS.GLOW_RED}
          opacity={zoneOpacity * 0.6}
          rx={8}
        />

        {/* Zone divider line */}
        <line
          x1={margins.left}
          y1={yScale(0.5)}
          x2={xScale(1.0)}
          y2={yScale(0.5)}
          stroke="rgba(255,255,255,0.15)"
          strokeWidth={1}
          strokeDasharray="8,6"
          opacity={zoneOpacity}
        />

        {/* Zone labels */}
        <text
          x={xScale(1.0) + 20}
          y={yScale(0.25)}
          fill={COLORS.ZONE_GREEN_TEXT}
          fontSize={18}
          fontFamily="Inter, system-ui, sans-serif"
          fontWeight={600}
          opacity={zoneOpacity}
          dominantBaseline="middle"
        >
          AI helps
        </text>
        <text
          x={xScale(1.0) + 20}
          y={yScale(0.75)}
          fill={COLORS.ZONE_RED_TEXT}
          fontSize={18}
          fontFamily="Inter, system-ui, sans-serif"
          fontWeight={600}
          opacity={zoneOpacity}
          dominantBaseline="middle"
        >
          AI struggles
        </text>

        {/* ── Y-axis label ──────────────────────────────────── */}
        <text
          x={margins.left - 30}
          y={margins.top + chartH / 2}
          fill={COLORS.LABEL_DIM}
          fontSize={16}
          fontFamily="Inter, system-ui, sans-serif"
          fontWeight={400}
          textAnchor="middle"
          dominantBaseline="middle"
          transform={`rotate(-90, ${margins.left - 30}, ${margins.top + chartH / 2})`}
          opacity={interpolate(frame, [10, 40], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Codebase Size
        </text>

        {/* ── X-axis label ──────────────────────────────────── */}
        <text
          x={margins.left + chartW / 2}
          y={height - margins.bottom + 60}
          fill={COLORS.LABEL_DIM}
          fontSize={16}
          fontFamily="Inter, system-ui, sans-serif"
          fontWeight={400}
          textAnchor="middle"
          opacity={interpolate(frame, [10, 40], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Patches Applied
        </text>

        {/* ── Axes ──────────────────────────────────────────── */}
        <line
          x1={margins.left}
          y1={margins.top}
          x2={margins.left}
          y2={margins.top + chartH}
          stroke={COLORS.AXIS}
          strokeWidth={2}
        />
        <line
          x1={margins.left}
          y1={margins.top + chartH}
          x2={margins.left + chartW}
          y2={margins.top + chartH}
          stroke={COLORS.AXIS}
          strokeWidth={2}
        />

        {/* ── Approach path (before fork) ───────────────────── */}
        <path
          d={approachPath}
          fill="none"
          stroke={COLORS.LINE_PATCH_SMALL}
          strokeWidth={4}
          strokeLinecap="round"
          strokeDasharray={pathLen}
          strokeDashoffset={pathLen * (1 - approachProgress)}
          filter="url(#lineGlow)"
        />

        {/* ── Small codebase fork (drops down) ──────────────── */}
        <path
          d={smallPath}
          fill="none"
          stroke={COLORS.LINE_PATCH_SMALL}
          strokeWidth={3}
          strokeLinecap="round"
          strokeDasharray={pathLen}
          strokeDashoffset={pathLen * (1 - forkProgress)}
          filter="url(#lineGlow)"
        />

        {/* ── Large codebase fork (rises up) ────────────────── */}
        <path
          d={largePath}
          fill="none"
          stroke={COLORS.LINE_PATCH_LARGE}
          strokeWidth={4}
          strokeLinecap="round"
          opacity={0.8}
          strokeDasharray={pathLen}
          strokeDashoffset={pathLen * (1 - forkProgress)}
          filter="url(#lineGlow)"
        />

        {/* ── Fork labels ───────────────────────────────────── */}
        <text
          x={xScale(0.88)}
          y={yScale(0.15)}
          fill={COLORS.ZONE_GREEN_TEXT}
          fontSize={20}
          fontFamily="Inter, system-ui, sans-serif"
          fontWeight={600}
          textAnchor="middle"
          opacity={forkProgress * interpolate(frame, [BEATS.FORK_DRAW_END - 10, BEATS.FORK_DRAW_END + 20], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Small codebase
        </text>
        <text
          x={xScale(0.88)}
          y={yScale(0.88)}
          fill={COLORS.ZONE_RED_TEXT}
          fontSize={20}
          fontFamily="Inter, system-ui, sans-serif"
          fontWeight={600}
          textAnchor="middle"
          opacity={forkProgress * interpolate(frame, [BEATS.FORK_DRAW_END - 10, BEATS.FORK_DRAW_END + 20], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Large codebase
        </text>

        {/* ── Fork origin dot ───────────────────────────────── */}
        <circle
          cx={forkX}
          cy={forkY}
          r={8}
          fill={COLORS.LINE_PATCH_SMALL}
          opacity={approachProgress * dotPulse}
        />
        <circle
          cx={forkX}
          cy={forkY}
          r={14}
          fill="none"
          stroke={COLORS.LINE_PATCH_SMALL}
          strokeWidth={2}
          opacity={approachProgress * dotPulse * 0.4}
        />

        {/* ── Curved arrow: small -> large ──────────────────── */}
        <path
          d={arrowCurve}
          fill="none"
          stroke={COLORS.ARROW}
          strokeWidth={2.5}
          strokeDasharray="8,5"
          opacity={arrowDrawProgress}
          markerEnd="url(#patchArrowhead)"
          strokeDashoffset={pathLen * (1 - arrowDrawProgress)}
        />
      </svg>

      {/* ── "Every patch adds code." label ─────────────────── */}
      {frame >= BEATS.LABEL_FADE_START && (
        <div
          style={{
            position: "absolute",
            left: arrowBaseX + 120,
            top: (arrowStartY + arrowEndY) / 2 - 24,
            transform: `scale(${labelScale})`,
            transformOrigin: "left center",
            opacity: labelOpacity,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 28,
            fontWeight: 700,
            color: COLORS.LABEL_WHITE,
            textShadow: `0 0 20px rgba(232, 145, 45, 0.5), 0 2px 10px rgba(0,0,0,0.8)`,
            whiteSpace: "nowrap",
            padding: "12px 24px",
            backgroundColor: "rgba(26, 26, 46, 0.85)",
            borderRadius: 10,
            border: `2px solid rgba(232, 145, 45, 0.5)`,
            boxShadow: "0 0 30px rgba(232, 145, 45, 0.15)",
          }}
        >
          Every patch adds code.
        </div>
      )}
    </AbsoluteFill>
  );
};

/**
 * Build a cubic bezier path string from (x0,y0) to (x1,y1).
 * controlBiasX/Y shift the midpoint control handles to create curvature.
 */
function buildCurvePath(
  x0: number,
  y0: number,
  x1: number,
  y1: number,
  controlBiasX: number,
  controlBiasY: number
): string {
  const dx = x1 - x0;
  const dy = y1 - y0;
  const cx1 = x0 + dx * (0.3 + controlBiasX);
  const cy1 = y0 + dy * controlBiasY;
  const cx2 = x0 + dx * (0.7 + controlBiasX * 0.3);
  const cy2 = y1 - dy * controlBiasY * 0.3;
  return `M ${x0} ${y0} C ${cx1} ${cy1}, ${cx2} ${cy2}, ${x1} ${y1}`;
}
