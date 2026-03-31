import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

// ── Node definitions (authoritative from structured data) ───────────
interface LoopNode {
  id: string;
  text: string;
  color: string;
  x: number;
  y: number;
}

const NODES: LoopNode[] = [
  { id: "faster_patching", text: "Faster patching", color: "#4A90D9", x: 960, y: 350 },
  { id: "faster_growth", text: "Faster growth", color: "#D9944A", x: 1100, y: 550 },
  { id: "faster_rot", text: "Faster rot", color: "#EF4444", x: 820, y: 550 },
];

// ── Timing constants ────────────────────────────────────────────────
const NODE_APPEAR_DURATION = 20;
const ARROW_DRAW_DURATION = 25;
const SEGMENT_SPACING = 30; // frames between each node+arrow pair build
const PULSE_CYCLE_FRAMES = 90;

// ── Styling ─────────────────────────────────────────────────────────
const ARROW_COLOR = "#E2E8F0";
const ARROW_OPACITY_BASE = 0.5;
const ARROW_PULSE_COLOR = "#FFFFFF";
const ARROW_PULSE_OPACITY = 0.8;
const ARROW_THICKNESS = 2;
const FONT_SIZE = 16;
const FONT_WEIGHT = 600;
const FONT_FAMILY = "Inter, sans-serif";
const LABEL_BG = "rgba(10, 15, 26, 0.75)";
const LABEL_PAD_X = 14;
const LABEL_PAD_Y = 8;
const LABEL_RADIUS = 6;

// ── Helpers ─────────────────────────────────────────────────────────

/** Get a quadratic bezier control point for a curved arrow between two nodes */
function getControlPoint(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
  curvature: number = 40
): { cx: number; cy: number } {
  const mx = (x1 + x2) / 2;
  const my = (y1 + y2) / 2;
  const dx = x2 - x1;
  const dy = y2 - y1;
  const len = Math.sqrt(dx * dx + dy * dy) || 1;
  // perpendicular offset (clockwise bias)
  const nx = -dy / len;
  const ny = dx / len;
  return { cx: mx + nx * curvature, cy: my + ny * curvature };
}

/** SVG path for a quadratic bezier with shortening so arrow doesn't overlap the label */
function curvedArrowPath(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
  curvature: number = 40,
  shortenStart: number = 55,
  shortenEnd: number = 55
): string {
  const { cx, cy } = getControlPoint(x1, y1, x2, y2, curvature);

  // Shorten start: evaluate bezier at t=shortenStart/totalLen fraction
  const totalLen = Math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2);
  const tStart = Math.min(shortenStart / totalLen, 0.3);
  const tEnd = 1 - Math.min(shortenEnd / totalLen, 0.3);

  const bx = (t: number) => (1 - t) * (1 - t) * x1 + 2 * (1 - t) * t * cx + t * t * x2;
  const by = (t: number) => (1 - t) * (1 - t) * y1 + 2 * (1 - t) * t * cy + t * t * y2;

  const sx = bx(tStart);
  const sy = by(tStart);
  const ex = bx(tEnd);
  const ey = by(tEnd);

  // Recalculate a new control point for the shortened segment
  // Use the midpoint of the original curve as the new control
  const midX = bx(0.5);
  const midY = by(0.5);

  return `M ${sx} ${sy} Q ${midX} ${midY} ${ex} ${ey}`;
}

/** Get tangent direction at the end of curve for arrowhead */
function getEndTangent(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
  curvature: number = 40,
  shortenEnd: number = 55
): { angle: number; ex: number; ey: number } {
  const { cx, cy } = getControlPoint(x1, y1, x2, y2, curvature);
  const totalLen = Math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2);
  const tEnd = 1 - Math.min(shortenEnd / totalLen, 0.3);

  const bx = (t: number) => (1 - t) * (1 - t) * x1 + 2 * (1 - t) * t * cx + t * t * x2;
  const by = (t: number) => (1 - t) * (1 - t) * y1 + 2 * (1 - t) * t * cy + t * t * y2;

  const ex = bx(tEnd);
  const ey = by(tEnd);

  // Tangent at tEnd: derivative of quadratic bezier
  const dtx = 2 * (1 - tEnd) * (cx - x1) + 2 * tEnd * (x2 - cx);
  const dty = 2 * (1 - tEnd) * (cy - y1) + 2 * tEnd * (y2 - cy);
  const angle = Math.atan2(dty, dtx);

  return { angle, ex, ey };
}

// ── Arrows definition (clockwise: patching->growth->rot->patching) ──
const ARROWS = [
  { from: 0, to: 1 }, // patching -> growth
  { from: 1, to: 2 }, // growth -> rot
  { from: 2, to: 0 }, // rot -> patching
];

interface FeedbackLoopProps {
  /**
   * Local frame relative to the Sequence this component is in.
   * The parent passes `useCurrentFrame()` — which is relative to the Sequence.
   */
  localFrame: number;
}

/**
 * Renders the triangular feedback loop annotation:
 * "Faster patching" -> "Faster growth" -> "Faster rot" -> ...
 *
 * Build phase: nodes + arrows appear sequentially.
 * Cycle phase: a pulse travels clockwise around the loop.
 */
const FeedbackLoop: React.FC<FeedbackLoopProps> = ({ localFrame }) => {
  // Build phase: each segment = node appear + arrow draw
  // Segment 0: frames 0-29 (node 0, then arrow 0)
  // Segment 1: frames 30-59 (node 1, then arrow 1)
  // Segment 2: frames 60-89 (node 2, then arrow 2)
  const buildDuration = 3 * SEGMENT_SPACING; // 90 frames total

  // After build, cycling begins
  const cycleFrame = Math.max(0, localFrame - buildDuration);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", left: 0, top: 0, pointerEvents: "none" }}
    >
      <defs>
        <marker
          id="arrowhead"
          markerWidth="8"
          markerHeight="6"
          refX="7"
          refY="3"
          orient="auto"
        >
          <polygon points="0 0, 8 3, 0 6" fill={ARROW_COLOR} opacity={ARROW_OPACITY_BASE} />
        </marker>
        <marker
          id="arrowhead-pulse"
          markerWidth="8"
          markerHeight="6"
          refX="7"
          refY="3"
          orient="auto"
        >
          <polygon points="0 0, 8 3, 0 6" fill={ARROW_PULSE_COLOR} opacity={ARROW_PULSE_OPACITY} />
        </marker>
      </defs>

      {/* Render arrows (behind nodes so labels overlap cleanly) */}
      {ARROWS.map((arrow, i) => {
        const arrowBuildStart = i * SEGMENT_SPACING + NODE_APPEAR_DURATION;
        const drawProgress = interpolate(
          localFrame,
          [arrowBuildStart, arrowBuildStart + ARROW_DRAW_DURATION],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
        );

        if (drawProgress <= 0) return null;

        const fromNode = NODES[arrow.from];
        const toNode = NODES[arrow.to];
        const path = curvedArrowPath(fromNode.x, fromNode.y, toNode.x, toNode.y);
        const tangent = getEndTangent(fromNode.x, fromNode.y, toNode.x, toNode.y);

        // Pulse: which arrow segment is currently highlighted?
        const pulseSegment = cycleFrame >= 0
          ? Math.floor((cycleFrame % PULSE_CYCLE_FRAMES) / (PULSE_CYCLE_FRAMES / 3))
          : -1;
        const isPulsing = pulseSegment === i && localFrame >= buildDuration;

        // Smooth pulse intensity using sine easing within the segment
        const segmentProgress = cycleFrame >= 0
          ? ((cycleFrame % PULSE_CYCLE_FRAMES) % (PULSE_CYCLE_FRAMES / 3)) / (PULSE_CYCLE_FRAMES / 3)
          : 0;
        const pulseIntensity = isPulsing
          ? interpolate(segmentProgress, [0, 0.5, 1], [0, 1, 0], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            })
          : 0;

        // Arrowhead
        const arrowSize = 10;
        const ah1x = tangent.ex - arrowSize * Math.cos(tangent.angle - 0.4);
        const ah1y = tangent.ey - arrowSize * Math.sin(tangent.angle - 0.4);
        const ah2x = tangent.ex - arrowSize * Math.cos(tangent.angle + 0.4);
        const ah2y = tangent.ey - arrowSize * Math.sin(tangent.angle + 0.4);

        const currentColor = pulseIntensity > 0
          ? ARROW_PULSE_COLOR
          : ARROW_COLOR;
        const currentOpacity = ARROW_OPACITY_BASE + pulseIntensity * (ARROW_PULSE_OPACITY - ARROW_OPACITY_BASE);

        return (
          <g key={`arrow-${i}`} opacity={drawProgress}>
            {/* Arrow path */}
            <path
              d={path}
              fill="none"
              stroke={currentColor}
              strokeWidth={ARROW_THICKNESS + (pulseIntensity > 0 ? 1 : 0)}
              strokeOpacity={currentOpacity}
              strokeDasharray={drawProgress < 1 ? `${drawProgress * 300} 300` : "none"}
            />
            {/* Arrowhead */}
            {drawProgress >= 0.9 && (
              <polygon
                points={`${tangent.ex},${tangent.ey} ${ah1x},${ah1y} ${ah2x},${ah2y}`}
                fill={currentColor}
                opacity={currentOpacity}
              />
            )}
          </g>
        );
      })}

      {/* Render nodes */}
      {NODES.map((node, i) => {
        const nodeStart = i * SEGMENT_SPACING;
        const appearProgress = interpolate(
          localFrame,
          [nodeStart, nodeStart + NODE_APPEAR_DURATION],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.4)) }
        );

        if (appearProgress <= 0) return null;

        const scale = interpolate(appearProgress, [0, 1], [0.9, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        });

        // Highlight node during pulse cycle
        const pulseSegment = cycleFrame >= 0
          ? Math.floor((cycleFrame % PULSE_CYCLE_FRAMES) / (PULSE_CYCLE_FRAMES / 3))
          : -1;
        const isHighlighted = pulseSegment === i && localFrame >= buildDuration;

        const segmentProgress = cycleFrame >= 0
          ? ((cycleFrame % PULSE_CYCLE_FRAMES) % (PULSE_CYCLE_FRAMES / 3)) / (PULSE_CYCLE_FRAMES / 3)
          : 0;
        const highlightIntensity = isHighlighted
          ? interpolate(segmentProgress, [0, 0.5, 1], [0, 1, 0], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            })
          : 0;

        const glowRadius = highlightIntensity * 12;

        return (
          <g
            key={`node-${i}`}
            transform={`translate(${node.x}, ${node.y}) scale(${scale})`}
            opacity={appearProgress}
          >
            {/* Glow effect when highlighted */}
            {highlightIntensity > 0 && (
              <rect
                x={-70}
                y={-18}
                width={140}
                height={36}
                rx={LABEL_RADIUS}
                fill={node.color}
                opacity={highlightIntensity * 0.2}
                filter={`blur(${glowRadius}px)`}
                style={{ filter: `blur(${glowRadius}px)` }}
              />
            )}
            {/* Background pill */}
            <rect
              x={-70}
              y={-18}
              width={140}
              height={36}
              rx={LABEL_RADIUS}
              fill={LABEL_BG}
              stroke={node.color}
              strokeWidth={highlightIntensity > 0 ? 1.5 : 1}
              strokeOpacity={0.4 + highlightIntensity * 0.4}
            />
            {/* Text label */}
            <text
              x={0}
              y={5}
              textAnchor="middle"
              fill={node.color}
              fontSize={FONT_SIZE}
              fontWeight={FONT_WEIGHT}
              fontFamily={FONT_FAMILY}
              opacity={0.85 + highlightIntensity * 0.15}
            >
              {node.text}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export default FeedbackLoop;

/**
 * Returns the "pulse progress" for the "faster rot" node (index 2),
 * ranging from 0 to 1. Used to sync the noise texture with the rot pulse.
 */
export function getRotPulseProgress(
  feedbackLoopLocalFrame: number,
  buildDuration: number = 90
): number {
  const cycleFrame = Math.max(0, feedbackLoopLocalFrame - buildDuration);
  if (feedbackLoopLocalFrame < buildDuration) return 0;

  const segmentLen = PULSE_CYCLE_FRAMES / 3;
  const segmentIndex = Math.floor((cycleFrame % PULSE_CYCLE_FRAMES) / segmentLen);
  if (segmentIndex !== 2) return 0; // only pulse on "faster rot" segment

  const segmentProgress = ((cycleFrame % PULSE_CYCLE_FRAMES) % segmentLen) / segmentLen;
  return interpolate(segmentProgress, [0, 0.5, 1], [0, 1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
}
