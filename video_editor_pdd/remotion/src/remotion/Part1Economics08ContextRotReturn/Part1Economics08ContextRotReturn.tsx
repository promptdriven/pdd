import React, { useMemo } from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

// ════════════════════════════════════════════════════════════════════
// Constants (inlined — no cross-file imports per spec requirement)
// ════════════════════════════════════════════════════════════════════

const WIDTH = 1920;
const HEIGHT = 1080;
const TOTAL_FRAMES = 330;
const BG_COLOR = "#0A0F1A";

// Chart geometry
const CHART_LEFT = 120;
const CHART_RIGHT = 1800;
const CHART_TOP = 100;
const CHART_BOTTOM = 800;
const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

const GRID_COLOR = "#1E293B";
const GRID_OPACITY = 0.06;
const AXIS_COLOR = "#475569";
const IDEAL_LINE_COLOR = "#22C55E";
const ACTUAL_LINE_COLOR = "#EF4444";

// Feedback loop
const LOOP_BUILD_START = 60;
const NODE_APPEAR_DURATION = 20;
const ARROW_DRAW_DURATION = 25;
const SEGMENT_SPACING = 30;
const PULSE_CYCLE_FRAMES = 90;
const BUILD_DURATION = 90; // 3 * SEGMENT_SPACING

// Node definitions
const NODES = [
  { id: "faster_patching", text: "Faster patching", color: "#4A90D9", x: 960, y: 350 },
  { id: "faster_growth", text: "Faster growth", color: "#D9944A", x: 1100, y: 550 },
  { id: "faster_rot", text: "Faster rot", color: "#EF4444", x: 820, y: 550 },
] as const;

const ARROWS_DEF = [
  { from: 0, to: 1 },
  { from: 1, to: 2 },
  { from: 2, to: 0 },
];

// Arrow styling
const ARROW_COLOR = "#E2E8F0";
const ARROW_OPACITY_BASE = 0.5;
const ARROW_PULSE_COLOR = "#FFFFFF";
const ARROW_PULSE_OPACITY = 0.8;
const ARROW_THICKNESS = 2;
const FONT_SIZE = 16;
const FONT_WEIGHT = 600;
const FONT_FAMILY = "Inter, sans-serif";
const LABEL_BG = "rgba(10, 15, 26, 0.75)";
const LABEL_RADIUS = 6;

// Noise
const NOISE_BASE_OPACITY = 0.12;
const NOISE_PULSE_AMPLITUDE = 0.15;

// ════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════

function getControlPoint(
  x1: number, y1: number, x2: number, y2: number, curvature = 40
) {
  const mx = (x1 + x2) / 2;
  const my = (y1 + y2) / 2;
  const dx = x2 - x1;
  const dy = y2 - y1;
  const len = Math.sqrt(dx * dx + dy * dy) || 1;
  return { cx: mx + (-dy / len) * curvature, cy: my + (dx / len) * curvature };
}

function curvedArrowPath(
  x1: number, y1: number, x2: number, y2: number,
  curvature = 40, shortenStart = 55, shortenEnd = 55
): string {
  const { cx, cy } = getControlPoint(x1, y1, x2, y2, curvature);
  const totalLen = Math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2);
  const tStart = Math.min(shortenStart / totalLen, 0.3);
  const tEnd = 1 - Math.min(shortenEnd / totalLen, 0.3);

  const bx = (t: number) => (1 - t) ** 2 * x1 + 2 * (1 - t) * t * cx + t * t * x2;
  const by = (t: number) => (1 - t) ** 2 * y1 + 2 * (1 - t) * t * cy + t * t * y2;

  return `M ${bx(tStart)} ${by(tStart)} Q ${bx(0.5)} ${by(0.5)} ${bx(tEnd)} ${by(tEnd)}`;
}

function getEndTangent(
  x1: number, y1: number, x2: number, y2: number,
  curvature = 40, shortenEnd = 55
) {
  const { cx, cy } = getControlPoint(x1, y1, x2, y2, curvature);
  const totalLen = Math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2);
  const tEnd = 1 - Math.min(shortenEnd / totalLen, 0.3);

  const ex = (1 - tEnd) ** 2 * x1 + 2 * (1 - tEnd) * tEnd * cx + tEnd * tEnd * x2;
  const ey = (1 - tEnd) ** 2 * y1 + 2 * (1 - tEnd) * tEnd * cy + tEnd * tEnd * y2;
  const dtx = 2 * (1 - tEnd) * (cx - x1) + 2 * tEnd * (x2 - cx);
  const dty = 2 * (1 - tEnd) * (cy - y1) + 2 * tEnd * (y2 - cy);

  return { angle: Math.atan2(dty, dtx), ex, ey };
}

function getRotPulseProgress(loopLocalFrame: number): number {
  const cycleFrame = Math.max(0, loopLocalFrame - BUILD_DURATION);
  if (loopLocalFrame < BUILD_DURATION) return 0;
  const segmentLen = PULSE_CYCLE_FRAMES / 3;
  const segmentIndex = Math.floor((cycleFrame % PULSE_CYCLE_FRAMES) / segmentLen);
  if (segmentIndex !== 2) return 0;
  const segProg = ((cycleFrame % PULSE_CYCLE_FRAMES) % segmentLen) / segmentLen;
  return interpolate(segProg, [0, 0.5, 1], [0, 1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
}

// ════════════════════════════════════════════════════════════════════
// Sub-components (inline to avoid cross-file imports)
// ════════════════════════════════════════════════════════════════════

/** Code Cost Chart with debt shading and Context Rot label */
const CodeCostChartInline: React.FC = () => {
  const sampleCount = 60;
  const idealPoints: string[] = [];
  const actualPoints: string[] = [];
  const debtTop: string[] = [];
  const debtBottom: string[] = [];

  for (let i = 0; i <= sampleCount; i++) {
    const t = i / sampleCount;
    const x = CHART_LEFT + t * CHART_WIDTH;
    const idealY = CHART_BOTTOM - (t * 0.3 + 0.05) * CHART_HEIGHT;
    const actualY = CHART_BOTTOM - (t * 0.3 + 0.05 + Math.pow(t, 2.2) * 0.45) * CHART_HEIGHT;

    idealPoints.push(`${x},${idealY}`);
    actualPoints.push(`${x},${actualY}`);
    debtTop.push(`${x},${actualY}`);
    debtBottom.unshift(`${x},${idealY}`);
  }

  const debtPath = [...debtTop, ...debtBottom].join(" ");

  const hGridCount = 6;
  const vGridCount = 10;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: "absolute", left: 0, top: 0 }}
    >
      {/* Grid */}
      {Array.from({ length: hGridCount + 1 }).map((_, i) => {
        const y = CHART_TOP + (i / hGridCount) * CHART_HEIGHT;
        return (
          <line key={`h${i}`} x1={CHART_LEFT} y1={y} x2={CHART_RIGHT} y2={y}
            stroke={GRID_COLOR} strokeOpacity={GRID_OPACITY} strokeWidth={1} />
        );
      })}
      {Array.from({ length: vGridCount + 1 }).map((_, i) => {
        const x = CHART_LEFT + (i / vGridCount) * CHART_WIDTH;
        return (
          <line key={`v${i}`} x1={x} y1={CHART_TOP} x2={x} y2={CHART_BOTTOM}
            stroke={GRID_COLOR} strokeOpacity={GRID_OPACITY} strokeWidth={1} />
        );
      })}

      {/* Debt gradient fill */}
      <defs>
        <linearGradient id="debtGrad" x1="0" y1="0" x2="1" y2="0">
          <stop offset="0%" stopColor="rgba(239,68,68,0.08)" />
          <stop offset="100%" stopColor="rgba(239,68,68,0.25)" />
        </linearGradient>
      </defs>
      <polygon points={debtPath} fill="url(#debtGrad)" />

      {/* Axes */}
      <line x1={CHART_LEFT} y1={CHART_BOTTOM} x2={CHART_RIGHT} y2={CHART_BOTTOM}
        stroke={AXIS_COLOR} strokeWidth={2} />
      <line x1={CHART_LEFT} y1={CHART_TOP} x2={CHART_LEFT} y2={CHART_BOTTOM}
        stroke={AXIS_COLOR} strokeWidth={2} />

      {/* Ideal line */}
      <polyline points={idealPoints.join(" ")} fill="none"
        stroke={IDEAL_LINE_COLOR} strokeWidth={2.5} strokeOpacity={0.7} />

      {/* Actual line */}
      <polyline points={actualPoints.join(" ")} fill="none"
        stroke={ACTUAL_LINE_COLOR} strokeWidth={2.5} strokeOpacity={0.85} />

      {/* Axis labels */}
      <text x={CHART_LEFT + CHART_WIDTH / 2} y={CHART_BOTTOM + 50}
        textAnchor="middle" fill="#94A3B8" fontSize={14} fontFamily={FONT_FAMILY}>
        Project Timeline
      </text>
      <text x={CHART_LEFT - 50} y={CHART_TOP + CHART_HEIGHT / 2}
        textAnchor="middle" fill="#94A3B8" fontSize={14} fontFamily={FONT_FAMILY}
        transform={`rotate(-90, ${CHART_LEFT - 50}, ${CHART_TOP + CHART_HEIGHT / 2})`}>
        Cost per Change
      </text>

      {/* Context Rot label */}
      <text x={CHART_LEFT + CHART_WIDTH * 0.7} y={CHART_TOP + CHART_HEIGHT * 0.45}
        textAnchor="middle" fill="#EF4444" fontSize={18} fontWeight={600}
        fontFamily={FONT_FAMILY} opacity={0.85}>
        Context Rot
      </text>

      {/* Legend */}
      <circle cx={CHART_RIGHT - 250} cy={CHART_TOP + 20} r={5} fill={IDEAL_LINE_COLOR} />
      <text x={CHART_RIGHT - 238} y={CHART_TOP + 25} fill="#94A3B8" fontSize={12}
        fontFamily={FONT_FAMILY}>Ideal cost</text>
      <circle cx={CHART_RIGHT - 250} cy={CHART_TOP + 44} r={5} fill={ACTUAL_LINE_COLOR} />
      <text x={CHART_RIGHT - 238} y={CHART_TOP + 49} fill="#94A3B8" fontSize={12}
        fontFamily={FONT_FAMILY}>Actual cost</text>
    </svg>
  );
};

/** Noise texture overlay for the Context Rot area */
const NoiseOverlay: React.FC<{ pulseProgress: number }> = ({ pulseProgress }) => {
  const frame = useCurrentFrame();
  const seed = useMemo(() => frame % 120, [frame]);

  const pulseExtra = interpolate(pulseProgress, [0, 0.5, 1], [0, NOISE_PULSE_AMPLITUDE, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const opacity = NOISE_BASE_OPACITY + pulseExtra;

  // Position the noise roughly in the upper part of the debt area (right half of chart)
  const noiseLeft = CHART_LEFT + CHART_WIDTH * 0.35;
  const noiseTop = CHART_TOP + CHART_HEIGHT * 0.1;
  const noiseWidth = CHART_WIDTH * 0.6;
  const noiseHeight = CHART_HEIGHT * 0.55;

  return (
    <div
      style={{
        position: "absolute",
        left: noiseLeft,
        top: noiseTop,
        width: noiseWidth,
        height: noiseHeight,
        opacity,
        overflow: "hidden",
        pointerEvents: "none",
      }}
    >
      <svg width={noiseWidth} height={noiseHeight} style={{ position: "absolute", top: 0, left: 0 }}>
        <defs>
          <filter id={`ctxNoise-${seed}`}>
            <feTurbulence type="fractalNoise" baseFrequency="0.65"
              numOctaves={3} seed={seed} stitchTiles="stitch" />
            <feColorMatrix type="matrix"
              values="0 0 0 0 0.94
                      0 0 0 0 0.27
                      0 0 0 0 0.27
                      0 0 0 0.6 0" />
          </filter>
        </defs>
        <rect width={noiseWidth} height={noiseHeight} filter={`url(#ctxNoise-${seed})`} />
      </svg>
    </div>
  );
};

/** Feedback Loop — three-node triangle with animated arrows */
const FeedbackLoopInline: React.FC<{ localFrame: number }> = ({ localFrame }) => {
  const cycleFrame = Math.max(0, localFrame - BUILD_DURATION);

  return (
    <svg width={WIDTH} height={HEIGHT}
      style={{ position: "absolute", left: 0, top: 0, pointerEvents: "none" }}>
      {/* Arrows */}
      {ARROWS_DEF.map((arrow, i) => {
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

        const pulseSegment = localFrame >= BUILD_DURATION
          ? Math.floor((cycleFrame % PULSE_CYCLE_FRAMES) / (PULSE_CYCLE_FRAMES / 3))
          : -1;
        const isPulsing = pulseSegment === i;

        const segmentProgress = localFrame >= BUILD_DURATION
          ? ((cycleFrame % PULSE_CYCLE_FRAMES) % (PULSE_CYCLE_FRAMES / 3)) / (PULSE_CYCLE_FRAMES / 3)
          : 0;
        const pulseIntensity = isPulsing
          ? interpolate(segmentProgress, [0, 0.5, 1], [0, 1, 0], {
              extrapolateLeft: "clamp", extrapolateRight: "clamp",
            })
          : 0;

        const arrowSize = 10;
        const ah1x = tangent.ex - arrowSize * Math.cos(tangent.angle - 0.4);
        const ah1y = tangent.ey - arrowSize * Math.sin(tangent.angle - 0.4);
        const ah2x = tangent.ex - arrowSize * Math.cos(tangent.angle + 0.4);
        const ah2y = tangent.ey - arrowSize * Math.sin(tangent.angle + 0.4);

        const currentColor = pulseIntensity > 0 ? ARROW_PULSE_COLOR : ARROW_COLOR;
        const currentOpacity = ARROW_OPACITY_BASE + pulseIntensity * (ARROW_PULSE_OPACITY - ARROW_OPACITY_BASE);

        return (
          <g key={`arrow-${i}`} opacity={drawProgress}>
            <path d={path} fill="none" stroke={currentColor}
              strokeWidth={ARROW_THICKNESS + (pulseIntensity > 0 ? 1 : 0)}
              strokeOpacity={currentOpacity}
              strokeDasharray={drawProgress < 1 ? `${drawProgress * 300} 300` : "none"} />
            {drawProgress >= 0.9 && (
              <polygon
                points={`${tangent.ex},${tangent.ey} ${ah1x},${ah1y} ${ah2x},${ah2y}`}
                fill={currentColor} opacity={currentOpacity} />
            )}
          </g>
        );
      })}

      {/* Nodes */}
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
          extrapolateLeft: "clamp", extrapolateRight: "clamp",
        });

        const cycleFrameNode = Math.max(0, localFrame - BUILD_DURATION);
        const pulseSegmentNode = localFrame >= BUILD_DURATION
          ? Math.floor((cycleFrameNode % PULSE_CYCLE_FRAMES) / (PULSE_CYCLE_FRAMES / 3))
          : -1;
        const isHighlighted = pulseSegmentNode === i && localFrame >= BUILD_DURATION;

        const segmentProgress = localFrame >= BUILD_DURATION
          ? ((cycleFrameNode % PULSE_CYCLE_FRAMES) % (PULSE_CYCLE_FRAMES / 3)) / (PULSE_CYCLE_FRAMES / 3)
          : 0;
        const highlightIntensity = isHighlighted
          ? interpolate(segmentProgress, [0, 0.5, 1], [0, 1, 0], {
              extrapolateLeft: "clamp", extrapolateRight: "clamp",
            })
          : 0;

        const glowRadius = highlightIntensity * 12;

        return (
          <g key={`node-${i}`}
            transform={`translate(${node.x}, ${node.y}) scale(${scale})`}
            opacity={appearProgress}>
            {highlightIntensity > 0 && (
              <rect x={-75} y={-20} width={150} height={40} rx={LABEL_RADIUS}
                fill={node.color} opacity={highlightIntensity * 0.25}
                style={{ filter: `blur(${glowRadius}px)` }} />
            )}
            <rect x={-75} y={-20} width={150} height={40} rx={LABEL_RADIUS}
              fill={LABEL_BG} stroke={node.color}
              strokeWidth={highlightIntensity > 0 ? 1.5 : 1}
              strokeOpacity={0.4 + highlightIntensity * 0.4} />
            <text x={0} y={5} textAnchor="middle" fill={node.color}
              fontSize={FONT_SIZE} fontWeight={FONT_WEIGHT} fontFamily={FONT_FAMILY}
              opacity={0.85 + highlightIntensity * 0.15}>
              {node.text}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

// ════════════════════════════════════════════════════════════════════
// Main Component
// ════════════════════════════════════════════════════════════════════

export const defaultPart1Economics08ContextRotReturnProps = {};

export const Part1Economics08ContextRotReturn: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame relative to the feedback loop Sequence (starts at frame 60)
  const loopLocalFrame = Math.max(0, frame - LOOP_BUILD_START);

  // Noise pulse progress — synced to the "faster rot" arrow segment
  const noisePulseProgress = getRotPulseProgress(loopLocalFrame);

  // Subtle initial noise pulse during frames 0-60 (before loop builds)
  const earlyPulse = frame < LOOP_BUILD_START
    ? interpolate(
        Math.sin((frame / 30) * Math.PI * 2),
        [-1, 1],
        [0, 0.5],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : noisePulseProgress;

  // Transition fade at end (frames 270-330)
  const transitionOpacity = interpolate(frame, [300, 330], [1, 0.7], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        opacity: transitionOpacity,
      }}
    >
      {/* Code Cost Chart (always visible) */}
      <CodeCostChartInline />

      {/* Context Rot noise texture overlay */}
      <NoiseOverlay pulseProgress={earlyPulse} />

      {/* Feedback Loop annotation (builds starting at frame 60) */}
      {frame >= LOOP_BUILD_START && (
        <Sequence from={0} durationInFrames={TOTAL_FRAMES - LOOP_BUILD_START}>
          <FeedbackLoopInline localFrame={loopLocalFrame} />
        </Sequence>
      )}

      {/* Narration caption (overlay text for accessibility) */}
      <div
        style={{
          position: "absolute",
          bottom: 80,
          left: 0,
          right: 0,
          display: "flex",
          justifyContent: "center",
        }}
      >
        <div
          style={{
            backgroundColor: "rgba(10, 15, 26, 0.8)",
            borderRadius: 8,
            padding: "10px 24px",
            opacity: interpolate(frame, [60, 80, 270, 310], [0, 0.9, 0.9, 0], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        >
          <span
            style={{
              color: "#E2E8F0",
              fontSize: 20,
              fontFamily: FONT_FAMILY,
              fontWeight: 500,
              letterSpacing: 0.3,
            }}
          >
            {frame < 120
              ? "Faster patching..."
              : frame < 180
                ? "...means faster growth..."
                : "...means faster rot."}
          </span>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics08ContextRotReturn;
