import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  COLORS,
  CYCLE_LENGTH,
  CYCLE_BEATS,
  FINAL_HOLD_START,
  TRIANGLE,
  CODE_BLOCK,
  PARTICLE_COUNT,
  seededRandom,
  generateCodePattern,
  CodeRegenerationLoopPropsType,
} from "./constants";

// ── Helper: hex to rgba ─────────────────────────────────────────
const hexToRgb = (hex: string): string => {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  if (!result) return "255, 255, 255";
  return `${parseInt(result[1], 16)}, ${parseInt(result[2], 16)}, ${parseInt(result[3], 16)}`;
};

// ── easeOutBack implementation ──────────────────────────────────
// Remotion's Easing module does not expose Easing.back, so we implement it directly.
const easeOutBack = (t: number): number => {
  const c1 = 1.70158;
  const c3 = c1 + 1;
  return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
};

// ── Persistent Triangle Background ─────────────────────────────
interface TriangleBgProps {
  opacity: number;
}

const TriangleBackground: React.FC<TriangleBgProps> = ({ opacity }) => {
  const { PROMPT, TESTS, GROUNDING } = TRIANGLE;

  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        <linearGradient id="triEdge01" x1={PROMPT.x} y1={PROMPT.y} x2={TESTS.x} y2={TESTS.y} gradientUnits="userSpaceOnUse">
          <stop offset="0%" stopColor={COLORS.PROMPT_BLUE} stopOpacity={0.6 * opacity} />
          <stop offset="100%" stopColor={COLORS.TESTS_AMBER} stopOpacity={0.6 * opacity} />
        </linearGradient>
        <linearGradient id="triEdge02" x1={TESTS.x} y1={TESTS.y} x2={GROUNDING.x} y2={GROUNDING.y} gradientUnits="userSpaceOnUse">
          <stop offset="0%" stopColor={COLORS.TESTS_AMBER} stopOpacity={0.6 * opacity} />
          <stop offset="100%" stopColor={COLORS.GROUNDING_GREEN} stopOpacity={0.6 * opacity} />
        </linearGradient>
        <linearGradient id="triEdge03" x1={GROUNDING.x} y1={GROUNDING.y} x2={PROMPT.x} y2={PROMPT.y} gradientUnits="userSpaceOnUse">
          <stop offset="0%" stopColor={COLORS.GROUNDING_GREEN} stopOpacity={0.6 * opacity} />
          <stop offset="100%" stopColor={COLORS.PROMPT_BLUE} stopOpacity={0.6 * opacity} />
        </linearGradient>
        <filter id="vertexGlow" x="-100%" y="-100%" width="300%" height="300%">
          <feGaussianBlur stdDeviation="12" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Triangle edges */}
      <line x1={PROMPT.x} y1={PROMPT.y} x2={TESTS.x} y2={TESTS.y} stroke="url(#triEdge01)" strokeWidth={2} />
      <line x1={TESTS.x} y1={TESTS.y} x2={GROUNDING.x} y2={GROUNDING.y} stroke="url(#triEdge02)" strokeWidth={2} />
      <line x1={GROUNDING.x} y1={GROUNDING.y} x2={PROMPT.x} y2={PROMPT.y} stroke="url(#triEdge03)" strokeWidth={2} />

      {/* Vertex glows */}
      <circle cx={PROMPT.x} cy={PROMPT.y} r={8} fill={COLORS.PROMPT_BLUE} opacity={0.7 * opacity} filter="url(#vertexGlow)" />
      <circle cx={TESTS.x} cy={TESTS.y} r={8} fill={COLORS.TESTS_AMBER} opacity={0.7 * opacity} filter="url(#vertexGlow)" />
      <circle cx={GROUNDING.x} cy={GROUNDING.y} r={8} fill={COLORS.GROUNDING_GREEN} opacity={0.7 * opacity} filter="url(#vertexGlow)" />

      {/* Vertex labels */}
      <text x={PROMPT.x} y={PROMPT.y - 22} textAnchor="middle" fill={COLORS.PROMPT_BLUE} fontSize={15} fontFamily="sans-serif" fontWeight="bold" opacity={0.8 * opacity}>
        PROMPT
      </text>
      <text x={TESTS.x - 10} y={TESTS.y + 30} textAnchor="middle" fill={COLORS.TESTS_AMBER} fontSize={15} fontFamily="sans-serif" fontWeight="bold" opacity={0.8 * opacity}>
        TESTS
      </text>
      <text x={GROUNDING.x + 10} y={GROUNDING.y + 30} textAnchor="middle" fill={COLORS.GROUNDING_GREEN} fontSize={15} fontFamily="sans-serif" fontWeight="bold" opacity={0.8 * opacity}>
        GROUNDING
      </text>
    </svg>
  );
};

// ── Code Block ──────────────────────────────────────────────────
interface CodeBlockProps {
  pattern: number[];
  opacity: number;
  label: string;
}

const CodeBlock: React.FC<CodeBlockProps> = ({ pattern, opacity, label }) => (
  <div
    style={{
      position: "absolute",
      left: CODE_BLOCK.x,
      top: CODE_BLOCK.y,
      width: CODE_BLOCK.width,
      opacity,
    }}
  >
    <div
      style={{
        backgroundColor: "rgba(160, 160, 160, 0.1)",
        border: "1px solid rgba(160, 160, 160, 0.2)",
        borderRadius: 6,
        padding: 10,
      }}
    >
      {pattern.map((width, i) => (
        <div
          key={i}
          style={{
            height: 4,
            backgroundColor: "rgba(160, 160, 160, 0.35)",
            marginBottom: 3,
            borderRadius: 2,
            width: `${width}%`,
          }}
        />
      ))}
    </div>
    <div
      style={{
        textAlign: "center",
        fontSize: 11,
        color: "rgba(160, 160, 160, 0.4)",
        marginTop: 4,
      }}
    >
      {label}
    </div>
  </div>
);

// ── Dissolution Particle Effect ─────────────────────────────────
interface DissolutionEffectProps {
  progress: number;
  cycleIndex: number;
}

const DissolutionEffect: React.FC<DissolutionEffectProps> = ({ progress, cycleIndex }) => {
  const particles = useMemo(() => {
    return Array.from({ length: PARTICLE_COUNT }, (_, i) => ({
      id: i,
      angle:
        (i / PARTICLE_COUNT) * Math.PI * 2 +
        (seededRandom(i * 7 + 3 + cycleIndex * 1000) - 0.5) * 0.8,
      distance: 40 + seededRandom(i + cycleIndex * 1000) * 80,
      delay: seededRandom(i + 1000 + cycleIndex * 1000) * 0.3,
      size: 2 + seededRandom(i + 2000 + cycleIndex * 1000) * 3,
    }));
  }, [cycleIndex]);

  const cx = TRIANGLE.CENTROID.x;
  const cy = TRIANGLE.CENTROID.y;

  return (
    <>
      {particles.map((p) => {
        const t = Math.max(0, Math.min(1, (progress - p.delay) / (1 - p.delay)));
        const eased = Easing.out(Easing.quad)(t);
        const px = cx + Math.cos(p.angle) * eased * p.distance;
        const py = cy + Math.sin(p.angle) * eased * p.distance;
        const particleOpacity = 0.5 * (1 - eased);

        if (particleOpacity < 0.01) return null;

        return (
          <div
            key={p.id}
            style={{
              position: "absolute",
              left: px,
              top: py,
              width: p.size,
              height: p.size,
              borderRadius: "50%",
              backgroundColor: `rgba(160, 160, 160, ${particleOpacity})`,
            }}
          />
        );
      })}
    </>
  );
};

// ── Regeneration Particle Effect ────────────────────────────────
interface RegenerationEffectProps {
  progress: number;
  cycleIndex: number;
}

const RegenerationEffect: React.FC<RegenerationEffectProps> = ({ progress, cycleIndex }) => {
  const { PROMPT, TESTS, GROUNDING, CENTROID } = TRIANGLE;

  const particles = useMemo(() => {
    const vertices = [PROMPT, TESTS, GROUNDING];
    return Array.from({ length: PARTICLE_COUNT }, (_, i) => {
      // Assign each particle to a triangle vertex/edge source
      const vertexIdx = i % 3;
      const vertex = vertices[vertexIdx];
      const nextVertex = vertices[(vertexIdx + 1) % 3];
      // Spread along the edge from vertex toward next vertex
      const edgeT = seededRandom(i * 17 + 5 + cycleIndex * 2000);
      const sourceX = vertex.x + (nextVertex.x - vertex.x) * edgeT;
      const sourceY = vertex.y + (nextVertex.y - vertex.y) * edgeT;

      return {
        id: i,
        sourceX,
        sourceY,
        delay: seededRandom(i + 3000 + cycleIndex * 2000) * 0.3,
        size: 2 + seededRandom(i + 4000 + cycleIndex * 2000) * 3,
      };
    });
  }, [cycleIndex, PROMPT, TESTS, GROUNDING]);

  return (
    <>
      {particles.map((p) => {
        const t = Math.max(0, Math.min(1, (progress - p.delay) / (1 - p.delay)));
        const eased = Easing.in(Easing.cubic)(t);
        // Interpolate from edge source toward centroid
        const px = p.sourceX + (CENTROID.x - p.sourceX) * eased;
        const py = p.sourceY + (CENTROID.y - p.sourceY) * eased;

        // Opacity: fade in then solidify
        const particleOpacity = interpolate(
          t,
          [0, 0.2, 0.8, 1],
          [0, 0.4, 0.7, 0.5],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );

        if (particleOpacity < 0.01) return null;

        return (
          <div
            key={p.id}
            style={{
              position: "absolute",
              left: px,
              top: py,
              width: p.size * (0.4 + 0.6 * eased),
              height: p.size * (0.4 + 0.6 * eased),
              borderRadius: "50%",
              backgroundColor: `rgba(160, 160, 160, ${particleOpacity})`,
            }}
          />
        );
      })}
    </>
  );
};

// ── Terminal Loop ───────────────────────────────────────────────
interface TerminalLoopProps {
  frame: number;
  cycleLength: number;
  isFinalHold: boolean;
}

const TerminalLoop: React.FC<TerminalLoopProps> = ({ frame, cycleLength, isFinalHold }) => {
  const cycleFrame = frame % cycleLength;

  let terminalText: string;
  let textColor: string;

  if (isFinalHold) {
    terminalText = "\u2713 All tests passed";
    textColor = `rgba(${hexToRgb(COLORS.SUCCESS_GREEN)}, 0.6)`;
  } else if (cycleFrame < CYCLE_BEATS.HOLD_END) {
    terminalText = "\u2713 All tests passed";
    textColor = `rgba(${hexToRgb(COLORS.SUCCESS_GREEN)}, 0.6)`;
  } else if (cycleFrame < CYCLE_BEATS.DISSOLVE_END) {
    terminalText = "$ pdd generate parser...";
    textColor = `rgba(${hexToRgb(COLORS.PROMPT_BLUE)}, 0.6)`;
  } else if (cycleFrame < CYCLE_BEATS.REGENERATE_END) {
    terminalText = "Regenerating parser.py...";
    textColor = "rgba(255, 255, 255, 0.4)";
  } else {
    terminalText = "$ pdd test parser \u2192 \u2713";
    textColor = `rgba(${hexToRgb(COLORS.SUCCESS_GREEN)}, 0.6)`;
  }

  return (
    <div
      style={{
        position: "absolute",
        bottom: 60,
        left: "50%",
        transform: "translateX(-50%)",
        backgroundColor: COLORS.TERMINAL_BG,
        borderRadius: 8,
        padding: "8px 20px",
        fontFamily: "JetBrains Mono, monospace",
        fontSize: 13,
        color: textColor,
        border: `1px solid ${COLORS.TERMINAL_BORDER}`,
      }}
    >
      {terminalText}
    </div>
  );
};

// ── Green Checkmark ─────────────────────────────────────────────
interface CheckmarkProps {
  cycleFrame: number;
  isFinalHold: boolean;
}

const GreenCheckmark: React.FC<CheckmarkProps> = ({ cycleFrame, isFinalHold }) => {
  // During final hold, show a persistent subtle checkmark
  if (isFinalHold) {
    return (
      <div
        style={{
          position: "absolute",
          left: 960,
          top: 520,
          transform: "translate(-50%, -50%)",
          fontSize: 28,
          color: COLORS.SUCCESS_GREEN,
          opacity: 0.5,
          textShadow: `0 0 12px ${COLORS.SUCCESS_GREEN}`,
        }}
      >
        {"\u2713"}
      </div>
    );
  }

  // Per-cycle checkmark during verify phase (frames 90-120)
  if (cycleFrame < CYCLE_BEATS.VERIFY_START) return null;

  const rawCheckOpacity = interpolate(
    cycleFrame,
    [90, 100, 115, 120],
    [0, 1, 1, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Scale with easeOutBack for pop effect
  const scaleProgress = interpolate(
    cycleFrame,
    [90, 105],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const scale = easeOutBack(scaleProgress);

  return (
    <div
      style={{
        position: "absolute",
        left: 960,
        top: 520,
        transform: `translate(-50%, -50%) scale(${scale})`,
        fontSize: 28,
        color: COLORS.SUCCESS_GREEN,
        opacity: rawCheckOpacity,
        textShadow: `0 0 12px ${COLORS.SUCCESS_GREEN}`,
      }}
    >
      {"\u2713"}
    </div>
  );
};

// ── Main Composition ────────────────────────────────────────────
export const CodeRegenerationLoop: React.FC<CodeRegenerationLoopPropsType> = ({
  showTerminal = true,
}) => {
  const frame = useCurrentFrame();

  // Cycle management
  const cycleIndex = Math.floor(frame / CYCLE_LENGTH);
  const cycleFrame = frame % CYCLE_LENGTH;
  const isFinalHold = frame >= FINAL_HOLD_START;

  // Triangle background at 60% opacity (persistent, not animated)
  const triangleOpacity = 0.6;

  // Per-cycle phase flags
  const isHolding = cycleFrame < CYCLE_BEATS.HOLD_END;
  const isDissolving =
    cycleFrame >= CYCLE_BEATS.DISSOLVE_START &&
    cycleFrame < CYCLE_BEATS.DISSOLVE_END;
  const isRegenerating =
    cycleFrame >= CYCLE_BEATS.REGENERATE_START &&
    cycleFrame < CYCLE_BEATS.REGENERATE_END;
  const isVerifying = cycleFrame >= CYCLE_BEATS.VERIFY_START;

  // Dissolution progress (easeOutQuad applied inside component)
  const dissolveProgress = interpolate(
    cycleFrame,
    [CYCLE_BEATS.DISSOLVE_START, CYCLE_BEATS.DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Regeneration progress (easeInCubic applied inside component)
  const regenProgress = interpolate(
    cycleFrame,
    [CYCLE_BEATS.REGENERATE_START, CYCLE_BEATS.REGENERATE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Current code pattern (deterministic per cycle)
  const codePattern = useMemo(
    () => generateCodePattern(cycleIndex),
    [cycleIndex]
  );

  // Next code pattern (for regeneration effect targeting the next version)
  const nextCodePattern = useMemo(
    () => generateCodePattern(cycleIndex + 1),
    [cycleIndex]
  );

  // Show the code block during hold and verify phases, or during final hold
  const showCodeBlock = isFinalHold || isHolding || isVerifying;

  // During verify phase, show the NEXT cycle's pattern (just regenerated)
  // During hold phase, show the current cycle's pattern
  const displayPattern = isVerifying && !isFinalHold ? nextCodePattern : codePattern;
  const displayLabel = isVerifying && !isFinalHold
    ? `v${cycleIndex + 2}`
    : `v${cycleIndex + 1}`;

  // Code block opacity: slight fade at cycle transitions
  const codeBlockOpacity = isFinalHold
    ? 0.5
    : isVerifying
      ? interpolate(cycleFrame, [90, 95], [0, 0.5], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 0.5;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Persistent triangle background (dimmed at 60%) */}
      <TriangleBackground opacity={triangleOpacity} />

      {/* Code block (visible during hold, verify, and final hold) */}
      {showCodeBlock && (
        <CodeBlock
          pattern={displayPattern}
          opacity={codeBlockOpacity}
          label={displayLabel}
        />
      )}

      {/* Dissolution effect (particles scattering outward) */}
      {isDissolving && !isFinalHold && (
        <DissolutionEffect
          progress={dissolveProgress}
          cycleIndex={cycleIndex}
        />
      )}

      {/* Regeneration effect (particles coalescing from triangle edges) */}
      {isRegenerating && !isFinalHold && (
        <RegenerationEffect
          progress={regenProgress}
          cycleIndex={cycleIndex}
        />
      )}

      {/* Green checkmark per cycle */}
      <GreenCheckmark cycleFrame={cycleFrame} isFinalHold={isFinalHold} />

      {/* Subtle terminal readout at bottom center */}
      {showTerminal && (
        <TerminalLoop
          frame={frame}
          cycleLength={CYCLE_LENGTH}
          isFinalHold={isFinalHold}
        />
      )}
    </AbsoluteFill>
  );
};
