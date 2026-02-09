import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, OLD_CODE, NEW_CODE, MOLD_CAVITY, WALLS, CONTACT_POINTS, CodeRegeneratesPropsType } from "./constants";

/** Terminal snippet overlay styled as a small terminal window. */
const TerminalOverlay: React.FC<{
  lines: Array<{ text: string; color?: string }>;
  opacity: number;
}> = ({ lines, opacity }) => {
  if (opacity <= 0) return null;
  return (
    <div
      style={{
        position: "absolute",
        bottom: 30,
        right: 30,
        width: 300,
        opacity,
      }}
    >
      <div
        style={{
          background: "#252535",
          border: "1px solid #444",
          borderRadius: 6,
          padding: "10px 14px",
          minHeight: 80,
        }}
      >
        {/* Terminal title bar dots */}
        <div style={{ display: "flex", gap: 5, marginBottom: 8 }}>
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#E74C3C" }} />
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#F1C40F" }} />
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#2ECC71" }} />
        </div>
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontSize: 12,
              fontFamily: "JetBrains Mono, monospace",
              color: line.color || "#ccc",
              lineHeight: 1.6,
              whiteSpace: "pre",
            }}
          >
            {line.text}
          </div>
        ))}
      </div>
    </div>
  );
};

/** Mold cross-section showing the cavity structure */
const MoldCrossSection: React.FC<{ opacity: number }> = ({ opacity }) => {
  if (opacity <= 0) return null;

  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* Mold outer structure */}
      <rect
        x={MOLD_CAVITY.x - 40}
        y={MOLD_CAVITY.y - 40}
        width={MOLD_CAVITY.width + 80}
        height={MOLD_CAVITY.height + 80}
        fill={COLORS.MOLD_DARK}
        opacity={opacity * 0.3}
        rx={8}
      />
      {/* Mold cavity (empty space) */}
      <rect
        x={MOLD_CAVITY.x}
        y={MOLD_CAVITY.y}
        width={MOLD_CAVITY.width}
        height={MOLD_CAVITY.height}
        fill="none"
        stroke={COLORS.MOLD_DARK}
        strokeWidth={2}
        opacity={opacity * 0.5}
        rx={4}
      />
      {/* Injection nozzle at top center */}
      <path
        d={`M ${MOLD_CAVITY.x + MOLD_CAVITY.width / 2 - 30} ${MOLD_CAVITY.y - 40}
            L ${MOLD_CAVITY.x + MOLD_CAVITY.width / 2 - 20} ${MOLD_CAVITY.y}
            L ${MOLD_CAVITY.x + MOLD_CAVITY.width / 2 + 20} ${MOLD_CAVITY.y}
            L ${MOLD_CAVITY.x + MOLD_CAVITY.width / 2 + 30} ${MOLD_CAVITY.y - 40}
            Z`}
        fill={COLORS.MOLD_DARK}
        opacity={opacity * 0.5}
      />
    </svg>
  );
};

/** Test walls that constrain the code */
const TestWalls: React.FC<{ frame: number }> = ({ frame }) => {
  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        {/* Wall glow filter */}
        <filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="6" result="blur" />
          <feFlood floodColor={COLORS.WALLS_AMBER} floodOpacity="0.6" />
          <feComposite in2="blur" operator="in" result="glowColor" />
          <feMerge>
            <feMergeNode in="glowColor" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        {/* New wall highlight glow */}
        <filter id="newWallGlow" x="-100%" y="-100%" width="300%" height="300%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="12" result="blur" />
          <feFlood floodColor={COLORS.WALLS_AMBER} floodOpacity="0.8" />
          <feComposite in2="blur" operator="in" result="glowColor" />
          <feMerge>
            <feMergeNode in="glowColor" />
            <feMergeNode in="glowColor" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {WALLS.map((wall, i) => {
        // Check if this wall should be highlighted during contact
        const contactPoint = CONTACT_POINTS.find(cp => cp.wallIndex === i);
        const contactProgress = contactPoint
          ? interpolate(
              frame,
              [contactPoint.frame, contactPoint.frame + 30],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )
          : 0;

        // New wall gets extra glow
        const isNewAndHighlighted = wall.isNew && frame >= BEATS.WALL_INTERACTION_START;
        const glowIntensity = wall.isNew
          ? Math.max(contactProgress, isNewAndHighlighted ? 0.8 : 0)
          : contactProgress;

        const isVertical = wall.height > wall.width;
        const labelX = isVertical
          ? wall.x + (i === 3 ? -20 : 20)
          : wall.x + wall.width / 2;
        const labelY = isVertical
          ? wall.y + wall.height / 2
          : wall.y + (i === 0 ? -20 : 30);
        const labelTransform = isVertical
          ? `rotate(${i === 3 ? -90 : 90}, ${labelX}, ${labelY})`
          : undefined;

        return (
          <g key={`wall-${i}`}>
            {/* Wall bar */}
            <rect
              x={wall.x}
              y={wall.y}
              width={wall.width}
              height={wall.height}
              rx={2}
              fill={COLORS.WALLS_AMBER}
              opacity={0.8 + glowIntensity * 0.2}
              filter={wall.isNew && glowIntensity > 0.3 ? "url(#newWallGlow)" : "url(#wallGlow)"}
            />

            {/* Wall label */}
            <text
              x={labelX}
              y={labelY}
              textAnchor="middle"
              dominantBaseline="central"
              transform={labelTransform}
              style={{
                fontSize: wall.isNew ? 13 : 11,
                fontFamily: "'JetBrains Mono', monospace",
                fontWeight: wall.isNew ? 600 : 500,
                fill: COLORS.LABEL_WHITE,
                opacity: 0.9,
              }}
            >
              {wall.label}
            </text>

            {/* Contact point pulse */}
            {contactProgress > 0 && (
              <circle
                cx={labelX}
                cy={labelY}
                r={20 + contactProgress * 40}
                fill="none"
                stroke={COLORS.WALLS_AMBER}
                strokeWidth={3 * (1 - contactProgress)}
                opacity={1 - contactProgress}
              />
            )}
          </g>
        );
      })}
    </svg>
  );
};

/** Particle-based dissolve effect where code breaks into particles */
const DissolveEffect: React.FC<{ progress: number }> = ({ progress }) => {
  // Generate a grid of particles
  const particles = useMemo(() => {
    const grid = [];
    const gridSize = 50;
    const cellSize = 12;
    for (let row = 0; row < gridSize; row++) {
      for (let col = 0; col < gridSize; col++) {
        grid.push({
          x: MOLD_CAVITY.x + (col * MOLD_CAVITY.width) / gridSize,
          y: MOLD_CAVITY.y + (row * MOLD_CAVITY.height) / gridSize,
          size: cellSize * (0.5 + Math.random() * 0.5),
          driftX: (Math.random() - 0.5) * 2,
          driftY: (Math.random() - 0.5) * 2,
          delay: (row + col) * 0.002,
        });
      }
    }
    return grid;
  }, []);

  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {particles.map((p, i) => {
        const particleProgress = Math.max(0, Math.min(1, progress - p.delay));
        const drift = particleProgress * 150;

        return (
          <circle
            key={i}
            cx={p.x + p.driftX * drift}
            cy={p.y + p.driftY * drift}
            r={p.size * (1 - particleProgress * 0.5)}
            fill={COLORS.DISSOLVE_ORANGE}
            opacity={(1 - particleProgress) * 0.6}
          />
        );
      })}
    </svg>
  );
};

/** Fluid flow simulation showing liquid filling the cavity */
const FluidSimulation: React.FC<{ progress: number; frame: number }> = ({ progress, frame }) => {
  // Injection point at top center
  const injectionX = MOLD_CAVITY.x + MOLD_CAVITY.width / 2;
  const injectionY = MOLD_CAVITY.y;

  // Flow downward then spread
  const flowY = interpolate(progress, [0, 0.3], [injectionY, MOLD_CAVITY.y + MOLD_CAVITY.height / 2], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.quad),
  });

  const spreadX = interpolate(progress, [0.3, 1], [0, MOLD_CAVITY.width / 2 - 40], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const fillHeight = interpolate(progress, [0.3, 1], [0, MOLD_CAVITY.height - 40], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        <filter id="liquidGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Main liquid blob */}
      <ellipse
        cx={injectionX}
        cy={flowY}
        rx={60 + spreadX}
        ry={60 + fillHeight}
        fill={COLORS.LIQUID_BLUE}
        opacity={0.5}
        filter="url(#liquidGlow)"
      />

      {/* Flow particles for visual interest */}
      {progress > 0 && [...Array(12)].map((_, i) => {
        const angle = (i / 12) * Math.PI * 2;
        const distance = progress * 100 + Math.sin((frame + i * 10) * 0.1) * 20;
        const particleX = injectionX + Math.cos(angle) * distance;
        const particleY = flowY + Math.sin(angle) * distance;
        const particleProgress = Math.min(1, progress + i * 0.02);

        return (
          <circle
            key={i}
            cx={particleX}
            cy={particleY}
            r={8 - i * 0.3}
            fill={COLORS.LIQUID_BLUE}
            opacity={(1 - particleProgress) * 0.4}
            filter="url(#liquidGlow)"
          />
        );
      })}

      {/* Code liquid (text representation) */}
      {progress > 0.5 && (
        <foreignObject
          x={MOLD_CAVITY.x + 20}
          y={MOLD_CAVITY.y + 20}
          width={MOLD_CAVITY.width - 40}
          height={MOLD_CAVITY.height - 40}
        >
          <div
            style={{
              fontSize: 13,
              fontFamily: "JetBrains Mono, monospace",
              color: COLORS.CODE_GRAY,
              opacity: interpolate(progress, [0.5, 1], [0, 1], { extrapolateRight: "clamp" }),
              lineHeight: 1.6,
              overflow: "hidden",
            }}
          >
            <pre style={{ margin: 0 }}>{NEW_CODE}</pre>
          </div>
        </foreignObject>
      )}
    </svg>
  );
};

/** Success indicator with checkmark */
const SuccessIndicator: React.FC<{ opacity: number }> = ({ opacity }) => {
  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        right: 40,
        top: 40,
        opacity,
        display: "flex",
        alignItems: "center",
        gap: 10,
      }}
    >
      <div
        style={{
          width: 32,
          height: 32,
          borderRadius: "50%",
          background: COLORS.SUCCESS_GREEN,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          fontSize: 24,
          color: COLORS.LABEL_WHITE,
          boxShadow: `0 0 20px ${COLORS.SUCCESS_GREEN}`,
        }}
      >
        ✓
      </div>
      <span
        style={{
          color: COLORS.SUCCESS_GREEN,
          fontSize: 24,
          fontFamily: "JetBrains Mono, monospace",
          textShadow: `0 0 10px ${COLORS.SUCCESS_GREEN}`,
        }}
      >
        All tests passing
      </span>
    </div>
  );
};

export const CodeRegenerates: React.FC<CodeRegeneratesPropsType> = ({
  showTransition = true,
}) => {
  const frame = useCurrentFrame();

  // Mold visibility
  const moldOpacity = interpolate(
    frame,
    [0, 30],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Old code dissolve progress
  const dissolveProgress = interpolate(
    frame,
    [BEATS.DISSOLVE_START, BEATS.DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // Fluid flow progress
  const flowProgress = interpolate(
    frame,
    [BEATS.INJECTION_START, BEATS.CAVITY_FILL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Success indicator
  const successOpacity = interpolate(
    frame,
    [BEATS.SUCCESS_START, BEATS.SUCCESS_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Terminal overlay opacity
  const terminalOpacity = interpolate(
    frame,
    [BEATS.TERMINAL_START, BEATS.TERMINAL_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Terminal lines (progressively revealed)
  const terminalLines: Array<{ text: string; color?: string }> = [
    { text: "$ pdd fix user_parser", color: "#4A90D9" },
  ];
  if (frame >= BEATS.INJECTION_START) {
    terminalLines.push({ text: "Regenerating code...", color: "#ccc" });
  }
  if (frame >= BEATS.SUCCESS_START) {
    terminalLines.push({ text: "All tests passing ✓", color: COLORS.SUCCESS_GREEN });
  }

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Mold cross-section structure */}
      <MoldCrossSection opacity={moldOpacity} />

      {/* Test walls (including new wall) */}
      <TestWalls frame={frame} />

      {/* Old code dissolving effect */}
      {showTransition && dissolveProgress > 0 && dissolveProgress < 1 && (
        <DissolveEffect progress={dissolveProgress} />
      )}

      {/* New fluid flowing and filling cavity */}
      {frame >= BEATS.INJECTION_START && (
        <FluidSimulation progress={flowProgress} frame={frame} />
      )}

      {/* Success indicator */}
      <SuccessIndicator opacity={successOpacity} />

      {/* Terminal snippet overlay */}
      <TerminalOverlay lines={terminalLines} opacity={terminalOpacity} />

      {/* Caption */}
      <div
        style={{
          position: "absolute",
          bottom: 80,
          left: 0,
          right: 340,
          textAlign: "center",
          opacity: interpolate(
            frame,
            [BEATS.HOLD_START, BEATS.HOLD_START + 30],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
        }}
      >
        <div
          style={{
            fontSize: 22,
            color: COLORS.LABEL_WHITE,
            fontFamily: "sans-serif",
          }}
        >
          Fresh code flows into the refined mold, conforming to all walls—including the new constraint.
        </div>
      </div>

      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 40,
          opacity: moldOpacity,
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.WALLS_AMBER,
            fontWeight: "bold",
          }}
        >
          Code Regenerates
        </span>
        <div
          style={{
            fontSize: 16,
            color: COLORS.LABEL_WHITE,
            marginTop: 4,
            opacity: 0.7,
          }}
        >
          Mold Cross-Section View
        </div>
      </div>
    </AbsoluteFill>
  );
};
