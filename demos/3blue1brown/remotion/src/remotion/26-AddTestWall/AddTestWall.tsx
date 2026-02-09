import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, EXISTING_TESTS, NEW_TEST, AddTestWallPropsType } from "./constants";
import { ADD_TEST_WALL_FPS } from "./constants";

/** Particle convergence effect - particles gather to form the wall */
const ParticleEffect: React.FC<{
  opacity: number;
  convergenceProgress: number;
  centerX: number;
  centerY: number;
}> = ({ opacity, convergenceProgress, centerX, centerY }) => {
  const particles = useMemo(() =>
    Array.from({ length: 30 }, () => ({
      x: Math.random() * 200 - 100,
      y: Math.random() * 200 - 100,
      size: Math.random() * 4 + 2,
    })),
  []);

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        top: centerY,
        left: centerX,
        transform: "translate(-50%, -50%)",
        pointerEvents: "none",
      }}
    >
      {particles.map((p, i) => (
        <div
          key={i}
          style={{
            position: "absolute",
            left: p.x * (1 - convergenceProgress),
            top: p.y * (1 - convergenceProgress),
            width: p.size,
            height: p.size,
            borderRadius: "50%",
            background: COLORS.WALLS_AMBER,
            opacity: opacity * 0.8,
            boxShadow: `0 0 ${p.size * 2}px ${COLORS.WALLS_AMBER}`,
          }}
        />
      ))}
    </div>
  );
};

/** Ratchet mechanism visual - gear with engaging pawl */
const RatchetMechanism: React.FC<{
  engaged: boolean;
  opacity: number;
  x: number;
  y: number;
}> = ({ engaged, opacity, x, y }) => {
  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        transform: "translate(-50%, -50%)",
        opacity,
      }}
    >
      <svg width={80} height={80} viewBox="0 0 80 80">
        {/* Gear wheel */}
        <g transform="translate(40, 40)">
          {/* Gear teeth */}
          {Array.from({ length: 8 }).map((_, i) => {
            const angle = (i * 360) / 8;
            const rad = (angle * Math.PI) / 180;
            const x1 = Math.cos(rad) * 20;
            const y1 = Math.sin(rad) * 20;
            const x2 = Math.cos(rad) * 28;
            const y2 = Math.sin(rad) * 28;
            return (
              <line
                key={i}
                x1={x1}
                y1={y1}
                x2={x2}
                y2={y2}
                stroke={COLORS.WALLS_AMBER}
                strokeWidth={4}
                strokeLinecap="round"
              />
            );
          })}
          {/* Inner circle */}
          <circle
            cx={0}
            cy={0}
            r={18}
            fill="none"
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
          />
          {/* Center dot */}
          <circle cx={0} cy={0} r={4} fill={COLORS.WALLS_AMBER} />
        </g>

        {/* Pawl (engaging mechanism) */}
        <g transform={`translate(60, 40) rotate(${engaged ? 0 : -15} 0 0)`}>
          <line
            x1={0}
            y1={-15}
            x2={0}
            y2={15}
            stroke={engaged ? COLORS.NEW_WALL_GLOW : COLORS.WALLS_AMBER}
            strokeWidth={3}
            strokeLinecap="round"
          />
          {engaged && (
            <>
              {/* Engagement indicator */}
              <rect
                x={-4}
                y={-2}
                width={8}
                height={4}
                fill={COLORS.NEW_WALL_GLOW}
              />
              {/* Flash effect */}
              <circle
                cx={0}
                cy={0}
                r={15}
                fill="none"
                stroke={COLORS.NEW_WALL_GLOW}
                strokeWidth={2}
                opacity={0.5}
              />
            </>
          )}
        </g>
      </svg>
    </div>
  );
};

/** Mold cross-section view showing the cavity structure */
const MoldCrossSection: React.FC<{ opacity: number }> = ({ opacity }) => {
  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        top: "50%",
        left: "50%",
        transform: "translate(-50%, -50%)",
        opacity,
      }}
    >
      {/* Mold cavity outline */}
      <svg width={280} height={400} viewBox="0 0 280 400">
        {/* Left wall of mold */}
        <line
          x1={20}
          y1={0}
          x2={20}
          y2={400}
          stroke={COLORS.LABEL_GRAY}
          strokeWidth={3}
          opacity={0.4}
        />
        {/* Right wall of mold */}
        <line
          x1={260}
          y1={0}
          x2={260}
          y2={400}
          stroke={COLORS.LABEL_GRAY}
          strokeWidth={3}
          opacity={0.4}
        />
        {/* Bottom of mold */}
        <line
          x1={20}
          y1={380}
          x2={260}
          y2={380}
          stroke={COLORS.LABEL_GRAY}
          strokeWidth={3}
          opacity={0.4}
        />
        {/* Mold label */}
        <text
          x={140}
          y={395}
          textAnchor="middle"
          fill={COLORS.LABEL_GRAY}
          fontSize={10}
          fontFamily="sans-serif"
        >
          Test Mold
        </text>
      </svg>
    </div>
  );
};

/** Terminal snippet overlay styled as a small terminal window. */
const TerminalOverlay: React.FC<{
  lines: string[];
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
              color: line.startsWith("$") ? "#4A90D9" : line.includes("Test created") ? "#4CAF50" : "#ccc",
              lineHeight: 1.6,
              whiteSpace: "pre",
            }}
          >
            {line}
          </div>
        ))}
      </div>
    </div>
  );
};

export const AddTestWall: React.FC<AddTestWallPropsType> = ({
  showNewTest = true,
}) => {
  const frame = useCurrentFrame();

  // Mold cross-section opacity
  const moldOpacity = interpolate(
    frame,
    [BEATS.WALLS_VISIBLE_START, BEATS.WALLS_VISIBLE_END],
    [0, 0.8],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Existing walls visibility
  const wallsOpacity = interpolate(
    frame,
    [BEATS.WALLS_VISIBLE_START, BEATS.WALLS_VISIBLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Particle effect (Frame 90-180)
  const particleOpacity = interpolate(
    frame,
    [BEATS.PARTICLES_START, BEATS.PARTICLES_START + 30, BEATS.PARTICLES_END - 30, BEATS.PARTICLES_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const particleConvergence = interpolate(
    frame,
    [BEATS.PARTICLES_START, BEATS.PARTICLES_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // Wall forming outline (Frame 180-270)
  const wallOutlineOpacity = interpolate(
    frame,
    [BEATS.WALL_SOLIDIFY_START, BEATS.WALL_SOLIDIFY_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Wall solidification progress
  const wallSolidProgress = interpolate(
    frame,
    [BEATS.WALL_SOLIDIFY_START, BEATS.WALL_SOLIDIFY_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_START, BEATS.LABEL_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Ratchet engagement
  const ratchetEngaged = frame >= BEATS.RATCHET_ENGAGE;
  const ratchetOpacity = interpolate(
    frame,
    [BEATS.WALL_SOLIDIFY_END - 30, BEATS.WALL_SOLIDIFY_END, BEATS.RATCHET_VISUAL_END, BEATS.RATCHET_VISUAL_END + 30],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Hold phase - pulse effect on new wall
  const holdPulse = interpolate(
    frame,
    [BEATS.HOLD_START, BEATS.HOLD_START + 30, BEATS.HOLD_START + 60],
    [0, 0.3, 0],
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
  const terminalLines: string[] = ["$ pdd bug user_parser"];
  if (frame >= BEATS.TERMINAL_COMMAND_START) {
    terminalLines.push("Creating failing test...");
  }
  if (frame >= BEATS.TERMINAL_COMPLETE) {
    terminalLines.push("Test created: test_whitespace_returns_none");
  }

  // Wall dimensions
  const wallConfig = {
    width: 200,
    height: 60,
    gap: 20,
    centerY: 540, // Center of screen
  };

  // Calculate positions for walls
  const totalHeight = (EXISTING_TESTS.length + 1) * (wallConfig.height + wallConfig.gap);
  const startY = wallConfig.centerY - totalHeight / 2;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Mold cross-section view */}
      <MoldCrossSection opacity={moldOpacity} />

      {/* Existing walls */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: "translate(-50%, -50%)",
          opacity: wallsOpacity,
        }}
      >
        {EXISTING_TESTS.map((test, i) => (
          <div
            key={i}
            style={{
              width: wallConfig.width,
              height: wallConfig.height,
              background: "rgba(217, 148, 74, 0.3)",
              border: `2px solid ${COLORS.WALLS_AMBER}`,
              borderRadius: 8,
              marginBottom: wallConfig.gap,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              fontSize: 14,
              fontFamily: "JetBrains Mono, monospace",
              color: COLORS.WALLS_AMBER,
            }}
          >
            {test}
          </div>
        ))}

        {/* New wall - three phases: particles → forming outline → solid */}
        {showNewTest && (
          <div style={{ position: "relative" }}>
            {/* Phase 1: Particles converging */}
            {frame >= BEATS.PARTICLES_START && frame < BEATS.PARTICLES_END && (
              <ParticleEffect
                opacity={particleOpacity}
                convergenceProgress={particleConvergence}
                centerX={960} // Center of 1920px width
                centerY={startY + EXISTING_TESTS.length * (wallConfig.height + wallConfig.gap) + wallConfig.height / 2}
              />
            )}

            {/* Phase 2 & 3: Forming outline → solid → hold with pulse */}
            {frame >= BEATS.WALL_SOLIDIFY_START && wallOutlineOpacity > 0 && (
              <div
                style={{
                  width: wallConfig.width,
                  height: wallConfig.height,
                  background: `rgba(217, 148, 74, ${0.1 + 0.2 * wallSolidProgress})`,
                  border: wallSolidProgress < 1
                    ? `2px dashed ${COLORS.WALLS_AMBER}`
                    : `2px solid ${COLORS.WALLS_AMBER}`,
                  borderRadius: 8,
                  display: "flex",
                  alignItems: "center",
                  justifyContent: "center",
                  fontSize: 14,
                  fontFamily: "JetBrains Mono, monospace",
                  color: COLORS.WALLS_AMBER,
                  opacity: wallOutlineOpacity,
                  // Pulse effect during hold phase
                  boxShadow: frame >= BEATS.HOLD_START && holdPulse > 0
                    ? `0 0 ${20 + 30 * holdPulse}px ${COLORS.WALLS_AMBER}`
                    : "none",
                }}
              >
                {/* Label appears near end of solidification */}
                <span style={{ opacity: labelOpacity }}>{NEW_TEST}</span>
              </div>
            )}
          </div>
        )}
      </div>

      {/* Ratchet mechanism - gear with engaging pawl */}
      {ratchetOpacity > 0 && (
        <RatchetMechanism
          engaged={ratchetEngaged}
          opacity={ratchetOpacity}
          x={960}
          y={startY + (EXISTING_TESTS.length + 0.5) * (wallConfig.height + wallConfig.gap) + 50}
        />
      )}

      {/* Terminal snippet overlay */}
      <TerminalOverlay lines={terminalLines} opacity={terminalOpacity} />

      {/* Explanation text - emphasize permanence */}
      <div
        style={{
          position: "absolute",
          bottom: 140,
          left: 0,
          right: 340,
          textAlign: "center",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        <div
          style={{
            fontSize: 22,
            color: COLORS.LABEL_WHITE,
            fontFamily: "sans-serif",
          }}
        >
          Wall is now <span style={{ color: COLORS.WALLS_AMBER, fontWeight: "bold" }}>permanent</span>. That bug can never occur again.
        </div>
      </div>

      {/* Section header */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: wallsOpacity,
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
          Adding a Test Wall
        </span>
        <div
          style={{
            fontSize: 16,
            color: COLORS.LABEL_GRAY,
            marginTop: 8,
          }}
        >
          The ratchet clicks forward
        </div>
      </div>
    </AbsoluteFill>
  );
};
