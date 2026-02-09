import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, SockMetaphorFinalPropsType } from "./constants";

// ── Particle Component ──────────────────────────────────────────
interface ParticleProps {
  index: number;
  progress: number;
  startX: number;
  startY: number;
}

const CrumpleParticle: React.FC<ParticleProps> = ({ index, progress, startX, startY }) => {
  // Each particle has a unique trajectory
  const angle = (index / 12) * Math.PI * 2 + Math.PI / 4;
  const distance = 80 + Math.random() * 60;
  const endX = startX + Math.cos(angle) * distance;
  const endY = startY + Math.sin(angle) * distance + 40; // Extra gravity

  const x = interpolate(progress, [0, 1], [startX, endX], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const y = interpolate(progress, [0, 1], [startY, endY], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const opacity = interpolate(progress, [0, 0.3, 1], [0.8, 0.6, 0], {
    extrapolateRight: "clamp",
  });

  const size = 4 + Math.random() * 4;

  return (
    <circle
      cx={x}
      cy={y}
      r={size}
      fill={COLORS.PARTICLE_GRAY}
      opacity={opacity}
    />
  );
};

// ── Side-view Sock SVG ──────────────────────────────────────────
const WornSock: React.FC<{ scale?: number }> = ({ scale = 1 }) => {
  const width = 280 * scale;
  const height = 200 * scale;

  return (
    <svg width={width} height={height} viewBox="0 0 280 200" style={{ filter: "drop-shadow(3px 6px 8px rgba(0,0,0,0.4))" }}>
      <defs>
        <pattern id="wornWoolTexture" patternUnits="userSpaceOnUse" width="6" height="6">
          <circle cx="2" cy="2" r="0.8" fill="rgba(0,0,0,0.08)" />
          <circle cx="5" cy="5" r="0.8" fill="rgba(0,0,0,0.08)" />
        </pattern>
      </defs>

      {/* Main sock shape - SIDE VIEW L-shape */}
      <path
        d="M 40 15
           L 70 15
           L 70 95
           C 70 115 75 130 95 140
           L 240 140
           C 265 140 275 155 270 170
           C 265 185 245 190 220 190
           L 80 190
           C 50 190 30 175 30 155
           L 30 130
           C 30 115 35 105 40 95
           L 40 15
           Z"
        fill={COLORS.SOCK_OLD}
        stroke={COLORS.SOCK_BORDER}
        strokeWidth="3"
      />

      {/* Wool texture overlay */}
      <path
        d="M 40 15
           L 70 15
           L 70 95
           C 70 115 75 130 95 140
           L 240 140
           C 265 140 275 155 270 170
           C 265 185 245 190 220 190
           L 80 190
           C 50 190 30 175 30 155
           L 30 130
           C 30 115 35 105 40 95
           L 40 15
           Z"
        fill="url(#wornWoolTexture)"
      />

      {/* Ribbed cuff at top of leg */}
      <rect x="38" y="15" width="34" height="30" fill="#A67B5B" rx="2" />
      {[0, 6, 12, 18, 24].map((y) => (
        <line key={y} x1="40" y1={17 + y} x2="70" y2={17 + y} stroke={COLORS.SOCK_BORDER} strokeWidth="1.5" opacity="0.5" />
      ))}

      {/* THE HOLE - visible on the heel/bottom area */}
      <g transform="translate(100, 155)">
        {/* Dark hole */}
        <ellipse
          cx="30"
          cy="12"
          rx="28"
          ry="14"
          fill="#2d2416"
          stroke="#1a1510"
          strokeWidth="2"
        />

        {/* Frayed edges around hole */}
        <g opacity="0.8">
          {[0, 40, 80, 120, 180, 220, 260, 320].map((angle, i) => (
            <line
              key={i}
              x1={30 + Math.cos((angle * Math.PI) / 180) * 26}
              y1={12 + Math.sin((angle * Math.PI) / 180) * 12}
              x2={30 + Math.cos((angle * Math.PI) / 180) * 32}
              y2={12 + Math.sin((angle * Math.PI) / 180) * 16}
              stroke={COLORS.SOCK_BORDER}
              strokeWidth="2"
              strokeLinecap="round"
            />
          ))}
        </g>
      </g>
    </svg>
  );
};

// ── Fresh Sock SVG ──────────────────────────────────────────────
const FreshSock: React.FC<{ scale?: number }> = ({ scale = 1 }) => {
  const width = 280 * scale;
  const height = 200 * scale;

  return (
    <svg width={width} height={height} viewBox="0 0 280 200" style={{ filter: "drop-shadow(3px 6px 8px rgba(0,0,0,0.4))" }}>
      <defs>
        <pattern id="freshWoolTexture" patternUnits="userSpaceOnUse" width="6" height="6">
          <circle cx="2" cy="2" r="0.8" fill="rgba(0,0,0,0.05)" />
          <circle cx="5" cy="5" r="0.8" fill="rgba(0,0,0,0.05)" />
        </pattern>
      </defs>

      {/* Main sock shape - pristine */}
      <path
        d="M 40 15
           L 70 15
           L 70 95
           C 70 115 75 130 95 140
           L 240 140
           C 265 140 275 155 270 170
           C 265 185 245 190 220 190
           L 80 190
           C 50 190 30 175 30 155
           L 30 130
           C 30 115 35 105 40 95
           L 40 15
           Z"
        fill={COLORS.SOCK_FRESH}
        stroke={COLORS.SOCK_BORDER}
        strokeWidth="3"
      />

      {/* Fresh texture overlay */}
      <path
        d="M 40 15
           L 70 15
           L 70 95
           C 70 115 75 130 95 140
           L 240 140
           C 265 140 275 155 270 170
           C 265 185 245 190 220 190
           L 80 190
           C 50 190 30 175 30 155
           L 30 130
           C 30 115 35 105 40 95
           L 40 15
           Z"
        fill="url(#freshWoolTexture)"
      />

      {/* Pristine ribbed cuff */}
      <rect x="38" y="15" width="34" height="30" fill="#D4C4A8" rx="2" />
      {[0, 6, 12, 18, 24].map((y) => (
        <line key={y} x1="40" y1={17 + y} x2="70" y2={17 + y} stroke={COLORS.SOCK_BORDER} strokeWidth="1.5" opacity="0.3" />
      ))}
    </svg>
  );
};

// ── Main Component ──────────────────────────────────────────────
export const SockMetaphorFinal: React.FC<SockMetaphorFinalPropsType> = ({
  showCostLabel = true,
  showParticles = true,
  showGlow = true,
}) => {
  const frame = useCurrentFrame();

  // ── Phase 1: Examination (0-60) ──
  const sockHoldY = interpolate(
    frame,
    [BEATS.EXAMINATION_START, 30, 50, BEATS.EXAMINATION_END],
    [200, 180, 185, 190],
    { extrapolateRight: "clamp", easing: Easing.inOut(Easing.ease) }
  );

  const sockHoldRotation = interpolate(
    frame,
    [BEATS.EXAMINATION_START, 30, BEATS.EXAMINATION_END],
    [0, -5, 0],
    { extrapolateRight: "clamp" }
  );

  // Cost label fade
  const costLabelOpacity = interpolate(
    frame,
    [BEATS.COST_LABEL_FADE_IN, 30, BEATS.COST_LABEL_FADE_OUT - 20, BEATS.COST_LABEL_FADE_OUT],
    [0, 0.6, 0.6, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // ── Phase 3: Discard (120-240) ──
  const discardProgress = interpolate(
    frame,
    [BEATS.DISCARD_START, BEATS.DISCARD_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const oldSockX = interpolate(discardProgress, [0, 1], [0, -800]);
  const oldSockY = interpolate(discardProgress, [0, 1], [0, 300]);
  const oldSockRotation = interpolate(discardProgress, [0, 1], [0, -180]);
  const oldSockOpacity = interpolate(discardProgress, [0, 0.5, 1], [1, 0.6, 0]);

  // Particle effect progress
  const particleProgress = interpolate(
    frame,
    [BEATS.PARTICLE_START, BEATS.PARTICLE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // ── Phase 4: Fresh sock appears (240-360) ──
  const freshSockProgress = interpolate(
    frame,
    [BEATS.GRAB_FRESH_START, BEATS.GRAB_FRESH_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const freshSockX = interpolate(freshSockProgress, [0, 1], [800, 0]);
  const freshSockOpacity = interpolate(freshSockProgress, [0, 0.2, 1], [0, 1, 1]);

  // Fresh sock glow
  const freshGlow = interpolate(
    frame,
    [BEATS.FRESH_GLOW_START, BEATS.FRESH_GLOW_START + 20, BEATS.FRESH_GLOW_END - 20, BEATS.FRESH_GLOW_END],
    [0, 0.5, 0.5, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Show old sock until discard is complete
  const showOldSock = frame < BEATS.DISCARD_END;
  // Show fresh sock from grab start
  const showFreshSock = frame >= BEATS.GRAB_FRESH_START;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Warm gradient background */}
      <div
        style={{
          position: "absolute",
          top: 0,
          right: 0,
          width: "70%",
          height: "70%",
          background: "radial-gradient(ellipse at 75% 25%, rgba(232, 168, 72, 0.15) 0%, transparent 60%)",
          pointerEvents: "none",
        }}
      />

      {/* Old/worn sock (examination and discard phases) */}
      {showOldSock && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: frame < BEATS.DISCARD_START ? sockHoldY : 190 + oldSockY,
            transform: `translate(-50%, -50%) translateX(${oldSockX}px) rotate(${
              frame < BEATS.DISCARD_START ? sockHoldRotation : oldSockRotation
            }deg)`,
            opacity: oldSockOpacity,
          }}
        >
          <WornSock scale={1.5} />
        </div>
      )}

      {/* Cost label overlay */}
      {showCostLabel && costLabelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            right: 280,
            top: 200,
            opacity: costLabelOpacity,
            textAlign: "right",
          }}
        >
          <div
            style={{
              fontFamily: "JetBrains Mono, monospace",
              fontSize: 32,
              color: COLORS.COST_LABEL,
              fontWeight: 600,
              marginBottom: 8,
            }}
          >
            $0.50
          </div>
          <div
            style={{
              fontFamily: "JetBrains Mono, monospace",
              fontSize: 14,
              color: "rgba(255, 255, 255, 0.4)",
            }}
          >
            Cost to replace: nearly zero
          </div>
        </div>
      )}

      {/* Crumple particles during toss */}
      {showParticles && particleProgress > 0 && particleProgress < 1 && (
        <svg
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            pointerEvents: "none",
          }}
        >
          {Array.from({ length: 12 }).map((_, i) => (
            <CrumpleParticle
              key={i}
              index={i}
              progress={particleProgress}
              startX={960 - 100}
              startY={380}
            />
          ))}
        </svg>
      )}

      {/* Fresh sock (grab and hold phases) */}
      {showFreshSock && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: 300,
            transform: `translate(-50%, -50%) translateX(${freshSockX}px)`,
            opacity: freshSockOpacity,
          }}
        >
          <FreshSock scale={1.5} />

          {/* Fresh sock glow effect */}
          {showGlow && freshGlow > 0 && (
            <div
              style={{
                position: "absolute",
                left: "50%",
                top: "50%",
                transform: "translate(-50%, -50%)",
                width: 300,
                height: 225,
                borderRadius: "50%",
                background: `radial-gradient(circle, ${COLORS.GLOW_AMBER.replace("0.3", String(freshGlow * 0.5))}, transparent 70%)`,
                pointerEvents: "none",
              }}
            />
          )}
        </div>
      )}

      {/* Sparkle particles when fresh sock appears */}
      {showGlow && showFreshSock && freshSockProgress > 0.3 && freshSockProgress < 0.8 && (
        <svg
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            pointerEvents: "none",
          }}
        >
          {Array.from({ length: 8 }).map((_, i) => {
            const angle = (i / 8) * Math.PI * 2;
            const radius = 60;
            const cx = 960 + Math.cos(angle) * radius;
            const cy = 300 + Math.sin(angle) * radius;
            const sparkleOpacity = interpolate(
              freshSockProgress,
              [0.3, 0.5, 0.8],
              [0, 0.8, 0],
              { extrapolateRight: "clamp" }
            );

            return (
              <circle
                key={i}
                cx={cx}
                cy={cy}
                r={3}
                fill="#FFD700"
                opacity={sparkleOpacity}
              />
            );
          })}
        </svg>
      )}
    </AbsoluteFill>
  );
};
