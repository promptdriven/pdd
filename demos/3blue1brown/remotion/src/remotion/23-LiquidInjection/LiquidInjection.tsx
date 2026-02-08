import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, MOLD, GENERATED_CODE, LiquidInjectionPropsType } from "./constants";

/**
 * Generates deterministic pseudo-random numbers using a seed.
 * Avoids Math.random() which is non-deterministic across renders.
 */
const seededRandom = (seed: number): number => {
  const x = Math.sin(seed * 9301 + 49297) * 233280;
  return x - Math.floor(x);
};

interface FluidParticle {
  id: number;
  /** Start delay in frames after injection starts */
  delay: number;
  /** Horizontal drift from center (-1 to 1) */
  drift: number;
  /** Size multiplier */
  size: number;
  /** Speed multiplier */
  speed: number;
}

export const LiquidInjection: React.FC<LiquidInjectionPropsType> = ({
  showCode = true,
}) => {
  const frame = useCurrentFrame();

  // Mold fade in
  const moldOpacity = interpolate(
    frame,
    [BEATS.MOLD_START, BEATS.MOLD_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Fill progress (0 to 1) -- controls the rising fill level
  const fillProgress = interpolate(
    frame,
    [BEATS.INJECTION_START, BEATS.FILL_PROGRESS],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Individual wall flash timings for each wall contact
  const leftWallFlash = interpolate(
    frame,
    [BEATS.WALL_CONTACT_START, BEATS.WALL_CONTACT_START + 10, BEATS.WALL_CONTACT_START + 30],
    [0, 1, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const rightWallFlash = interpolate(
    frame,
    [BEATS.WALL_CONTACT_START + 15, BEATS.WALL_CONTACT_START + 25, BEATS.WALL_CONTACT_START + 45],
    [0, 1, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const bottomWallFlash = interpolate(
    frame,
    [BEATS.WALL_CONTACT_START + 40, BEATS.WALL_CONTACT_START + 50, BEATS.WALL_CONTACT_START + 70],
    [0, 1, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Code appearance
  const codeOpacity = showCode
    ? interpolate(
        frame,
        [BEATS.CODE_START, BEATS.CODE_COMPLETE],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  // Checkmark
  const checkmarkOpacity = interpolate(
    frame,
    [BEATS.CHECKMARK_START, BEATS.CHECKMARK_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Mold interior dimensions
  const moldLeft = MOLD.centerX - MOLD.width / 2 + MOLD.wallThickness;
  const moldRight = MOLD.centerX + MOLD.width / 2 - MOLD.wallThickness;
  const moldTop = MOLD.centerY - MOLD.height / 2;
  const moldBottom = MOLD.centerY + MOLD.height / 2 - MOLD.wallThickness;
  const interiorWidth = moldRight - moldLeft;
  const interiorHeight = moldBottom - moldTop;

  // Calculate fill dimensions
  const fillHeight = interiorHeight * fillProgress;

  // Generate fluid particles that fall from the nozzle
  const fluidParticles = useMemo<FluidParticle[]>(() => {
    const particles: FluidParticle[] = [];
    for (let i = 0; i < 40; i++) {
      particles.push({
        id: i,
        delay: i * 2.5, // Staggered release
        drift: (seededRandom(i * 3) - 0.5) * 2, // -1 to 1
        size: 4 + seededRandom(i * 7) * 6, // 4-10px
        speed: 0.7 + seededRandom(i * 11) * 0.6, // speed multiplier
      });
    }
    return particles;
  }, []);

  // Splash particles generated at wall contacts
  const wallSplashParticles = useMemo(() => {
    const splashes: Array<{
      id: number;
      originX: number;
      originY: number;
      angle: number;
      speed: number;
      size: number;
      triggerFrame: number;
    }> = [];

    // Left wall splashes
    for (let i = 0; i < 6; i++) {
      splashes.push({
        id: i,
        originX: moldLeft,
        originY: moldBottom - interiorHeight * 0.3 + seededRandom(i * 13) * interiorHeight * 0.3,
        angle: Math.PI + (seededRandom(i * 17) - 0.5) * 1.2,
        speed: 15 + seededRandom(i * 19) * 25,
        size: 3 + seededRandom(i * 23) * 4,
        triggerFrame: BEATS.WALL_CONTACT_START,
      });
    }

    // Right wall splashes
    for (let i = 0; i < 6; i++) {
      splashes.push({
        id: i + 6,
        originX: moldRight,
        originY: moldBottom - interiorHeight * 0.3 + seededRandom(i * 29) * interiorHeight * 0.3,
        angle: (seededRandom(i * 31) - 0.5) * 1.2,
        speed: 15 + seededRandom(i * 37) * 25,
        size: 3 + seededRandom(i * 41) * 4,
        triggerFrame: BEATS.WALL_CONTACT_START + 15,
      });
    }

    // Bottom wall splashes
    for (let i = 0; i < 8; i++) {
      splashes.push({
        id: i + 12,
        originX: moldLeft + seededRandom(i * 43) * interiorWidth,
        originY: moldBottom,
        angle: -Math.PI / 2 + (seededRandom(i * 47) - 0.5) * 1.5,
        speed: 10 + seededRandom(i * 53) * 30,
        size: 3 + seededRandom(i * 59) * 4,
        triggerFrame: BEATS.WALL_CONTACT_START + 40,
      });
    }

    return splashes;
  }, [moldLeft, moldRight, moldBottom, interiorWidth, interiorHeight]);

  // Nozzle stream progress
  const streamActive = frame >= BEATS.INJECTION_START && fillProgress < 1;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg width="100%" height="100%" viewBox="0 0 1920 1080" style={{ opacity: moldOpacity }}>
        {/* Mold outline */}
        <rect
          x={MOLD.centerX - MOLD.width / 2}
          y={MOLD.centerY - MOLD.height / 2}
          width={MOLD.width}
          height={MOLD.height}
          fill="none"
          stroke={COLORS.OUTLINE_GRAY}
          strokeWidth={2}
          rx={8}
        />

        {/* Test walls (amber) - Left wall */}
        <rect
          x={MOLD.centerX - MOLD.width / 2}
          y={MOLD.centerY - MOLD.height / 2}
          width={MOLD.wallThickness}
          height={MOLD.height}
          fill={`rgba(217, 148, 74, ${0.3 + 0.3 * leftWallFlash})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: leftWallFlash > 0.3 ? `drop-shadow(0 0 ${15 * leftWallFlash}px ${COLORS.WALLS_AMBER})` : "none",
          }}
        />
        {/* Right wall */}
        <rect
          x={MOLD.centerX + MOLD.width / 2 - MOLD.wallThickness}
          y={MOLD.centerY - MOLD.height / 2}
          width={MOLD.wallThickness}
          height={MOLD.height}
          fill={`rgba(217, 148, 74, ${0.3 + 0.3 * rightWallFlash})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: rightWallFlash > 0.3 ? `drop-shadow(0 0 ${15 * rightWallFlash}px ${COLORS.WALLS_AMBER})` : "none",
          }}
        />
        {/* Bottom wall */}
        <rect
          x={MOLD.centerX - MOLD.width / 2 + MOLD.wallThickness}
          y={MOLD.centerY + MOLD.height / 2 - MOLD.wallThickness}
          width={MOLD.width - 2 * MOLD.wallThickness}
          height={MOLD.wallThickness}
          fill={`rgba(217, 148, 74, ${0.3 + 0.3 * bottomWallFlash})`}
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={2}
          style={{
            filter: bottomWallFlash > 0.3 ? `drop-shadow(0 0 ${15 * bottomWallFlash}px ${COLORS.WALLS_AMBER})` : "none",
          }}
        />

        {/* Nozzle (blue) */}
        <rect
          x={MOLD.centerX - MOLD.nozzleWidth / 2}
          y={MOLD.centerY - MOLD.height / 2 - MOLD.nozzleHeight}
          width={MOLD.nozzleWidth}
          height={MOLD.nozzleHeight + 10}
          fill="rgba(74, 144, 217, 0.4)"
          stroke={COLORS.NOZZLE_BLUE}
          strokeWidth={2}
          rx={6}
          style={{
            filter: frame >= BEATS.INJECTION_START ? `drop-shadow(0 0 15px ${COLORS.NOZZLE_BLUE})` : "none",
          }}
        />

        {/* Liquid stream from nozzle -- falling droplets/particles */}
        {streamActive && (
          <g>
            {/* Central stream */}
            <rect
              x={MOLD.centerX - 8}
              y={moldTop}
              width={16}
              height={Math.min(
                interiorHeight - fillHeight,
                interpolate(
                  frame,
                  [BEATS.INJECTION_START, BEATS.INJECTION_START + 20],
                  [0, interiorHeight - fillHeight],
                  { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
                )
              )}
              fill={COLORS.CODE_GRAY}
              opacity={0.5}
              rx={4}
            />

            {/* Falling fluid particles from nozzle */}
            {fluidParticles.map((p) => {
              const particleFrame = frame - BEATS.INJECTION_START - p.delay;
              if (particleFrame < 0) return null;

              // Gravity-affected fall
              const fallDuration = 40 / p.speed;
              const fallProgress = Math.min(1, particleFrame / fallDuration);

              // Gravity: y = 0.5 * g * t^2, normalized
              const yProgress = fallProgress * fallProgress;
              const maxFallY = interiorHeight - fillHeight;
              const particleY = moldTop + yProgress * maxFallY;

              // Horizontal drift increases as particle falls
              const driftX = MOLD.centerX + p.drift * (interiorWidth * 0.35) * fallProgress;

              // Particle disappears when it reaches the fill surface
              if (particleY >= moldBottom - fillHeight - 5) return null;

              return (
                <circle
                  key={p.id}
                  cx={driftX}
                  cy={particleY}
                  r={p.size}
                  fill={COLORS.CODE_GRAY}
                  opacity={0.6 + 0.2 * (1 - fallProgress)}
                />
              );
            })}
          </g>
        )}

        {/* Filling liquid body (rising from bottom) with wavy surface */}
        {fillProgress > 0 && (
          <g>
            {/* Clip to mold interior */}
            <defs>
              <clipPath id="moldInteriorClip">
                <rect
                  x={moldLeft + 2}
                  y={moldTop}
                  width={interiorWidth - 4}
                  height={interiorHeight}
                />
              </clipPath>
            </defs>

            <g clipPath="url(#moldInteriorClip)">
              {/* Main fill body */}
              <path
                d={(() => {
                  const fillTop = moldBottom - fillHeight;
                  // Wavy top surface
                  const waveAmplitude = fillProgress < 1 ? 6 : 0;
                  const waveFreq = 0.03;
                  const waveOffset = frame * 0.08;

                  let d = `M ${moldLeft + 2} ${moldBottom}`;
                  d += ` L ${moldLeft + 2} ${fillTop}`;

                  // Draw wavy top
                  for (let x = moldLeft + 2; x <= moldRight - 2; x += 4) {
                    const waveY = fillTop + Math.sin((x - moldLeft) * waveFreq + waveOffset) * waveAmplitude;
                    d += ` L ${x} ${waveY}`;
                  }

                  d += ` L ${moldRight - 2} ${moldBottom}`;
                  d += ` Z`;
                  return d;
                })()}
                fill={`rgba(138, 156, 175, ${0.4 + 0.3 * fillProgress})`}
                style={{
                  filter: `drop-shadow(0 0 ${10 * fillProgress}px ${COLORS.CODE_GRAY})`,
                }}
              />

              {/* Internal ripple/flow lines */}
              {fillProgress > 0.1 && [0, 1, 2].map((rippleIdx) => {
                const rippleY = moldBottom - fillHeight * (0.25 + rippleIdx * 0.25);
                const rippleAmplitude = 3 + rippleIdx * 2;
                const rippleOffset = frame * (0.05 + rippleIdx * 0.02) + rippleIdx * 2;

                let d = `M ${moldLeft + 10} ${rippleY}`;
                for (let x = moldLeft + 10; x <= moldRight - 10; x += 6) {
                  const ry = rippleY + Math.sin((x - moldLeft) * 0.04 + rippleOffset) * rippleAmplitude;
                  d += ` L ${x} ${ry}`;
                }

                return (
                  <path
                    key={rippleIdx}
                    d={d}
                    fill="none"
                    stroke="rgba(255,255,255,0.08)"
                    strokeWidth={1.5}
                  />
                );
              })}
            </g>
          </g>
        )}

        {/* Wall splash particles */}
        {wallSplashParticles.map((sp) => {
          const elapsed = frame - sp.triggerFrame;
          if (elapsed < 0 || elapsed > 25) return null;
          const progress = elapsed / 25;
          const px = sp.originX + Math.cos(sp.angle) * sp.speed * progress;
          const py = sp.originY + Math.sin(sp.angle) * sp.speed * progress;
          const opacity = (1 - progress) * 0.7;
          const size = sp.size * (1 - progress * 0.5);

          return (
            <circle
              key={sp.id}
              cx={px}
              cy={py}
              r={size}
              fill={COLORS.CODE_GRAY}
              opacity={opacity}
            />
          );
        })}
      </svg>

      {/* Generated code panel */}
      {codeOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 140,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: codeOpacity,
          }}
        >
          <div
            style={{
              background: "#1E1E2E",
              padding: 20,
              borderRadius: 8,
              border: "1px solid #333",
              boxShadow: `0 0 ${20 * codeOpacity}px rgba(138, 156, 175, 0.3)`,
            }}
          >
            <pre
              style={{
                fontSize: 14,
                fontFamily: "JetBrains Mono, monospace",
                color: COLORS.CODE_GRAY,
                margin: 0,
                lineHeight: 1.5,
              }}
            >
              {GENERATED_CODE}
            </pre>
          </div>
        </div>
      )}

      {/* Checkmark */}
      {checkmarkOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: MOLD.centerY - 30,
            left: "50%",
            transform: "translateX(-50%)",
            fontSize: 48,
            color: COLORS.SUCCESS_GREEN,
            opacity: checkmarkOpacity,
            textShadow: `0 0 20px ${COLORS.SUCCESS_GREEN}`,
          }}
        >
          ✓
        </div>
      )}

      {/* Caption */}
      <div
        style={{
          position: "absolute",
          bottom: 40,
          left: 0,
          right: 0,
          textAlign: "center",
          fontSize: 18,
          color: COLORS.LABEL_WHITE,
          fontFamily: "sans-serif",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        Code flows in through the prompt, shaped by the test walls.
      </div>
    </AbsoluteFill>
  );
};
