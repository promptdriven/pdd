import React from 'react';
import { useCurrentFrame, interpolate, random, Easing } from 'remotion';
import { CANVAS, COLORS, PARTICLES, TIMING } from './constants';

interface ParticleData {
  id: number;
  /** Random starting position on screen (before gather) */
  originX: number;
  originY: number;
  /** Random angle for radial burst (radians) */
  burstAngle: number;
  /** Speed in px/frame during burst */
  burstSpeed: number;
  /** Particle diameter */
  size: number;
}

const generateParticles = (count: number): ParticleData[] => {
  const particles: ParticleData[] = [];
  for (let i = 0; i < count; i++) {
    particles.push({
      id: i,
      originX: random(`pt-ox-${i}`) * CANVAS.width,
      originY: random(`pt-oy-${i}`) * CANVAS.height,
      burstAngle: random(`pt-angle-${i}`) * Math.PI * 2,
      burstSpeed:
        random(`pt-speed-${i}`) * (PARTICLES.burstMaxSpeed - PARTICLES.burstMinSpeed) +
        PARTICLES.burstMinSpeed,
      size:
        random(`pt-size-${i}`) * (PARTICLES.maxSize - PARTICLES.minSize) +
        PARTICLES.minSize,
    });
  }
  return particles;
};

export const ParticleBurst: React.FC = () => {
  const frame = useCurrentFrame();
  const particles = React.useMemo(() => generateParticles(PARTICLES.count), []);

  return (
    <>
      {particles.map((p) => {
        // --- Phase 1: Gather toward center (0..10) ---
        const gatherProgress = interpolate(
          frame,
          [TIMING.gatherStart, TIMING.gatherEnd],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.in(Easing.quad),
          }
        );

        // Position during gather: lerp from origin to center
        const gatheredX = p.originX + (CANVAS.centerX - p.originX) * gatherProgress;
        const gatheredY = p.originY + (CANVAS.centerY - p.originY) * gatherProgress;

        // --- Phase 2: Hold at center (10..15) ---
        // Just stay at center

        // --- Phase 3: Radial explosion (15..35) ---
        const burstElapsed = Math.max(0, frame - TIMING.burstStart);
        const burstProgress = interpolate(
          frame,
          [TIMING.burstStart, TIMING.burstEnd],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        // Distance traveled along burst vector (easeOutCubic applied via progress)
        const maxBurstDist = p.burstSpeed * (TIMING.burstEnd - TIMING.burstStart);
        const burstDist = burstProgress * maxBurstDist;
        const burstDx = Math.cos(p.burstAngle) * burstDist;
        const burstDy = Math.sin(p.burstAngle) * burstDist;

        // --- Compute final position ---
        let x: number;
        let y: number;
        if (frame < TIMING.burstStart) {
          x = gatheredX;
          y = gatheredY;
        } else {
          x = CANVAS.centerX + burstDx;
          y = CANVAS.centerY + burstDy;
        }

        // --- Phase 4: Fade out trails (35..45) ---
        const mainOpacity = interpolate(
          frame,
          [TIMING.fadeStart, TIMING.fadeEnd],
          [1, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        // Size shrinks as particles gather
        const displaySize = frame < TIMING.burstStart
          ? p.size * interpolate(gatherProgress, [0, 1], [1, 0.5])
          : p.size;

        // --- Trail ghost copies (only during/after burst) ---
        const trails: React.ReactNode[] = [];
        if (frame >= TIMING.burstStart && burstElapsed > 0) {
          for (let t = 0; t < PARTICLES.trailCopies; t++) {
            const trailLag = (t + 1) * 3; // frames behind
            const trailFrame = frame - trailLag;
            if (trailFrame < TIMING.burstStart) continue;

            const trailBurstProgress = interpolate(
              trailFrame,
              [TIMING.burstStart, TIMING.burstEnd],
              [0, 1],
              {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
                easing: Easing.out(Easing.cubic),
              }
            );
            const trailDist = trailBurstProgress * maxBurstDist;
            const trailX = CANVAS.centerX + Math.cos(p.burstAngle) * trailDist;
            const trailY = CANVAS.centerY + Math.sin(p.burstAngle) * trailDist;

            trails.push(
              <div
                key={`trail-${p.id}-${t}`}
                style={{
                  position: 'absolute',
                  left: trailX - displaySize / 2,
                  top: trailY - displaySize / 2,
                  width: displaySize,
                  height: displaySize,
                  borderRadius: '50%',
                  backgroundColor: COLORS.particleColor,
                  opacity: PARTICLES.trailOpacities[t] * mainOpacity,
                }}
              />
            );
          }
        }

        return (
          <React.Fragment key={p.id}>
            {trails}
            <div
              style={{
                position: 'absolute',
                left: x - displaySize / 2,
                top: y - displaySize / 2,
                width: displaySize,
                height: displaySize,
                borderRadius: '50%',
                backgroundColor: COLORS.particleColor,
                opacity: mainOpacity,
                boxShadow: `0 0 ${displaySize * 2}px ${COLORS.particleColor}`,
              }}
            />
          </React.Fragment>
        );
      })}
    </>
  );
};
