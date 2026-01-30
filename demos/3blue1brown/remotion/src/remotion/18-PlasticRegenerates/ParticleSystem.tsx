import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PART,
  PARTICLE_COUNT,
  BEATS,
  seededRandom,
} from "./constants";

interface Particle {
  /** Angle for radial scatter on dissolution (radians) */
  angle: number;
  /** Max distance from center on dissolution */
  distance: number;
  /** Stagger delay as fraction of phase (0-0.3) */
  delay: number;
  /** Particle radius in px */
  size: number;
  /** Source angle for regeneration (from mold direction) */
  regenAngle: number;
  /** Source distance for regeneration */
  regenDistance: number;
}

/**
 * Renders the 300-particle dissolve and regenerate system.
 * - Dissolution (frames 30-90): particles scatter outward from part center
 * - Absence (frames 90-120): particles drift and fade
 * - Regeneration (frames 120-180): particles flow from mold direction inward
 */
export const ParticleSystem: React.FC = () => {
  const frame = useCurrentFrame();

  // Precompute particle data once
  const particles: Particle[] = useMemo(() => {
    return Array.from({ length: PARTICLE_COUNT }, (_, i) => {
      const baseAngle = (i / PARTICLE_COUNT) * Math.PI * 2;
      const angleOffset = (seededRandom(i * 7 + 3) - 0.5) * 1.2;
      return {
        angle: baseAngle + angleOffset,
        distance: 50 + seededRandom(i) * 100,
        delay: seededRandom(i + 1000) * 0.3,
        size: 2 + seededRandom(i + 2000) * 3,
        // Regeneration comes from mold direction (left side, roughly -PI to PI spread)
        regenAngle:
          Math.PI + (seededRandom(i + 3000) - 0.5) * Math.PI * 0.8,
        regenDistance: 150 + seededRandom(i + 4000) * 250,
      };
    });
  }, []);

  // --- Dissolution phase (frames 30-90) ---
  const isDissolving =
    frame >= BEATS.DISSOLVE_START && frame < BEATS.ABSENCE_END;
  // --- Regeneration phase (frames 120-180) ---
  const isRegenerating =
    frame >= BEATS.REGEN_START && frame < BEATS.REFORMED_START;

  if (!isDissolving && !isRegenerating) return null;

  return (
    <g>
      {particles.map((p, i) => {
        let cx: number;
        let cy: number;
        let opacity: number;
        let r: number;
        let fillColor: string;

        if (isDissolving) {
          // Progress 0->1 over dissolve phase, accounting for stagger
          const rawProgress = interpolate(
            frame,
            [BEATS.DISSOLVE_START, BEATS.DISSOLVE_END],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          // Apply per-particle stagger delay
          const staggered = Math.max(0, rawProgress - p.delay) / (1 - p.delay);
          // Ease out for fast burst then drift
          const easedProgress = Easing.out(Easing.quad)(
            Math.min(staggered, 1)
          );

          cx = PART.centerX + Math.cos(p.angle) * easedProgress * p.distance;
          cy = PART.centerY + Math.sin(p.angle) * easedProgress * p.distance;

          // Continue drifting during absence beat
          if (frame >= BEATS.ABSENCE_START) {
            const absenceProgress = interpolate(
              frame,
              [BEATS.ABSENCE_START, BEATS.ABSENCE_END],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );
            const drift = absenceProgress * 40;
            cx += Math.cos(p.angle) * drift;
            cy += Math.sin(p.angle) * drift;
          }

          r = p.size * (0.6 + 0.4 * (1 - easedProgress));

          // Color: amber -> gray as dissolve progresses
          const colorProgress = interpolate(
            frame,
            [BEATS.DISSOLVE_START, BEATS.DISSOLVE_END],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          // Interpolate amber (217,148,74) -> gray (136,136,136)
          const rVal = Math.round(217 + (136 - 217) * colorProgress);
          const gVal = Math.round(148 + (136 - 148) * colorProgress);
          const bVal = Math.round(74 + (136 - 74) * colorProgress);
          fillColor = `rgb(${rVal},${gVal},${bVal})`;

          // Opacity: full during dissolve, fade out during absence
          if (frame < BEATS.ABSENCE_START) {
            opacity = interpolate(
              rawProgress,
              [0, 0.1, 0.8, 1],
              [0, 1, 0.7, 0.5],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );
          } else {
            opacity = interpolate(
              frame,
              [BEATS.ABSENCE_START, BEATS.ABSENCE_END],
              [0.5, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );
          }
        } else {
          // Regeneration: particles flow inward from mold direction
          const rawProgress = interpolate(
            frame,
            [BEATS.REGEN_START, BEATS.REGEN_END],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          // Apply per-particle stagger
          const staggered = Math.max(0, rawProgress - p.delay) / (1 - p.delay);
          // Ease in cubic for accelerating toward center
          const easedProgress = Easing.in(Easing.cubic)(
            Math.min(staggered, 1)
          );

          // Start position: offset from part center in mold direction
          const startX =
            PART.centerX +
            Math.cos(p.regenAngle) * p.regenDistance;
          const startY =
            PART.centerY +
            Math.sin(p.regenAngle) * p.regenDistance;

          // Interpolate from start to part center
          cx = startX + (PART.centerX - startX) * easedProgress;
          cy = startY + (PART.centerY - startY) * easedProgress;

          // Size grows as particles converge
          r = p.size * (0.4 + 0.6 * easedProgress);

          // Color: gray -> amber
          const rVal = Math.round(136 + (217 - 136) * easedProgress);
          const gVal = Math.round(136 + (148 - 136) * easedProgress);
          const bVal = Math.round(136 + (74 - 136) * easedProgress);
          fillColor = `rgb(${rVal},${gVal},${bVal})`;

          // Opacity: fade in then solidify
          opacity = interpolate(
            staggered,
            [0, 0.2, 0.8, 1],
            [0, 0.6, 0.9, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
        }

        if (opacity < 0.01) return null;

        return (
          <circle
            key={i}
            cx={cx}
            cy={cy}
            r={r}
            fill={fillColor}
            opacity={opacity}
          />
        );
      })}
    </g>
  );
};
