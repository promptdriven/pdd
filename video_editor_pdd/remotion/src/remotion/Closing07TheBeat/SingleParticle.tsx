import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PARTICLE_START,
  PARTICLE_END,
  PARTICLE_SIZE,
  PARTICLE_COLOR,
  PARTICLE_BASE_OPACITY,
  PARTICLE_GLINT_Y,
  PARTICLE_GLINT_PEAK_OPACITY,
  PARTICLE_GLINT_DURATION,
} from './constants';

/**
 * A single particle that drifts upward through the ghost triangle center.
 * Starts at frame 30 (handled by parent Sequence), runs for 90 frames.
 * Brief glint when passing through triangle center at y=520.
 */
export const SingleParticle: React.FC = () => {
  const frame = useCurrentFrame(); // 0-based relative to Sequence from={30}
  const driftDuration = 90;

  // Linear vertical drift
  const y = interpolate(frame, [0, driftDuration], [PARTICLE_START[1], PARTICLE_END[1]], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const x = PARTICLE_START[0]; // Straight vertical path

  // Calculate the frame at which particle passes through glint Y
  // Linear mapping: glintFrame = driftDuration * (startY - glintY) / (startY - endY)
  const glintFrame =
    driftDuration *
    (PARTICLE_START[1] - PARTICLE_GLINT_Y) /
    (PARTICLE_START[1] - PARTICLE_END[1]);
  const halfGlint = PARTICLE_GLINT_DURATION / 2;

  // Base opacity — fades in at start, fades out at end
  const baseOpacity = interpolate(
    frame,
    [0, 8, driftDuration - 20, driftDuration],
    [0, PARTICLE_BASE_OPACITY, PARTICLE_BASE_OPACITY, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Glint — opacity spike when passing through center
  const glintOpacity = (() => {
    const glintStart = glintFrame - halfGlint;
    const glintEnd = glintFrame + halfGlint;

    if (frame < glintStart || frame > glintEnd) return 0;

    if (frame <= glintFrame) {
      // Rising: easeOut(quad)
      return interpolate(frame, [glintStart, glintFrame], [0, PARTICLE_GLINT_PEAK_OPACITY - PARTICLE_BASE_OPACITY], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      });
    } else {
      // Falling: easeIn(quad)
      return interpolate(frame, [glintFrame, glintEnd], [PARTICLE_GLINT_PEAK_OPACITY - PARTICLE_BASE_OPACITY, 0], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.quad),
      });
    }
  })();

  const opacity = Math.min(1, baseOpacity + glintOpacity);

  if (opacity < 0.001) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - PARTICLE_SIZE,
        top: y - PARTICLE_SIZE,
        width: PARTICLE_SIZE * 2,
        height: PARTICLE_SIZE * 2,
        borderRadius: '50%',
        backgroundColor: PARTICLE_COLOR,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};

export default SingleParticle;
