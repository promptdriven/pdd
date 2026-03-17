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
  PARTICLE_DRIFT_DURATION,
  WIDTH,
  HEIGHT,
} from './constants';

/**
 * A single particle that drifts upward through the ghost triangle center,
 * catching a brief glint as it passes through the triangle's center point.
 * This component expects to be placed inside a <Sequence from={30}>.
 */
export const SingleParticle: React.FC = () => {
  const frame = useCurrentFrame();

  // Linear vertical drift from start to end over drift duration
  const y = interpolate(frame, [0, PARTICLE_DRIFT_DURATION], [PARTICLE_START[1], PARTICLE_END[1]], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const x = PARTICLE_START[0]; // Straight vertical path

  // Calculate the frame when particle reaches glint Y (center of triangle)
  // The particle travels from 650 to 350, total = 300px over 90 frames
  const totalDistance = PARTICLE_START[1] - PARTICLE_END[1]; // 300
  const glintDistance = PARTICLE_START[1] - PARTICLE_GLINT_Y; // 130
  const glintFrame = (glintDistance / totalDistance) * PARTICLE_DRIFT_DURATION; // ~39

  const halfGlint = PARTICLE_GLINT_DURATION / 2; // 3 frames

  // Glint opacity: spike from base to peak and back
  const glintOpacity = interpolate(
    frame,
    [
      glintFrame - halfGlint,
      glintFrame,
      glintFrame + halfGlint,
    ],
    [PARTICLE_BASE_OPACITY, PARTICLE_GLINT_PEAK_OPACITY, PARTICLE_BASE_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Fade out as particle approaches top
  const fadeOut = interpolate(frame, [PARTICLE_DRIFT_DURATION - 30, PARTICLE_DRIFT_DURATION], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Fade in at the start
  const fadeIn = interpolate(frame, [0, 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const opacity = glintOpacity * fadeOut * fadeIn;

  // Don't render after drift is complete
  if (frame > PARTICLE_DRIFT_DURATION + 5) return null;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
      }}
    >
      <circle
        cx={x}
        cy={y}
        r={PARTICLE_SIZE}
        fill={PARTICLE_COLOR}
        opacity={opacity}
      />
    </svg>
  );
};

export default SingleParticle;
