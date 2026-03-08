import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, RINGS } from './constants';
import { RadialLines } from './RadialLines';
import { PulsingDot } from './PulsingDot';
import { ExpandingRing } from './ExpandingRing';
import { OrbitLabels } from './OrbitLabels';

export const AnimationSection02IntroDataPulse: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Static radial lines from center */}
      <RadialLines />

      {/* Central pulsing dot */}
      <PulsingDot />

      {/* Three expanding concentric rings */}
      {RINGS.map((ring, i) => (
        <ExpandingRing
          key={i}
          targetRadius={ring.radius}
          strokeColor={ring.color}
          ringOpacity={ring.opacity}
          startFrame={ring.startFrame}
          endFrame={ring.endFrame}
        />
      ))}

      {/* Orbiting text labels */}
      <OrbitLabels />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection02IntroDataPulseProps = {};

export default AnimationSection02IntroDataPulse;
