import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolateColors,
  interpolate,
  Easing,
} from 'remotion';
import { BG_FROM, BG_TO, BG_DARKEN_DURATION } from './constants';
import { ParticleField } from './ParticleField';
import { TriangleGlow } from './TriangleGlow';
import { AnimatedNodes } from './AnimatedNode';
import { CodeLinesFading } from './CodeLines';
import { ThesisText } from './ThesisText';

export const defaultClosing06MoldGlowFinaleProps = {};

export const Closing06MoldGlowFinale: React.FC = () => {
  const frame = useCurrentFrame();

  // Background darkens from #0A1225 → #080E1A over first 60 frames
  const bgProgress = interpolate(frame, [0, BG_DARKEN_DURATION], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.sin),
  });

  const bgColor = interpolateColors(bgProgress, [0, 1], [BG_FROM, BG_TO]);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: bgColor,
      }}
    >
      {/* Particle field — atmospheric upward drift */}
      <ParticleField />

      {/* Code lines inside the triangle — dimming to ghost */}
      <CodeLinesFading />

      {/* Triangle edges with multi-layer glow */}
      <TriangleGlow />

      {/* Three radiant nodes at triangle vertices */}
      <AnimatedNodes />

      {/* Thesis text with horizontal rule */}
      <ThesisText />
    </AbsoluteFill>
  );
};

export default Closing06MoldGlowFinale;
