// Closing08MoldIsWhatMatters.tsx — Final thesis: "The mold is what matters."
// Triangle reignites from darkness, thesis text fades in.
import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  NODES,
  THESIS_TEXT,
  THESIS_FONT_SIZE,
  THESIS_FONT_WEIGHT,
  THESIS_COLOR,
  THESIS_OPACITY,
  THESIS_LETTER_SPACING,
  THESIS_Y,
  THESIS_FADE_START,
  THESIS_FADE_DURATION,
  TOTAL_FRAMES,
  WIDTH,
} from './constants';
import { TriangleEdges } from './TriangleEdges';
import { AnimatedNode } from './AnimatedNode';

export const defaultClosing08MoldIsWhatMattersProps = {};

const ThesisText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, THESIS_FADE_DURATION],
    [0, THESIS_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: THESIS_Y - THESIS_FONT_SIZE,
        left: 0,
        width: WIDTH,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        pointerEvents: 'none',
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: THESIS_FONT_SIZE,
          fontWeight: THESIS_FONT_WEIGHT,
          color: THESIS_COLOR,
          opacity,
          letterSpacing: THESIS_LETTER_SPACING,
          textAlign: 'center',
        }}
      >
        {THESIS_TEXT}
      </span>
    </div>
  );
};

export const Closing08MoldIsWhatMatters: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Triangle edges — reigniting with glow */}
      <TriangleEdges />

      {/* Nodes — reigniting to peak brightness, then pulsing */}
      {NODES.map((node) => (
        <AnimatedNode
          key={node.label}
          center={node.center}
          fillColor={node.fillColor}
          glowColor={node.glowColor}
          glowOpacity={node.glowOpacity}
        />
      ))}

      {/* No code at center — intentionally empty. The mold stands alone. */}

      {/* Thesis text — fades in starting at frame 80 */}
      <Sequence from={THESIS_FADE_START} durationInFrames={TOTAL_FRAMES - THESIS_FADE_START}>
        <ThesisText />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Closing08MoldIsWhatMatters;
