import React from 'react';
import { AbsoluteFill, useCurrentFrame, Easing, interpolate } from 'remotion';
import { TriangleEdges } from './TriangleEdges';
import { AnimatedNode } from './AnimatedNode';
import {
  BG_COLOR,
  WIDTH,
  HEIGHT,
  TRIANGLE_VERTICES,
  PROMPT_FILL,
  PROMPT_GLOW,
  TESTS_FILL,
  TESTS_GLOW,
  GROUNDING_FILL,
  GROUNDING_GLOW,
  TEXT_COLOR,
  THESIS_TEXT,
  THESIS_FONT_SIZE,
  THESIS_FONT_WEIGHT,
  THESIS_TEXT_OPACITY,
  THESIS_LETTER_SPACING,
  THESIS_Y,
  THESIS_TEXT_START,
  THESIS_TEXT_FADE_DURATION,
} from './constants';

export const defaultClosing08MoldIsWhatMattersProps = {};

export const Closing08MoldIsWhatMatters: React.FC = () => {
  const frame = useCurrentFrame();

  // Thesis text fades in starting at frame 80
  const thesisOpacity = interpolate(
    frame,
    [THESIS_TEXT_START, THESIS_TEXT_START + THESIS_TEXT_FADE_DURATION],
    [0, THESIS_TEXT_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
      }}
    >
      {/* SVG canvas for the triangle and nodes */}
      <svg
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
        }}
      >
        {/* Triangle edges with glow */}
        <TriangleEdges />

        {/* Three nodes at vertices */}
        {/* PROMPT — top */}
        <AnimatedNode
          cx={TRIANGLE_VERTICES[0][0]}
          cy={TRIANGLE_VERTICES[0][1]}
          fillColor={PROMPT_FILL}
          glowColor={PROMPT_GLOW}
        />
        {/* TESTS — bottom-left */}
        <AnimatedNode
          cx={TRIANGLE_VERTICES[1][0]}
          cy={TRIANGLE_VERTICES[1][1]}
          fillColor={TESTS_FILL}
          glowColor={TESTS_GLOW}
        />
        {/* GROUNDING — bottom-right */}
        <AnimatedNode
          cx={TRIANGLE_VERTICES[2][0]}
          cy={TRIANGLE_VERTICES[2][1]}
          fillColor={GROUNDING_FILL}
          glowColor={GROUNDING_GLOW}
        />
      </svg>

      {/* Thesis text — centered below the triangle */}
      <div
        style={{
          position: 'absolute',
          top: THESIS_Y,
          left: 0,
          width: '100%',
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          opacity: thesisOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, system-ui, -apple-system, sans-serif',
            fontSize: THESIS_FONT_SIZE,
            fontWeight: THESIS_FONT_WEIGHT,
            color: TEXT_COLOR,
            letterSpacing: THESIS_LETTER_SPACING,
            userSelect: 'none',
          }}
        >
          {THESIS_TEXT}
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default Closing08MoldIsWhatMatters;
