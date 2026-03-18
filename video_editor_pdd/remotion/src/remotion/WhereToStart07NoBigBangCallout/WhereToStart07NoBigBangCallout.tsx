import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, COLORS, TIMING } from './constants';
import { GhostCodebase } from './GhostCodebase';
import { AnimatedLine } from './AnimatedLine';
import { HorizontalRule } from './HorizontalRule';
import { Line3Rich } from './Line3Rich';

export const defaultWhereToStart07NoBigBangCalloutProps = {};

/**
 * WhereToStart07NoBigBangCallout
 *
 * A clean text card delivering the section's core takeaway about gradual migration.
 * Three lines appear sequentially over a ghosted codebase topology background.
 *
 * Duration: 150 frames (5s @ 30fps)
 */
export const WhereToStart07NoBigBangCallout: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.BG,
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Ghost codebase background — blurred topology at very low opacity */}
      <GhostCodebase />

      {/* Line 1: "One module at a time." */}
      <AnimatedLine
        text="One module at a time."
        startFrame={TIMING.LINE1_START}
        duration={TIMING.LINE1_DURATION}
        slideDistance={8}
        fontSize={28}
        fontWeight={600}
        color={COLORS.TEXT_PRIMARY}
        opacity={0.8}
        y={380}
      />

      {/* Line 2: "No big bang. No rewrite." */}
      <AnimatedLine
        text="No big bang. No rewrite."
        startFrame={TIMING.LINE2_START}
        duration={TIMING.LINE2_DURATION}
        slideDistance={6}
        fontSize={22}
        fontWeight={400}
        color={COLORS.TEXT_PRIMARY}
        opacity={0.5}
        y={430}
      />

      {/* Horizontal rule separating tactical from conceptual */}
      <HorizontalRule />

      {/* Line 3: Rich text with "code" in gray and "specification" in blue */}
      <Line3Rich />
    </AbsoluteFill>
  );
};

export default WhereToStart07NoBigBangCallout;
