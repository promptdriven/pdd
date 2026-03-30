// Part1Economics13CrossingLinesMoment.tsx
// Section 1.13: The Crossing Lines Moment — "We Are Here"
// ~12s (360 frames @ 30fps) — The blue "cost to generate" line crosses below
// both amber cost lines. "We are here." label appears at the crossing.

import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BACKGROUND_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  FONT_FAMILY,
  LINE_GENERATE_COLOR,
  LINE_TOTAL_COST_COLOR,
  LINE_IMMEDIATE_PATCH_COLOR,
  CROSSING_FLASH_COLOR,
  GENERATE_LINE_POINTS,
  TOTAL_COST_LINE_POINTS,
  IMMEDIATE_PATCH_LINE_POINTS,
  CROSSING_1_X,
  CROSSING_1_Y,
  CROSSING_2_X,
  CROSSING_2_Y,
  FLASH1_FRAME,
  FLASH2_FRAME,
  FLASH_DURATION,
  PHASE_LABEL_START,
  PHASE_LABEL_END,
  PHASE_ESTABLISH_END,
  PHASE_CROSS2_END,
} from './constants';
import { ChartAxes } from './ChartAxes';
import { AnimatedLine } from './AnimatedLine';
import { RadialFlash } from './RadialFlash';
import { WeAreHereLabel } from './WeAreHereLabel';

export const defaultPart1Economics13CrossingLinesMomentProps = {};

/**
 * Part1Economics13CrossingLinesMoment
 *
 * Returns to the code cost chart for the climactic crossing moment.
 * The blue "cost to generate" line plunges below both amber cost lines.
 * A "We are here." label appears with a connector to the second crossing.
 */
export const Part1Economics13CrossingLinesMoment: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Amber lines: static lines drawn progressively during establish phase (0-60) ──
  // They're "already on chart" so we draw them quickly at start

  // ── Blue line: split into two parts ──
  // Part 1: the portion above amber lines (drawn during establish, frames 0-60)
  //   Points from index 0 to 5 (year 2020 → 2024.8, cost 95 → 28)
  const generateEstablishedPoints = GENERATE_LINE_POINTS.slice(0, 6);

  // Part 2: the descent through crossings (drawn frames 60-180)
  //   The full line, animated from index 5 onward
  const generateFullPoints = GENERATE_LINE_POINTS;

  // ── Establish phase opacity for the whole chart (subtle fade-in at very start) ──
  const chartOpacity = interpolate(frame, [0, 15], [0.7, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: 'hidden',
        fontFamily: FONT_FAMILY,
      }}
    >
      <div style={{ opacity: chartOpacity, width: '100%', height: '100%' }}>
        {/* Base chart: axes, grid, labels, legend */}
        <ChartAxes />

        {/* ── Amber dashed line (total cost with debt) — draws in during establish ── */}
        <AnimatedLine
          data={TOTAL_COST_LINE_POINTS}
          color={LINE_TOTAL_COST_COLOR}
          strokeWidth={2}
          drawStart={0}
          drawDuration={PHASE_ESTABLISH_END}
          dashed
        />

        {/* ── Amber solid line (immediate patch cost) — draws in during establish ── */}
        <AnimatedLine
          data={IMMEDIATE_PATCH_LINE_POINTS}
          color={LINE_IMMEDIATE_PATCH_COLOR}
          strokeWidth={3}
          drawStart={0}
          drawDuration={PHASE_ESTABLISH_END}
        />

        {/* ── Blue line: established portion (above amber, drawn during 0-60) ── */}
        <AnimatedLine
          data={generateEstablishedPoints}
          color={LINE_GENERATE_COLOR}
          strokeWidth={3}
          drawStart={0}
          drawDuration={PHASE_ESTABLISH_END}
        />

        {/* ── Blue line: full descent (continues from established, animated 60-180) ── */}
        <AnimatedLine
          data={generateFullPoints}
          color={LINE_GENERATE_COLOR}
          strokeWidth={3}
          drawStart={PHASE_ESTABLISH_END}
          drawDuration={PHASE_CROSS2_END - PHASE_ESTABLISH_END}
          revealFromIndex={5}
        />

        {/* ── Crossing flash 1: where blue crosses total cost dashed line ── */}
        <RadialFlash
          cx={CROSSING_1_X}
          cy={CROSSING_1_Y}
          maxRadius={24}
          startFrame={FLASH1_FRAME}
          duration={FLASH_DURATION}
          color={CROSSING_FLASH_COLOR}
        />

        {/* ── Crossing flash 2: where blue crosses immediate patch solid line ── */}
        <RadialFlash
          cx={CROSSING_2_X}
          cy={CROSSING_2_Y}
          maxRadius={18}
          startFrame={FLASH2_FRAME}
          duration={FLASH_DURATION}
          color={CROSSING_FLASH_COLOR}
        />

        {/* ── "We are here." label with connector ── */}
        <WeAreHereLabel
          targetX={CROSSING_2_X}
          targetY={CROSSING_2_Y}
          fadeInStart={PHASE_LABEL_START}
          fadeInDuration={PHASE_LABEL_END - PHASE_LABEL_START}
        />

        {/* ── Subtle vignette overlay for depth ── */}
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: CANVAS_WIDTH,
            height: CANVAS_HEIGHT,
            background:
              'radial-gradient(ellipse at center, transparent 50%, rgba(0,0,0,0.3) 100%)',
            pointerEvents: 'none',
          }}
        />
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics13CrossingLinesMoment;
