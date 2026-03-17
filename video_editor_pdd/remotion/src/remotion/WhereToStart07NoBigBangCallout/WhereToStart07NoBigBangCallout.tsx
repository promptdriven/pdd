import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { CANVAS, COLORS, TYPOGRAPHY, TIMING } from './constants';
import { GhostCodebase } from './GhostCodebase';
import { AnimatedLine } from './AnimatedLine';
import { HorizontalRule } from './HorizontalRule';
import { SpecificationLine } from './SpecificationGlow';

export const defaultWhereToStart07NoBigBangCalloutProps = {};

/**
 * Section 6.7: No Big Bang Callout — Gradual Migration Takeaway
 *
 * A clean text card delivering the section's core takeaway:
 * 1. "One module at a time." — clean, direct
 * 2. "No big bang. No rewrite." — reassuring
 * 3. "A gradual migration of where value lives — from code to specification." — payoff
 *
 * Background: ghostly blurred codebase topology from previous shot.
 * Duration: 150 frames (5s @ 30fps)
 */
export const WhereToStart07NoBigBangCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Line 3 part A fade-in (the "A gradual migration..." line)
  const line3AOpacity = interpolate(
    frame,
    [TIMING.LINE3_START, TIMING.LINE3_START + TIMING.LINE3_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Line 3 part B fade-in (the "from code to specification." line)
  const line3BStart = TIMING.LINE3_START + TIMING.LINE3B_OFFSET;
  const line3BOpacity = interpolate(
    frame,
    [line3BStart, line3BStart + TIMING.LINE3B_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.BACKGROUND,
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Ghost codebase background — blurred topology */}
      <GhostCodebase />

      {/* Line 1: "One module at a time." */}
      <AnimatedLine
        startFrame={TIMING.LINE1_START}
        duration={TIMING.LINE1_DURATION}
        slideDistance={TIMING.LINE1_SLIDE}
        y={TYPOGRAPHY.LINE1.y}
      >
        <span
          style={{
            fontFamily: TYPOGRAPHY.FONT_FAMILY,
            fontSize: TYPOGRAPHY.LINE1.size,
            fontWeight: TYPOGRAPHY.LINE1.weight,
            color: COLORS.TEXT_PRIMARY,
            opacity: TYPOGRAPHY.LINE1.opacity,
            whiteSpace: 'nowrap',
          }}
        >
          One module at a time.
        </span>
      </AnimatedLine>

      {/* Line 2: "No big bang. No rewrite." */}
      <AnimatedLine
        startFrame={TIMING.LINE2_START}
        duration={TIMING.LINE2_DURATION}
        slideDistance={TIMING.LINE2_SLIDE}
        y={TYPOGRAPHY.LINE2.y}
      >
        <span
          style={{
            fontFamily: TYPOGRAPHY.FONT_FAMILY,
            fontSize: TYPOGRAPHY.LINE2.size,
            fontWeight: TYPOGRAPHY.LINE2.weight,
            color: COLORS.TEXT_PRIMARY,
            opacity: TYPOGRAPHY.LINE2.opacity,
            whiteSpace: 'nowrap',
          }}
        >
          No big bang. No rewrite.
        </span>
      </AnimatedLine>

      {/* Horizontal rule — draws from center outward */}
      <HorizontalRule />

      {/* Line 3 part A: "A gradual migration of where value lives —" */}
      <div
        style={{
          position: 'absolute',
          top: TYPOGRAPHY.LINE3A.y,
          left: 0,
          right: 0,
          display: 'flex',
          justifyContent: 'center',
          opacity: line3AOpacity,
        }}
      >
        <span
          style={{
            fontFamily: TYPOGRAPHY.FONT_FAMILY,
            fontSize: TYPOGRAPHY.LINE3A.size,
            fontWeight: TYPOGRAPHY.LINE3A.weight,
            color: COLORS.TEXT_PRIMARY,
            opacity: TYPOGRAPHY.LINE3A.opacity,
            whiteSpace: 'nowrap',
          }}
        >
          A gradual migration of where value lives —
        </span>
      </div>

      {/* Line 3 part B: "from code to specification." with colored keywords */}
      <div
        style={{
          position: 'absolute',
          top: TYPOGRAPHY.LINE3B.y,
          left: 0,
          right: 0,
          display: 'flex',
          justifyContent: 'center',
        }}
      >
        <SpecificationLine opacity={line3BOpacity} />
      </div>
    </AbsoluteFill>
  );
};

export default WhereToStart07NoBigBangCallout;
