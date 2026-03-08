import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TYPOGRAPHY, TIMING } from './constants';
import { NoiseOverlay } from './NoiseOverlay';
import { AnimatedDivider } from './AnimatedDivider';

export const AnimationSection06SplitSummary: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel fade-in: frames 0-15
  const panelOpacity = interpolate(
    frame,
    [TIMING.panelFadeStart, TIMING.panelFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // "Before" text fade-in: frames 15-30
  const beforeTextOpacity = interpolate(
    frame,
    [TIMING.beforeTextStart, TIMING.beforeTextEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // "After" text fade-in: frames 20-35
  const afterTextOpacity = interpolate(
    frame,
    [TIMING.afterTextStart, TIMING.afterTextEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Right panel animated gradient hue shift: 0-15deg over full duration
  const hueRotation = interpolate(frame, [0, TIMING.totalDuration], [0, 15], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Split panels container */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          display: 'flex',
          opacity: panelOpacity,
        }}
      >
        {/* Left panel — "Before" */}
        <div
          style={{
            position: 'relative',
            width: CANVAS.width / 2,
            height: CANVAS.height,
            backgroundColor: COLORS.leftPanel,
            overflow: 'hidden',
          }}
        >
          <NoiseOverlay opacity={0.03} />
          <div
            style={{
              position: 'absolute',
              top: '50%',
              left: '50%',
              transform: 'translate(-50%, -50%)',
              fontSize: TYPOGRAPHY.panelLabel.fontSize,
              fontFamily: TYPOGRAPHY.panelLabel.fontFamily,
              fontWeight: TYPOGRAPHY.panelLabel.fontWeight,
              color: COLORS.text,
              opacity: beforeTextOpacity,
              whiteSpace: 'nowrap',
            }}
          >
            Before
          </div>
        </div>

        {/* Right panel — "After" */}
        <div
          style={{
            position: 'relative',
            width: CANVAS.width / 2,
            height: CANVAS.height,
            backgroundColor: COLORS.rightPanel,
            overflow: 'hidden',
            filter: `hue-rotate(${hueRotation}deg)`,
          }}
        >
          <div
            style={{
              position: 'absolute',
              top: '50%',
              left: '50%',
              transform: 'translate(-50%, -50%)',
              fontSize: TYPOGRAPHY.panelLabel.fontSize,
              fontFamily: TYPOGRAPHY.panelLabel.fontFamily,
              fontWeight: TYPOGRAPHY.panelLabel.fontWeight,
              color: COLORS.text,
              opacity: afterTextOpacity,
              whiteSpace: 'nowrap',
            }}
          >
            After
          </div>
        </div>
      </div>

      {/* Animated vertical divider */}
      <AnimatedDivider />

      {/* Heading */}
      <div
        style={{
          position: 'absolute',
          top: 64,
          left: 64,
          fontSize: TYPOGRAPHY.heading.fontSize,
          fontFamily: TYPOGRAPHY.heading.fontFamily,
          fontWeight: TYPOGRAPHY.heading.fontWeight,
          color: COLORS.text,
          zIndex: 20,
        }}
      >
        Split Summary
      </div>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06SplitSummaryProps = {};

export default AnimationSection06SplitSummary;
