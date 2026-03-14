import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, PANELS, COLORS, TYPOGRAPHY } from './constants';
import { DividerLine } from './DividerLine';

export const defaultAnimationSection09SplitSummaryProps = {};

export const AnimationSection09SplitSummary: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.background,
        fontFamily: 'sans-serif',
        color: COLORS.text,
      }}
    >
      {/* Split panels */}
      <div style={{ position: 'absolute', inset: 0, display: 'flex' }}>
        {/* Left – Before */}
        <div
          style={{
            flex: 1,
            backgroundColor: PANELS.left.background,
            display: 'flex',
            justifyContent: 'center',
            alignItems: 'center',
          }}
        >
          <div style={{ fontSize: TYPOGRAPHY.panelLabel.fontSize, fontWeight: TYPOGRAPHY.panelLabel.fontWeight }}>
            {PANELS.left.label}
          </div>
        </div>

        {/* Right – After */}
        <div
          style={{
            flex: 1,
            backgroundColor: PANELS.right.background,
            display: 'flex',
            justifyContent: 'center',
            alignItems: 'center',
          }}
        >
          <div style={{ fontSize: TYPOGRAPHY.panelLabel.fontSize, fontWeight: TYPOGRAPHY.panelLabel.fontWeight }}>
            {PANELS.right.label}
          </div>
        </div>
      </div>

      {/* Glowing cyan divider */}
      <DividerLine />

      {/* Title label */}
      <div
        style={{
          position: 'absolute',
          top: 64,
          left: 64,
          fontSize: TYPOGRAPHY.title.fontSize,
          fontWeight: TYPOGRAPHY.title.fontWeight,
        }}
      >
        Split Summary
      </div>
    </AbsoluteFill>
  );
};

export default AnimationSection09SplitSummary;
