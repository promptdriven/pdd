import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { DividerWipe } from './DividerWipe';
import { SplitPanel } from './SplitPanel';
import { CenterBadge } from './CenterBadge';

export const VeoSection06SplitOceanForest: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Left panel — ocean sunset */}
      <SplitPanel side="left" />

      {/* Right panel — forest canopy */}
      <SplitPanel side="right" />

      {/* Vertical divider wiping down */}
      <DividerWipe />

      {/* Center "Veo 3.1" badge */}
      <CenterBadge />
    </AbsoluteFill>
  );
};

export const defaultVeoSection06SplitOceanForestProps = {};

export default VeoSection06SplitOceanForest;
