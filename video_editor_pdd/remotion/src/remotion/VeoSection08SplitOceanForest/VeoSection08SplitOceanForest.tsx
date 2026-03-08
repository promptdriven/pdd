import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { DividerWipe } from './DividerWipe';
import { SplitPanel } from './SplitPanel';
import { CenterBadge } from './CenterBadge';

export const VeoSection08SplitOceanForest: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Left panel — ocean sunset recap */}
      <SplitPanel side="left" />

      {/* Right panel — forest canopy recap */}
      <SplitPanel side="right" />

      {/* Vertical divider wiping down */}
      <DividerWipe />

      {/* Center "Veo 3.1" badge */}
      <CenterBadge />
    </AbsoluteFill>
  );
};

export const defaultVeoSection08SplitOceanForestProps = {};

export default VeoSection08SplitOceanForest;
