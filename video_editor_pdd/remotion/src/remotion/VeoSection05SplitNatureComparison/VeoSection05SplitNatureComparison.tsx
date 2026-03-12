import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { VerticalDivider } from './VerticalDivider';
import { SplitPanel } from './SplitPanel';
import { PanelLabel } from './PanelLabel';

export const VeoSection05SplitNatureComparison: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Left panel: Ocean sunset */}
      <SplitPanel side="left" videoSrc="veo/ocean_sunset.mp4" />

      {/* Right panel: Forest canopy */}
      <SplitPanel side="right" videoSrc="veo/aerial_forest.mp4" />

      {/* Center divider */}
      <VerticalDivider />

      {/* Panel labels */}
      <PanelLabel text="Ocean at Sunset" side="left" />
      <PanelLabel text="Forest Canopy" side="right" />
    </AbsoluteFill>
  );
};

export const defaultVeoSection05SplitNatureComparisonProps = {};

export default VeoSection05SplitNatureComparison;
