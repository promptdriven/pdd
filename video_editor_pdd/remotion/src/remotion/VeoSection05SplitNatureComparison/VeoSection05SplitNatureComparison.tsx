import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { COLORS, resolveSplitNatureComparisonLayout } from './constants';
import { VerticalDivider } from './VerticalDivider';
import { SplitPanel } from './SplitPanel';
import { PanelLabel } from './PanelLabel';

export const VeoSection05SplitNatureComparison: React.FC = () => {
  const { width, height } = useVideoConfig();
  const layout = resolveSplitNatureComparisonLayout(width, height);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Left panel: Ocean sunset */}
      <SplitPanel side="left" videoSrc="veo/ocean_sunset.mp4" layout={layout} />

      {/* Right panel: Forest canopy */}
      <SplitPanel side="right" videoSrc="veo/aerial_forest.mp4" layout={layout} />

      {/* Center divider */}
      <VerticalDivider layout={layout} />

      {/* Panel labels */}
      <PanelLabel text="Ocean at Sunset" side="left" layout={layout} />
      <PanelLabel text="Forest Canopy" side="right" layout={layout} />
    </AbsoluteFill>
  );
};

export const defaultVeoSection05SplitNatureComparisonProps = {};

export default VeoSection05SplitNatureComparison;
