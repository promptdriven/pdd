import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { COLORS, resolveSplitNatureComparisonLayout } from './constants';
import { HeaderText } from './HeaderText';
import { SplitPanel } from './SplitPanel';
import { VerticalDivider } from './VerticalDivider';
import { PanelLabel } from './PanelLabel';
import { useVisualMediaSrc } from '../_shared/visual-runtime';

export const VeoSection05SplitNatureComparison: React.FC = () => {
  const { width, height } = useVideoConfig();
  const layout = resolveSplitNatureComparisonLayout(width, height);

  const defaultSrc = useVisualMediaSrc('defaultSrc', 'veo/veo_section.mp4');
  const leftSrc = useVisualMediaSrc('leftSrc', defaultSrc ?? 'veo/veo_section.mp4');
  const rightSrc = useVisualMediaSrc(
    'rightSrc',
    leftSrc ?? defaultSrc ?? 'veo/veo_section.mp4',
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Header */}
      <HeaderText layout={layout} />

      {/* Left panel: Ocean sunset */}
      {leftSrc ? (
        <SplitPanel side="left" videoSrc={leftSrc} layout={layout} />
      ) : null}

      {/* Right panel: Forest canopy */}
      {rightSrc ? (
        <SplitPanel side="right" videoSrc={rightSrc} layout={layout} />
      ) : null}

      {/* Glowing center divider */}
      <VerticalDivider layout={layout} />

      {/* Panel labels */}
      <PanelLabel text="OCEAN — Sunset" side="left" layout={layout} />
      <PanelLabel text="FOREST — Canopy" side="right" layout={layout} />
    </AbsoluteFill>
  );
};

export const defaultVeoSection05SplitNatureComparisonProps = {};

export default VeoSection05SplitNatureComparison;
