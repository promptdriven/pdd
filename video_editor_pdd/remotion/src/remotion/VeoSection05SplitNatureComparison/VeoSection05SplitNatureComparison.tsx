import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { COLORS, resolveSplitNatureComparisonLayout } from './constants';
import { VerticalDivider } from './VerticalDivider';
import { SplitPanel } from './SplitPanel';
import { PanelLabel } from './PanelLabel';
import { useVisualMediaSrc } from '../_shared/visual-runtime';

export const VeoSection05SplitNatureComparison: React.FC = () => {
  const { width, height } = useVideoConfig();
  const layout = resolveSplitNatureComparisonLayout(width, height);
  const defaultSrc = useVisualMediaSrc('defaultSrc', 'veo/veo_section.mp4');
  const leftSrc = useVisualMediaSrc('leftSrc', defaultSrc ?? 'veo/veo_section.mp4');
  const rightSrc = useVisualMediaSrc(
    'rightSrc',
    leftSrc ?? defaultSrc ?? 'veo/veo_section.mp4'
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Left panel: Ocean sunset */}
      {leftSrc ? <SplitPanel side="left" videoSrc={leftSrc} layout={layout} /> : null}

      {/* Right panel: Forest canopy */}
      {rightSrc ? <SplitPanel side="right" videoSrc={rightSrc} layout={layout} /> : null}

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
