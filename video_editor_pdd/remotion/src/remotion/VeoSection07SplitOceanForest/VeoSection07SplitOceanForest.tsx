import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { VideoPanel } from './VideoPanel';
import { DividerLine } from './DividerLine';
import { SplitLabel } from './SplitLabel';
import { POSITIONS, LABELS } from './constants';
import { useVisualMediaSrc } from '../_shared/visual-runtime';

export const VeoSection07SplitOceanForest: React.FC = () => {
  const leftSrc = useVisualMediaSrc('leftSrc', 'veo/veo_section.mp4');
  const rightSrc = useVisualMediaSrc('rightSrc', leftSrc ?? 'veo/veo_section.mp4');

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Left panel: Forest canopy aerial */}
      {leftSrc ? <VideoPanel src={leftSrc} side="left" /> : null}

      {/* Right panel: Ocean wave sunset */}
      {rightSrc ? <VideoPanel src={rightSrc} side="right" /> : null}

      {/* Vertical divider with glow */}
      <DividerLine />

      {/* Panel labels */}
      <SplitLabel
        text={LABELS.left}
        x={POSITIONS.leftLabelX}
        y={POSITIONS.labelY}
        align="left"
      />
      <SplitLabel
        text={LABELS.right}
        x={POSITIONS.rightLabelX}
        y={POSITIONS.labelY}
        align="right"
      />
    </AbsoluteFill>
  );
};

export const defaultVeoSection07SplitOceanForestProps = {};

export default VeoSection07SplitOceanForest;
