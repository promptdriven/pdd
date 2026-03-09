import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { VideoPanel } from './VideoPanel';
import { DividerLine } from './DividerLine';
import { SplitLabel } from './SplitLabel';
import { POSITIONS, LABELS } from './constants';

export const VeoSection07SplitOceanForest: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Left panel: Ocean wave sunset */}
      <VideoPanel src="veo/veo_section.mp4" side="left" />

      {/* Right panel: Forest canopy aerial */}
      <VideoPanel src="veo/veo_section.mp4" side="right" />

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
