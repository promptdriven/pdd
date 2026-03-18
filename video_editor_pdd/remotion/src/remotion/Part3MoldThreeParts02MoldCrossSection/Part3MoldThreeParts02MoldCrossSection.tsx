import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { BG_COLOR, TOTAL_FRAMES } from './constants';
import { EngineeringGrid } from './EngineeringGrid';
import { MoldShape } from './MoldShape';
import { RegionHighlight } from './RegionHighlight';
import { SectionTitle, WallLabels, NozzleLabels, CavityLabels } from './Labels';

export const defaultPart3MoldThreeParts02MoldCrossSectionProps = {};

/**
 * 02_mold_cross_section — Three Regions Illuminate
 *
 * A technical cross-section of an injection mold with three sequentially
 * illuminated regions: walls (amber), nozzle (blue), cavity (green).
 *
 * Duration: 300 frames (10s @ 30fps)
 */
export const Part3MoldThreeParts02MoldCrossSection: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Engineering grid background */}
        <EngineeringGrid />

        {/* Mold cross-section draws in (frames 0-40) */}
        <MoldShape />

        {/* Region highlights: walls → nozzle → cavity → all */}
        <RegionHighlight />

        {/* Section title (frames 40+) */}
        <SectionTitle />

        {/* Wall labels with callout arrows (frames 60+) */}
        <WallLabels />

        {/* Nozzle labels (frames 120+) */}
        <NozzleLabels />

        {/* Cavity labels (frames 180+) */}
        <CavityLabels />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts02MoldCrossSection;
