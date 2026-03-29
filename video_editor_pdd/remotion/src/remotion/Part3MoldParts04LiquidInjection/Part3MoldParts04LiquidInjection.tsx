import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import {
  BG_COLOR,
  DURATION_FRAMES,
  ANNOTATIONS,
} from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { LiquidFlow } from './LiquidFlow';
import { ResearchAnnotation } from './ResearchAnnotation';
import { FocusZoom, FocusWallHighlight } from './FocusZoom';

export const defaultPart3MoldParts04LiquidInjectionProps = {};

export const Part3MoldParts04LiquidInjection: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Main scene — zoom effect wraps mold + liquid */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <FocusZoom>
          {/* Mold cross-section with walls */}
          <MoldCrossSection />

          {/* Liquid injection animation */}
          <LiquidFlow />

          {/* Focus wall highlight (pulse, extra glow) */}
          <FocusWallHighlight />
        </FocusZoom>
      </Sequence>

      {/* Research annotations — positioned outside the zoom transform */}
      {ANNOTATIONS.map((ann, i) => (
        <Sequence key={i} from={0} durationInFrames={DURATION_FRAMES}>
          <ResearchAnnotation
            text={ann.text}
            source={ann.source}
            textColor={ann.color}
            posX={ann.posX}
            posY={ann.posY}
            frameIn={ann.frameIn}
          />
        </Sequence>
      ))}
    </AbsoluteFill>
  );
};

export default Part3MoldParts04LiquidInjection;
