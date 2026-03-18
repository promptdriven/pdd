import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
} from 'remotion';
import {
  BG_COLOR,
  LINE1_START,
  LINE1_Y,
  LINE2_START,
  LINE2_Y,
  LINE3_START,
  LINE3_Y,
} from './constants';
import { StaggeredLine } from './StaggeredLine';
import { InverseAnimation } from './InverseAnimation';

export const defaultPart4PrecisionTradeoff06TakeawayCalloutProps = {};

export const Part4PrecisionTradeoff06TakeawayCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Initial fade-in of background (frames 0-15)
  const bgOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: bgOpacity,
      }}
    >
      {/* Line 1: "The more walls you have," */}
      <StaggeredLine lineStart={LINE1_START} y={LINE1_Y} lineIndex={0} />

      {/* Line 2: "the less you need to specify." */}
      <StaggeredLine lineStart={LINE2_START} y={LINE2_Y} lineIndex={1} />

      {/* Line 3: "The mold does the precision work." */}
      <StaggeredLine lineStart={LINE3_START} y={LINE3_Y} lineIndex={2} />

      {/* Mini inverse animation: prompt shrinks, walls multiply */}
      <InverseAnimation />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff06TakeawayCallout;
