import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing, Sequence } from 'remotion';
import { CANVAS, GRID } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { NetworkGraph } from './NetworkGraph';
import { SectionLabel, TitleLine1, HorizontalRule, TitleLine2 } from './TitleText';

export const defaultWhereToStart01SectionTitleCardProps = {};

export const WhereToStart01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fades in from black over frames 0-15
  const bgOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(2)),
  });

  // Grid appears with background
  const gridOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(2)),
  });

  return (
    <AbsoluteFill style={{ backgroundColor: '#000000' }}>
      {/* Main content fades in from black */}
      <AbsoluteFill style={{ opacity: bgOpacity, backgroundColor: CANVAS.backgroundColor }}>
        {/* Blueprint grid */}
        <div style={{ opacity: gridOpacity }}>
          <BlueprintGrid
            spacing={GRID.spacing}
            color={GRID.color}
            opacity={GRID.opacity}
            canvasWidth={CANVAS.width}
            canvasHeight={CANVAS.height}
          />
        </div>

        {/* Ghost codebase topology — starts drawing at frame 15 */}
        <Sequence from={15}>
          <NetworkGraph />
        </Sequence>

        {/* Section label */}
        <SectionLabel />

        {/* Title line 1: "WHERE TO" — typewriter from frame 40 */}
        <TitleLine1 />

        {/* Horizontal rule — draws from center at frame 60 */}
        <HorizontalRule />

        {/* Title line 2: "START" — fade+slide from frame 70 */}
        <TitleLine2 />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default WhereToStart01SectionTitleCard;
