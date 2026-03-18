import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame } from 'remotion';
import { CANVAS, TIMING } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { GhostShapes } from './GhostShapes';
import {
  SectionLabel,
  TitleLine1,
  HorizontalRule,
  TitleLine2,
} from './TitleText';

export const defaultPart3MoldThreeParts01SectionTitleCardProps = {};

export const Part3MoldThreeParts01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fades in from black over first 15 frames
  const bgOpacity = interpolate(frame, [0, TIMING.BG_FADE_END], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: '#000000',
      }}
    >
      <AbsoluteFill
        style={{
          backgroundColor: CANVAS.BG_COLOR,
          opacity: bgOpacity,
        }}
      >
        {/* Blueprint grid background */}
        <BlueprintGrid />

        {/* Three ghost shapes — wall, nozzle, material */}
        <GhostShapes />

        {/* "PART 3" section label */}
        <SectionLabel />

        {/* "THE MOLD HAS" typewriter */}
        <TitleLine1 />

        {/* Horizontal divider rule */}
        <HorizontalRule />

        {/* "THREE PARTS" slide-up */}
        <TitleLine2 />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts01SectionTitleCard;
