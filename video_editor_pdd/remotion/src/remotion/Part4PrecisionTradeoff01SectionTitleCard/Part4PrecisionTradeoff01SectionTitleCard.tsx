import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, COLORS } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { StaggerDots } from './StaggerDots';
import { MoldOutline } from './MoldOutline';
import { SectionLabel, TitleLine1, HorizontalRule, TitleLine2 } from './TitleText';

export const defaultPart4PrecisionTradeoff01SectionTitleCardProps = {};

export const Part4PrecisionTradeoff01SectionTitleCard: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Background grid fading in */}
      <BlueprintGrid />

      {/* Ghost shapes — precision paradigms foreshadowed */}
      <StaggerDots />
      <MoldOutline />

      {/* Section label */}
      <SectionLabel />

      {/* Title: THE PRECISION (typewriter) */}
      <TitleLine1 />

      {/* Horizontal rule between title lines */}
      <HorizontalRule />

      {/* Title: TRADEOFF (fade + slide up) */}
      <TitleLine2 />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff01SectionTitleCard;
