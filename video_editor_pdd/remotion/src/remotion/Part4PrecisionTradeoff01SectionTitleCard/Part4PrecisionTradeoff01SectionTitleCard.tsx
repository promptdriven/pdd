import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { CANVAS, TIMING } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { StaggerDots } from './StaggerDots';
import { MoldOutline } from './MoldOutline';
import {
  TypewriterText,
  SlideUpText,
  SectionLabel,
  HorizontalRule,
} from './TitleText';

export const defaultPart4PrecisionTradeoff01SectionTitleCardProps = {};

export const Part4PrecisionTradeoff01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade from black over first 15 frames
  const bgOpacity = interpolate(
    frame,
    [TIMING.BG_FADE_START, TIMING.BG_FADE_END],
    [0, 1],
    {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: '#000000',
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
      }}
    >
      {/* Main content fading in over background */}
      <AbsoluteFill style={{ opacity: bgOpacity }}>
        {/* Deep navy-black background */}
        <AbsoluteFill style={{ backgroundColor: CANVAS.BACKGROUND }} />

        {/* Blueprint grid */}
        <BlueprintGrid opacity={bgOpacity} />

        {/* SVG overlay for all animated elements */}
        <AbsoluteFill>
          <svg
            width={CANVAS.WIDTH}
            height={CANVAS.HEIGHT}
            viewBox={`0 0 ${CANVAS.WIDTH} ${CANVAS.HEIGHT}`}
            style={{ position: 'absolute', top: 0, left: 0 }}
          >
            {/* Ghost shapes — coordinate grid (left) and mold outline (right) */}
            <StaggerDots startFrame={TIMING.GHOST_START} />
            <MoldOutline startFrame={TIMING.GHOST_START} />

            {/* Section label "PART 4" */}
            <SectionLabel startFrame={TIMING.SECTION_LABEL_START} />

            {/* Title line 1: "THE PRECISION" typewriter */}
            <TypewriterText startFrame={TIMING.TITLE_LINE1_START} />

            {/* Horizontal rule between title lines */}
            <HorizontalRule startFrame={TIMING.RULE_START} />

            {/* Title line 2: "TRADEOFF" slide-up + fade */}
            <SlideUpText startFrame={TIMING.TITLE_LINE2_START} />
          </svg>
        </AbsoluteFill>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff01SectionTitleCard;
