import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { CANVAS, TIMING } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { NetworkGraph } from './NetworkGraph';
import {
  TypewriterTitle,
  SlideUpTitle,
  SectionLabel,
  HorizontalRule,
} from './TitleText';

export const defaultWhereToStart01SectionTitleCardProps = {};

export const WhereToStart01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade from black over first 15 frames
  const bgOpacity = interpolate(
    frame,
    [TIMING.BG_FADE_START, TIMING.BG_FADE_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#000000' }}>
      {/* Main content with fade-in */}
      <AbsoluteFill style={{ opacity: bgOpacity, backgroundColor: CANVAS.BG }}>
        {/* Blueprint grid */}
        <BlueprintGrid opacity={bgOpacity} />

        {/* Ghost codebase topology — starts at frame 15 */}
        <Sequence from={TIMING.TOPOLOGY_START} layout="none">
          <NetworkGraph />
        </Sequence>

        {/* Section label — starts at frame 15 */}
        <Sequence from={TIMING.LABEL_START} layout="none">
          <SectionLabel />
        </Sequence>

        {/* Title line 1: "WHERE TO" typewriter — starts at frame 40 */}
        <Sequence from={TIMING.TITLE_LINE1_START} layout="none">
          <TypewriterTitle />
        </Sequence>

        {/* Horizontal rule — starts at frame 60 */}
        <Sequence from={TIMING.RULE_START} layout="none">
          <HorizontalRule />
        </Sequence>

        {/* Title line 2: "START" slide-up — starts at frame 70 */}
        <Sequence from={TIMING.TITLE_LINE2_START} layout="none">
          <SlideUpTitle />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default WhereToStart01SectionTitleCard;
