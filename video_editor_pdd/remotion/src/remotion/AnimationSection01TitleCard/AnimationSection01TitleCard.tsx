import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';
import { TitleText } from './TitleText';
import { AccentLine } from './AccentLine';
import { SubtitleText } from './SubtitleText';

export const AnimationSection01TitleCard: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Frame 0-15: Title fades in and scales up */}
      <Sequence from={ANIMATION_TIMING.titleFadeStart} durationInFrames={ANIMATION_TIMING.totalDuration}>
        <TitleText />
      </Sequence>

      {/* Frame 9-24: Accent line expands outward from center */}
      <Sequence from={ANIMATION_TIMING.accentLineStart} durationInFrames={ANIMATION_TIMING.totalDuration - ANIMATION_TIMING.accentLineStart}>
        <AccentLine />
      </Sequence>

      {/* Frame 15-30: Subtitle fades in */}
      <Sequence from={ANIMATION_TIMING.subtitleFadeStart} durationInFrames={ANIMATION_TIMING.totalDuration - ANIMATION_TIMING.subtitleFadeStart}>
        <SubtitleText />
      </Sequence>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection01TitleCardProps = {};

export default AnimationSection01TitleCard;
