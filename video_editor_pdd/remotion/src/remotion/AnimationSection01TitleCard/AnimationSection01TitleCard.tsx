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
      {/* Frame 0-15: Title fades in and scales from 0.85 to 1.0 */}
      <Sequence from={ANIMATION_TIMING.titleFadeStart} durationInFrames={ANIMATION_TIMING.totalDuration}>
        <TitleText />
      </Sequence>

      {/* Frame 12-30: Accent line expands outward from center */}
      <Sequence from={ANIMATION_TIMING.accentLineStart} durationInFrames={ANIMATION_TIMING.totalDuration - ANIMATION_TIMING.accentLineStart}>
        <AccentLine />
      </Sequence>

      {/* Frame 20-40: Subtitle fades in with upward drift */}
      <Sequence from={ANIMATION_TIMING.subtitleFadeStart} durationInFrames={ANIMATION_TIMING.totalDuration - ANIMATION_TIMING.subtitleFadeStart}>
        <SubtitleText />
      </Sequence>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection01TitleCardProps = {};

export default AnimationSection01TitleCard;
