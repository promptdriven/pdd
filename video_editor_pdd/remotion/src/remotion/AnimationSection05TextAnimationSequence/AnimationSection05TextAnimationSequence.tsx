import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { TypewriterText } from './TypewriterText';
import { WordFadeText } from './WordFadeText';
import { WaveText } from './WaveText';
import { COLORS, ANIMATION, TEXT_CONTENT } from './constants';

export const AnimationSection05TextAnimationSequence: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        display: 'flex',
        flexDirection: 'column',
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      {/* Headline - Typewriter Effect */}
      <Sequence from={ANIMATION.typewriter.startFrame}>
        <TypewriterText text={TEXT_CONTENT.headline} />
      </Sequence>

      {/* Subtitle - Word Fade */}
      <Sequence from={ANIMATION.subtitle.startFrame}>
        <WordFadeText
          words={TEXT_CONTENT.subtitle}
          separator={TEXT_CONTENT.separator}
        />
      </Sequence>

      {/* Emphasis - Wave Animation */}
      <Sequence from={ANIMATION.wave.startFrame}>
        <WaveText text={TEXT_CONTENT.emphasis} />
      </Sequence>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection05TextAnimationSequenceProps = {};

export default AnimationSection05TextAnimationSequence;
