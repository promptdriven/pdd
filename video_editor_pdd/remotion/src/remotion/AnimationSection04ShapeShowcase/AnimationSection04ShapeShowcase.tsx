import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';
import { SubtitleText } from './SubtitleText';
import { ShapeCard } from './ShapeCard';
import { DottedArrow } from './DottedArrow';
import { CardLabel } from './CardLabel';

export const AnimationSection04ShapeShowcase: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Subtitle: "Pure Remotion — No Veo Required" */}
      <SubtitleText />

      {/* Left card with blue circle */}
      {frame >= ANIMATION_TIMING.leftCardStart && (
        <ShapeCard
          shape="circle"
          color={COLORS.circleBlue}
          centerX={DIMENSIONS.leftCardCenterX}
          centerY={DIMENSIONS.cardCenterY}
          direction="left"
        />
      )}

      {/* Right card with green square */}
      {frame >= ANIMATION_TIMING.rightCardStart && (
        <ShapeCard
          shape="square"
          color={COLORS.squareGreen}
          centerX={DIMENSIONS.rightCardCenterX}
          centerY={DIMENSIONS.cardCenterY}
          direction="right"
        />
      )}

      {/* Dotted connecting arrow */}
      <DottedArrow />

      {/* Labels beneath cards */}
      <CardLabel
        text="Pulse Animation"
        centerX={DIMENSIONS.leftCardCenterX}
        cardCenterY={DIMENSIONS.cardCenterY}
      />
      <CardLabel
        text="Morph + Slide"
        centerX={DIMENSIONS.rightCardCenterX}
        cardCenterY={DIMENSIONS.cardCenterY}
      />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection04ShapeShowcaseProps = {};

export default AnimationSection04ShapeShowcase;
