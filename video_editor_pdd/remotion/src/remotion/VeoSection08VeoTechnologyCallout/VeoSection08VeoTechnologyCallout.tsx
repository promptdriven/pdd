import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, CARD, ANIMATION, HEADER_TEXT } from './constants';
import { FlowNode } from './FlowNode';
import { FlowArrow } from './FlowArrow';
import { CardHeader } from './CardHeader';

export const VeoSection08VeoTechnologyCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Card slide in: Y from 1100 → 680, opacity 0 → 1 (frames 0-20)
  const cardY = interpolate(
    frame,
    [ANIMATION.cardSlideInStart, ANIMATION.cardSlideInEnd],
    [CARD.offscreenY, CARD.restY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const cardOpacity = interpolate(
    frame,
    [ANIMATION.cardSlideInStart, ANIMATION.cardSlideInEnd],
    [0.15, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Card fade out: opacity 1 → 0, Y 680 → 720 (frames 75-90)
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  const fadeOutY = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [0, 40],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  const finalOpacity = cardOpacity * fadeOutOpacity;
  const finalY = cardY + fadeOutY;

  // Whether to show glow on Veo AI node (during hold phase)
  const showVeoGlow = frame >= ANIMATION.holdStart;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Card panel */}
      <div
        style={{
          position: 'absolute',
          left: (1920 - CARD.width) / 2,
          top: finalY,
          width: CARD.width,
          height: CARD.height,
          borderRadius: CARD.borderRadius,
          backgroundColor: COLORS.cardBg,
          backdropFilter: 'blur(16px)',
          WebkitBackdropFilter: 'blur(16px)',
          border: `1px solid ${COLORS.cardBorder}`,
          opacity: finalOpacity,
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          justifyContent: 'center',
          padding: '24px 40px',
        }}
      >
        {/* Header text */}
        <CardHeader text={HEADER_TEXT} />

        {/* Flow diagram: Node → Arrow → Node → Arrow → Node */}
        <div
          style={{
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            gap: 0,
          }}
        >
          {/* Node 1: Text Prompt */}
          <FlowNode
            label="Text Prompt"
            borderColor={COLORS.nodeIndigo}
            filled={false}
            icon="cursor"
            animStartFrame={ANIMATION.node1Start}
            animEndFrame={ANIMATION.node1End}
            showGlow={false}
          />

          {/* Arrow 1 */}
          <FlowArrow
            drawStartFrame={ANIMATION.arrow1Start}
            drawEndFrame={ANIMATION.arrow1End}
          />

          {/* Node 2: Veo AI */}
          <FlowNode
            label="Veo AI"
            borderColor={COLORS.nodeAmber}
            filled={true}
            icon="sparkle"
            animStartFrame={ANIMATION.node2Start}
            animEndFrame={ANIMATION.node2End}
            showGlow={showVeoGlow}
          />

          {/* Arrow 2 */}
          <FlowArrow
            drawStartFrame={ANIMATION.arrow2Start}
            drawEndFrame={ANIMATION.arrow2End}
          />

          {/* Node 3: Video Clip */}
          <FlowNode
            label="Video Clip"
            borderColor={COLORS.nodeEmerald}
            filled={false}
            icon="film"
            animStartFrame={ANIMATION.node3Start}
            animEndFrame={ANIMATION.node3End}
            showGlow={false}
          />
        </div>
      </div>
    </AbsoluteFill>
  );
};

export const defaultVeoSection08VeoTechnologyCalloutProps = {};

export default VeoSection08VeoTechnologyCallout;
