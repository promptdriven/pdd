import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TYPOGRAPHY, LAYOUT, METRICS, ANIMATION } from './constants';
import { MetricCard } from './MetricCard';
import { ExpandingRule } from './ExpandingRule';

export const VeoSection13VeoTechnologyReprise: React.FC = () => {
  const frame = useCurrentFrame();

  // Background gradient opacity (subtle fade in)
  const bgOpacity = interpolate(
    frame,
    [ANIMATION.headerFadeStart, ANIMATION.headerFadeEnd],
    [0.5, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Header fade in + upward drift
  const headerOpacity = interpolate(
    frame,
    [ANIMATION.headerFadeStart, ANIMATION.headerFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const headerDrift = interpolate(
    frame,
    [ANIMATION.headerFadeStart, ANIMATION.headerFadeEnd],
    [12, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Header fade out
  const headerFadeOut = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  // Total card row width: 3 cards + 2 gaps
  const totalWidth =
    METRICS.length * LAYOUT.cardWidth +
    (METRICS.length - 1) * LAYOUT.cardGap;
  const startX = (CANVAS.width - totalWidth) / 2;

  // Card animation start frames
  const cardStarts = [
    ANIMATION.card1Start,
    ANIMATION.card2Start,
    ANIMATION.card3Start,
  ];
  const cardEnds = [
    ANIMATION.card1End,
    ANIMATION.card2End,
    ANIMATION.card3End,
  ];

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.backgroundOuter,
      }}
    >
      {/* Radial gradient overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: CANVAS.width,
          height: CANVAS.height,
          background: `radial-gradient(ellipse at center, ${COLORS.backgroundInner} 0%, transparent 70%)`,
          opacity: bgOpacity,
        }}
      />

      {/* Section header */}
      <div
        style={{
          position: 'absolute',
          top: LAYOUT.headerY + headerDrift,
          left: 0,
          width: CANVAS.width,
          textAlign: 'center',
          fontFamily: TYPOGRAPHY.header.fontFamily,
          fontSize: TYPOGRAPHY.header.fontSize,
          fontWeight: TYPOGRAPHY.header.fontWeight,
          letterSpacing: TYPOGRAPHY.header.letterSpacing,
          color: COLORS.headerText,
          textTransform: 'uppercase',
          opacity: headerOpacity * headerFadeOut,
        }}
      >
        VEO INTEGRATION SUMMARY
      </div>

      {/* Expanding horizontal rule */}
      <ExpandingRule />

      {/* Metric cards row */}
      <div
        style={{
          position: 'absolute',
          top: LAYOUT.cardsY,
          left: startX,
          display: 'flex',
          flexDirection: 'row',
          gap: LAYOUT.cardGap,
        }}
      >
        {METRICS.map((metric, i) => (
          <MetricCard
            key={metric.icon}
            icon={metric.icon}
            value={metric.value}
            label={metric.label}
            accentColor={metric.color}
            animStart={cardStarts[i]}
            animEnd={cardEnds[i]}
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};

export const defaultVeoSection13VeoTechnologyRepriseProps = {};

export default VeoSection13VeoTechnologyReprise;
