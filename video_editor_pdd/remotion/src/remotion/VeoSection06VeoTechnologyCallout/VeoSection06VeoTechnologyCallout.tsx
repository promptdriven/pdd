import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  TYPOGRAPHY,
  CARD,
  ANIMATION,
  TECH_SPECS,
  TECH_TAGS,
  HEADING_TEXT,
} from './constants';
import { StatusDot } from './StatusDot';
import { ScanlineOverlay } from './ScanlineOverlay';
import { SpecRow } from './SpecRow';
import { TechTag } from './TechTag';

export const VeoSection06VeoTechnologyCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Card reveal: slide up + fade in, frames 0-15
  const cardOpacity = interpolate(
    frame,
    [0, ANIMATION.cardRevealEnd],
    [0.4, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  const cardTranslateY = interpolate(
    frame,
    [0, ANIMATION.cardRevealEnd],
    [ANIMATION.cardSlideDistance, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  // Heading: fade in, frames 5-18
  const headingOpacity = interpolate(
    frame,
    [ANIMATION.headingStart, ANIMATION.headingEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(2)) },
  );

  // Accent line under heading: width grows
  const accentWidth = interpolate(
    frame,
    [ANIMATION.headingStart, ANIMATION.headingEnd + 5],
    [0, 80],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  // Global fade out
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.poly(3)) },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        opacity: fadeOutOpacity,
      }}
    >
      {/* Card container */}
      <div
        style={{
          position: 'absolute',
          left: CARD.x,
          top: CARD.y,
          width: CARD.width,
          height: CARD.height,
          borderRadius: CARD.borderRadius,
          backgroundColor: COLORS.cardBg,
          border: `1px solid ${COLORS.cardBorder}`,
          boxShadow: `0 0 40px ${COLORS.cardGlow}, inset 0 1px 0 rgba(255,255,255,0.05)`,
          opacity: cardOpacity,
          transform: `translateY(${cardTranslateY}px)`,
          overflow: 'hidden',
        }}
      >
        {/* Scanline sweep effect */}
        <ScanlineOverlay />

        {/* Card content */}
        <div
          style={{
            position: 'relative',
            padding: CARD.padding,
            width: '100%',
            height: '100%',
            display: 'flex',
            flexDirection: 'column',
          }}
        >
          {/* Heading row */}
          <div
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 14,
              opacity: headingOpacity,
              marginBottom: 12,
            }}
          >
            <StatusDot x={0} y={4} />
            <span
              style={{
                color: COLORS.headingText,
                fontSize: TYPOGRAPHY.heading.fontSize,
                fontFamily: TYPOGRAPHY.heading.fontFamily,
                fontWeight: TYPOGRAPHY.heading.fontWeight,
                letterSpacing: TYPOGRAPHY.heading.letterSpacing,
                marginLeft: 24,
              }}
            >
              {HEADING_TEXT}
            </span>
          </div>

          {/* Accent line */}
          <div
            style={{
              width: accentWidth,
              height: 3,
              borderRadius: 2,
              background: `linear-gradient(90deg, ${COLORS.accentBlue}, ${COLORS.accentCyan})`,
              marginBottom: 36,
            }}
          />

          {/* Tech spec rows */}
          {TECH_SPECS.map((spec, i) => (
            <SpecRow key={spec.label} label={spec.label} value={spec.value} index={i} />
          ))}

          {/* Tags row */}
          <div
            style={{
              display: 'flex',
              flexWrap: 'wrap',
              gap: 10,
              marginTop: 8,
            }}
          >
            {TECH_TAGS.map((tag, i) => (
              <TechTag key={tag} label={tag} index={i} />
            ))}
          </div>
        </div>
      </div>

      {/* Right side: large accent glow circle (decorative) */}
      <div
        style={{
          position: 'absolute',
          right: 200,
          top: 300,
          width: 400,
          height: 400,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${COLORS.cardGlow} 0%, transparent 70%)`,
          opacity: interpolate(frame, [0, 20], [0, 0.6], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }),
        }}
      />

      {/* Right side: concentric tech rings */}
      {[180, 260, 340].map((radius, i) => {
        const ringOpacity = interpolate(
          frame,
          [10 + i * 5, 25 + i * 5],
          [0, 0.15 - i * 0.03],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );
        const rotation = frame * (0.3 + i * 0.15);
        return (
          <div
            key={radius}
            style={{
              position: 'absolute',
              right: 200 + 200 - radius,
              top: 300 + 200 - radius,
              width: radius * 2,
              height: radius * 2,
              borderRadius: '50%',
              border: `1px solid ${COLORS.accentBlue}`,
              opacity: ringOpacity,
              transform: `rotate(${rotation}deg)`,
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};

export const defaultVeoSection06VeoTechnologyCalloutProps = {};

export default VeoSection06VeoTechnologyCallout;
