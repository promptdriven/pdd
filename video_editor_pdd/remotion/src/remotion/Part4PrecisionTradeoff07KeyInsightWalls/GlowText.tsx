/**
 * GlowText – the primary "pull quote" text with a one-shot glow pulse.
 * Fades in with a subtle scale, then glows once before holding.
 */
import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface GlowTextProps {
  /** The text to display */
  text: string;
  /** Font size in px */
  fontSize: number;
  /** Font weight */
  fontWeight: number;
  /** Font family */
  fontFamily: string;
  /** Text color */
  color: string;
  /** Y position (center of text) */
  y: number;
  /** Canvas width for centering */
  canvasWidth: number;
  /** Absolute frame when the fade-in starts */
  fadeInStart: number;
  /** Duration of the fade-in (frames) */
  fadeInDuration: number;
  /** Scale at start of fade-in */
  scaleFrom: number;
  /** Scale at end of fade-in */
  scaleTo: number;
  /** Glow color */
  glowColor: string;
  /** Max glow opacity */
  glowMaxOpacity: number;
  /** Glow blur radius in px */
  glowBlur: number;
  /** Delay of the glow pulse relative to fadeInStart */
  glowDelay: number;
  /** Duration of the glow pulse in frames */
  glowDuration: number;
  /** Absolute frame when fade-out starts */
  fadeOutStart: number;
  /** Duration of fade-out in frames */
  fadeOutDuration: number;
}

const GlowText: React.FC<GlowTextProps> = ({
  text,
  fontSize,
  fontWeight,
  fontFamily,
  color,
  y,
  canvasWidth,
  fadeInStart,
  fadeInDuration,
  scaleFrom,
  scaleTo,
  glowColor,
  glowMaxOpacity,
  glowBlur,
  glowDelay,
  glowDuration,
  fadeOutStart,
  fadeOutDuration,
}) => {
  const frame = useCurrentFrame();

  // Fade-in opacity: 0→1
  const fadeInOpacity = interpolate(
    frame,
    [fadeInStart, fadeInStart + fadeInDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Scale: scaleFrom → scaleTo
  const scale = interpolate(
    frame,
    [fadeInStart, fadeInStart + fadeInDuration],
    [scaleFrom, scaleTo],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Glow pulse: 0 → glowMaxOpacity → 0 (one-shot)
  const glowAbsStart = fadeInStart + glowDelay;
  const glowPeak = glowAbsStart + glowDuration / 2;
  const glowEnd = glowAbsStart + glowDuration;

  // First half: ramp up
  const glowUp = interpolate(
    frame,
    [glowAbsStart, glowPeak],
    [0, glowMaxOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    },
  );
  // Second half: ramp down
  const glowDown = interpolate(
    frame,
    [glowPeak, glowEnd],
    [glowMaxOpacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    },
  );
  const glowOpacity = frame < glowPeak ? glowUp : glowDown;

  // Fade-out
  const fadeOutOpacity = interpolate(
    frame,
    [fadeOutStart, fadeOutStart + fadeOutDuration],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const combinedOpacity = fadeInOpacity * fadeOutOpacity;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: canvasWidth,
        height: '100%',
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'flex-start',
        pointerEvents: 'none',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: y,
          transform: `scale(${scale}) translateY(-50%)`,
          opacity: combinedOpacity,
          fontFamily,
          fontSize,
          fontWeight,
          color,
          textAlign: 'center',
          whiteSpace: 'nowrap',
          textShadow: `0 0 ${glowBlur}px rgba(255,255,255,${glowOpacity})`,
        }}
      >
        {text}
      </div>
    </div>
  );
};

export default GlowText;
