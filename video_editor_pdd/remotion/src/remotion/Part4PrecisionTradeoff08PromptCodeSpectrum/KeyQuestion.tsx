import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TEXT_PRIMARY,
  BLUE,
  GREEN,
  STRIKE_COLOR,
  WIDTH,
  TIMING,
} from './constants';

/**
 * The three-line key question / answer text that appears below the spectrum.
 * Line 1: "The question isn't prompts OR code." (with strikethrough)
 * Line 2: "It's how far into prompt space can you stay?"
 * Line 3: "For most of the specification — further than you'd think."
 */
export const KeyQuestion: React.FC = () => {
  const frame = useCurrentFrame();

  // Line 1 fade in (frame 150-170)
  const line1Opacity = interpolate(
    frame,
    [TIMING.line1Start, TIMING.line1Start + TIMING.textFadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Strikethrough draws across "prompts OR code" (frame 160-175)
  const strikeStart = TIMING.line1Start + TIMING.strikethroughDelay;
  const strikeProgress = interpolate(
    frame,
    [strikeStart, strikeStart + TIMING.strikethroughDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Line 2 fade in (frame 200-220)
  const line2Opacity = interpolate(
    frame,
    [TIMING.line2Start, TIMING.line2Start + TIMING.textFadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Line 3 fade in (frame 260-280)
  const line3Opacity = interpolate(
    frame,
    [TIMING.line3Start, TIMING.line3Start + TIMING.textFadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 680,
        width: WIDTH,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        gap: 16,
      }}
    >
      {/* Line 1: "The question isn't prompts OR code." */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          color: TEXT_PRIMARY,
          opacity: 0.7 * line1Opacity,
          textAlign: 'center',
          lineHeight: 1.4,
        }}
      >
        The question isn&apos;t{' '}
        <span
          style={{
            position: 'relative',
            display: 'inline-block',
            color: STRIKE_COLOR,
            opacity: 0.4 / 0.7, // relative to parent
          }}
        >
          prompts OR code.
          {/* Animated strikethrough line */}
          <span
            style={{
              position: 'absolute',
              left: 0,
              top: '52%',
              height: 1.5,
              width: `${strikeProgress * 100}%`,
              backgroundColor: STRIKE_COLOR,
              opacity: 0.6,
            }}
          />
        </span>
      </div>

      {/* Line 2: "It's how far into prompt space can you stay?" */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          color: TEXT_PRIMARY,
          opacity: 0.85 * line2Opacity,
          textAlign: 'center',
          lineHeight: 1.4,
        }}
      >
        It&apos;s{' '}
        <span
          style={{
            fontWeight: 700,
            color: BLUE,
            opacity: 0.8 / 0.85, // relative to parent
          }}
        >
          how far into prompt space can you stay?
        </span>
      </div>

      {/* Line 3: "For most of the specification — further than you'd think." */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 18,
          color: TEXT_PRIMARY,
          opacity: 0.6 * line3Opacity,
          textAlign: 'center',
          lineHeight: 1.4,
          marginTop: 8,
        }}
      >
        For most of the specification —{' '}
        <span
          style={{
            fontWeight: 700,
            color: GREEN,
            opacity: 0.7 / 0.6, // relative to parent
          }}
        >
          further than you&apos;d think.
        </span>
      </div>
    </div>
  );
};
