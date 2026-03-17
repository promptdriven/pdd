import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  WIDTH,
  TEXT_PRIMARY,
  TEXT_DIM,
  BLUE,
  GREEN,
  ANIM,
} from './constants';

/**
 * The three lines of key question text below the spectrum,
 * with strikethrough animation and staggered reveals.
 */
export const KeyQuestion: React.FC = () => {
  const frame = useCurrentFrame();

  // Line 1 fade
  const line1Opacity = interpolate(
    frame,
    [ANIM.line1Start, ANIM.line1Start + ANIM.line1FadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Strikethrough draws after line 1 appears
  const strikeStart = ANIM.line1Start + ANIM.strikethroughDelay;
  const strikeProgress = interpolate(
    frame,
    [strikeStart, strikeStart + ANIM.strikethroughDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Line 2 fade
  const line2Opacity = interpolate(
    frame,
    [ANIM.line2Start, ANIM.line2Start + ANIM.line2FadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Line 3 fade
  const line3Opacity = interpolate(
    frame,
    [ANIM.line3Start, ANIM.line3Start + ANIM.line3FadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const centerX = WIDTH / 2;

  return (
    <>
      {/* Line 1: "The question isn't prompts OR code." */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 680,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          color: TEXT_PRIMARY,
          opacity: 0.7 * line1Opacity,
          whiteSpace: 'nowrap',
        }}
      >
        The question isn&apos;t{' '}
        <span
          style={{
            position: 'relative',
            display: 'inline',
            color: TEXT_DIM,
            opacity: 0.57, // 0.4/0.7 to get effective 0.4
          }}
        >
          prompts OR code.
          {/* Strikethrough line, drawn left to right */}
          <span
            style={{
              position: 'absolute',
              left: 0,
              top: '50%',
              height: 1.5,
              width: `${strikeProgress * 100}%`,
              backgroundColor: TEXT_DIM,
              opacity: 0.6,
            }}
          />
        </span>
      </div>

      {/* Line 2: "It's how far into prompt space can you stay?" */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 720,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          color: TEXT_PRIMARY,
          opacity: 0.85 * line2Opacity,
          whiteSpace: 'nowrap',
        }}
      >
        It&apos;s{' '}
        <span style={{ fontWeight: 700, color: BLUE, opacity: 0.94 }}>
          how far into prompt space can you stay?
        </span>
      </div>

      {/* Line 3: "For most of the specification — further than you'd think." */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 770,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 18,
          color: TEXT_PRIMARY,
          opacity: 0.6 * line3Opacity,
          whiteSpace: 'nowrap',
        }}
      >
        For most of the specification —{' '}
        <span style={{ fontWeight: 700, color: GREEN, opacity: 1 }}>
          further than you&apos;d think.
        </span>
      </div>
    </>
  );
};
