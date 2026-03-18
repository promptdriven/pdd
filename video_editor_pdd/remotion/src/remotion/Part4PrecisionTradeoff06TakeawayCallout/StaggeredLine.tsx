import React from 'react';
import { useCurrentFrame, Easing, interpolate, spring, useVideoConfig } from 'remotion';
import {
  FONT_FAMILY,
  BASE_FONT_SIZE,
  LESS_FONT_SIZE,
  TEXT_COLOR,
  TEXT_OPACITY,
  AMBER,
  LESS_SCALE,
  MOLD_GLOW_BLUR,
  MOLD_GLOW_OPACITY,
  WORD_STAGGER,
  PULSE_START,
  PULSE_DURATION,
  WIDTH,
} from './constants';
import { WallIcon } from './WallIcon';

interface StaggeredLineProps {
  lineStart: number;
  y: number;
  lineIndex: number;
}

const LINE_DATA = [
  {
    segments: [
      { text: 'The more ', type: 'normal' as const },
      { text: 'walls', type: 'walls' as const },
      { text: ' you have,', type: 'normal' as const },
    ],
  },
  {
    segments: [
      { text: 'the ', type: 'normal' as const },
      { text: 'less', type: 'less' as const },
      { text: ' you need to specify.', type: 'normal' as const },
    ],
  },
  {
    segments: [
      { text: 'The ', type: 'normal' as const },
      { text: 'mold', type: 'mold' as const },
      { text: ' does the ', type: 'normal' as const },
      { text: 'precision work', type: 'precision' as const },
      { text: '.', type: 'normal' as const },
    ],
  },
];

export const StaggeredLine: React.FC<StaggeredLineProps> = ({
  lineStart,
  y,
  lineIndex,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const localFrame = frame - lineStart;
  const line = LINE_DATA[lineIndex];

  if (localFrame < 0) return null;

  // Count words across all segments for stagger timing
  let wordIndex = 0;

  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 0,
        width: WIDTH,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'baseline',
        fontFamily: FONT_FAMILY,
        fontSize: BASE_FONT_SIZE,
        color: TEXT_COLOR,
        whiteSpace: 'pre',
      }}
    >
      {line.segments.map((segment, segIdx) => {
        if (segment.type === 'walls') {
          const wi = wordIndex;
          wordIndex++;
          const delay = wi * WORD_STAGGER;
          const opacity = interpolate(localFrame, [delay, delay + 12], [0, TEXT_OPACITY], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          const translateY = interpolate(localFrame, [delay, delay + 12], [8, 0], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          return (
            <span
              key={segIdx}
              style={{
                opacity,
                transform: `translateY(${translateY}px)`,
                display: 'inline-flex',
                alignItems: 'baseline',
              }}
            >
              <WallIcon size={10} color={AMBER} />
              <span
                style={{
                  fontWeight: 700,
                  color: AMBER,
                }}
              >
                walls
              </span>
            </span>
          );
        }

        if (segment.type === 'less') {
          const wi = wordIndex;
          wordIndex++;
          const delay = wi * WORD_STAGGER;
          const opacity = interpolate(localFrame, [delay, delay + 12], [0, TEXT_OPACITY], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          const scaleSpring = spring({
            frame: Math.max(0, localFrame - delay),
            fps,
            config: { stiffness: 200, damping: 15 },
          });
          const scale = interpolate(scaleSpring, [0, 1], [1, LESS_SCALE]);
          return (
            <span
              key={segIdx}
              style={{
                opacity,
                transform: `scale(${scale})`,
                display: 'inline-block',
                fontWeight: 700,
                fontSize: LESS_FONT_SIZE,
                color: TEXT_COLOR,
              }}
            >
              less
            </span>
          );
        }

        if (segment.type === 'mold') {
          const wi = wordIndex;
          wordIndex++;
          const delay = wi * WORD_STAGGER;
          const opacity = interpolate(localFrame, [delay, delay + 12], [0, TEXT_OPACITY], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          // Glow ramp over 15 frames after appearing
          const glowOpacity = interpolate(
            localFrame,
            [delay + 5, delay + 20],
            [0, MOLD_GLOW_OPACITY],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.inOut(Easing.sin),
            }
          );
          return (
            <span
              key={segIdx}
              style={{
                opacity,
                fontWeight: 700,
                color: AMBER,
                textShadow: `0 0 ${MOLD_GLOW_BLUR}px rgba(217, 148, 74, ${glowOpacity})`,
                display: 'inline-block',
              }}
            >
              mold
            </span>
          );
        }

        if (segment.type === 'precision') {
          const wi = wordIndex;
          wordIndex++;
          const delay = wi * WORD_STAGGER;
          const opacity = interpolate(localFrame, [delay, delay + 12], [0, TEXT_OPACITY], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          // Pulse at the end: single sine cycle from frame 150-180
          const pulsePhase = interpolate(
            frame,
            [PULSE_START, PULSE_START + PULSE_DURATION],
            [0, Math.PI * 2],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            }
          );
          const pulse = frame >= PULSE_START ? 1 + 0.05 * Math.sin(pulsePhase) : 1;
          return (
            <span
              key={segIdx}
              style={{
                opacity,
                fontWeight: 600,
                color: TEXT_COLOR,
                display: 'inline-block',
                transform: `scale(${pulse})`,
              }}
            >
              precision work
            </span>
          );
        }

        // Normal text — split into words for stagger
        const words = segment.text.split(/(?<=\s)/); // split keeping trailing spaces
        return words.map((word, wIdx) => {
          if (word.trim() === '') {
            return (
              <span key={`${segIdx}-${wIdx}`} style={{ opacity: TEXT_OPACITY }}>
                {word}
              </span>
            );
          }
          const wi = wordIndex;
          wordIndex++;
          const delay = wi * WORD_STAGGER;
          const opacity = interpolate(localFrame, [delay, delay + 12], [0, TEXT_OPACITY], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          const translateY = interpolate(localFrame, [delay, delay + 12], [8, 0], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          return (
            <span
              key={`${segIdx}-${wIdx}`}
              style={{
                opacity,
                transform: `translateY(${translateY}px)`,
                display: 'inline-block',
              }}
            >
              {word}
            </span>
          );
        });
      })}
    </div>
  );
};

export default StaggeredLine;
