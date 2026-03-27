import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  BLOCK_BG_COLOR,
  WINDOW_WIDTH,
  WINDOW_HEIGHT,
  WINDOW_FILL_DURATION,
  EMPHASIS_PULSE_DURATION,
  DENSE_CODE_LINES,
  CLEAN_PROMPT_LINES,
  RED_TINT,
  RED_LABEL_COLOR,
  GREEN_TINT,
  SUBLABEL_COLOR,
} from './constants';

interface ContextWindowProps {
  side: 'left' | 'right';
  x: number;
  y: number;
  fillStartFrame: number;
  emphasisFrame: number;
}

export const ContextWindow: React.FC<ContextWindowProps> = ({
  side,
  x,
  y,
  fillStartFrame,
  emphasisFrame,
}) => {
  const frame = useCurrentFrame();

  const isLeft = side === 'left';
  const tintColor = isLeft ? RED_TINT : GREEN_TINT;
  const labelColor = isLeft ? RED_LABEL_COLOR : GREEN_TINT;
  const label = isLeft
    ? '15,000 tokens of raw code'
    : 'Prompts for 10 modules';
  const sublabel = isLeft ? 'Dense. Hard to parse.' : '';
  const emphasisText = isLeft ? '' : '10\u00D7 more system knowledge';
  const lines = isLeft ? DENSE_CODE_LINES : CLEAN_PROMPT_LINES;

  // Fill animation
  const fillProgress = interpolate(
    frame,
    [fillStartFrame, fillStartFrame + WINDOW_FILL_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Content opacity
  const contentOpacity = fillProgress;

  // Emphasis glow (right side only)
  const glowOpacity = !isLeft
    ? interpolate(
        frame,
        [
          emphasisFrame,
          emphasisFrame + EMPHASIS_PULSE_DURATION / 2,
          emphasisFrame + EMPHASIS_PULSE_DURATION,
        ],
        [0, 0.6, 0.3],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      )
    : 0;

  // Label fade
  const labelOpacity = interpolate(
    frame,
    [fillStartFrame + 10, fillStartFrame + 25],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Emphasis text fade
  const emphasisOpacity = !isLeft
    ? interpolate(
        frame,
        [emphasisFrame, emphasisFrame + EMPHASIS_PULSE_DURATION],
        [0, 1],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        }
      )
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: WINDOW_WIDTH,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: labelColor,
          marginBottom: 6,
          opacity: labelOpacity,
        }}
      >
        {label}
      </div>

      {/* Sublabel */}
      {sublabel && (
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 12,
            color: SUBLABEL_COLOR,
            marginBottom: 8,
            opacity: labelOpacity,
          }}
        >
          {sublabel}
        </div>
      )}

      {/* Emphasis text (right window) */}
      {emphasisText && (
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 700,
            color: GREEN_TINT,
            marginBottom: 8,
            opacity: emphasisOpacity,
          }}
        >
          {emphasisText}
        </div>
      )}

      {/* Window rect */}
      <div
        style={{
          width: WINDOW_WIDTH,
          height: WINDOW_HEIGHT,
          backgroundColor: BLOCK_BG_COLOR,
          border: `1px solid rgba(${isLeft ? '239, 68, 68' : '74, 222, 128'}, 0.2)`,
          borderRadius: 8,
          padding: 10,
          overflow: 'hidden',
          boxSizing: 'border-box',
          position: 'relative',
        }}
      >
        {/* Glow effect for right window */}
        {!isLeft && (
          <div
            style={{
              position: 'absolute',
              inset: -2,
              borderRadius: 10,
              boxShadow: `0 0 30px rgba(74, 222, 128, ${glowOpacity})`,
              pointerEvents: 'none',
            }}
          />
        )}

        {/* Content lines */}
        <div style={{ opacity: contentOpacity }}>
          {isLeft
            ? /* Dense code lines, repeated to fill space */
              Array.from({ length: 35 }, (_, i) => {
                const line = lines[i % lines.length];
                return (
                  <div
                    key={i}
                    style={{
                      fontFamily: 'JetBrains Mono, monospace',
                      fontSize: 8,
                      lineHeight: '12px',
                      color: RED_LABEL_COLOR,
                      opacity: 0.35,
                      whiteSpace: 'nowrap',
                      overflow: 'hidden',
                    }}
                  >
                    {line}
                  </div>
                );
              })
            : /* Clean prompt lines */
              lines.map((line, i) => (
                <div
                  key={i}
                  style={{
                    fontFamily: 'Inter, sans-serif',
                    fontSize: 10,
                    lineHeight: '16px',
                    color: GREEN_TINT,
                    opacity: 0.8,
                    padding: '6px 8px',
                    marginBottom: 4,
                    backgroundColor: 'rgba(74, 222, 128, 0.05)',
                    borderRadius: 4,
                    borderLeft: '2px solid rgba(74, 222, 128, 0.3)',
                  }}
                >
                  {line}
                </div>
              ))}
        </div>

        {/* Fill progress bar at bottom */}
        <div
          style={{
            position: 'absolute',
            bottom: 0,
            left: 0,
            width: `${fillProgress * 100}%`,
            height: 3,
            backgroundColor: tintColor,
            opacity: 0.4,
            borderRadius: '0 0 8px 8px',
          }}
        />
      </div>
    </div>
  );
};
