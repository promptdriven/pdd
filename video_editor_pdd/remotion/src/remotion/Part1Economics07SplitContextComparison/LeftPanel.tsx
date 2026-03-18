import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  LEFT_COLOR,
  CODE_COLOR,
  RED_HIGHLIGHT,
  GREEN_HIGHLIGHT as GREEN_COLOR,
  PANEL_PADDING,
  FAKE_CODE_LINES,
  RED_HIGHLIGHTS,
  GREEN_HIGHLIGHT_REGION,
  LEFT_CODE_IN,
  LEFT_CODE_DURATION,
  TOKEN_COUNTS_IN,
  FILL_BARS_IN,
  HOLD_START,
  PULSE_CYCLE,
} from './constants';

const LINE_HEIGHT = 10;

export const LeftPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel header fade: frames 30-45
  const headerOpacity = interpolate(frame, [30, 45], [0, 0.6], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Code fill progress: frames 60-150
  const codeFill = interpolate(frame, [LEFT_CODE_IN, LEFT_CODE_IN + LEFT_CODE_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Token count fade: frames 240-255
  const tokenOpacity = interpolate(frame, [TOKEN_COUNTS_IN, TOKEN_COUNTS_IN + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Fill bar: frames 300-320
  const fillBarWidth = interpolate(frame, [FILL_BARS_IN, FILL_BARS_IN + 20], [0, 100], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Red highlight pulse after HOLD_START
  const pulseOpacity =
    frame >= HOLD_START
      ? interpolate(
          frame % PULSE_CYCLE,
          [0, PULSE_CYCLE / 2, PULSE_CYCLE],
          [0.08, 0.12, 0.08],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
        )
      : 0.08;

  const windowTop = 90;
  const windowLeft = PANEL_PADDING;
  const windowWidth = 960 - PANEL_PADDING * 2;
  const windowHeight = 870;

  const visibleLines = Math.floor(codeFill * FAKE_CODE_LINES.length);

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 958,
        height: 1080,
        overflow: 'hidden',
      }}
    >
      {/* Panel Header */}
      <div
        style={{
          position: 'absolute',
          top: 30,
          left: 0,
          width: 958,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: LEFT_COLOR,
          opacity: headerOpacity,
          letterSpacing: 2,
          textTransform: 'uppercase',
        }}
      >
        Agentic Patching
      </div>

      {/* Context Window Border */}
      <div
        style={{
          position: 'absolute',
          top: windowTop,
          left: windowLeft,
          width: windowWidth,
          height: windowHeight,
          border: `1px solid rgba(217, 148, 74, 0.3)`,
          borderRadius: 8,
          overflow: 'hidden',
        }}
      >
        {/* Dense code lines */}
        <div
          style={{
            position: 'absolute',
            top: 8,
            left: 8,
            right: 8,
            bottom: 60,
            overflow: 'hidden',
          }}
        >
          {FAKE_CODE_LINES.slice(0, visibleLines).map((line, i) => (
            <div
              key={i}
              style={{
                fontFamily: 'JetBrains Mono, monospace',
                fontSize: 8,
                lineHeight: `${LINE_HEIGHT}px`,
                color: CODE_COLOR,
                opacity: 0.35,
                whiteSpace: 'pre',
                height: LINE_HEIGHT,
              }}
            >
              {line}
            </div>
          ))}
          {/* Repeat lines to fill the window densely */}
          {codeFill > 0.5 &&
            FAKE_CODE_LINES.slice(0, Math.floor((codeFill - 0.5) * 2 * FAKE_CODE_LINES.length)).map(
              (line, i) => (
                <div
                  key={`r-${i}`}
                  style={{
                    fontFamily: 'JetBrains Mono, monospace',
                    fontSize: 8,
                    lineHeight: `${LINE_HEIGHT}px`,
                    color: CODE_COLOR,
                    opacity: 0.3,
                    whiteSpace: 'pre',
                    height: LINE_HEIGHT,
                  }}
                >
                  {line}
                </div>
              )
            )}
        </div>

        {/* Red highlight regions */}
        {RED_HIGHLIGHTS.map((h, idx) => {
          const staggerFrame = LEFT_CODE_IN + 30 + idx * 10;
          const hOpacity = interpolate(frame, [staggerFrame, staggerFrame + 15], [0, 1], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });

          return (
            <div
              key={`red-${idx}`}
              style={{
                position: 'absolute',
                top: 8 + h.yFrac * (windowHeight - 68),
                left: 8,
                right: 8,
                height: h.hFrac * (windowHeight - 68),
                backgroundColor: `rgba(231, 76, 60, ${frame >= HOLD_START ? pulseOpacity : 0.08})`,
                border: `1px solid rgba(231, 76, 60, 0.2)`,
                borderRadius: 3,
                opacity: hOpacity,
                display: 'flex',
                alignItems: 'flex-start',
                justifyContent: 'flex-end',
                padding: 4,
              }}
            >
              <span
                style={{
                  fontFamily: 'Inter, sans-serif',
                  fontSize: 7,
                  color: RED_HIGHLIGHT,
                  opacity: 0.4,
                }}
              >
                irrelevant
              </span>
            </div>
          );
        })}

        {/* Green highlight region */}
        {(() => {
          const greenFrame = LEFT_CODE_IN + 60;
          const gOpacity = interpolate(frame, [greenFrame, greenFrame + 15], [0, 1], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          return (
            <div
              style={{
                position: 'absolute',
                top: 8 + GREEN_HIGHLIGHT_REGION.yFrac * (windowHeight - 68),
                left: 8,
                right: 8,
                height: GREEN_HIGHLIGHT_REGION.hFrac * (windowHeight - 68),
                backgroundColor: `rgba(90, 170, 110, 0.10)`,
                border: `1px solid rgba(90, 170, 110, 0.3)`,
                borderRadius: 3,
                opacity: gOpacity,
                display: 'flex',
                alignItems: 'flex-start',
                justifyContent: 'flex-end',
                padding: 4,
              }}
            >
              <span
                style={{
                  fontFamily: 'Inter, sans-serif',
                  fontSize: 7,
                  color: GREEN_COLOR,
                  opacity: 0.5,
                }}
              >
                relevant
              </span>
            </div>
          );
        })()}

        {/* Fill indicator bar at bottom of window */}
        <div
          style={{
            position: 'absolute',
            bottom: 36,
            left: 8,
            right: 8,
            height: 4,
            backgroundColor: 'rgba(231, 76, 60, 0.05)',
            borderRadius: 2,
          }}
        >
          <div
            style={{
              width: `${fillBarWidth}%`,
              height: '100%',
              backgroundColor: `rgba(231, 76, 60, 0.2)`,
              borderRadius: 2,
            }}
          />
        </div>

        {/* Token count */}
        <div
          style={{
            position: 'absolute',
            bottom: 14,
            left: 0,
            right: 0,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            color: LEFT_COLOR,
            opacity: tokenOpacity * 0.5,
          }}
        >
          15,000 tokens
        </div>
      </div>

      {/* Quality note below window */}
      <div
        style={{
          position: 'absolute',
          top: windowTop + windowHeight + 8,
          left: 0,
          width: 958,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color: RED_HIGHLIGHT,
          opacity: tokenOpacity * 0.4,
        }}
      >
        ~60% irrelevant
      </div>
    </div>
  );
};

export default LeftPanel;
