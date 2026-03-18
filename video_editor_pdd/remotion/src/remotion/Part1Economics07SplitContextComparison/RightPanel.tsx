import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  RIGHT_COLOR,
  GREEN_HIGHLIGHT as GREEN_COLOR,
  CODE_COLOR,
  PROMPT_TEXT_COLOR,
  PANEL_PADDING,
  PROMPT_LINES,
  TEST_LINES,
  GROUNDING_LINES,
  RIGHT_CONTENT_IN,
  TOKEN_COUNTS_IN,
  FILL_BARS_IN,
} from './constants';

export const RightPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel header fade: frames 30-45
  const headerOpacity = interpolate(frame, [30, 45], [0, 0.6], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Prompt block: frames 150-170
  const promptOpacity = interpolate(frame, [RIGHT_CONTENT_IN, RIGHT_CONTENT_IN + 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Tests block: frames 180-200
  const testsOpacity = interpolate(frame, [RIGHT_CONTENT_IN + 30, RIGHT_CONTENT_IN + 50], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Grounding block: frames 210-230
  const groundingOpacity = interpolate(
    frame,
    [RIGHT_CONTENT_IN + 60, RIGHT_CONTENT_IN + 80],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Token count fade: frames 240-255
  const tokenOpacity = interpolate(frame, [TOKEN_COUNTS_IN, TOKEN_COUNTS_IN + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Fill bar: frames 300-320
  const fillBarWidth = interpolate(frame, [FILL_BARS_IN, FILL_BARS_IN + 20], [0, 25], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  const windowTop = 90;
  const windowLeft = PANEL_PADDING;
  const windowWidth = 960 - PANEL_PADDING * 2;
  const windowHeight = 870;

  return (
    <div
      style={{
        position: 'absolute',
        left: 962,
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
          color: RIGHT_COLOR,
          opacity: headerOpacity,
          letterSpacing: 2,
          textTransform: 'uppercase',
        }}
      >
        PDD Regeneration
      </div>

      {/* Context Window Border */}
      <div
        style={{
          position: 'absolute',
          top: windowTop,
          left: windowLeft,
          width: windowWidth,
          height: windowHeight,
          border: `1px solid rgba(74, 144, 217, 0.3)`,
          borderRadius: 8,
          overflow: 'hidden',
        }}
      >
        {/* Prompt block */}
        <div
          style={{
            position: 'absolute',
            top: 16,
            left: 16,
            right: 16,
            opacity: promptOpacity,
          }}
        >
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 8,
              color: RIGHT_COLOR,
              opacity: 0.4,
              marginBottom: 6,
              textTransform: 'uppercase',
              letterSpacing: 1,
            }}
          >
            prompt
          </div>
          <div
            style={{
              borderLeft: `3px solid ${RIGHT_COLOR}`,
              paddingLeft: 12,
            }}
          >
            {PROMPT_LINES.map((line, i) => (
              <div
                key={i}
                style={{
                  fontFamily: 'Inter, sans-serif',
                  fontSize: 10,
                  lineHeight: '16px',
                  color: PROMPT_TEXT_COLOR,
                  opacity: 0.6,
                  minHeight: 16,
                }}
              >
                {line}
              </div>
            ))}
          </div>
        </div>

        {/* Tests block */}
        <div
          style={{
            position: 'absolute',
            top: 270,
            left: 16,
            right: 16,
            opacity: testsOpacity,
          }}
        >
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 8,
              color: GREEN_COLOR,
              opacity: 0.4,
              marginBottom: 6,
              textTransform: 'uppercase',
              letterSpacing: 1,
            }}
          >
            tests
          </div>
          <div
            style={{
              borderLeft: `3px solid ${GREEN_COLOR}`,
              paddingLeft: 12,
            }}
          >
            {TEST_LINES.map((line, i) => (
              <div
                key={i}
                style={{
                  fontFamily: 'JetBrains Mono, monospace',
                  fontSize: 8,
                  lineHeight: '14px',
                  color: GREEN_COLOR,
                  opacity: 0.5,
                }}
              >
                {line}
              </div>
            ))}
          </div>
        </div>

        {/* Grounding block */}
        <div
          style={{
            position: 'absolute',
            top: 460,
            left: 16,
            right: 16,
            opacity: groundingOpacity,
          }}
        >
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 8,
              color: CODE_COLOR,
              opacity: 0.3,
              marginBottom: 6,
              textTransform: 'uppercase',
              letterSpacing: 1,
            }}
          >
            grounding
          </div>
          <div
            style={{
              borderLeft: `3px solid rgba(148, 163, 184, 0.3)`,
              paddingLeft: 12,
            }}
          >
            {GROUNDING_LINES.map((line, i) => (
              <div
                key={i}
                style={{
                  fontFamily: 'JetBrains Mono, monospace',
                  fontSize: 8,
                  lineHeight: '13px',
                  color: CODE_COLOR,
                  opacity: 0.3,
                  whiteSpace: 'pre',
                }}
              >
                {line}
              </div>
            ))}
          </div>
        </div>

        {/* Whitespace below — the window is ~30% empty (implicit, no content here) */}

        {/* Fill indicator bar at bottom of window */}
        <div
          style={{
            position: 'absolute',
            bottom: 36,
            left: 8,
            right: 8,
            height: 4,
            backgroundColor: 'rgba(74, 144, 217, 0.05)',
            borderRadius: 2,
          }}
        >
          <div
            style={{
              width: `${fillBarWidth}%`,
              height: '100%',
              backgroundColor: `rgba(74, 144, 217, 0.2)`,
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
            color: RIGHT_COLOR,
            opacity: tokenOpacity * 0.5,
          }}
        >
          2,300 tokens
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
          color: GREEN_COLOR,
          opacity: tokenOpacity * 0.5,
        }}
      >
        100% author-curated
      </div>
    </div>
  );
};

export default RightPanel;
