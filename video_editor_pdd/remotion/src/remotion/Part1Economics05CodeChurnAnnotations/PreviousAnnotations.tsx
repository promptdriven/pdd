import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const FONT_FAMILY = 'Inter, system-ui, sans-serif';
const COLOR_SLATE_DARK = '#1E293B';
const COLOR_SLATE = '#94A3B8';
const COLOR_INDIGO = '#6366F1';
const CALLOUT_WIDTH = 350;
const CALLOUT_BORDER_RADIUS = 8;

const PREV_FADE_DURATION = 30;

/**
 * Simulated "previous annotations" from the GitHub/Uplevel section.
 * These fade to 30% opacity as the new GitClear annotations appear.
 */
export const PreviousAnnotations: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, PREV_FADE_DURATION], [1.0, 0.3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const annotations = [
    {
      x: 1400,
      y: 180,
      text: 'Bugs: +41% post-Copilot',
      source: '(Uplevel, 2024)',
    },
    {
      x: 1400,
      y: 270,
      text: 'PR revert rate: 2× baseline',
      source: '(GitHub internal)',
    },
  ];

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        opacity,
        pointerEvents: 'none',
      }}
    >
      {/* Connector lines */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', left: 0, top: 0 }}
      >
        <line
          x1={1400}
          y1={215}
          x2={1050}
          y2={380}
          stroke={COLOR_INDIGO}
          strokeWidth={1}
          opacity={0.4}
        />
        <line
          x1={1400}
          y1={305}
          x2={1080}
          y2={480}
          stroke={COLOR_INDIGO}
          strokeWidth={1}
          opacity={0.4}
        />
      </svg>

      {annotations.map((ann, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            left: ann.x,
            top: ann.y,
            width: CALLOUT_WIDTH,
            background: COLOR_SLATE_DARK,
            border: `1.5px solid ${COLOR_INDIGO}`,
            borderRadius: CALLOUT_BORDER_RADIUS,
            padding: '12px 18px',
          }}
        >
          <div
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: 16,
              fontWeight: 700,
              color: COLOR_INDIGO,
              lineHeight: 1.3,
            }}
          >
            {ann.text}
          </div>
          <div
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: 11,
              fontWeight: 400,
              color: COLOR_SLATE,
              marginTop: 3,
            }}
          >
            {ann.source}
          </div>
        </div>
      ))}
    </div>
  );
};

export default PreviousAnnotations;
