import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const FONT_FAMILY = 'Inter, sans-serif';
const CALLOUT_BG = '#1E293B';
const SOURCE_TEXT_COLOR = '#94A3B8';

interface PrevAnnotation {
  text: string;
  source: string;
  x: number;
  y: number;
  accentColor: string;
}

const PREVIOUS_ANNOTATIONS: PrevAnnotation[] = [
  {
    text: 'GitHub survey: 55% faster',
    source: '(GitHub, 2024)',
    x: 900,
    y: 260,
    accentColor: '#3B82F6',
  },
  {
    text: 'Uplevel: +41% PRs merged',
    source: '(Uplevel, 2024)',
    x: 900,
    y: 370,
    accentColor: '#8B5CF6',
  },
];

export const PreviousAnnotations: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade from full opacity to 0.3 over frames 0-30
  const opacity = interpolate(frame, [0, 30], [1.0, 0.3], {
    easing: Easing.in(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <>
      {PREVIOUS_ANNOTATIONS.map((ann) => (
        <div
          key={ann.text}
          style={{
            position: 'absolute',
            left: ann.x,
            top: ann.y,
            width: 360,
            background: CALLOUT_BG,
            border: `1.5px solid ${ann.accentColor}`,
            borderRadius: 8,
            padding: '12px 18px',
            boxSizing: 'border-box',
            opacity,
          }}
        >
          <div
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: 17,
              fontWeight: 700,
              color: ann.accentColor,
              lineHeight: 1.3,
            }}
          >
            {ann.text}
          </div>
          <div
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: 12,
              fontWeight: 400,
              color: SOURCE_TEXT_COLOR,
              marginTop: 3,
              lineHeight: 1.3,
            }}
          >
            {ann.source}
          </div>
        </div>
      ))}
    </>
  );
};

export default PreviousAnnotations;
