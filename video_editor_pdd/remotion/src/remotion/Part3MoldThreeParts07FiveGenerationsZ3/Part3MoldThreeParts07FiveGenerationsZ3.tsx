import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  COLORS,
  PANEL_POSITIONS,
  CODE_VARIANTS,
  TEST_RESULTS,
  TIMING,
} from './constants';
import { DotGrid } from './DotGrid';
import { CodePanel } from './CodePanel';
import { ProofSection } from './ProofSection';

export const defaultPart3MoldThreeParts07FiveGenerationsZ3Props = {};

export const Part3MoldThreeParts07FiveGenerationsZ3: React.FC = () => {
  const frame = useCurrentFrame();

  // Beat 1 fade-out during cross-dissolve
  const beat1Opacity = interpolate(
    frame,
    [TIMING.beat2Start, TIMING.beat2Start + TIMING.crossDissolveDuration],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  // Caption fade-in
  const captionOpacity = interpolate(
    frame,
    [TIMING.captionStart, TIMING.captionStart + 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );
  const captionSlideY = interpolate(
    frame,
    [TIMING.captionStart, TIMING.captionStart + 20],
    [12, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const filenames = [
    'user_parser_v1.py',
    'user_parser_v2.py',
    'user_parser_v3.py',
    'user_parser_v4.py',
    'user_parser_v5.py',
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.bg }}>
      {/* Dot grid background */}
      <DotGrid />

      {/* Beat 1: Five Code Panels */}
      <AbsoluteFill style={{ opacity: beat1Opacity }}>
        {/* Section title */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 100,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            color: COLORS.textMuted,
            opacity: interpolate(frame, [0, 15], [0, 0.5], {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
            }),
            letterSpacing: 3,
            textTransform: 'uppercase',
          }}
        >
          Five Generations
        </div>

        {/* Five code panels */}
        {PANEL_POSITIONS.map((pos, i) => (
          <CodePanel
            key={i}
            x={pos.x}
            y={pos.y}
            panelIndex={i}
            code={CODE_VARIANTS[i]}
            filename={filenames[i]}
            testResult={TEST_RESULTS[i]}
            isWinner={i === 2}
          />
        ))}

        {/* Caption */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 750 + captionSlideY,
            textAlign: 'center',
            opacity: captionOpacity,
          }}
        >
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 18,
              color: COLORS.textPrimary,
              opacity: 0.7,
              lineHeight: '28px',
            }}
          >
            Generate five. Pick the one that passes all tests.
          </div>
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 14,
              color: COLORS.textMuted,
              opacity: 0.5,
              marginTop: 10,
            }}
          >
            The walls don't care how many attempts it took.
          </div>
        </div>
      </AbsoluteFill>

      {/* Beat 2: Z3 Formal Proof (overlays with its own background) */}
      <ProofSection />
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts07FiveGenerationsZ3;
