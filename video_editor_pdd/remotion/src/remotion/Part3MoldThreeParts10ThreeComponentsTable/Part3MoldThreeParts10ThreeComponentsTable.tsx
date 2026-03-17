import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { EngineeringGrid } from './EngineeringGrid';
import { MoldDiagram } from './MoldDiagram';
import { SummaryTable } from './SummaryTable';
import {
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  AMBER,
  TEXT_PRIMARY,
  CODE_SNIPPET,
  TIMING,
} from './constants';

export const defaultPart3MoldThreeParts10ThreeComponentsTableProps = {};

export const Part3MoldThreeParts10ThreeComponentsTable: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Conflict Resolution Line ───
  const conflictOpacity = interpolate(
    frame,
    [TIMING.CONFLICT_START, TIMING.CONFLICT_START + TIMING.CONFLICT_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Underline draw progress
  const underlineProgress = interpolate(
    frame,
    [TIMING.CONFLICT_START + 5, TIMING.CONFLICT_START + 5 + TIMING.UNDERLINE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
  );

  // ─── Code Output ───
  const codeAppearOpacity = interpolate(
    frame,
    [TIMING.CODE_START, TIMING.CODE_START + 20],
    [0, 0.6],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Code glow
  const codeGlowOpacity = interpolate(
    frame,
    [
      TIMING.CODE_START,
      TIMING.CODE_START + 15,
      TIMING.CODE_GLOW_FADE_START,
      TIMING.CODE_GLOW_FADE_START + TIMING.CODE_GLOW_FADE_DURATION,
    ],
    [0, 0.15, 0.15, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Code dim after glow fades
  const codeDimOpacity = interpolate(
    frame,
    [
      TIMING.CODE_GLOW_FADE_START,
      TIMING.CODE_GLOW_FADE_START + TIMING.CODE_DIM_DURATION,
    ],
    [0.6, 0.2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const codeTextOpacity = frame >= TIMING.CODE_GLOW_FADE_START
    ? codeDimOpacity
    : codeAppearOpacity;

  // ─── Final Caption ───
  const captionOpacity = interpolate(
    frame,
    [TIMING.CAPTION_START, TIMING.CAPTION_START + TIMING.CAPTION_DURATION],
    [0, 0.7],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Engineering grid background */}
      <EngineeringGrid
        spacing={GRID_SPACING}
        color={GRID_COLOR}
        opacity={GRID_OPACITY}
      />

      {/* Mold diagram — visible from frame 0, slides left at frame 60 */}
      <MoldDiagram />

      {/* Summary table — fades in starting at frame 60 */}
      <SummaryTable />

      {/* Conflict resolution line */}
      {frame >= TIMING.CONFLICT_START && (
        <div
          style={{
            position: 'absolute',
            left: 650,
            right: 170,
            top: 700,
            opacity: conflictOpacity,
            textAlign: 'center',
          }}
        >
          <p
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 18,
              color: TEXT_PRIMARY,
              opacity: 0.8,
              margin: 0,
              lineHeight: 1.6,
            }}
          >
            When these conflict,{' '}
            <span style={{ fontWeight: 700, color: AMBER }}>tests win</span>.{' '}
            <span style={{ fontWeight: 700, color: AMBER }}>Always.</span>
          </p>

          {/* Underline under "tests win. Always." */}
          <svg
            width={260}
            height={6}
            style={{
              display: 'block',
              margin: '4px auto 0',
            }}
          >
            <line
              x1={0}
              y1={3}
              x2={260 * underlineProgress}
              y2={3}
              stroke={AMBER}
              strokeWidth={2}
              opacity={0.3}
            />
          </svg>
        </div>
      )}

      {/* Code output — appears below mold, glows then fades */}
      {frame >= TIMING.CODE_START && (
        <div
          style={{
            position: 'absolute',
            left: 150,
            top: 820,
            width: 400,
          }}
        >
          {/* Glow background */}
          <div
            style={{
              position: 'absolute',
              inset: -12,
              borderRadius: 8,
              backgroundColor: TEXT_PRIMARY,
              opacity: codeGlowOpacity,
              filter: 'blur(16px)',
            }}
          />

          <pre
            style={{
              fontFamily: 'JetBrains Mono, monospace',
              fontSize: 10,
              color: TEXT_PRIMARY,
              opacity: codeTextOpacity,
              margin: 0,
              padding: '10px 14px',
              backgroundColor: '#0F172A',
              borderRadius: 6,
              border: '1px solid #1E293B',
              lineHeight: 1.6,
              position: 'relative',
              whiteSpace: 'pre-wrap',
            }}
          >
            {CODE_SNIPPET}
          </pre>
        </div>
      )}

      {/* Final caption */}
      {frame >= TIMING.CAPTION_START && (
        <div
          style={{
            position: 'absolute',
            bottom: 40,
            left: 0,
            right: 0,
            textAlign: 'center',
            opacity: captionOpacity,
          }}
        >
          <p
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 14,
              color: AMBER,
              margin: 0,
            }}
          >
            The code is output. The mold is what matters.
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts10ThreeComponentsTable;
