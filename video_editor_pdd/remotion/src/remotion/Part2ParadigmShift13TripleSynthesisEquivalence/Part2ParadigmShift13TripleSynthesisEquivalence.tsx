import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BG_COLOR,
  TOTAL_FRAMES,
  RUN1_START,
  RUN2_START,
  RUN3_START,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  RUNS,
} from './constants';
import CodeBlock from './CodeBlock';
import DownArrows from './DownArrows';
import NetlistColumn from './NetlistColumn';
import Checkmark from './Checkmark';

export const defaultPart2ParadigmShift13TripleSynthesisEquivalenceProps = {};

export const Part2ParadigmShift13TripleSynthesisEquivalence: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade out columns starting at frame 600 over 60 frames
  const columnFadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Equivalence message persists longer — fades from 660
  const equivFadeOut = interpolate(
    frame,
    [FADE_OUT_START + FADE_OUT_DURATION, FADE_OUT_START + FADE_OUT_DURATION + 60],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  const runStartFrames = [RUN1_START, RUN2_START, RUN3_START];

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Verilog source code (visible from frame 0) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div style={{ opacity: columnFadeOut }}>
          <CodeBlock />
        </div>
      </Sequence>

      {/* Arrows from code to columns */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div style={{ opacity: columnFadeOut }}>
          <DownArrows />
        </div>
      </Sequence>

      {/* Three netlist columns */}
      {RUNS.map((run, i) => (
        <Sequence key={run.id} from={0} durationInFrames={TOTAL_FRAMES}>
          <div style={{ opacity: columnFadeOut }}>
            <NetlistColumn
              topology={run.topology}
              colX={run.colX}
              startFrame={runStartFrames[i]}
              label={run.label}
            />
          </div>
        </Sequence>
      ))}

      {/* Equivalence checkmarks — visible from frame 300 */}
      {RUNS.map((run, i) => (
        <Sequence key={`check-${run.id}`} from={0} durationInFrames={TOTAL_FRAMES}>
          <div style={{ opacity: equivFadeOut }}>
            <Checkmark colX={run.colX} index={i} />
          </div>
        </Sequence>
      ))}

      {/* Central equivalence banner that persists through fade-out */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <EquivalenceBanner />
      </Sequence>
    </AbsoluteFill>
  );
};

/**
 * A centered banner that appears after all columns are shown equivalent,
 * persists during fade-out, and provides the key takeaway.
 */
const EquivalenceBanner: React.FC = () => {
  const frame = useCurrentFrame();

  // Appear at frame 420 (after checkmarks settle)
  const bannerOpacity = interpolate(frame, [420, 450], [0, 0.95], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Fade at end
  const bannerFadeOut = interpolate(frame, [680, 740], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  if (frame < 420) return null;

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 60,
        left: 0,
        width: 1920,
        display: 'flex',
        justifyContent: 'center',
        opacity: bannerOpacity * bannerFadeOut,
      }}
    >
      <div
        style={{
          background: 'rgba(90, 170, 110, 0.1)',
          border: '2px solid rgba(90, 170, 110, 0.4)',
          borderRadius: 12,
          padding: '14px 40px',
          display: 'flex',
          alignItems: 'center',
          gap: 12,
        }}
      >
        <svg width={28} height={28} viewBox="0 0 28 28">
          <circle cx={14} cy={14} r={13} fill="none" stroke="#5AAA6E" strokeWidth={2} />
          <polyline
            points="8,14 12,19 20,9"
            fill="none"
            stroke="#5AAA6E"
            strokeWidth={2.5}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </svg>
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 20,
            fontWeight: 600,
            color: '#5AAA6E',
            letterSpacing: '0.02em',
          }}
        >
          Different gates, different wiring — identical behavior
        </span>
      </div>
    </div>
  );
};

export default Part2ParadigmShift13TripleSynthesisEquivalence;
