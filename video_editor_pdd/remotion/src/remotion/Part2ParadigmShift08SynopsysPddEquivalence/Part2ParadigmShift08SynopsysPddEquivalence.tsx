import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import { FlowRow } from './FlowRow';
import { DashedConnection } from './DashedConnection';
import {
  BG_COLOR,
  SYNOPSYS_COLOR,
  PDD_COLOR,
  TEXT_COLOR,
  SYNOPSYS_STAGES,
  PDD_STAGES,
  SYNOPSYS_Y,
  PDD_Y,
  EQUIVALENCE_Y,
  STAGE_X_POSITIONS,
  TIMING,
} from './constants';

export const defaultPart2ParadigmShift08SynopsysPddEquivalenceProps = {};

export const Part2ParadigmShift08SynopsysPddEquivalence: React.FC = () => {
  const frame = useCurrentFrame();

  // === Row Labels (fade in from frame 0) ===
  const labelOpacity = interpolate(
    frame,
    [TIMING.LABELS_START, TIMING.LABELS_START + TIMING.LABELS_FADE],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // === Equivalence Symbol ===
  const equivFadeIn = interpolate(
    frame,
    [TIMING.EQUIV_START, TIMING.EQUIV_START + TIMING.EQUIV_FADE],
    [0, 1],
    {
      easing: Easing.out(Easing.cubic),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Pulsing: cycles opacity between 0.3 and 0.6
  const pulsePhase = frame - TIMING.EQUIV_START;
  const pulseValue = frame >= TIMING.EQUIV_START
    ? interpolate(
        pulsePhase % TIMING.EQUIV_PULSE_PERIOD,
        [0, TIMING.EQUIV_PULSE_PERIOD / 2, TIMING.EQUIV_PULSE_PERIOD],
        [0.3, 0.6, 0.3],
        {
          easing: Easing.inOut(Easing.sin),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      )
    : 0;

  const equivOpacity = equivFadeIn * pulseValue;

  // === Summary Text ===
  const summaryOpacity = interpolate(
    frame,
    [TIMING.SUMMARY_START, TIMING.SUMMARY_START + TIMING.SUMMARY_FADE],
    [0, 0.6],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* === Row Labels === */}
      <div
        style={{
          position: 'absolute',
          left: 80,
          top: SYNOPSYS_Y - 6,
          fontSize: 12,
          fontWeight: 600,
          color: SYNOPSYS_COLOR,
          opacity: labelOpacity * 0.4,
          letterSpacing: 2,
        }}
      >
        SYNOPSYS
      </div>

      <div
        style={{
          position: 'absolute',
          left: 80,
          top: PDD_Y - 6,
          fontSize: 12,
          fontWeight: 600,
          color: PDD_COLOR,
          opacity: labelOpacity * 0.4,
          letterSpacing: 2,
        }}
      >
        PDD
      </div>

      {/* === Top Row: Synopsys Flow === */}
      <Sequence from={TIMING.TOP_ROW_START}>
        <FlowRow
          stages={SYNOPSYS_STAGES}
          y={SYNOPSYS_Y}
        />
      </Sequence>

      {/* === Bottom Row: PDD Flow === */}
      <Sequence from={TIMING.BOTTOM_ROW_START}>
        <FlowRow
          stages={PDD_STAGES}
          y={PDD_Y}
        />
      </Sequence>

      {/* === Vertical Dashed Connections === */}
      <Sequence from={TIMING.CONNECTIONS_START}>
        {STAGE_X_POSITIONS.map((x, i) => (
          <DashedConnection
            key={x}
            x={x}
            delay={i * TIMING.CONNECTION_STAGGER}
            drawDuration={TIMING.CONNECTION_DRAW}
          />
        ))}
      </Sequence>

      {/* === Equivalence Symbol === */}
      <div
        style={{
          position: 'absolute',
          left: 960,
          top: EQUIVALENCE_Y,
          transform: 'translate(-50%, -50%)',
          fontSize: 64,
          fontWeight: 700,
          color: TEXT_COLOR,
          opacity: equivOpacity,
          textAlign: 'center',
          lineHeight: 1,
        }}
      >
        {/* Glow layer */}
        <div
          style={{
            position: 'absolute',
            left: '50%',
            top: '50%',
            transform: 'translate(-50%, -50%)',
            fontSize: 64,
            fontWeight: 700,
            color: TEXT_COLOR,
            opacity: 0.08,
            filter: 'blur(20px)',
            pointerEvents: 'none',
          }}
        >
          ≡
        </div>
        ≡
      </div>

      {/* === Summary Text === */}
      <div
        style={{
          position: 'absolute',
          left: 960,
          top: 900,
          transform: 'translateX(-50%)',
          fontSize: 16,
          fontWeight: 600,
          color: TEXT_COLOR,
          opacity: summaryOpacity,
          whiteSpace: 'nowrap',
          textAlign: 'center',
        }}
      >
        Specification in → verified artifact out
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift08SynopsysPddEquivalence;
