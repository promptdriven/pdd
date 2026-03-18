import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  SPLIT_X,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_WIDTH,
  BG_COLOR,
  LEFT_BG,
  RIGHT_BG,
  SPLIT_LINE_COLOR,
  CRAFT_ACCENT,
  MOLD_ACCENT,
  CHAIR_CENTER,
  CHAIR_SIZE,
  MOLD_CENTER,
  MOLD_SIZE,
  SPLIT_LINE_DRAW_DURATION,
  PHASE_1_END,
  PHASE_4_START,
  PHASE_7_START,
  SUMMARY_FADE_DURATION,
} from './constants';
import { WoodenChair } from './WoodenChair';
import { MoldCrossSection } from './MoldCrossSection';
import { ValueAura } from './ValueAura';

export const defaultPart2ParadigmShift05ValueMigrationSplitProps = {};

export const Part2ParadigmShift05ValueMigrationSplit: React.FC = () => {
  const frame = useCurrentFrame();

  // === Split line draw animation ===
  const splitLineHeight = interpolate(
    frame,
    [0, SPLIT_LINE_DRAW_DURATION],
    [0, HEIGHT],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // === Panel header fade-in ===
  const headerOpacity = interpolate(
    frame,
    [0, PHASE_1_END],
    [0, 0.5],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // === Summary labels fade-in ===
  const summaryOpacity = interpolate(
    frame,
    [PHASE_7_START, PHASE_7_START + SUMMARY_FADE_DURATION],
    [0, 0.6],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* ========== LEFT PANEL — CRAFTING ========== */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: HEIGHT,
          backgroundColor: LEFT_BG,
          overflow: 'hidden',
        }}
      >
        {/* Panel Header */}
        <div
          style={{
            position: 'absolute',
            top: 40,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 600,
            color: CRAFT_ACCENT,
            opacity: headerOpacity,
            letterSpacing: 2,
            zIndex: 10,
          }}
        >
          CRAFTING
        </div>

        {/* Value Aura — on the chair (renders behind) */}
        <ValueAura
          centerX={CHAIR_CENTER.x}
          centerY={CHAIR_CENTER.y}
          width={CHAIR_SIZE.w}
          height={CHAIR_SIZE.h}
          color={CRAFT_ACCENT}
          startFrame={PHASE_4_START}
        />

        {/* Wooden Chair with chisel marks and history labels */}
        <WoodenChair />

        {/* Summary label */}
        <div
          style={{
            position: 'absolute',
            bottom: HEIGHT - 980,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 13,
            color: CRAFT_ACCENT,
            opacity: summaryOpacity,
          }}
        >
          Value lives in the object
        </div>
      </div>

      {/* ========== SPLIT DIVIDER ========== */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X - 1,
          top: 0,
          width: 2,
          height: splitLineHeight,
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: 0.25,
        }}
      />

      {/* ========== RIGHT PANEL — MOLDING ========== */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X + 2,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: HEIGHT,
          backgroundColor: RIGHT_BG,
          overflow: 'hidden',
        }}
      >
        {/* Panel Header */}
        <div
          style={{
            position: 'absolute',
            top: 40,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 600,
            color: MOLD_ACCENT,
            opacity: headerOpacity,
            letterSpacing: 2,
            zIndex: 10,
          }}
        >
          MOLDING
        </div>

        {/* Value Aura — on the MOLD (not the plastic part) */}
        <ValueAura
          centerX={MOLD_CENTER.x}
          centerY={MOLD_CENTER.y}
          width={MOLD_SIZE.w}
          height={MOLD_SIZE.h}
          color={MOLD_ACCENT}
          startFrame={PHASE_4_START}
        />

        {/* Mold cross-section with plastic part */}
        <MoldCrossSection />

        {/* Summary label */}
        <div
          style={{
            position: 'absolute',
            bottom: HEIGHT - 980,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 13,
            color: MOLD_ACCENT,
            opacity: summaryOpacity,
          }}
        >
          Value lives in the specification
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift05ValueMigrationSplit;
