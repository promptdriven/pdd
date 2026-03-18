import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { COLORS, LAYOUT, GRID, TIMING, FONT } from './constants';
import { CoordinateGrid } from './CoordinateGrid';
import { PrinterNozzle } from './PrinterNozzle';
import { MoldCrossSection } from './MoldCrossSection';
import { FluidFill } from './FluidFill';

export const defaultPart4PrecisionTradeoff02PrinterVsMoldSplitProps = {};

export const Part4PrecisionTradeoff02PrinterVsMoldSplit: React.FC = () => {
  const frame = useCurrentFrame();

  // ──────────── SPLIT LINE ────────────
  const splitLineProgress = interpolate(
    frame,
    [TIMING.splitStart, TIMING.splitStart + TIMING.splitDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // ──────────── HEADER FADE ────────────
  const headerOpacity = interpolate(
    frame,
    [TIMING.headerFadeStart, TIMING.headerFadeStart + TIMING.headerFadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // ──────────── GRID APPEAR ────────────
  const gridAppearProgress = interpolate(
    frame,
    [TIMING.gridAppearStart, TIMING.gridAppearStart + TIMING.gridAppearDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // ──────────── NOZZLE TRAVERSAL / DOT COUNT ────────────
  const nozzleRawProgress = interpolate(
    frame,
    [TIMING.nozzleStart, TIMING.nozzleEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const activeDotCount = Math.round(nozzleRawProgress * GRID.totalPoints);

  // ──────────── MOLD WALL DRAW ────────────
  const wallDrawProgress = interpolate(
    frame,
    [TIMING.moldWallDrawStart, TIMING.moldWallDrawStart + TIMING.moldWallDrawDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // ──────────── FLUID FILL ────────────
  const fluidProgress = interpolate(
    frame,
    [TIMING.fluidStart, TIMING.fluidEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // ──────────── CALLOUT FADE ────────────
  const calloutOpacity = interpolate(
    frame,
    [TIMING.calloutFadeStart, TIMING.calloutFadeStart + TIMING.calloutFadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Counter display value
  const counterValue = activeDotCount;

  // Is the nozzle actively traversing?
  const nozzleVisible = frame >= TIMING.nozzleStart && frame <= TIMING.nozzleEnd;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.sceneBg }}>
      {/* ═══════ LEFT PANEL — 3D PRINTING ═══════ */}
      <div
        style={{
          position: 'absolute',
          left: LAYOUT.leftPanelX,
          top: 0,
          width: LAYOUT.leftPanelWidth,
          height: LAYOUT.height,
          backgroundColor: COLORS.leftPanelBg,
          overflow: 'hidden',
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.headerY,
            width: '100%',
            textAlign: 'center',
            fontFamily: FONT.family,
            fontSize: FONT.headerSize,
            fontWeight: FONT.headerWeight,
            letterSpacing: FONT.headerLetterSpacing,
            color: COLORS.leftHeader,
            opacity: 0.5 * headerOpacity,
          }}
        >
          3D PRINTING
        </div>

        {/* Coordinate grid + active dots */}
        <CoordinateGrid
          gridAppearProgress={gridAppearProgress}
          activeDotCount={activeDotCount}
        />

        {/* Printer nozzle */}
        <PrinterNozzle
          activeDotCount={activeDotCount}
          visible={nozzleVisible}
        />

        {/* Counter */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.counterY,
            width: '100%',
            textAlign: 'center',
            fontFamily: FONT.family,
            fontSize: FONT.counterSize,
            color: COLORS.leftHeader,
          }}
        >
          Points specified:{' '}
          <span style={{ fontVariantNumeric: 'tabular-nums' }}>
            {counterValue}
          </span>
        </div>

        {/* Annotation */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.annotationY,
            width: '100%',
            textAlign: 'center',
            fontFamily: FONT.family,
            fontSize: FONT.annotationSize,
            color: COLORS.leftAnnotation,
            opacity: 0.4,
          }}
        >
          Every point must be specified
        </div>
      </div>

      {/* ═══════ SPLIT DIVIDER ═══════ */}
      <div
        style={{
          position: 'absolute',
          left: LAYOUT.splitX - 1,
          top: 0,
          width: LAYOUT.splitLineWidth,
          height: LAYOUT.height * splitLineProgress,
          backgroundColor: COLORS.splitLine,
          opacity: 0.25,
        }}
      />

      {/* ═══════ RIGHT PANEL — INJECTION MOLDING ═══════ */}
      <div
        style={{
          position: 'absolute',
          left: LAYOUT.rightPanelX,
          top: 0,
          width: LAYOUT.rightPanelWidth,
          height: LAYOUT.height,
          backgroundColor: COLORS.rightPanelBg,
          overflow: 'hidden',
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.headerY,
            width: '100%',
            textAlign: 'center',
            fontFamily: FONT.family,
            fontSize: FONT.headerSize,
            fontWeight: FONT.headerWeight,
            letterSpacing: FONT.headerLetterSpacing,
            color: COLORS.rightHeader,
            opacity: 0.5 * headerOpacity,
          }}
        >
          INJECTION MOLDING
        </div>

        {/* Mold cross-section (walls) */}
        <MoldCrossSection wallDrawProgress={wallDrawProgress} />

        {/* Fluid fill */}
        {frame >= TIMING.fluidStart && (
          <FluidFill fillProgress={fluidProgress} />
        )}

        {/* Counter (static) */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.counterY,
            width: '100%',
            textAlign: 'center',
            fontFamily: FONT.family,
            fontSize: FONT.counterSize,
            color: COLORS.rightHeader,
          }}
        >
          Walls defined: 4
        </div>

        {/* Annotation */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.annotationY,
            width: '100%',
            textAlign: 'center',
            fontFamily: FONT.family,
            fontSize: FONT.annotationSize,
            color: COLORS.rightAnnotation,
            opacity: 0.4,
          }}
        >
          Precision comes from the walls
        </div>
      </div>

      {/* ═══════ BOTTOM CALLOUT ═══════ */}
      <div
        style={{
          position: 'absolute',
          top: LAYOUT.calloutY,
          width: LAYOUT.width,
          textAlign: 'center',
          fontFamily: FONT.family,
          fontSize: FONT.calloutSize,
          color: COLORS.calloutText,
          opacity: 0.6 * calloutOpacity,
        }}
      >
        Precision through{' '}
        <span style={{ color: COLORS.calloutSpec }}>specification</span>
        {' '}vs. precision through{' '}
        <span style={{ color: COLORS.calloutConstraint }}>constraint</span>
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff02PrinterVsMoldSplit;
