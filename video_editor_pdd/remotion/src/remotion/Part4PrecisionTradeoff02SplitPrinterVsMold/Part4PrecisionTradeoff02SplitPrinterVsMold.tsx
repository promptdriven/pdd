import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CANVAS_HEIGHT,
  PANEL_WIDTH,
  DIVIDER_WIDTH_PX,
  DIVIDER_COLOR,
  DIVIDER_LINE_WIDTH,
  DIVIDER_OPACITY,
  DIVIDER_BG,
  BG_OUTER,
  BG_PANEL,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_FONT_FAMILY,
  PRINTER_HEADER_COLOR,
  MOLD_HEADER_COLOR,
  PHASE_ESTABLISH_START,
  PHASE_ESTABLISH_END,
  PHASE_FADEOUT_START,
  PHASE_FADEOUT_END,
} from './constants';
import { CoordinateGrid } from './CoordinateGrid';
import { PrinterNozzle } from './PrinterNozzle';
import { MoldCavity } from './MoldCavity';
import { LiquidFlow } from './LiquidFlow';

export const defaultPart4PrecisionTradeoff02SplitPrinterVsMoldProps = {};

export const Part4PrecisionTradeoff02SplitPrinterVsMold: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel fade-in: easeOut(quad) over 30 frames
  const panelOpacity = interpolate(
    frame,
    [PHASE_ESTABLISH_START, PHASE_ESTABLISH_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Divider fade-in: easeOut(quad) over 15 frames
  const dividerOpacity = interpolate(
    frame,
    [PHASE_ESTABLISH_START, 15],
    [0, DIVIDER_OPACITY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Divider draw (height grows from center)
  const dividerHeight = interpolate(
    frame,
    [PHASE_ESTABLISH_START, PHASE_ESTABLISH_END],
    [0, CANVAS_HEIGHT],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Final fade out: easeIn(quad) over 60 frames (420-480)
  const fadeOutOpacity = interpolate(
    frame,
    [PHASE_FADEOUT_START, PHASE_FADEOUT_END],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
  );

  const masterOpacity = Math.min(panelOpacity, fadeOutOpacity);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_OUTER,
        opacity: masterOpacity,
      }}
    >
      {/* Left Panel — 3D Printer */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: BG_PANEL,
          overflow: 'hidden',
        }}
      >
        {/* Header */}
        <div
          style={{
            position: 'absolute',
            top: 24,
            left: 0,
            width: PANEL_WIDTH,
            textAlign: 'center',
            fontFamily: HEADER_FONT_FAMILY,
            fontSize: HEADER_FONT_SIZE,
            fontWeight: HEADER_FONT_WEIGHT,
            color: PRINTER_HEADER_COLOR,
            zIndex: 10,
            opacity: 0.9,
          }}
        >
          3D Printer
        </div>

        {/* Coordinate Grid */}
        <CoordinateGrid panelOpacity={1} />

        {/* Nozzle and deposits */}
        <PrinterNozzle />
      </div>

      {/* Center Divider */}
      <div
        style={{
          position: 'absolute',
          left: PANEL_WIDTH,
          top: 0,
          width: DIVIDER_WIDTH_PX,
          height: CANVAS_HEIGHT,
          backgroundColor: DIVIDER_BG,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
        }}
      >
        <div
          style={{
            width: DIVIDER_LINE_WIDTH,
            height: dividerHeight,
            backgroundColor: DIVIDER_COLOR,
            opacity: dividerOpacity,
            borderRadius: 1,
          }}
        />
      </div>

      {/* Right Panel — Injection Mold */}
      <div
        style={{
          position: 'absolute',
          left: PANEL_WIDTH + DIVIDER_WIDTH_PX,
          top: 0,
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: BG_PANEL,
          overflow: 'hidden',
        }}
      >
        {/* Header */}
        <div
          style={{
            position: 'absolute',
            top: 24,
            left: 0,
            width: PANEL_WIDTH,
            textAlign: 'center',
            fontFamily: HEADER_FONT_FAMILY,
            fontSize: HEADER_FONT_SIZE,
            fontWeight: HEADER_FONT_WEIGHT,
            color: MOLD_HEADER_COLOR,
            zIndex: 10,
            opacity: 0.9,
          }}
        >
          Injection Mold
        </div>

        {/* Mold cavity walls and glow */}
        <MoldCavity panelOpacity={1} />

        {/* Liquid flow particles */}
        <LiquidFlow />
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff02SplitPrinterVsMold;
