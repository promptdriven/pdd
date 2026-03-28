import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { CoordinateGrid } from './CoordinateGrid';
import { PrinterNozzle } from './PrinterNozzle';
import { MoldCavity } from './MoldCavity';
import { LiquidFlow } from './LiquidFlow';

// ── Layout constants ──────────────────────────────────────────
const CANVAS_WIDTH = 1920;
const CANVAS_HEIGHT = 1080;
const PANEL_WIDTH = 940;
const DIVIDER_GAP = 40;
const DIVIDER_WIDTH = 2;
const DIVIDER_COLOR = '#FFFFFF';
const DIVIDER_OPACITY = 0.4;

const SCENE_BG = '#0A0F1A';
const PANEL_BG = '#0D1117';

// Colors
const PRINTER_HEADER_COLOR = '#94A3B8';
const MOLD_HEADER_COLOR = '#D9944A';

// Typography
const HEADER_FONT_SIZE = 16;
const HEADER_FONT_WEIGHT = 600;

// Timing
const FADE_OUT_START = 420;
const FADE_OUT_DURATION = 60;

// ── Default props export ──────────────────────────────────────
export const defaultPart4PrecisionTradeoff02SplitPrinterVsMoldProps = {};

// ── Main component ────────────────────────────────────────────
export const Part4PrecisionTradeoff02SplitPrinterVsMold: React.FC = () => {
  const frame = useCurrentFrame();

  // Establish: panels and divider fade in over 0-30
  const panelOpacity = interpolate(frame, [0, 30], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });

  // Divider draws from center outward
  const dividerOpacity = interpolate(frame, [0, 15], [0, DIVIDER_OPACITY], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });
  const dividerScale = interpolate(frame, [0, 20], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });

  // Final fade out
  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      easing: Easing.in(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const masterOpacity = panelOpacity * fadeOut;

  // Panel positions
  const leftPanelX = 0;
  const rightPanelX = PANEL_WIDTH + DIVIDER_GAP;
  const dividerX = PANEL_WIDTH + (DIVIDER_GAP - DIVIDER_WIDTH) / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: SCENE_BG,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Center divider */}
      <div
        style={{
          position: 'absolute',
          left: dividerX,
          top: CANVAS_HEIGHT * 0.5 * (1 - dividerScale),
          width: DIVIDER_WIDTH,
          height: CANVAS_HEIGHT * dividerScale,
          backgroundColor: DIVIDER_COLOR,
          opacity: dividerOpacity * fadeOut,
        }}
      />

      {/* ── LEFT PANEL: 3D Printer ── */}
      <div
        style={{
          position: 'absolute',
          left: leftPanelX,
          top: 0,
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: PANEL_BG,
          opacity: masterOpacity,
          overflow: 'hidden',
        }}
      >
        {/* Header */}
        <div
          style={{
            position: 'absolute',
            top: 30,
            left: 0,
            width: PANEL_WIDTH,
            textAlign: 'center',
            fontSize: HEADER_FONT_SIZE,
            fontWeight: HEADER_FONT_WEIGHT,
            color: PRINTER_HEADER_COLOR,
            opacity: 0.85,
            letterSpacing: '0.05em',
            zIndex: 10,
          }}
        >
          3D Printer
        </div>

        {/* Coordinate Grid */}
        <CoordinateGrid
          panelWidth={PANEL_WIDTH}
          panelHeight={CANVAS_HEIGHT}
          showLabels={true}
        />

        {/* Printer Nozzle + deposit trail */}
        <PrinterNozzle
          panelWidth={PANEL_WIDTH}
          panelHeight={CANVAS_HEIGHT}
        />
      </div>

      {/* ── RIGHT PANEL: Injection Mold ── */}
      <div
        style={{
          position: 'absolute',
          left: rightPanelX,
          top: 0,
          width: PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: PANEL_BG,
          opacity: masterOpacity,
          overflow: 'hidden',
        }}
      >
        {/* Header */}
        <div
          style={{
            position: 'absolute',
            top: 30,
            left: 0,
            width: PANEL_WIDTH,
            textAlign: 'center',
            fontSize: HEADER_FONT_SIZE,
            fontWeight: HEADER_FONT_WEIGHT,
            color: MOLD_HEADER_COLOR,
            opacity: 0.85,
            letterSpacing: '0.05em',
            zIndex: 10,
          }}
        >
          Injection Mold
        </div>

        {/* Mold Cavity walls */}
        <MoldCavity
          panelWidth={PANEL_WIDTH}
          panelHeight={CANVAS_HEIGHT}
        />

        {/* Liquid Flow particles */}
        <LiquidFlow
          panelWidth={PANEL_WIDTH}
          panelHeight={CANVAS_HEIGHT}
        />
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff02SplitPrinterVsMold;
