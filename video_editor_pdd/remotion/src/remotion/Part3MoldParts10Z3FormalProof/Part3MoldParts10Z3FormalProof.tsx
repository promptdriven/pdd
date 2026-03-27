import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import {
  BG_COLOR,
  PANEL_SLIDE_IN_END,
  PANEL_SLIDE_OUT_START,
  PANEL_SLIDE_OUT_END,
  PURPLE_ACCENT,
} from './constants';
import { MoldCrossSection } from './MoldCrossSection';
import { AnnotationPanel } from './AnnotationPanel';
import { ConnectorLines } from './ConnectorLines';

export const defaultPart3MoldParts10Z3FormalProofProps = {};

/**
 * Section 3.10 — Z3 Formal Proof Sidebar Annotation
 *
 * A sidebar panel slides in from the right, overlaying a dimmed mold cross-section.
 * The panel contains word-by-word text about Z3/SMT formal verification,
 * emphasis lines, logo badges, and animated connector lines to proven mold walls.
 *
 * Duration: 780 frames (26s @ 30fps)
 */
export const Part3MoldParts10Z3FormalProof: React.FC = () => {
  const frame = useCurrentFrame();

  // Mold dims to 0.3 during annotation, returns to full at exit
  const moldDimIn = interpolate(frame, [0, PANEL_SLIDE_IN_END], [0.7, 0.3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });
  const moldDimOut = interpolate(
    frame,
    [PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [0.3, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );
  const moldOpacity =
    frame < PANEL_SLIDE_OUT_START ? moldDimIn : moldDimOut;

  // Subtle background grid pattern
  const gridOpacity = 0.03;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, system-ui, sans-serif',
      }}
    >
      {/* Subtle grid overlay */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0, opacity: gridOpacity }}
      >
        <defs>
          <pattern
            id="gridPattern"
            width={60}
            height={60}
            patternUnits="userSpaceOnUse"
          >
            <path
              d="M 60 0 L 0 0 0 60"
              fill="none"
              stroke="#FFFFFF"
              strokeWidth={0.5}
            />
          </pattern>
        </defs>
        <rect width={1920} height={1080} fill="url(#gridPattern)" />
      </svg>

      {/* Ambient purple glow in background */}
      <div
        style={{
          position: 'absolute',
          left: 200,
          top: 300,
          width: 400,
          height: 400,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${PURPLE_ACCENT}08 0%, transparent 70%)`,
          pointerEvents: 'none',
        }}
      />

      {/* Mold cross-section (left side) */}
      <MoldCrossSection dimOpacity={moldOpacity} />

      {/* Connector lines from panel to proven walls */}
      <ConnectorLines />

      {/* Annotation panel (right side) */}
      <AnnotationPanel />

      {/* Section label — visible from frame 0 */}
      <div
        style={{
          position: 'absolute',
          top: 40,
          right: 60,
          fontFamily: 'Inter, system-ui, sans-serif',
          fontSize: 13,
          fontWeight: 500,
          color: PURPLE_ACCENT,
          opacity: 0.5,
          letterSpacing: 2,
          textTransform: 'uppercase',
        }}
      >
        Formal Verification
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldParts10Z3FormalProof;
