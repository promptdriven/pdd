import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from 'remotion';

const FONT_FAMILY = 'Inter, sans-serif';
const CALLOUT_BG = '#1E293B';
const SOURCE_TEXT_COLOR = '#94A3B8';
const CONNECTOR_DRAW_FRAMES = 30;
const CALLOUT_SCALE_FRAMES = 20;

interface AnnotationCalloutProps {
  /** Frame at which this annotation starts appearing */
  startFrame: number;
  /** Position of the callout box */
  x: number;
  y: number;
  /** Main annotation text (e.g. "Code churn: +44%") */
  mainText: string;
  /** Source/fine-print line */
  sourceText: string;
  /** Accent/border color */
  accentColor: string;
  /** Connector target point (where the line points into the chart) */
  connectorTargetX: number;
  connectorTargetY: number;
}

export const AnnotationCallout: React.FC<AnnotationCalloutProps> = ({
  startFrame,
  x,
  y,
  mainText,
  sourceText,
  accentColor,
  connectorTargetX,
  connectorTargetY,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Connector line draws in over CONNECTOR_DRAW_FRAMES
  const connectorProgress = interpolate(
    localFrame,
    [0, CONNECTOR_DRAW_FRAMES],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Callout scales in after connector starts drawing (overlapping slightly)
  const scaleProgress = spring({
    frame: Math.max(0, localFrame - 10),
    fps,
    config: {
      damping: 12,
      stiffness: 150,
      mass: 0.6,
    },
  });

  // Text typing effect: fades in over a few frames after the callout appears
  const textOpacity = interpolate(
    localFrame,
    [CALLOUT_SCALE_FRAMES, CALLOUT_SCALE_FRAMES + 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Connector line intermediate point: from callout left edge to target
  const connectorStartX = x;
  const connectorStartY = y + 40;

  const currentEndX = interpolate(
    connectorProgress,
    [0, 1],
    [connectorStartX, connectorTargetX],
  );
  const currentEndY = interpolate(
    connectorProgress,
    [0, 1],
    [connectorStartY, connectorTargetY],
  );

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: 1920, height: 1080 }}>
      {/* Connector line */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
      >
        <line
          x1={connectorStartX}
          y1={connectorStartY}
          x2={currentEndX}
          y2={currentEndY}
          stroke={accentColor}
          strokeWidth={1}
          opacity={0.5}
        />
        {/* Small dot at the target end */}
        {connectorProgress > 0.9 && (
          <circle
            cx={connectorTargetX}
            cy={connectorTargetY}
            r={3}
            fill={accentColor}
            opacity={connectorProgress}
          />
        )}
      </svg>

      {/* Callout box */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: 440,
          transform: `scale(${scaleProgress})`,
          transformOrigin: 'left center',
          background: CALLOUT_BG,
          border: `1.5px solid ${accentColor}`,
          borderRadius: 8,
          padding: '14px 20px',
          boxSizing: 'border-box',
        }}
      >
        {/* Main text */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 18,
            fontWeight: 700,
            color: accentColor,
            opacity: textOpacity,
            lineHeight: 1.3,
          }}
        >
          {mainText}
        </div>

        {/* Source text */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 12,
            fontWeight: 400,
            color: SOURCE_TEXT_COLOR,
            opacity: textOpacity * 0.85,
            marginTop: 4,
            lineHeight: 1.3,
          }}
        >
          {sourceText}
        </div>
      </div>
    </div>
  );
};

export default AnnotationCallout;
