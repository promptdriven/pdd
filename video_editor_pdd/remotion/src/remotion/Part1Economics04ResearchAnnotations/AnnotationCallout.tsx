import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';

export interface AnnotationCalloutProps {
  /** Frame offset within the parent Sequence (already handled by Sequence from=) */
  borderColor: string;
  mainText: string;
  source: string;
  finePrint: string;
  /** Position of the callout box top-left corner */
  boxX: number;
  boxY: number;
  /** Position of the connector target (on the chart line) */
  targetX: number;
  targetY: number;
}

const CALLOUT_FILL = '#1E293B';
const CALLOUT_BORDER_WIDTH = 1.5;
const CALLOUT_RADIUS = 8;
const CALLOUT_PADDING = 16;
const CALLOUT_WIDTH = 340;

const CONNECTOR_DRAW_DURATION = 30;
const BOX_SCALE_DURATION = 20;
const TEXT_FRAMES_PER_CHAR = 2;

const SOURCE_COLOR = '#94A3B8';
const FINEPRINT_COLOR = '#64748B';
const FINEPRINT_OPACITY = 0.78;

const AnnotationCallout: React.FC<AnnotationCalloutProps> = ({
  borderColor,
  mainText,
  source,
  finePrint,
  boxX,
  boxY,
  targetX,
  targetY,
}) => {
  const frame = useCurrentFrame();

  // ── Phase 1: connector line draws (0 → 30 frames) ───────────────
  const connectorProgress = interpolate(
    frame,
    [0, CONNECTOR_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Connector: from box edge to target point on chart line
  const connectorStartX = boxX;
  const connectorStartY = boxY + 30; // roughly middle-left of callout box
  const currentEndX =
    connectorStartX + (targetX - connectorStartX) * connectorProgress;
  const currentEndY =
    connectorStartY + (targetY - connectorStartY) * connectorProgress;

  // ── Phase 2: callout box scales in (frames 20 → 40, with overlap) ──
  const boxScaleStart = CONNECTOR_DRAW_DURATION - 10;
  const boxScale = interpolate(
    frame,
    [boxScaleStart, boxScaleStart + BOX_SCALE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.4)),
    },
  );
  const boxOpacity = interpolate(
    frame,
    [boxScaleStart, boxScaleStart + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // ── Phase 3: text type-in (starts after box is mostly visible) ───
  const textStart = boxScaleStart + BOX_SCALE_DURATION - 5;
  const mainTextChars = Math.floor(
    interpolate(
      frame,
      [textStart, textStart + mainText.length * TEXT_FRAMES_PER_CHAR],
      [0, mainText.length],
      {extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
    ),
  );
  const sourceDelay = textStart + mainText.length * TEXT_FRAMES_PER_CHAR + 4;
  const sourceChars = Math.floor(
    interpolate(
      frame,
      [sourceDelay, sourceDelay + source.length * TEXT_FRAMES_PER_CHAR],
      [0, source.length],
      {extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
    ),
  );
  const finePrintDelay = sourceDelay + source.length * TEXT_FRAMES_PER_CHAR + 4;
  const finePrintChars = Math.floor(
    interpolate(
      frame,
      [
        finePrintDelay,
        finePrintDelay + finePrint.length * TEXT_FRAMES_PER_CHAR,
      ],
      [0, finePrint.length],
      {extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
    ),
  );

  // Small pulsing dot at the connector target
  const dotPulse = interpolate(
    frame,
    [CONNECTOR_DRAW_DURATION, CONNECTOR_DRAW_DURATION + 20],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
  );

  return (
    <div style={{position: 'absolute', inset: 0, pointerEvents: 'none'}}>
      {/* Connector line (SVG) */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{position: 'absolute', top: 0, left: 0}}
      >
        {connectorProgress > 0 && (
          <line
            x1={connectorStartX}
            y1={connectorStartY}
            x2={currentEndX}
            y2={currentEndY}
            stroke={borderColor}
            strokeWidth={1}
            opacity={0.65}
          />
        )}
        {/* Target dot */}
        {dotPulse > 0 && (
          <circle
            cx={targetX}
            cy={targetY}
            r={4 * dotPulse}
            fill={borderColor}
            opacity={0.7 * dotPulse}
          />
        )}
      </svg>

      {/* Callout box */}
      <div
        style={{
          position: 'absolute',
          left: boxX,
          top: boxY,
          width: CALLOUT_WIDTH,
          padding: CALLOUT_PADDING,
          backgroundColor: CALLOUT_FILL,
          border: `${CALLOUT_BORDER_WIDTH}px solid ${borderColor}`,
          borderRadius: CALLOUT_RADIUS,
          transform: `scale(${boxScale})`,
          transformOrigin: 'left center',
          opacity: boxOpacity,
        }}
      >
        {/* Main text */}
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 18,
            fontWeight: 700,
            color: borderColor,
            minHeight: 24,
            opacity: 0.95,
          }}
        >
          {mainText.slice(0, mainTextChars)}
          {mainTextChars < mainText.length && (
            <span
              style={{
                display: 'inline-block',
                width: 2,
                height: 18,
                backgroundColor: borderColor,
                marginLeft: 1,
                verticalAlign: 'text-bottom',
                opacity: frame % 10 < 5 ? 1 : 0.8,
              }}
            />
          )}
        </div>

        {/* Source */}
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 400,
            color: SOURCE_COLOR,
            marginTop: 4,
            minHeight: 18,
            opacity: 0.85,
          }}
        >
          {source.slice(0, sourceChars)}
        </div>

        {/* Fine print */}
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 13,
            fontStyle: 'italic',
            color: FINEPRINT_COLOR,
            marginTop: 6,
            minHeight: 16,
            opacity: FINEPRINT_OPACITY,
          }}
        >
          {finePrint.slice(0, finePrintChars)}
        </div>
      </div>
    </div>
  );
};

export default AnnotationCallout;
