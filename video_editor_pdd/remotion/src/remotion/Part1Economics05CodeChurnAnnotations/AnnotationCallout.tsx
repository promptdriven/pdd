import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const FONT_FAMILY = 'Inter, system-ui, sans-serif';
const COLOR_SLATE_DARK = '#1E293B';
const COLOR_SLATE = '#94A3B8';

const CONNECTOR_DRAW_DURATION = 30;
const CALLOUT_SCALE_DURATION = 20;
const TEXT_TYPE_DURATION = 30;
const CALLOUT_WIDTH = 380;
const CALLOUT_BORDER_RADIUS = 8;
const CALLOUT_BORDER_WIDTH = 1.5;

interface AnnotationCalloutProps {
  /** Frame at which this annotation begins animating in */
  startFrame: number;
  /** Accent / border color */
  accentColor: string;
  /** Primary bold text, e.g. "Code churn: +44%" */
  mainText: string;
  /** Source line beneath the main text */
  sourceText: string;
  /** Position of callout box (top-left) */
  boxX: number;
  boxY: number;
  /** Target point for the connector line (where it points into the chart) */
  connectorTargetX: number;
  connectorTargetY: number;
}

export const AnnotationCallout: React.FC<AnnotationCalloutProps> = ({
  startFrame,
  accentColor,
  mainText,
  sourceText,
  boxX,
  boxY,
  connectorTargetX,
  connectorTargetY,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // ── Connector draw progress (0→1) ───────────────────────────────
  const connectorProgress = interpolate(
    localFrame,
    [0, CONNECTOR_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // ── Callout scale (0→1, with overshoot via back easing) ─────────
  const scaleStart = CONNECTOR_DRAW_DURATION * 0.5;
  const calloutScale = interpolate(
    localFrame,
    [scaleStart, scaleStart + CALLOUT_SCALE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.4)),
    },
  );

  // ── Text reveal (character count) ───────────────────────────────
  const textStart = scaleStart + CALLOUT_SCALE_DURATION * 0.5;
  const textProgress = interpolate(
    localFrame,
    [textStart, textStart + TEXT_TYPE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );
  const visibleMainChars = Math.floor(textProgress * mainText.length);
  const visibleSourceChars = Math.floor(
    interpolate(textProgress, [0.4, 1], [0, sourceText.length], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }),
  );

  // Connector line origin: left-center of callout
  const connectorOriginX = boxX;
  const connectorOriginY = boxY + 40;
  const currentConnectorX =
    connectorOriginX + (connectorTargetX - connectorOriginX) * connectorProgress;
  const currentConnectorY =
    connectorOriginY + (connectorTargetY - connectorOriginY) * connectorProgress;

  return (
    <>
      {/* Connector line */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', left: 0, top: 0, pointerEvents: 'none' }}
      >
        <line
          x1={connectorOriginX}
          y1={connectorOriginY}
          x2={currentConnectorX}
          y2={currentConnectorY}
          stroke={accentColor}
          strokeWidth={1}
          opacity={0.5}
        />
        {/* Small dot at the end of the connector */}
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
          left: boxX,
          top: boxY,
          width: CALLOUT_WIDTH,
          background: COLOR_SLATE_DARK,
          border: `${CALLOUT_BORDER_WIDTH}px solid ${accentColor}`,
          borderRadius: CALLOUT_BORDER_RADIUS,
          padding: '14px 20px',
          transform: `scale(${calloutScale})`,
          transformOrigin: 'left center',
          opacity: calloutScale,
        }}
      >
        {/* Main text */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 18,
            fontWeight: 700,
            color: accentColor,
            lineHeight: 1.3,
            minHeight: 24,
            opacity: 0.95,
          }}
        >
          {mainText.slice(0, visibleMainChars)}
          {visibleMainChars < mainText.length && (
            <span
              style={{
                display: 'inline-block',
                width: 2,
                height: 18,
                background: accentColor,
                marginLeft: 1,
                verticalAlign: 'text-bottom',
                opacity: frame % 16 < 8 ? 1 : 0,
              }}
            />
          )}
        </div>

        {/* Source text */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 12,
            fontWeight: 400,
            color: COLOR_SLATE,
            marginTop: 4,
            minHeight: 16,
            opacity: 0.85,
          }}
        >
          {sourceText.slice(0, visibleSourceChars)}
        </div>
      </div>
    </>
  );
};

export default AnnotationCallout;
