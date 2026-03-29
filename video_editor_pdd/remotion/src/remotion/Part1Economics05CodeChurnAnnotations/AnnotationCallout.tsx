import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface AnnotationCalloutProps {
  /** Frame at which this annotation begins materializing */
  appearFrame: number;
  /** Border / accent color for the callout */
  borderColor: string;
  /** Primary stat text, e.g. "Code churn: +44%" */
  mainText: string;
  /** Source line, e.g. "(GitClear, 2025, 211M lines analyzed)" */
  sourceText: string;
  /** Top-left position of the callout box */
  posX: number;
  posY: number;
  /** Connector line end-point (the target in the chart area) */
  connectorTargetX: number;
  connectorTargetY: number;
}

const CALLOUT_WIDTH = 340;
const CONNECTOR_DRAW_DUR = 30;
const SCALE_DUR = 20;
const TYPE_DUR = 18;

export const AnnotationCallout: React.FC<AnnotationCalloutProps> = ({
  appearFrame,
  borderColor,
  mainText,
  sourceText,
  posX,
  posY,
  connectorTargetX,
  connectorTargetY,
}) => {
  const frame = useCurrentFrame();
  const rel = frame - appearFrame; // relative frame since appear

  if (rel < 0) return null;

  // 1. Connector line draws in over CONNECTOR_DRAW_DUR frames
  const connectorProgress = interpolate(rel, [0, CONNECTOR_DRAW_DUR], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // 2. Callout box scales in (starts after connector is 60% drawn)
  const scaleStart = Math.round(CONNECTOR_DRAW_DUR * 0.6);
  const scale = interpolate(rel, [scaleStart, scaleStart + SCALE_DUR], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.back(1.4)),
  });

  // 3. Text types in (starts when box is mostly scaled)
  const typeStart = scaleStart + Math.round(SCALE_DUR * 0.5);
  const textReveal = interpolate(rel, [typeStart, typeStart + TYPE_DUR], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });
  const visibleMainChars = Math.round(textReveal * mainText.length);
  const visibleSourceChars = Math.round(
    interpolate(rel, [typeStart + 6, typeStart + TYPE_DUR + 6], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }) * sourceText.length
  );

  // Connector line geometry: from left-center of callout box toward target
  const calloutCenterY = posY + 36;
  const lineStartX = posX;
  const lineStartY = calloutCenterY;
  const currentEndX = lineStartX + (connectorTargetX - lineStartX) * connectorProgress;
  const currentEndY = lineStartY + (connectorTargetY - lineStartY) * connectorProgress;

  return (
    <>
      {/* Connector line */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <line
          x1={lineStartX}
          y1={lineStartY}
          x2={currentEndX}
          y2={currentEndY}
          stroke={borderColor}
          strokeWidth={1}
          opacity={0.5}
        />
        {/* Small dot at the end of connector */}
        {connectorProgress > 0.9 && (
          <circle cx={currentEndX} cy={currentEndY} r={3} fill={borderColor} opacity={0.7} />
        )}
      </svg>

      {/* Callout box */}
      <div
        style={{
          position: "absolute",
          left: posX,
          top: posY,
          width: CALLOUT_WIDTH,
          background: "#1E293B",
          border: `1.5px solid ${borderColor}`,
          borderRadius: 8,
          padding: "14px 18px",
          transform: `scale(${scale})`,
          transformOrigin: "left center",
          opacity: scale > 0.01 ? 1 : 0,
        }}
      >
        {/* Main stat text */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 18,
            fontWeight: 700,
            color: borderColor,
            lineHeight: 1.3,
            minHeight: 24,
          }}
        >
          {mainText.slice(0, visibleMainChars)}
          {visibleMainChars < mainText.length && (
            <span style={{ opacity: 0.5 }}>|</span>
          )}
        </div>

        {/* Source / fine print */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 12,
            fontWeight: 400,
            color: "#94A3B8",
            marginTop: 4,
            lineHeight: 1.3,
            minHeight: 16,
          }}
        >
          {sourceText.slice(0, visibleSourceChars)}
        </div>
      </div>
    </>
  );
};

export default AnnotationCallout;
