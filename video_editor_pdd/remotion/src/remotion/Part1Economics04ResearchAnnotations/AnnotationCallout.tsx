import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CALLOUT_FILL,
  CALLOUT_RADIUS,
  CALLOUT_BORDER_WIDTH,
  FONT_FAMILY,
  MAIN_TEXT_SIZE,
  SOURCE_TEXT_SIZE,
  FINE_PRINT_SIZE,
  SOURCE_COLOR,
  FINE_PRINT_COLOR,
  FINE_PRINT_OPACITY,
} from "./constants";

export interface AnnotationCalloutProps {
  /** Frame at which this annotation starts animating in (relative to parent Sequence) */
  startFrame: number;
  /** Accent / border color */
  accentColor: string;
  /** Primary stat text */
  mainText: string;
  /** Source label e.g. "(GitHub, 2022)" */
  source: string;
  /** Fine-print description */
  finePrint: string;
  /** Position of the callout box */
  boxX: number;
  boxY: number;
  /** Target point on the chart line where the connector ends */
  targetX: number;
  targetY: number;
}

const CONNECTOR_DRAW_FRAMES = 30;
const BOX_SCALE_FRAMES = 20;
const TYPE_FRAMES_PER_CHAR = 2;

const AnnotationCallout: React.FC<AnnotationCalloutProps> = ({
  startFrame,
  accentColor,
  mainText,
  source,
  finePrint,
  boxX,
  boxY,
  targetX,
  targetY,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Phase 1: Connector line draws from callout toward target
  const connectorProgress = interpolate(
    localFrame,
    [0, CONNECTOR_DRAW_FRAMES],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Phase 2: Callout box scales in (with overshoot via back easing)
  const boxScaleStart = CONNECTOR_DRAW_FRAMES;
  const boxScale = interpolate(
    localFrame,
    [boxScaleStart, boxScaleStart + BOX_SCALE_FRAMES],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.4)),
    }
  );

  const boxOpacity = interpolate(
    localFrame,
    [boxScaleStart, boxScaleStart + 10],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Phase 3: Text types in character by character
  const textStart = boxScaleStart + BOX_SCALE_FRAMES;
  const totalMainChars = mainText.length;
  const mainTextVisible = Math.floor(
    interpolate(
      localFrame,
      [textStart, textStart + totalMainChars * TYPE_FRAMES_PER_CHAR],
      [0, totalMainChars],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    )
  );

  const sourceStart = textStart + totalMainChars * TYPE_FRAMES_PER_CHAR;
  const totalSourceChars = source.length;
  const sourceVisible = Math.floor(
    interpolate(
      localFrame,
      [sourceStart, sourceStart + totalSourceChars * TYPE_FRAMES_PER_CHAR],
      [0, totalSourceChars],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    )
  );

  const finePrintStart = sourceStart + totalSourceChars * TYPE_FRAMES_PER_CHAR;
  const totalFinePrintChars = finePrint.length;
  const finePrintVisible = Math.floor(
    interpolate(
      localFrame,
      [finePrintStart, finePrintStart + totalFinePrintChars * TYPE_FRAMES_PER_CHAR],
      [0, totalFinePrintChars],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    )
  );

  // Connector line: from left edge of callout box to target on chart
  const connectorFromX = boxX;
  const connectorFromY = boxY + 30; // mid-height of box roughly
  const currentEndX = connectorFromX + (targetX - connectorFromX) * connectorProgress;
  const currentEndY = connectorFromY + (targetY - connectorFromY) * connectorProgress;

  const calloutWidth = 320;
  const calloutHeight = 90;

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
          x1={connectorFromX}
          y1={connectorFromY}
          x2={currentEndX}
          y2={currentEndY}
          stroke={accentColor}
          strokeWidth={1}
          opacity={0.5}
        />
        {/* Small circle at the target end */}
        {connectorProgress > 0.9 && (
          <circle
            cx={currentEndX}
            cy={currentEndY}
            r={4}
            fill={accentColor}
            opacity={0.6 * connectorProgress}
          />
        )}
      </svg>

      {/* Callout box */}
      <div
        style={{
          position: "absolute",
          left: boxX,
          top: boxY,
          width: calloutWidth,
          height: calloutHeight,
          backgroundColor: CALLOUT_FILL,
          border: `${CALLOUT_BORDER_WIDTH}px solid ${accentColor}`,
          borderRadius: CALLOUT_RADIUS,
          padding: "12px 16px",
          transform: `scale(${boxScale})`,
          transformOrigin: "left center",
          opacity: boxOpacity,
          display: "flex",
          flexDirection: "column",
          justifyContent: "center",
          gap: 4,
        }}
      >
        {/* Main text */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: MAIN_TEXT_SIZE,
            fontWeight: 700,
            color: accentColor,
            lineHeight: 1.3,
            whiteSpace: "nowrap",
            overflow: "hidden",
            opacity: 0.95,
          }}
        >
          {mainText.slice(0, mainTextVisible)}
          {mainTextVisible < totalMainChars && (
            <span style={{ opacity: frame % 6 < 3 ? 1 : 0 }}>|</span>
          )}
        </div>

        {/* Source */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: SOURCE_TEXT_SIZE,
            fontWeight: 400,
            color: SOURCE_COLOR,
            lineHeight: 1.3,
            whiteSpace: "nowrap",
            overflow: "hidden",
            opacity: 0.85,
          }}
        >
          {source.slice(0, sourceVisible)}
        </div>

        {/* Fine print */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: FINE_PRINT_SIZE,
            fontWeight: 400,
            fontStyle: "italic",
            color: FINE_PRINT_COLOR,
            lineHeight: 1.3,
            whiteSpace: "nowrap",
            overflow: "hidden",
            opacity: FINE_PRINT_OPACITY,
          }}
        >
          {finePrint.slice(0, finePrintVisible)}
        </div>
      </div>
    </>
  );
};

export default AnnotationCallout;
