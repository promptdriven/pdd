/**
 * AnnotationCallout — A research annotation with callout box and connection line.
 *
 * Fades in with an 8px slide from right, draws a connection line to the target
 * point on the chart.
 */
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CALLOUT_BG,
  AXIS_LABEL_COLOR,
  FONT_FAMILY,
  CONNECTION_DRAW_DUR,
} from "./constants";

interface AnnotationCalloutProps {
  /** Frame at which this annotation starts appearing */
  startFrame: number;
  /** Fade + slide duration in frames */
  fadeDuration: number;
  /** Callout box top-left X */
  boxX: number;
  /** Callout box top-left Y */
  boxY: number;
  /** Connection line target X (on the chart) */
  targetX: number;
  /** Connection line target Y (on the chart) */
  targetY: number;
  /** Primary title text (string or array for multi-line) */
  title: string | string[];
  /** Title color */
  titleColor: string;
  /** Border color for callout box */
  borderColor: string;
  /** Citation subtitle */
  subtitle: string;
  /** Optional extra line (e.g. "+41% more bugs") */
  extra?: string;
  /** Extra line color */
  extraColor?: string;
}

export const AnnotationCallout: React.FC<AnnotationCalloutProps> = ({
  startFrame,
  fadeDuration,
  boxX,
  boxY,
  targetX,
  targetY,
  title,
  titleColor,
  borderColor,
  subtitle,
  extra,
  extraColor = "#E74C3C",
}) => {
  const frame = useCurrentFrame();

  if (frame < startFrame) return null;

  const localFrame = frame - startFrame;

  // Fade in opacity
  const fadeIn = interpolate(localFrame, [0, fadeDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Slide from right (8px)
  const slideX = interpolate(localFrame, [0, fadeDuration], [8, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Connection line draws after fade completes
  const lineProgress = interpolate(
    localFrame,
    [fadeDuration, fadeDuration + CONNECTION_DRAW_DUR],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const titles = Array.isArray(title) ? title : [title];
  const boxWidth = 280;
  const titleLineHeight = 20;
  const subtitleOffset = titles.length * titleLineHeight + 6;
  const extraOffset = subtitleOffset + 18;
  const boxHeight = extra ? extraOffset + 20 : subtitleOffset + 20;

  // Connection line start: left edge of box, vertically centered
  const lineStartX = boxX + slideX;
  const lineStartY = boxY + boxHeight / 2;

  // Interpolated end point for line draw animation
  const lineEndX =
    lineStartX + (targetX - lineStartX) * lineProgress;
  const lineEndY =
    lineStartY + (targetY - lineStartY) * lineProgress;

  return (
    <>
      {/* Connection line (SVG) */}
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <line
          x1={lineStartX}
          y1={lineStartY}
          x2={lineEndX}
          y2={lineEndY}
          stroke={borderColor}
          strokeWidth={1}
          opacity={fadeIn * 0.25}
        />
        {/* Small dot at the target end */}
        {lineProgress > 0.9 && (
          <circle
            cx={targetX}
            cy={targetY}
            r={3}
            fill={borderColor}
            opacity={fadeIn * 0.4}
          />
        )}
      </svg>

      {/* Callout box (HTML div for crisper text) */}
      <div
        style={{
          position: "absolute",
          left: boxX + slideX,
          top: boxY,
          width: boxWidth,
          padding: "12px 16px",
          backgroundColor: CALLOUT_BG,
          border: `1px solid ${borderColor}`,
          borderRadius: 6,
          opacity: fadeIn,
          borderColor: `${borderColor}4D`, // ~0.3 opacity via hex alpha
        }}
      >
        {/* Title lines */}
        {titles.map((t, i) => (
          <div
            key={i}
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: i === 0 && titles.length === 1 ? 14 : 13,
              fontWeight: 700,
              color: titleColor,
              opacity: 0.8,
              lineHeight: `${titleLineHeight}px`,
            }}
          >
            {t}
          </div>
        ))}

        {/* Subtitle (citation) */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 9,
            fontWeight: 400,
            color: AXIS_LABEL_COLOR,
            opacity: 0.35,
            marginTop: 6,
            lineHeight: "14px",
          }}
        >
          {subtitle}
        </div>

        {/* Extra line (e.g. "+41% more bugs") */}
        {extra && (
          <div
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: 10,
              fontWeight: 600,
              color: extraColor,
              opacity: 0.6,
              marginTop: 4,
              lineHeight: "14px",
            }}
          >
            {extra}
          </div>
        )}
      </div>
    </>
  );
};

export default AnnotationCallout;
