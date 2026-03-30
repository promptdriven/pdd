import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  RED_LINE_COLOR,
  CONTEXT_LABEL_COLOR,
  FONT_FAMILY,
  CONTEXT_LABEL_FRAME,
  ANNOTATION_1_FRAME,
  ANNOTATION_2_FRAME,
  xToPixel,
  yToPixel,
} from "./constants";

const FadeInText: React.FC<{
  startFrame: number;
  fadeDuration?: number;
  x: number;
  y: number;
  text: string;
  color: string;
  fontSize: number;
  fontWeight?: number;
  fontStyle?: string;
  maxWidth?: number;
}> = ({
  startFrame,
  fadeDuration = 20,
  x,
  y,
  text,
  color,
  fontSize,
  fontWeight = 400,
  fontStyle = "normal",
  maxWidth,
}) => {
  const frame = useCurrentFrame();
  const opacity = interpolate(
    frame,
    [startFrame, startFrame + fadeDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (frame < startFrame) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        opacity,
        color,
        fontSize,
        fontWeight,
        fontStyle,
        fontFamily: FONT_FAMILY,
        lineHeight: 1.4,
        maxWidth: maxWidth || "auto",
        whiteSpace: maxWidth ? "normal" : "nowrap",
      }}
    >
      {text}
    </div>
  );
};

export const Annotations: React.FC = () => {
  const frame = useCurrentFrame();

  // Position annotations relative to the chart
  const upperForkEndX = xToPixel(2025);
  const upperForkY = yToPixel(0.46);
  const forkPointX = xToPixel(2020);
  const forkPointY = yToPixel(0.48);

  return (
    <>
      {/* "Same tools. Different codebase sizes." near fork point */}
      <FadeInText
        startFrame={CONTEXT_LABEL_FRAME}
        fadeDuration={20}
        x={forkPointX - 120}
        y={forkPointY - 52}
        text="Same tools. Different codebase sizes."
        color={CONTEXT_LABEL_COLOR}
        fontSize={14}
        fontWeight={400}
      />

      {/* METR annotation on upper fork */}
      <FadeInText
        startFrame={ANNOTATION_1_FRAME}
        fadeDuration={24}
        x={xToPixel(2021.5)}
        y={yToPixel(0.52) - 4}
        text="METR, 2025: experienced devs 19% slower on mature repos"
        color={RED_LINE_COLOR}
        fontSize={13}
        fontWeight={400}
        maxWidth={380}
      />

      {/* Callout line from annotation to upper fork */}
      {frame >= ANNOTATION_1_FRAME && (
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            pointerEvents: "none",
          }}
        >
          <line
            x1={xToPixel(2023)}
            y1={yToPixel(0.52) + 4}
            x2={xToPixel(2023)}
            y2={yToPixel(0.465)}
            stroke={RED_LINE_COLOR}
            strokeWidth={1}
            strokeDasharray="3 3"
            opacity={interpolate(
              frame,
              [ANNOTATION_1_FRAME, ANNOTATION_1_FRAME + 24],
              [0, 0.6],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            )}
          />
        </svg>
      )}

      {/* "Developers believed AI saved 20%. It cost 19%." */}
      <FadeInText
        startFrame={ANNOTATION_2_FRAME}
        fadeDuration={24}
        x={xToPixel(2021.5)}
        y={yToPixel(0.52) + 36}
        text="Developers believed AI saved 20%. It cost 19%."
        color={RED_LINE_COLOR}
        fontSize={13}
        fontWeight={400}
        fontStyle="italic"
        maxWidth={380}
      />
    </>
  );
};

export default Annotations;
