import React from "react";
import { useCurrentFrame, Easing, interpolate } from "remotion";
import { COLORS, FRAMES } from "./constants";

/**
 * The narrator's reframe line that slides up from below the quote.
 * Contains the "economics" word with a pulse animation.
 *
 * NOTE: This component is rendered inside a <Sequence from={210}>,
 * so useCurrentFrame() returns frames relative to 210.
 * Local frame 0 = absolute frame 210.
 */
export const ReframeSubtitle: React.FC = () => {
  const frame = useCurrentFrame(); // 0 = absolute 210

  // Slide-up & fade for entire block
  const slideY = interpolate(
    frame,
    [0, FRAMES.reframeSlideFrames],
    [15, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const blockOpacity = interpolate(
    frame,
    [0, FRAMES.reframeSlideFrames],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Horizontal rule drawing animation (from center outward)
  const ruleProgress = interpolate(frame, [0, 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });
  const ruleWidth = 200 * ruleProgress;

  // "economics" pulse: absolute frame 260–280, local frame 50–70
  const pulseStart = FRAMES.economicsPulseStart - FRAMES.reframeStart; // 50
  const pulseEnd = pulseStart + FRAMES.economicsPulseDuration; // 70
  const pulseLocalFrame = frame - pulseStart;

  const pulseScale =
    pulseLocalFrame >= 0 && pulseLocalFrame <= FRAMES.economicsPulseDuration
      ? interpolate(
          pulseLocalFrame,
          [0, FRAMES.economicsPulseDuration / 2, FRAMES.economicsPulseDuration],
          [1.0, 1.08, 1.0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.sin),
          }
        )
      : 1.0;

  const economicsOpacity =
    pulseLocalFrame >= 0 && pulseLocalFrame <= FRAMES.economicsPulseDuration
      ? interpolate(
          pulseLocalFrame,
          [0, FRAMES.economicsPulseDuration / 2, FRAMES.economicsPulseDuration],
          [0.8, 1.0, 0.8],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.sin),
          }
        )
      : 0.8;

  const baseStyle: React.CSSProperties = {
    fontFamily: "Inter, sans-serif",
    fontSize: 18,
    fontWeight: 600,
    color: COLORS.reframeText,
    opacity: 0.6,
  };

  return (
    <div
      style={{
        position: "absolute",
        bottom: 0,
        left: 0,
        right: 0,
        top: 0,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "flex-start",
        opacity: blockOpacity,
        transform: `translateY(${slideY}px)`,
      }}
    >
      {/* Horizontal rule */}
      <div
        style={{
          position: "absolute",
          top: 690,
          left: "50%",
          transform: "translateX(-50%)",
          width: ruleWidth,
          height: 1,
          backgroundColor: COLORS.ruleLine,
          opacity: 0.15,
        }}
      />

      {/* Reframe text */}
      <div
        style={{
          position: "absolute",
          top: 710,
          left: 0,
          right: 0,
          textAlign: "center",
        }}
      >
        <span style={baseStyle}>
          He{"\u2019"}s right {"\u2014"} it{"\u2019"}s a contrarian bet. But the{" "}
        </span>
        <span
          style={{
            ...baseStyle,
            color: COLORS.blueHighlight,
            opacity: economicsOpacity,
            display: "inline-block",
            transform: `scale(${pulseScale})`,
          }}
        >
          economics
        </span>
        <span style={baseStyle}> are on our side.</span>
      </div>
    </div>
  );
};
