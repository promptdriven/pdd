import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  STEP_LABEL_COLOR,
  EMPHASIS_COLOR,
  STEP5_PULSE_START,
  STEP5_PULSE_CYCLE,
  type StepDef,
} from "./constants";

interface StaircaseStepProps {
  step: StepDef;
  /** Frame at which this step begins animating in */
  enterFrame: number;
  /** Duration of the entrance animation in frames */
  drawDuration: number;
}

const StaircaseStep: React.FC<StaircaseStepProps> = ({
  step,
  enterFrame,
  drawDuration,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - enterFrame;

  if (relFrame < 0) return null;

  // Bounce-in: step rises from below with overshoot
  const overshoot = step.emphasis ? 1.2 : 1.1;
  // We simulate easeOut(back) with overshoot using a custom approach via poly + spring-like math
  const rawProgress = interpolate(relFrame, [0, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(2)),
  });

  // Apply back-easing overshoot manually: f(t) = t * ((s+1)*t - s) inverted for easeOut
  const backEase = (t: number, s: number) => {
    const t1 = t - 1;
    return t1 * t1 * ((s + 1) * t1 + s) + 1;
  };
  const progress = backEase(rawProgress, overshoot);

  const width = step.x2 - step.x1;
  const originY = step.y + 200; // start 200px below final position
  const currentY = originY + (step.y - originY) * progress;

  // Step 5 pulse effect
  let pulseScale = 1;
  if (step.emphasis && frame >= STEP5_PULSE_START) {
    const pulseFrame = (frame - STEP5_PULSE_START) % STEP5_PULSE_CYCLE;
    pulseScale = interpolate(
      pulseFrame,
      [0, STEP5_PULSE_CYCLE / 2, STEP5_PULSE_CYCLE],
      [1, 1.02, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.sin),
      }
    );
  }

  // Glow for step 5
  const glowOpacity = step.emphasis
    ? interpolate(
        frame,
        [STEP5_PULSE_START, STEP5_PULSE_START + 30],
        [0, 0.6],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  const opacity = interpolate(relFrame, [0, 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: step.x1,
        top: currentY,
        width,
        height: step.stepHeight,
        opacity,
        transform: `scale(${pulseScale})`,
        transformOrigin: "center center",
      }}
    >
      {/* Glow behind step 5 */}
      {step.emphasis && glowOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: -20,
            top: -20,
            width: width + 40,
            height: step.stepHeight + 40,
            borderRadius: 8,
            background: step.fillColor,
            opacity: glowOpacity * 0.3,
            filter: "blur(20px)",
            pointerEvents: "none",
          }}
        />
      )}

      {/* Step rectangle */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width,
          height: step.stepHeight,
          backgroundColor: step.fillColor,
          opacity: step.fillOpacity,
          border: `2px solid ${step.fillColor}`,
          borderRadius: 4,
        }}
      />

      {/* Step border overlay (full opacity border) */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width,
          height: step.stepHeight,
          border: `2px solid ${step.fillColor}`,
          borderRadius: 4,
          pointerEvents: "none",
        }}
      />

      {/* Step label (inside step) */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width,
          height: step.stepHeight,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: step.emphasis ? 18 : 16,
          fontWeight: 700,
          color: step.emphasis ? EMPHASIS_COLOR : STEP_LABEL_COLOR,
          textAlign: "center",
          padding: "0 8px",
          lineHeight: 1.2,
        }}
      >
        {step.label} ({step.decade})
      </div>
    </div>
  );
};

export default StaircaseStep;
