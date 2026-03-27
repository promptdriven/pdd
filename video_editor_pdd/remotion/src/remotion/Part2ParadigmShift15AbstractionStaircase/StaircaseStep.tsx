import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface StaircaseStepProps {
  x: number;
  y: number;
  width: number;
  stepHeight: number;
  fillColor: string;
  fillOpacity: number;
  borderColor: string;
  label: string;
  decade: string;
  emphasis: boolean;
  entranceFrame: number;
  drawDuration: number;
  pulseStart: number;
  pulseCycle: number;
}

export const StaircaseStep: React.FC<StaircaseStepProps> = ({
  x,
  y,
  width,
  stepHeight,
  fillColor,
  fillOpacity,
  borderColor,
  label,
  decade,
  emphasis,
  entranceFrame,
  drawDuration,
  pulseStart,
  pulseCycle,
}) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - entranceFrame;

  if (relativeFrame < 0) return null;

  // Back easing with overshoot for bounce effect
  const overshoot = emphasis ? 1.2 : 1.1;
  const backEase = (t: number) => {
    const s = overshoot;
    return t * t * ((s + 1) * t - s);
  };

  // Progress of the step rising in (0 to 1)
  const riseProgress = interpolate(relativeFrame, [0, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Apply back-ease manually for the bounce
  const easedProgress = riseProgress >= 1 ? 1 : backEase(riseProgress);
  const clampedProgress = Math.max(0, Math.min(1, easedProgress));

  // Y offset: starts 200px below final position, rises up
  const yOffset = interpolate(clampedProgress, [0, 1], [200, 0]);
  const opacity = interpolate(clampedProgress, [0, 1], [0, 1]);

  // Scale for emphasis step entrance
  let scaleEntrance = 1;
  if (emphasis && relativeFrame < drawDuration + 20) {
    scaleEntrance = interpolate(
      relativeFrame,
      [0, drawDuration, drawDuration + 20],
      [0.8, 1.05, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      }
    );
  }

  // Pulse for emphasis step after pulseStart
  let pulseScale = 1;
  if (emphasis && frame >= pulseStart) {
    const pulseFrame = (frame - pulseStart) % pulseCycle;
    pulseScale = interpolate(
      pulseFrame,
      [0, pulseCycle / 2, pulseCycle],
      [1.0, 1.02, 1.0],
      {
        easing: Easing.inOut(Easing.sin),
        extrapolateRight: "clamp",
      }
    );
  }

  const totalScale = scaleEntrance * pulseScale;

  // Glow for emphasis step
  const glowShadow = emphasis
    ? `0 0 20px ${fillColor}88, 0 0 40px ${fillColor}44`
    : "none";
  const pulseShadow =
    emphasis && frame >= pulseStart
      ? `0 0 30px ${fillColor}AA, 0 0 60px ${fillColor}55, 0 0 80px ${fillColor}33`
      : glowShadow;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y + yOffset,
        width,
        height: stepHeight,
        opacity,
        transform: `scale(${totalScale})`,
        transformOrigin: "center center",
      }}
    >
      {/* Step rectangle */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "100%",
          height: "100%",
          backgroundColor: fillColor,
          opacity: fillOpacity,
          border: `2px solid ${borderColor}`,
          borderRadius: 4,
          boxShadow: pulseShadow,
        }}
      />
      {/* Label text */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "100%",
          height: "100%",
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          flexDirection: "column",
          gap: 2,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: emphasis ? 18 : 16,
            fontWeight: 700,
            color: emphasis ? fillColor : "#E2E8F0",
            textShadow: "0 1px 3px rgba(0,0,0,0.5)",
            whiteSpace: "nowrap",
          }}
        >
          {label}
        </span>
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 400,
            color: "#94A3B8",
            opacity: 0.8,
          }}
        >
          {decade}
        </span>
      </div>
    </div>
  );
};

export default StaircaseStep;
