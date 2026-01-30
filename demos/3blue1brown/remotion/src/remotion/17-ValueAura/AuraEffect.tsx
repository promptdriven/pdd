import React from "react";
import { useCurrentFrame } from "remotion";

interface AuraEffectProps {
  /** Center X position relative to the panel */
  centerX: number;
  /** Center Y position relative to the panel */
  centerY: number;
  /** Horizontal radius of the aura ellipse */
  radiusX: number;
  /** Vertical radius of the aura ellipse */
  radiusY: number;
  /** Opacity of the aura (0-1), controlled by parent for fade-in */
  opacity: number;
}

/**
 * Renders a soft, pulsing radial aura effect using CSS.
 * White-to-gold-to-transparent radial gradient with blur and scale pulse.
 */
export const AuraEffect: React.FC<AuraEffectProps> = ({
  centerX,
  centerY,
  radiusX,
  radiusY,
  opacity,
}) => {
  const frame = useCurrentFrame();

  // Pulse: scale oscillates between 95% and 105%
  const pulse = 1 + 0.05 * Math.sin((frame / 60) * Math.PI * 2);

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - radiusX,
        top: centerY - radiusY,
        width: radiusX * 2,
        height: radiusY * 2,
        borderRadius: "50%",
        background:
          "radial-gradient(ellipse at center, rgba(255,255,255,0.7) 0%, rgba(255,215,0,0.5) 35%, rgba(255,215,0,0.15) 60%, transparent 100%)",
        filter: "blur(20px)",
        opacity: opacity * 0.4,
        transform: `scale(${pulse})`,
        pointerEvents: "none",
      }}
    />
  );
};
