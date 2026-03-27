import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface ModuleBoxProps {
  label: string;
  x: number;
  y: number;
  width: number;
  height: number;
  borderColor: string;
  borderWidth?: number;
  borderRadius?: number;
  fillColor: string;
  labelColor: string;
  labelSize: number;
  labelWeight?: number;
  /** If provided, renders a glow effect */
  glowColor?: string;
  glowBlur?: number;
  glowOpacity?: number;
  /** Frame at which this box starts fading in (relative to component mount) */
  fadeInStart?: number;
  /** Additional opacity multiplier (for dimming) */
  opacityMultiplier?: number;
}

export const ModuleBox: React.FC<ModuleBoxProps> = ({
  label,
  x,
  y,
  width,
  height,
  borderColor,
  borderWidth = 2,
  borderRadius = 12,
  fillColor,
  labelColor,
  labelSize,
  labelWeight = 400,
  glowColor,
  glowBlur = 20,
  glowOpacity = 0.25,
  fadeInStart = 0,
  opacityMultiplier = 1,
}) => {
  const frame = useCurrentFrame();

  // Fade-in over 15 frames using easeOut(quad)
  const fadeOpacity = interpolate(
    frame,
    [fadeInStart, fadeInStart + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const finalOpacity = fadeOpacity * opacityMultiplier;

  // Glow pulse: 60 frame cycle — ramp up then ramp down
  const halfCycle = frame % 60;
  const pulseT =
    halfCycle < 30
      ? interpolate(halfCycle, [0, 30], [0, 1], {
          easing: Easing.inOut(Easing.sin),
        })
      : interpolate(halfCycle, [30, 60], [1, 0], {
          easing: Easing.inOut(Easing.sin),
        });
  const glowPulse = glowColor
    ? glowOpacity * 0.6 + pulseT * glowOpacity * 0.8
    : 0;

  const glowFilterId = `glow-${label.replace(/[^a-zA-Z0-9]/g, "")}`;

  return (
    <g opacity={finalOpacity}>
      {glowColor && (
        <defs>
          <filter
            id={glowFilterId}
            x="-50%"
            y="-50%"
            width="200%"
            height="200%"
          >
            <feGaussianBlur stdDeviation={glowBlur} result="blur" />
            <feFlood floodColor={glowColor} floodOpacity={glowPulse} />
            <feComposite in2="blur" operator="in" />
            <feMerge>
              <feMergeNode />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>
      )}

      <rect
        x={x - width / 2}
        y={y - height / 2}
        width={width}
        height={height}
        rx={borderRadius}
        ry={borderRadius}
        fill={fillColor}
        stroke={borderColor}
        strokeWidth={borderWidth}
        filter={glowColor ? `url(#${glowFilterId})` : undefined}
      />

      <text
        x={x}
        y={y + labelSize * 0.35}
        textAnchor="middle"
        fontFamily="JetBrains Mono, monospace"
        fontSize={labelSize}
        fontWeight={labelWeight}
        fill={labelColor}
      >
        {label}
      </text>
    </g>
  );
};
