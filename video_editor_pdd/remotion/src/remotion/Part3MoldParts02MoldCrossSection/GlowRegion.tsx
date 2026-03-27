import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_OUTER_WIDTH,
  MOLD_OUTER_HEIGHT,
  MOLD_INNER_WIDTH,
  MOLD_INNER_HEIGHT,
  MOLD_CORNER_RADIUS,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  REGION_GLOW_DURATION,
  PULSE_START_FRAME,
  PULSE_CYCLE_FRAMES,
} from "./constants";

export type RegionId = "walls" | "nozzle" | "cavity";

interface GlowRegionProps {
  region: RegionId;
  color: string;
  glowRadius: number;
  glowOpacity: number;
  /** Absolute frame at which this region starts glowing */
  startFrame: number;
}

export const GlowRegion: React.FC<GlowRegionProps> = ({
  region,
  color,
  glowRadius,
  glowOpacity,
  startFrame,
}) => {
  const frame = useCurrentFrame();

  // Glow fade-in
  const glowIn = interpolate(
    frame,
    [startFrame, startFrame + REGION_GLOW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse after all regions are lit (frame 300+)
  let pulse = 1;
  if (frame >= PULSE_START_FRAME) {
    const pulsePhase =
      ((frame - PULSE_START_FRAME) / PULSE_CYCLE_FRAMES) * Math.PI * 2;
    // Sine wave between 0.6 and 1.0
    pulse = 0.8 + 0.2 * Math.sin(pulsePhase);
  }

  const opacity = glowIn * glowOpacity * pulse;
  if (opacity <= 0) return null;

  const filterId = `glow-${region}`;

  // ── Geometry ──
  const outerLeft = MOLD_CENTER_X - MOLD_OUTER_WIDTH / 2;
  const outerTop = MOLD_CENTER_Y - MOLD_OUTER_HEIGHT / 2;
  const innerLeft = MOLD_CENTER_X - MOLD_INNER_WIDTH / 2;
  const innerTop = MOLD_CENTER_Y - MOLD_INNER_HEIGHT / 2 + 30;

  const r = MOLD_CORNER_RADIUS;

  const buildRoundedRect = (
    x: number,
    y: number,
    w: number,
    h: number,
    cr: number
  ) =>
    [
      `M ${x + cr} ${y}`,
      `L ${x + w - cr} ${y}`,
      `Q ${x + w} ${y} ${x + w} ${y + cr}`,
      `L ${x + w} ${y + h - cr}`,
      `Q ${x + w} ${y + h} ${x + w - cr} ${y + h}`,
      `L ${x + cr} ${y + h}`,
      `Q ${x} ${y + h} ${x} ${y + h - cr}`,
      `L ${x} ${y + cr}`,
      `Q ${x} ${y} ${x + cr} ${y}`,
      "Z",
    ].join(" ");

  let paths: React.ReactNode = null;

  if (region === "walls") {
    // Left wall: outer-left to inner-left
    const wallThickness = innerLeft - outerLeft;
    const wallHeight = MOLD_OUTER_HEIGHT;
    // Left wall
    const leftWallPath = buildRoundedRect(
      outerLeft,
      outerTop,
      wallThickness,
      wallHeight,
      r
    );
    // Right wall
    const rightWallX = innerLeft + MOLD_INNER_WIDTH;
    const rightWallPath = buildRoundedRect(
      rightWallX,
      outerTop,
      wallThickness,
      wallHeight,
      r
    );
    paths = (
      <>
        <path d={leftWallPath} fill={color} opacity={opacity} />
        <path d={rightWallPath} fill={color} opacity={opacity} />
      </>
    );
  } else if (region === "nozzle") {
    // Nozzle funnel
    const nozzleTopY = outerTop - NOZZLE_HEIGHT;
    const nozzlePath = [
      `M ${MOLD_CENTER_X - NOZZLE_WIDTH / 2} ${nozzleTopY}`,
      `L ${MOLD_CENTER_X + NOZZLE_WIDTH / 2} ${nozzleTopY}`,
      `L ${MOLD_CENTER_X + 20} ${outerTop}`,
      `L ${MOLD_CENTER_X - 20} ${outerTop}`,
      "Z",
    ].join(" ");
    paths = <path d={nozzlePath} fill={color} opacity={opacity} />;
  } else if (region === "cavity") {
    // Inner cavity area
    const cavityPath = buildRoundedRect(
      innerLeft,
      innerTop,
      MOLD_INNER_WIDTH,
      MOLD_INNER_HEIGHT,
      r
    );
    paths = <path d={cavityPath} fill={color} opacity={opacity} />;
  }

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <filter id={filterId} x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation={glowRadius} />
        </filter>
      </defs>
      {/* Glow layer */}
      <g filter={`url(#${filterId})`}>{paths}</g>
      {/* Solid layer on top */}
      {paths}
    </svg>
  );
};

export default GlowRegion;
