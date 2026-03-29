import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  NOZZLE_COLOR,
  WALLS_COLOR,
  CAVITY_COLOR,
  MOLD_GLOW_START,
  MOLD_GLOW_END,
  MOLD_GLOW_FROM,
  MOLD_GLOW_TO,
} from "./constants";

/**
 * Mold cross-section SVG showing nozzle, walls, and cavity.
 * Glow intensifies from frame 40–60.
 */
export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  const wallGlow = interpolate(
    frame,
    [MOLD_GLOW_START, MOLD_GLOW_END],
    [MOLD_GLOW_FROM, MOLD_GLOW_TO],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const nozzleGlow = interpolate(
    frame,
    [MOLD_GLOW_START, MOLD_GLOW_END],
    [0.3, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const cavityGlow = interpolate(
    frame,
    [MOLD_GLOW_START, MOLD_GLOW_END],
    [0.1, 0.25],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <svg
      width={800}
      height={350}
      viewBox="0 0 800 350"
      style={{ overflow: "visible" }}
    >
      <defs>
        {/* Nozzle glow */}
        <filter id="nozzleGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="12" result="blur" />
          <feComposite in="SourceGraphic" in2="blur" operator="over" />
        </filter>
        {/* Walls glow */}
        <filter id="wallsGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="10" result="blur" />
          <feComposite in="SourceGraphic" in2="blur" operator="over" />
        </filter>
        {/* Cavity glow */}
        <filter id="cavityGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="8" result="blur" />
          <feComposite in="SourceGraphic" in2="blur" operator="over" />
        </filter>
      </defs>

      {/* ---- LEFT MOLD HALF ---- */}
      <g>
        {/* Left wall */}
        <rect
          x={100}
          y={60}
          width={80}
          height={260}
          rx={6}
          fill={WALLS_COLOR}
          opacity={wallGlow}
          filter="url(#wallsGlow)"
        />
        {/* Left wall inner edge */}
        <rect
          x={180}
          y={80}
          width={12}
          height={220}
          rx={2}
          fill={WALLS_COLOR}
          opacity={wallGlow * 1.2}
        />
      </g>

      {/* ---- RIGHT MOLD HALF ---- */}
      <g>
        {/* Right wall */}
        <rect
          x={620}
          y={60}
          width={80}
          height={260}
          rx={6}
          fill={WALLS_COLOR}
          opacity={wallGlow}
          filter="url(#wallsGlow)"
        />
        {/* Right wall inner edge */}
        <rect
          x={608}
          y={80}
          width={12}
          height={220}
          rx={2}
          fill={WALLS_COLOR}
          opacity={wallGlow * 1.2}
        />
      </g>

      {/* ---- NOZZLE (top center) ---- */}
      <g filter="url(#nozzleGlow)">
        {/* Nozzle body */}
        <polygon
          points="370,0 430,0 420,50 380,50"
          fill={NOZZLE_COLOR}
          opacity={nozzleGlow}
        />
        {/* Nozzle tip */}
        <rect
          x={390}
          y={50}
          width={20}
          height={30}
          rx={3}
          fill={NOZZLE_COLOR}
          opacity={nozzleGlow * 1.3}
        />
      </g>

      {/* ---- CAVITY (center area) ---- */}
      <g filter="url(#cavityGlow)">
        <rect
          x={200}
          y={80}
          width={400}
          height={220}
          rx={12}
          fill={CAVITY_COLOR}
          opacity={cavityGlow}
        />
        {/* Inner cavity detail lines */}
        <rect
          x={240}
          y={120}
          width={320}
          height={3}
          rx={1}
          fill={CAVITY_COLOR}
          opacity={cavityGlow * 0.6}
        />
        <rect
          x={240}
          y={160}
          width={320}
          height={3}
          rx={1}
          fill={CAVITY_COLOR}
          opacity={cavityGlow * 0.6}
        />
        <rect
          x={240}
          y={200}
          width={280}
          height={3}
          rx={1}
          fill={CAVITY_COLOR}
          opacity={cavityGlow * 0.6}
        />
        <rect
          x={240}
          y={240}
          width={240}
          height={3}
          rx={1}
          fill={CAVITY_COLOR}
          opacity={cavityGlow * 0.6}
        />
      </g>

      {/* ---- TOP & BOTTOM PLATES ---- */}
      <rect
        x={90}
        y={50}
        width={620}
        height={10}
        rx={3}
        fill={WALLS_COLOR}
        opacity={wallGlow * 0.8}
      />
      <rect
        x={90}
        y={320}
        width={620}
        height={10}
        rx={3}
        fill={WALLS_COLOR}
        opacity={wallGlow * 0.8}
      />
    </svg>
  );
};

export default MoldCrossSection;
