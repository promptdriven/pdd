import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, PrinterFocusPropsType } from "./constants";

// 3D Perspective Coordinate Grid Component
const CoordinateGrid3D: React.FC<{ opacity: number; pulseIntensity: number }> = ({
  opacity,
  pulseIntensity,
}) => {
  const gridColor = COLORS.GRID_BLUE;
  const baseOpacity = opacity * (1 + pulseIntensity * 0.15);

  return (
    <svg
      style={{
        position: "absolute",
        width: "100%",
        height: "100%",
        opacity: baseOpacity,
      }}
    >
      {/* X-axis lines (vertical, with perspective) */}
      {[...Array(12)].map((_, i) => (
        <line
          key={`x-${i}`}
          x1={300 + i * 120}
          y1={100}
          x2={200 + i * 100}
          y2={800}
          stroke={gridColor}
          strokeWidth={1}
          opacity={0.6}
        />
      ))}

      {/* Y-axis lines (horizontal, with perspective tilt) */}
      {[...Array(10)].map((_, i) => (
        <line
          key={`y-${i}`}
          x1={100}
          y1={150 + i * 70}
          x2={1700}
          y2={180 + i * 65}
          stroke={gridColor}
          strokeWidth={1}
          opacity={0.5}
        />
      ))}

      {/* Z-axis indicator lines (diagonal, showing depth) */}
      {[...Array(5)].map((_, i) => (
        <line
          key={`z-${i}`}
          x1={1600 + i * 30}
          y1={700 - i * 80}
          x2={1700 + i * 30}
          y2={500 - i * 80}
          stroke={gridColor}
          strokeWidth={2}
          opacity={0.7}
        />
      ))}
    </svg>
  );
};

// Axis Labels Component
const AxisLabels: React.FC<{ opacity: number }> = ({ opacity }) => {
  const labelStyle: React.CSSProperties = {
    fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
    fontSize: 28,
    fontWeight: "bold",
    color: COLORS.AXIS_WHITE,
    textShadow: `0 0 10px ${COLORS.GLOW_BLUE}, 0 0 20px ${COLORS.GLOW_BLUE}`,
    opacity,
  };

  return (
    <>
      {/* X axis label */}
      <div
        style={{
          ...labelStyle,
          position: "absolute",
          left: 100,
          top: 80,
        }}
      >
        X
      </div>

      {/* Y axis label */}
      <div
        style={{
          ...labelStyle,
          position: "absolute",
          left: 60,
          top: 500,
        }}
      >
        Y
      </div>

      {/* Z axis label */}
      <div
        style={{
          ...labelStyle,
          position: "absolute",
          right: 100,
          bottom: 150,
        }}
      >
        Z
      </div>
    </>
  );
};

// Position Indicator Component
const PositionIndicator: React.FC<{
  x: number;
  y: number;
  z: number;
  opacity: number;
}> = ({ x, y, z, opacity }) => {
  return (
    <div
      style={{
        position: "absolute",
        right: 100,
        top: 200,
        opacity,
        background: "rgba(0, 0, 0, 0.7)",
        padding: "20px 30px",
        borderRadius: 12,
        border: `2px solid ${COLORS.POSITION_CYAN}`,
        boxShadow: `0 0 20px rgba(0, 229, 255, 0.3)`,
      }}
    >
      <div
        style={{
          fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
          fontSize: 20,
          color: COLORS.POSITION_CYAN,
          marginBottom: 8,
          fontWeight: "bold",
        }}
      >
        POSITION
      </div>
      <div
        style={{
          fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
          fontSize: 24,
          color: COLORS.AXIS_WHITE,
          display: "flex",
          flexDirection: "column",
          gap: 8,
        }}
      >
        <div>
          <span style={{ color: COLORS.GRID_BLUE }}>X: </span>
          <span>{x.toFixed(1)}</span>
        </div>
        <div>
          <span style={{ color: COLORS.GRID_BLUE }}>Y: </span>
          <span>{y.toFixed(1)}</span>
        </div>
        <div>
          <span style={{ color: COLORS.GRID_BLUE }}>Z: </span>
          <span>{z.toFixed(1)}</span>
        </div>
      </div>
    </div>
  );
};

// Nozzle Tracking Crosshair Component
const NozzleCrosshair: React.FC<{
  x: number;
  y: number;
  opacity: number;
}> = ({ x, y, opacity }) => {
  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        transform: "translate(-50%, -50%)",
        opacity,
      }}
    >
      {/* Crosshair circle */}
      <svg width="80" height="80" viewBox="0 0 80 80">
        <circle
          cx="40"
          cy="40"
          r="30"
          fill="none"
          stroke={COLORS.POSITION_CYAN}
          strokeWidth="2"
          opacity={0.8}
        />
        <circle
          cx="40"
          cy="40"
          r="20"
          fill="none"
          stroke={COLORS.POSITION_CYAN}
          strokeWidth="1"
          opacity={0.5}
        />
        {/* Crosshair lines */}
        <line x1="40" y1="5" x2="40" y2="25" stroke={COLORS.POSITION_CYAN} strokeWidth="2" />
        <line x1="40" y1="55" x2="40" y2="75" stroke={COLORS.POSITION_CYAN} strokeWidth="2" />
        <line x1="5" y1="40" x2="25" y2="40" stroke={COLORS.POSITION_CYAN} strokeWidth="2" />
        <line x1="55" y1="40" x2="75" y2="40" stroke={COLORS.POSITION_CYAN} strokeWidth="2" />
        {/* Center dot */}
        <circle cx="40" cy="40" r="4" fill={COLORS.POSITION_CYAN} />
      </svg>
    </div>
  );
};

// Main PrinterFocus Component
export const PrinterFocus: React.FC<PrinterFocusPropsType> = ({
  showLabel = true,
  gridOpacityMax = 0.3,
}) => {
  const frame = useCurrentFrame();

  // Grid opacity animation (0-3s fade in)
  const gridOpacity = interpolate(
    frame,
    [BEATS.GRID_FADE_START, BEATS.GRID_FADE_END],
    [0, gridOpacityMax],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Axis labels opacity
  const axisLabelsOpacity = interpolate(
    frame,
    [BEATS.AXIS_LABELS_START, BEATS.AXIS_LABELS_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Position indicator opacity (appears after frame 90)
  const positionOpacity = interpolate(
    frame,
    [BEATS.TRACKING_START, BEATS.TRACKING_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Simulated nozzle position tracking
  // Creates realistic-looking movement patterns
  const nozzleX = 142 + Math.sin(frame * 0.05) * 30 + Math.cos(frame * 0.03) * 15;
  const nozzleY = 87 + Math.cos(frame * 0.04) * 25 + Math.sin(frame * 0.02) * 10;
  const nozzleZ = 23 + Math.floor(frame / 180); // Z increases every 6 seconds (layer change)

  // Crosshair screen position (center area of screen, with motion)
  const crosshairX = 700 + Math.sin(frame * 0.05) * 150 + Math.cos(frame * 0.03) * 80;
  const crosshairY = 450 + Math.cos(frame * 0.04) * 100 + Math.sin(frame * 0.02) * 50;

  // Grid pulse effect (subtle movement during tracking phase)
  const gridPulse = frame > BEATS.TRACKING_ACTIVE
    ? Math.sin(frame * 0.1) * 0.3
    : 0;

  // Bottom label opacity (10-15s fade in)
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_START, BEATS.LABEL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Simulated video background placeholder - dark with grid pattern */}
      <div
        style={{
          position: "absolute",
          width: "100%",
          height: "100%",
          background: `
            radial-gradient(ellipse at 50% 50%, rgba(30, 35, 50, 1) 0%, rgba(26, 26, 46, 1) 100%)
          `,
        }}
      />

      {/* Simulated 3D printer nozzle area */}
      <div
        style={{
          position: "absolute",
          left: "30%",
          top: "35%",
          width: 400,
          height: 300,
          background: "rgba(40, 45, 60, 0.6)",
          borderRadius: 8,
          border: "1px solid rgba(90, 159, 233, 0.2)",
        }}
      />

      {/* Coordinate grid overlay */}
      <CoordinateGrid3D opacity={gridOpacity} pulseIntensity={gridPulse} />

      {/* Axis labels */}
      <AxisLabels opacity={axisLabelsOpacity} />

      {/* Nozzle tracking crosshair */}
      {frame > BEATS.TRACKING_START && (
        <NozzleCrosshair
          x={crosshairX}
          y={crosshairY}
          opacity={positionOpacity}
        />
      )}

      {/* Position indicator panel */}
      {frame > BEATS.TRACKING_START && (
        <PositionIndicator
          x={nozzleX}
          y={nozzleY}
          z={nozzleZ}
          opacity={positionOpacity}
        />
      )}

      {/* Bottom label */}
      {showLabel && labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: labelOpacity,
          }}
        >
          <div
            style={{
              fontSize: 32,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              fontWeight: "500",
              textShadow: `0 0 20px rgba(90, 159, 233, 0.5)`,
              letterSpacing: "0.05em",
            }}
          >
            Every point must be specified
          </div>
        </div>
      )}

      {/* Title overlay */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: axisLabelsOpacity,
        }}
      >
        <span
          style={{
            fontSize: 20,
            fontFamily: "sans-serif",
            color: COLORS.GRID_BLUE,
            fontWeight: "bold",
            letterSpacing: "0.1em",
            textTransform: "uppercase",
          }}
        >
          3D Printer Coordinate System
        </span>
      </div>
    </AbsoluteFill>
  );
};
