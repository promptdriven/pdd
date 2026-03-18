import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  METER_WIDTH,
  METER_HEIGHT,
  METER_BORDER_RADIUS,
  METER_CENTER_Y,
  TRACK_BG,
  TRACK_BORDER,
  SCALE_COLOR,
  TRACKS_APPEAR,
  SCALES_APPEAR,
  FILL_START,
  FILL_DURATION,
  PULSE_START,
  PULSE_END,
  HOLD_START,
  CHALLENGE_START,
} from "./constants";

interface VerticalMeterProps {
  x: number;
  label: string;
  color: string;
  scaleMarkers: readonly string[];
  maxValue: number;
  unit: string;
  prefix?: string;
  iconPath: string; // SVG path data for the icon
}

// The VerticalMeter is placed inside <Sequence from={TRACKS_APPEAR}>,
// so useCurrentFrame() is relative to that Sequence start.
// We offset all global frame references by TRACKS_APPEAR.
const SEQ_OFFSET = TRACKS_APPEAR;

const VerticalMeter: React.FC<VerticalMeterProps> = ({
  x,
  label,
  color,
  scaleMarkers,
  maxValue,
  unit,
  prefix = "",
  iconPath,
}) => {
  const frame = useCurrentFrame();
  // Convert to global frame for constants reference
  const globalFrame = frame + SEQ_OFFSET;

  // ── Track fade-in (global 45-65, local 0-20) ──
  const trackOpacity = interpolate(
    globalFrame,
    [TRACKS_APPEAR, TRACKS_APPEAR + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Scale markers fade-in (global 75-95) ──
  const scaleOpacity = interpolate(
    globalFrame,
    [SCALES_APPEAR, SCALES_APPEAR + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Fill progress (global 105-225) ──
  const fillProgress = interpolate(
    globalFrame,
    [FILL_START, FILL_START + FILL_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.bezier(0.42, 0, 0.58, 1),
    }
  );

  const fillHeight = fillProgress * METER_HEIGHT;

  // ── Current value counter ──
  const currentValue = Math.round(fillProgress * maxValue);

  // ── Peak pulse (global 225-270) ──
  const peakGlow = interpolate(
    globalFrame,
    [PULSE_START, PULSE_START + 15, PULSE_END],
    [0, 0.2, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ── Ongoing gentle pulse (global 390-480) ──
  const ongoingPulse =
    globalFrame >= HOLD_START && globalFrame < CHALLENGE_START
      ? interpolate(
          (globalFrame - HOLD_START) % 60,
          [0, 30, 60],
          [0, 0.05, 0],
          { extrapolateRight: "clamp" }
        )
      : 0;

  const glowOpacity = peakGlow + ongoingPulse;

  // Positions
  const trackLeft = x - METER_WIDTH / 2;
  const trackTop = METER_CENTER_Y;

  // Hex helper for glow alpha
  const glowHex = (opacity: number) =>
    Math.round(Math.min(1, Math.max(0, opacity)) * 255)
      .toString(16)
      .padStart(2, "0");

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: "100%",
        height: "100%",
        opacity: trackOpacity,
      }}
    >
      {/* Icon above meter */}
      <div
        style={{
          position: "absolute",
          left: x - 16,
          top: trackTop - 80,
          width: 32,
          height: 32,
          opacity: 0.3 * trackOpacity,
        }}
      >
        <svg viewBox="0 0 24 24" width={32} height={32} fill="none">
          <path
            d={iconPath}
            stroke={color}
            strokeWidth={1.5}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </svg>
      </div>

      {/* Label above meter */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: trackTop - 40,
          transform: "translateX(-50%)",
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: color,
          opacity: 0.7 * trackOpacity,
          whiteSpace: "nowrap",
        }}
      >
        {label}
      </div>

      {/* Meter track */}
      <div
        style={{
          position: "absolute",
          left: trackLeft,
          top: trackTop,
          width: METER_WIDTH,
          height: METER_HEIGHT,
          borderRadius: METER_BORDER_RADIUS,
          backgroundColor: TRACK_BG,
          border: `1px solid ${TRACK_BORDER}`,
          overflow: "hidden",
        }}
      >
        {/* Fill bar */}
        <div
          style={{
            position: "absolute",
            bottom: 0,
            left: 0,
            width: "100%",
            height: fillHeight,
            borderRadius: `0 0 ${METER_BORDER_RADIUS}px ${METER_BORDER_RADIUS}px`,
            background: `linear-gradient(to top, ${color}88, ${color})`,
            boxShadow:
              glowOpacity > 0
                ? `0 0 20px ${color}${glowHex(glowOpacity)}`
                : "none",
          }}
        />

        {/* Glow overlay when pulsing */}
        {glowOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              bottom: 0,
              left: -10,
              width: METER_WIDTH + 20,
              height: fillHeight + 10,
              borderRadius: METER_BORDER_RADIUS,
              background: `radial-gradient(ellipse at center bottom, ${color}${glowHex(glowOpacity)}, transparent 70%)`,
              pointerEvents: "none",
            }}
          />
        )}
      </div>

      {/* Scale markers */}
      {scaleMarkers.map((marker, i) => {
        const markerY =
          trackTop +
          METER_HEIGHT -
          (i / (scaleMarkers.length - 1)) * METER_HEIGHT;
        return (
          <div
            key={marker}
            style={{
              position: "absolute",
              left: trackLeft - 65,
              top: markerY - 8,
              width: 55,
              textAlign: "right",
              fontFamily: "Inter, sans-serif",
              fontSize: 12,
              color: SCALE_COLOR,
              opacity: 0.4 * scaleOpacity,
              whiteSpace: "nowrap",
            }}
          >
            {marker}
          </div>
        );
      })}

      {/* Tick marks for scale */}
      {scaleMarkers.map((marker, i) => {
        const markerY =
          trackTop +
          METER_HEIGHT -
          (i / (scaleMarkers.length - 1)) * METER_HEIGHT;
        return (
          <div
            key={`tick-${marker}`}
            style={{
              position: "absolute",
              left: trackLeft - 6,
              top: markerY - 0.5,
              width: 6,
              height: 1,
              backgroundColor: SCALE_COLOR,
              opacity: 0.3 * scaleOpacity,
            }}
          />
        );
      })}

      {/* Current value display */}
      {fillProgress > 0 && (
        <div
          style={{
            position: "absolute",
            left: trackLeft + METER_WIDTH + 14,
            top: trackTop + METER_HEIGHT - fillHeight - 14,
            fontFamily: "Inter, sans-serif",
            fontSize: 24,
            fontWeight: 700,
            color: color,
            opacity: 0.85,
            whiteSpace: "nowrap",
          }}
        >
          {prefix}
          {currentValue}
          {unit}
        </div>
      )}
    </div>
  );
};

export default VerticalMeter;
