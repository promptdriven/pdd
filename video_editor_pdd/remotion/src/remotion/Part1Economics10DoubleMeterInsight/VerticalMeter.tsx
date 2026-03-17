import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  METER_WIDTH,
  METER_HEIGHT,
  METER_RADIUS,
  METER_CENTER_Y,
  TRACK_FILL,
  TRACK_BORDER,
  SCALE_LABEL_COLOR,
  FONT_FAMILY,
  TRACK_FADE_START,
  TRACK_FADE_DURATION,
  SCALE_FADE_START,
  SCALE_FADE_DURATION,
  FILL_START,
  FILL_DURATION,
  PEAK_PULSE_START,
  PEAK_PULSE_DURATION,
  ONGOING_PULSE_START,
  ONGOING_PULSE_CYCLE,
} from "./constants";

type VerticalMeterProps = {
  x: number;
  label: string;
  color: string;
  scaleMarkers: string[];
  maxValue: number;
  valuePrefix: string;
  valueSuffix: string;
};

export const VerticalMeter: React.FC<VerticalMeterProps> = ({
  x,
  label,
  color,
  scaleMarkers,
  maxValue,
  valuePrefix,
  valueSuffix,
}) => {
  const frame = useCurrentFrame();

  const meterTop = METER_CENTER_Y - METER_HEIGHT / 2;
  const meterLeft = x - METER_WIDTH / 2;

  // Track fade-in
  const trackOpacity = interpolate(
    frame,
    [TRACK_FADE_START, TRACK_FADE_START + TRACK_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Scale markers fade-in
  const scaleOpacity = interpolate(
    frame,
    [SCALE_FADE_START, SCALE_FADE_START + SCALE_FADE_DURATION],
    [0, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Fill progress (0 to 1)
  const fillProgress = interpolate(
    frame,
    [FILL_START, FILL_START + FILL_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.bezier(0.42, 0, 0.58, 1) }
  );

  const fillHeight = fillProgress * METER_HEIGHT;
  const currentValue = fillProgress * maxValue;

  // Format the display value
  const displayValue =
    valueSuffix === "×"
      ? `${currentValue.toFixed(1)}${valueSuffix}`
      : `${valuePrefix}${Math.round(currentValue)}${valueSuffix}`;

  // Peak pulse glow
  const peakGlow = interpolate(
    frame,
    [
      PEAK_PULSE_START,
      PEAK_PULSE_START + PEAK_PULSE_DURATION * 0.4,
      PEAK_PULSE_START + PEAK_PULSE_DURATION,
    ],
    [0, 0.25, 0.08],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Ongoing gentle pulse after frame 390
  const ongoingPulse =
    frame >= ONGOING_PULSE_START
      ? 0.05 *
        Math.sin(
          ((frame - ONGOING_PULSE_START) / ONGOING_PULSE_CYCLE) * Math.PI * 2
        )
      : 0;

  const totalGlow = peakGlow + ongoingPulse;

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [TRACK_FADE_START, TRACK_FADE_START + TRACK_FADE_DURATION],
    [0, 0.7],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Value opacity (appears as fill starts)
  const valueOpacity = interpolate(
    frame,
    [FILL_START, FILL_START + 15],
    [0, 0.85],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: "100%", height: "100%" }}>
      {/* Label above meter */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: meterTop - 60,
          transform: "translateX(-50%)",
          fontFamily: FONT_FAMILY,
          fontSize: 14,
          fontWeight: 600,
          color,
          opacity: labelOpacity,
          whiteSpace: "nowrap",
          textAlign: "center",
        }}
      >
        {label}
      </div>

      {/* Icon above label */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: meterTop - 90,
          transform: "translateX(-50%)",
          fontSize: 22,
          opacity: labelOpacity * 0.5,
          textAlign: "center",
        }}
      >
        {color === "#4A90D9" ? "⊞" : "◈"}
      </div>

      {/* Meter track background */}
      <div
        style={{
          position: "absolute",
          left: meterLeft,
          top: meterTop,
          width: METER_WIDTH,
          height: METER_HEIGHT,
          borderRadius: METER_RADIUS,
          backgroundColor: TRACK_FILL,
          border: `1px solid ${TRACK_BORDER}`,
          opacity: trackOpacity,
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
            borderRadius: `0 0 ${METER_RADIUS - 1}px ${METER_RADIUS - 1}px`,
            background: `linear-gradient(to top, ${color}88, ${color})`,
            boxShadow: totalGlow > 0
              ? `0 0 ${20 + totalGlow * 40}px ${color}${Math.round(totalGlow * 255).toString(16).padStart(2, "0")}`
              : "none",
            transition: "box-shadow 0.1s",
          }}
        />
      </div>

      {/* Glow overlay on track when pulsing */}
      {totalGlow > 0.01 && (
        <div
          style={{
            position: "absolute",
            left: meterLeft - 10,
            top: meterTop - 10,
            width: METER_WIDTH + 20,
            height: METER_HEIGHT + 20,
            borderRadius: METER_RADIUS + 4,
            boxShadow: `0 0 ${30 + totalGlow * 60}px ${color}${Math.round(totalGlow * 200).toString(16).padStart(2, "0")}`,
            pointerEvents: "none",
            opacity: trackOpacity,
          }}
        />
      )}

      {/* Scale markers (left side of left meter, right side of right meter) */}
      {scaleMarkers.map((marker, i) => {
        const markerY =
          meterTop + METER_HEIGHT - (i / (scaleMarkers.length - 1)) * METER_HEIGHT;
        const isLeft = color === "#4A90D9";
        return (
          <div
            key={marker}
            style={{
              position: "absolute",
              left: isLeft ? meterLeft - 8 : meterLeft + METER_WIDTH + 8,
              top: markerY,
              transform: isLeft
                ? "translate(-100%, -50%)"
                : "translate(0, -50%)",
              fontFamily: FONT_FAMILY,
              fontSize: 12,
              color: SCALE_LABEL_COLOR,
              opacity: scaleOpacity,
              whiteSpace: "nowrap",
            }}
          >
            {marker}
          </div>
        );
      })}

      {/* Current value readout */}
      {fillProgress > 0.01 && (
        <div
          style={{
            position: "absolute",
            left: x,
            top: meterTop + METER_HEIGHT - fillHeight - 30,
            transform: "translateX(-50%)",
            fontFamily: FONT_FAMILY,
            fontSize: 24,
            fontWeight: 700,
            color,
            opacity: valueOpacity,
            whiteSpace: "nowrap",
            textAlign: "center",
            textShadow: `0 0 12px ${color}44`,
          }}
        >
          {displayValue}
        </div>
      )}
    </div>
  );
};
