import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TRACK_FILL_COLOR,
  TRACK_BORDER_COLOR,
  METER_WIDTH,
  METER_HEIGHT,
  METER_BORDER_RADIUS,
  METER_BORDER_WIDTH,
  METER_Y,
  LABEL_DIM_COLOR,
  TEXT_PRIMARY_COLOR,
  FONT_FAMILY,
  BG_LIGHTEN_START,
  BG_LIGHTEN_END,
  LABELS_APPEAR_START,
  LABELS_APPEAR_END,
  FILL_START,
  FILL_END,
  TOP_LABELS_START,
  TOP_LABELS_END,
  PULSE_START,
  PULSE_END,
  PULSE_CYCLE,
} from "./constants";

interface VerticalMeterProps {
  x: number;
  title: string;
  fillColor: string;
  bottomLabel: string;
  topLabel: string;
  bottomLabelSize?: number;
}

const VerticalMeter: React.FC<VerticalMeterProps> = ({
  x,
  title,
  fillColor,
  bottomLabel,
  topLabel,
  bottomLabelSize = 14,
}) => {
  const frame = useCurrentFrame();

  // Track draw-in: scale from 0 to 1 (frames 0-30)
  const trackScale = interpolate(frame, [BG_LIGHTEN_START, BG_LIGHTEN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Title + bottom label opacity (frames 30-60)
  const labelOpacity = interpolate(frame, [LABELS_APPEAR_START, LABELS_APPEAR_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Meter fill progress (frames 60-180)
  const fillProgress = interpolate(frame, [FILL_START, FILL_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.bezier(0.33, 1, 0.68, 1)),
  });

  // Top label opacity (frames 180-210)
  const topLabelOpacity = interpolate(frame, [TOP_LABELS_START, TOP_LABELS_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Pulse effect (frames 210-270)
  const pulseActive = frame >= PULSE_START && frame <= PULSE_END;
  let pulseScale = 1;
  if (pulseActive) {
    const pulseFrame = (frame - PULSE_START) % PULSE_CYCLE;
    pulseScale = interpolate(
      pulseFrame,
      [0, PULSE_CYCLE / 2, PULSE_CYCLE],
      [1, 1.02, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.sin),
      }
    );
  }

  // After pulse ends, keep a subtle glow
  const postPulseGlow = frame > PULSE_END;

  const fillHeight = fillProgress * METER_HEIGHT;
  const centerX = x - METER_WIDTH / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX,
        top: METER_Y - 40,
        width: METER_WIDTH,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        transform: `scale(${pulseScale})`,
        transformOrigin: "center center",
      }}
    >
      {/* Title above meter */}
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 16,
          fontWeight: 600,
          color: TEXT_PRIMARY_COLOR,
          opacity: labelOpacity,
          textAlign: "center",
          width: 220,
          marginBottom: 12,
          whiteSpace: "nowrap",
        }}
      >
        {title}
      </div>

      {/* Meter container */}
      <div
        style={{
          position: "relative",
          width: METER_WIDTH,
          height: METER_HEIGHT,
          transform: `scaleY(${trackScale})`,
          transformOrigin: "bottom center",
        }}
      >
        {/* Track background */}
        <div
          style={{
            position: "absolute",
            inset: 0,
            backgroundColor: TRACK_FILL_COLOR,
            border: `${METER_BORDER_WIDTH}px solid ${TRACK_BORDER_COLOR}`,
            borderRadius: METER_BORDER_RADIUS,
            overflow: "hidden",
          }}
        >
          {/* Fill bar */}
          <div
            style={{
              position: "absolute",
              bottom: 0,
              left: 0,
              right: 0,
              height: fillHeight,
              backgroundColor: fillColor,
              opacity: 0.7,
              borderRadius: `0 0 ${METER_BORDER_RADIUS - 1}px ${METER_BORDER_RADIUS - 1}px`,
              boxShadow:
                pulseActive || postPulseGlow
                  ? `0 0 20px ${fillColor}60, 0 0 40px ${fillColor}30`
                  : "none",
              transition: pulseActive ? "box-shadow 0.1s" : "none",
            }}
          />
        </div>

        {/* Bottom label */}
        <div
          style={{
            position: "absolute",
            bottom: -32,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: FONT_FAMILY,
            fontSize: bottomLabelSize,
            fontWeight: 400,
            color: LABEL_DIM_COLOR,
            opacity: labelOpacity,
            whiteSpace: "nowrap",
          }}
        >
          {bottomLabel}
        </div>

        {/* Top label */}
        <div
          style={{
            position: "absolute",
            top: -40,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: FONT_FAMILY,
            fontSize: 24,
            fontWeight: 700,
            color: fillColor,
            opacity: topLabelOpacity,
            whiteSpace: "nowrap",
          }}
        >
          {topLabel}
        </div>
      </div>
    </div>
  );
};

export default VerticalMeter;
