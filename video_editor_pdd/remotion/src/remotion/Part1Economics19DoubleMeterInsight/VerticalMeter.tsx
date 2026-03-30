import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  METER_WIDTH,
  METER_HEIGHT,
  METER_CORNER_RADIUS,
  METER_TRACK_COLOR,
  METER_TRACK_BORDER,
  COLOR_LABEL_DIM,
  COLOR_TEXT_PRIMARY,
  FONT_FAMILY,
  PHASE_TITLES_START,
  PHASE_TITLES_END,
  PHASE_FILL_START,
  PHASE_FILL_END,
  PHASE_TOP_LABELS_START,
  PHASE_TOP_LABELS_END,
  PHASE_PULSE_START,
  PHASE_PULSE_END,
  PULSE_CYCLE_FRAMES,
  PULSE_SCALE_MIN,
  PULSE_SCALE_MAX,
  PHASE_BG_START,
  PHASE_BG_END,
} from "./constants";

interface VerticalMeterProps {
  x: number;
  y: number;
  fillColor: string;
  title: string;
  bottomLabel: string;
  topLabel: string;
  bottomLabelSize?: number;
}

export const VerticalMeter: React.FC<VerticalMeterProps> = ({
  x,
  y,
  fillColor,
  title,
  bottomLabel,
  topLabel,
  bottomLabelSize = 18,
}) => {
  const frame = useCurrentFrame();

  // Track draw-in (scale Y from 0 to 1)
  const trackScale = interpolate(
    frame,
    [PHASE_BG_START, PHASE_BG_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Title + bottom label fade
  const titleOpacity = interpolate(
    frame,
    [PHASE_TITLES_START, PHASE_TITLES_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Fill progress (0 to 1)
  const fillProgress = interpolate(
    frame,
    [PHASE_FILL_START, PHASE_FILL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // Top label fade
  const topLabelOpacity = interpolate(
    frame,
    [PHASE_TOP_LABELS_START, PHASE_TOP_LABELS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse — synchronized sine cycle after PHASE_PULSE_START
  let pulseScale = PULSE_SCALE_MIN;
  if (frame >= PHASE_PULSE_START) {
    const pulseFrame = (frame - PHASE_PULSE_START) % PULSE_CYCLE_FRAMES;
    const pulseT = pulseFrame / PULSE_CYCLE_FRAMES;
    // sine in-out: 0→1→0 within one cycle
    const sineVal = Math.sin(pulseT * Math.PI * 2);
    pulseScale = PULSE_SCALE_MIN + (PULSE_SCALE_MAX - PULSE_SCALE_MIN) * ((sineVal + 1) / 2);
  }

  // Glow intensity during pulse phase
  const glowOpacity =
    frame >= PHASE_PULSE_START && frame <= PHASE_PULSE_END
      ? interpolate(
          frame,
          [PHASE_PULSE_START, PHASE_PULSE_START + 15, PHASE_PULSE_END - 15, PHASE_PULSE_END],
          [0, 0.6, 0.6, 0.3],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        )
      : frame > PHASE_PULSE_END
        ? 0.3
        : 0;

  const fillHeight = fillProgress * METER_HEIGHT;
  const centerX = x;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - METER_WIDTH / 2,
        top: y,
        width: METER_WIDTH,
        transformOrigin: "center bottom",
        transform: `scale(${pulseScale})`,
      }}
    >
      {/* Title above meter */}
      <div
        style={{
          position: "absolute",
          top: -40,
          left: "50%",
          transform: "translateX(-50%)",
          whiteSpace: "nowrap",
          fontFamily: FONT_FAMILY,
          fontSize: 16,
          fontWeight: 600,
          color: COLOR_TEXT_PRIMARY,
          opacity: titleOpacity,
        }}
      >
        {title}
      </div>

      {/* Meter track */}
      <div
        style={{
          position: "relative",
          width: METER_WIDTH,
          height: METER_HEIGHT,
          backgroundColor: METER_TRACK_COLOR,
          border: `1px solid ${METER_TRACK_BORDER}`,
          borderRadius: METER_CORNER_RADIUS,
          overflow: "hidden",
          transform: `scaleY(${trackScale})`,
          transformOrigin: "center bottom",
        }}
      >
        {/* Fill bar from bottom */}
        <div
          style={{
            position: "absolute",
            bottom: 0,
            left: 0,
            width: "100%",
            height: fillHeight,
            backgroundColor: fillColor,
            opacity: 0.7,
            borderRadius:
              fillProgress >= 0.98
                ? METER_CORNER_RADIUS
                : `0 0 ${METER_CORNER_RADIUS}px ${METER_CORNER_RADIUS}px`,
            transition: "border-radius 0.1s",
          }}
        />

        {/* Glow overlay on the fill */}
        {glowOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              bottom: 0,
              left: -4,
              width: METER_WIDTH + 8,
              height: fillHeight + 8,
              borderRadius: METER_CORNER_RADIUS + 4,
              boxShadow: `0 0 20px ${fillColor}, 0 0 40px ${fillColor}`,
              opacity: glowOpacity,
              pointerEvents: "none",
            }}
          />
        )}
      </div>

      {/* Bottom label */}
      <div
        style={{
          position: "absolute",
          bottom: -30,
          left: "50%",
          transform: "translateX(-50%)",
          whiteSpace: "nowrap",
          fontFamily: FONT_FAMILY,
          fontSize: bottomLabelSize,
          fontWeight: 400,
          color: COLOR_LABEL_DIM,
          opacity: titleOpacity,
        }}
      >
        {bottomLabel}
      </div>

      {/* Top label */}
      <div
        style={{
          position: "absolute",
          top: -70,
          left: "50%",
          transform: "translateX(-50%)",
          whiteSpace: "nowrap",
          fontFamily: FONT_FAMILY,
          fontSize: 24,
          fontWeight: 700,
          color: fillColor,
          opacity: topLabelOpacity,
        }}
      >
        {topLabel}
      </div>
    </div>
  );
};

export default VerticalMeter;
