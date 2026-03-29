import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TRACK_FILL,
  TRACK_BORDER,
  METER_WIDTH,
  METER_HEIGHT,
  METER_RADIUS,
  METER_TOP_Y,
  LABEL_DIM,
  TEXT_LIGHT,
  TITLES_START,
  TITLES_END,
  FILL_START,
  FILL_END,
  TOP_LABELS_START,
  TOP_LABELS_END,
  PULSE_START,
  PULSE_END,
  PULSE_CYCLE,
  TRACK_DRAW_END,
} from "./constants";

interface VerticalMeterProps {
  x: number;
  title: string;
  fillColor: string;
  bottomLabel: string;
  topLabel: string;
  bottomFontSize: number;
}

export const VerticalMeter: React.FC<VerticalMeterProps> = ({
  x,
  title,
  fillColor,
  bottomLabel,
  topLabel,
  bottomFontSize,
}) => {
  const frame = useCurrentFrame();

  // Track draw-in (scale Y from 0 to 1)
  const trackScale = interpolate(frame, [0, TRACK_DRAW_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Title fade in
  const titleOpacity = interpolate(
    frame,
    [TITLES_START, TITLES_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Bottom label fade in (same as titles)
  const bottomLabelOpacity = titleOpacity;

  // Fill progress (0 to 1)
  const fillProgress = interpolate(
    frame,
    [FILL_START, FILL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.poly(3)) }
  );

  // Top label fade in
  const topLabelOpacity = interpolate(
    frame,
    [TOP_LABELS_START, TOP_LABELS_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Pulse effect (scale oscillation)
  const isPulsing = frame >= PULSE_START && frame <= PULSE_END;
  let pulseScale = 1;
  if (isPulsing) {
    const pulseFrame = frame - PULSE_START;
    const cyclePos = (pulseFrame % PULSE_CYCLE) / PULSE_CYCLE;
    // sine wave: 0→1→0 over one cycle
    pulseScale = 1 + 0.02 * Math.sin(cyclePos * Math.PI * 2);
  }

  // Glow effect during pulse
  const glowOpacity = isPulsing ? 0.4 : 0;

  const fillHeight = METER_HEIGHT * fillProgress;
  const centeredX = x - METER_WIDTH / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: centeredX,
        top: METER_TOP_Y - 40,
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
          opacity: titleOpacity,
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color: TEXT_LIGHT,
          textAlign: "center",
          width: 200,
          marginBottom: 12,
          whiteSpace: "nowrap",
        }}
      >
        {title}
      </div>

      {/* Top label */}
      <div
        style={{
          opacity: topLabelOpacity,
          fontFamily: "Inter, sans-serif",
          fontSize: 24,
          fontWeight: 700,
          color: fillColor,
          textAlign: "center",
          marginBottom: 8,
          height: 30,
        }}
      >
        {topLabel}
      </div>

      {/* Meter track + fill */}
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
            top: 0,
            left: 0,
            width: METER_WIDTH,
            height: METER_HEIGHT,
            backgroundColor: TRACK_FILL,
            border: `1px solid ${TRACK_BORDER}`,
            borderRadius: METER_RADIUS,
            overflow: "hidden",
          }}
        >
          {/* Fill bar (grows from bottom) */}
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
                  ? METER_RADIUS
                  : `0 0 ${METER_RADIUS}px ${METER_RADIUS}px`,
              transition: "none",
            }}
          />
        </div>

        {/* Glow overlay during pulse */}
        {isPulsing && (
          <div
            style={{
              position: "absolute",
              top: -6,
              left: -6,
              width: METER_WIDTH + 12,
              height: METER_HEIGHT + 12,
              borderRadius: METER_RADIUS + 4,
              border: `2px solid ${fillColor}`,
              opacity: glowOpacity,
              boxShadow: `0 0 20px ${fillColor}, 0 0 40px ${fillColor}`,
              pointerEvents: "none",
            }}
          />
        )}
      </div>

      {/* Bottom label */}
      <div
        style={{
          opacity: bottomLabelOpacity,
          fontFamily: "Inter, sans-serif",
          fontSize: bottomFontSize,
          fontWeight: 400,
          color: LABEL_DIM,
          textAlign: "center",
          marginTop: 10,
        }}
      >
        {bottomLabel}
      </div>
    </div>
  );
};
