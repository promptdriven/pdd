import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BG_COLOR_START,
  BG_COLOR_END,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CONTEXT_FILL_COLOR,
  PERFORMANCE_FILL_COLOR,
  LEFT_METER_X,
  RIGHT_METER_X,
  BG_LIGHTEN_START,
  BG_LIGHTEN_END,
  FONT_FAMILY,
  TEXT_PRIMARY_COLOR,
  LABEL_DIM_COLOR,
  TRACK_FILL_COLOR,
  TRACK_BORDER_COLOR,
  METER_WIDTH,
  METER_HEIGHT,
  METER_BORDER_RADIUS,
  METER_BORDER_WIDTH,
  METER_Y,
  LABELS_APPEAR_START,
  LABELS_APPEAR_END,
  FILL_START,
  FILL_END,
  TOP_LABELS_START,
  TOP_LABELS_END,
  PULSE_START,
  PULSE_END,
  PULSE_CYCLE,
  ACCENT_AND_COLOR,
  INSIGHT_TEXT_Y,
  INSIGHT_TEXT_START,
  INSIGHT_TEXT_FADE_DURATION,
} from "./constants";

// ── Helpers ──────────────────────────────────────────────────────────

function hexLerp(a: string, b: string, t: number): string {
  const parseHex = (h: string) => {
    const hex = h.replace("#", "");
    return [
      parseInt(hex.slice(0, 2), 16),
      parseInt(hex.slice(2, 4), 16),
      parseInt(hex.slice(4, 6), 16),
    ];
  };
  const [r1, g1, b1] = parseHex(a);
  const [r2, g2, b2] = parseHex(b);
  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const bl = Math.round(b1 + (b2 - b1) * t);
  return `rgb(${r},${g},${bl})`;
}

// ── Vertical Meter (inline to avoid cross-file imports) ──────────────

interface VerticalMeterProps {
  x: number;
  title: string;
  fillColor: string;
  bottomLabel: string;
  topLabel: string;
  bottomLabelSize?: number;
  frame: number;
}

const VerticalMeter: React.FC<VerticalMeterProps> = ({
  x,
  title,
  fillColor,
  bottomLabel,
  topLabel,
  bottomLabelSize = 14,
  frame,
}) => {
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
      [0, PULSE_CYCLE / 2, PULSE_CYCLE - 1],
      [1, 1.02, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.sin),
      }
    );
  }

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
          opacity: labelOpacity > 0 ? Math.max(labelOpacity, 0.78) : 0,
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
              borderRadius:
                fillHeight >= METER_HEIGHT
                  ? METER_BORDER_RADIUS - 1
                  : `0 0 ${METER_BORDER_RADIUS - 1}px ${METER_BORDER_RADIUS - 1}px`,
              boxShadow:
                pulseActive || postPulseGlow
                  ? `0 0 20px ${fillColor}60, 0 0 40px ${fillColor}30`
                  : "none",
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
            opacity: labelOpacity > 0 ? Math.max(labelOpacity, 0.62) : 0,
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

// ── Insight Text ─────────────────────────────────────────────────────

const InsightText: React.FC<{ frame: number }> = ({ frame }) => {
  const opacity = interpolate(
    frame,
    [INSIGHT_TEXT_START, INSIGHT_TEXT_START + INSIGHT_TEXT_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [INSIGHT_TEXT_START, INSIGHT_TEXT_START + INSIGHT_TEXT_FADE_DURATION],
    [16, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: INSIGHT_TEXT_Y,
        left: 0,
        width: CANVAS_WIDTH,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: TEXT_PRIMARY_COLOR,
        }}
      >
        {"Bigger window "}
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: ACCENT_AND_COLOR,
        }}
      >
        AND
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: TEXT_PRIMARY_COLOR,
        }}
      >
        {" smarter model."}
      </span>
    </div>
  );
};

// ── Connecting Line ──────────────────────────────────────────────────

const ConnectingLine: React.FC<{ frame: number }> = ({ frame }) => {
  // Draw a faint connecting line between the two meters during pulse phase
  const lineOpacity = interpolate(frame, [PULSE_START, PULSE_START + 30], [0, 0.3], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  if (lineOpacity <= 0) return null;

  const lineY = METER_Y + METER_HEIGHT / 2 - 20;
  const lineLeft = LEFT_METER_X + METER_WIDTH / 2 + 10;
  const lineRight = RIGHT_METER_X - METER_WIDTH / 2 - 10;

  return (
    <div
      style={{
        position: "absolute",
        top: lineY,
        left: lineLeft,
        width: lineRight - lineLeft,
        height: 2,
        opacity: lineOpacity,
        background: `linear-gradient(90deg, ${CONTEXT_FILL_COLOR}80, ${PERFORMANCE_FILL_COLOR}80)`,
        borderRadius: 1,
      }}
    />
  );
};

// ── Main Component ───────────────────────────────────────────────────

export const defaultPart1Economics19DoubleMeterInsightProps = {};

export const Part1Economics19DoubleMeterInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // Background color transition (frames 0-30)
  const bgProgress = interpolate(frame, [BG_LIGHTEN_START, BG_LIGHTEN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const bgColor = hexLerp(BG_COLOR_START, BG_COLOR_END, bgProgress);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: bgColor,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* Left Meter: Effective Context Window */}
      <VerticalMeter
        x={LEFT_METER_X}
        title="Effective Context Window"
        fillColor={CONTEXT_FILL_COLOR}
        bottomLabel="1×"
        topLabel="5-10×"
        bottomLabelSize={18}
        frame={frame}
      />

      {/* Right Meter: Model Performance */}
      <VerticalMeter
        x={RIGHT_METER_X}
        title="Model Performance"
        fillColor={PERFORMANCE_FILL_COLOR}
        bottomLabel="Baseline"
        topLabel="+89%"
        bottomLabelSize={14}
        frame={frame}
      />

      {/* Connecting line between meters */}
      <ConnectingLine frame={frame} />

      {/* Insight text */}
      <InsightText frame={frame} />
    </AbsoluteFill>
  );
};

export default Part1Economics19DoubleMeterInsight;
