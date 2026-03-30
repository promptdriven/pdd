import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BG_COLOR_START,
  BG_COLOR_END,
  LEFT_METER_X,
  RIGHT_METER_X,
  METER_TOP,
  LEFT_FILL_COLOR,
  LEFT_TITLE,
  LEFT_BOTTOM_LABEL,
  LEFT_TOP_LABEL,
  RIGHT_FILL_COLOR,
  RIGHT_TITLE,
  RIGHT_BOTTOM_LABEL,
  RIGHT_TOP_LABEL,
  PHASE_BG_START,
  PHASE_BG_END,
  FONT_FAMILY,
  COLOR_TEXT_PRIMARY,
  COLOR_LABEL_DIM,
  COLOR_ACCENT_AND,
  METER_WIDTH,
  METER_HEIGHT,
  METER_CORNER_RADIUS,
  METER_TRACK_COLOR,
  METER_TRACK_BORDER,
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
  INSIGHT_Y,
  PHASE_TEXT_START,
  PHASE_TEXT_END,
} from "./constants";

// ── Default props (required export) ──
export const defaultPart1Economics19DoubleMeterInsightProps = {};

// ── Inline VerticalMeter (no cross-file local imports) ──
interface VerticalMeterProps {
  x: number;
  y: number;
  fillColor: string;
  title: string;
  bottomLabel: string;
  topLabel: string;
  bottomLabelSize?: number;
}

const VerticalMeter: React.FC<VerticalMeterProps> = ({
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
    const sineVal = Math.sin(pulseT * Math.PI * 2);
    pulseScale =
      PULSE_SCALE_MIN +
      (PULSE_SCALE_MAX - PULSE_SCALE_MIN) * ((sineVal + 1) / 2);
  }

  // Glow intensity during pulse phase
  const glowOpacity =
    frame >= PHASE_PULSE_START && frame <= PHASE_PULSE_END
      ? interpolate(
          frame,
          [
            PHASE_PULSE_START,
            PHASE_PULSE_START + 15,
            PHASE_PULSE_END - 15,
            PHASE_PULSE_END,
          ],
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
        height: METER_HEIGHT,
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

// ── Inline InsightText ──
const InsightText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [PHASE_TEXT_START, PHASE_TEXT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [PHASE_TEXT_START, PHASE_TEXT_END],
    [12, 0],
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
        top: INSIGHT_Y,
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
          color: COLOR_TEXT_PRIMARY,
        }}
      >
        Bigger window{" "}
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: COLOR_ACCENT_AND,
        }}
      >
        AND
      </span>
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: 28,
          fontWeight: 700,
          color: COLOR_TEXT_PRIMARY,
        }}
      >
        {" "}
        smarter model.
      </span>
    </div>
  );
};

// ── Connecting line between meters ──
const ConnectingLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Only show after both meters are full and pulsing
  const lineOpacity = interpolate(
    frame,
    [PHASE_PULSE_START, PHASE_PULSE_START + 20],
    [0, 0.4],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (lineOpacity <= 0) return null;

  const lineY = METER_TOP + METER_HEIGHT * 0.15; // Near top of filled meters
  const leftEdge = LEFT_METER_X + METER_WIDTH / 2 + 10;
  const rightEdge = RIGHT_METER_X - METER_WIDTH / 2 - 10;

  return (
    <svg
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        pointerEvents: "none",
        opacity: lineOpacity,
      }}
    >
      <defs>
        <linearGradient
          id="connectGradient"
          x1="0%"
          y1="0%"
          x2="100%"
          y2="0%"
        >
          <stop offset="0%" stopColor={LEFT_FILL_COLOR} stopOpacity={0.8} />
          <stop offset="50%" stopColor={COLOR_ACCENT_AND} stopOpacity={0.6} />
          <stop offset="100%" stopColor={RIGHT_FILL_COLOR} stopOpacity={0.8} />
        </linearGradient>
      </defs>
      <line
        x1={leftEdge}
        y1={lineY}
        x2={rightEdge}
        y2={lineY}
        stroke="url(#connectGradient)"
        strokeWidth={2}
        strokeDasharray="8 4"
      />
    </svg>
  );
};

// ── Main Component ──
export const Part1Economics19DoubleMeterInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // Background transition from deep black to dark navy
  const bgProgress = interpolate(
    frame,
    [PHASE_BG_START, PHASE_BG_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Lerp hex colors for background
  const bgColor = lerpColor(BG_COLOR_START, BG_COLOR_END, bgProgress);

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
        y={METER_TOP}
        fillColor={LEFT_FILL_COLOR}
        title={LEFT_TITLE}
        bottomLabel={LEFT_BOTTOM_LABEL}
        topLabel={LEFT_TOP_LABEL}
        bottomLabelSize={18}
      />

      {/* Right Meter: Model Performance */}
      <VerticalMeter
        x={RIGHT_METER_X}
        y={METER_TOP}
        fillColor={RIGHT_FILL_COLOR}
        title={RIGHT_TITLE}
        bottomLabel={RIGHT_BOTTOM_LABEL}
        topLabel={RIGHT_TOP_LABEL}
        bottomLabelSize={14}
      />

      {/* Connecting dashed line between meters */}
      <ConnectingLine />

      {/* Insight text at bottom */}
      <InsightText />
    </AbsoluteFill>
  );
};

// ── Utility: Lerp between two hex colors ──
function lerpColor(a: string, b: string, t: number): string {
  const parseHex = (hex: string) => {
    const h = hex.replace("#", "");
    return [
      parseInt(h.substring(0, 2), 16),
      parseInt(h.substring(2, 4), 16),
      parseInt(h.substring(4, 6), 16),
    ];
  };
  const [r1, g1, b1] = parseHex(a);
  const [r2, g2, b2] = parseHex(b);
  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const blue = Math.round(b1 + (b2 - b1) * t);
  const toHex = (n: number) => n.toString(16).padStart(2, "0");
  return `#${toHex(r)}${toHex(g)}${toHex(blue)}`;
}

export default Part1Economics19DoubleMeterInsight;
