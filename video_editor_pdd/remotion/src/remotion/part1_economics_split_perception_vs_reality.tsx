import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

/* ─── Speedometer ────────────────────────────────────────────────── */
const Speedometer: React.FC<{
  progress: number; // 0–1
  color: string;
  declining?: boolean;
}> = ({ progress, color, declining }) => {
  const startAngle = -225;
  const endAngle = 45;
  const needleAngle = startAngle + (endAngle - startAngle) * progress;

  const cx = 100;
  const cy = 100;
  const r = 70;

  const arcPath = (startDeg: number, endDeg: number) => {
    const s = (startDeg * Math.PI) / 180;
    const e = (endDeg * Math.PI) / 180;
    const x1 = cx + r * Math.cos(s);
    const y1 = cy + r * Math.sin(s);
    const x2 = cx + r * Math.cos(e);
    const y2 = cy + r * Math.sin(e);
    const large = endDeg - startDeg > 180 ? 1 : 0;
    return `M ${x1} ${y1} A ${r} ${r} 0 ${large} 1 ${x2} ${y2}`;
  };

  const needleRad = (needleAngle * Math.PI) / 180;
  const nx = cx + (r - 15) * Math.cos(needleRad);
  const ny = cy + (r - 15) * Math.sin(needleRad);

  return (
    <svg width={200} height={140} viewBox="0 0 200 140">
      {/* Track */}
      <path
        d={arcPath(-225, 45)}
        fill="none"
        stroke="rgba(255,255,255,0.15)"
        strokeWidth={8}
        strokeLinecap="round"
      />
      {/* Filled arc */}
      <path
        d={arcPath(-225, needleAngle)}
        fill="none"
        stroke={color}
        strokeWidth={8}
        strokeLinecap="round"
      />
      {/* Needle */}
      <line
        x1={cx}
        y1={cy}
        x2={nx}
        y2={ny}
        stroke="white"
        strokeWidth={3}
        strokeLinecap="round"
      />
      {/* Center dot */}
      <circle cx={cx} cy={cy} r={6} fill="white" />
      {/* Tick marks */}
      {[0, 0.25, 0.5, 0.75, 1].map((t) => {
        const a = ((-225 + 270 * t) * Math.PI) / 180;
        const ix = cx + (r - 2) * Math.cos(a);
        const iy = cy + (r - 2) * Math.sin(a);
        const ox = cx + (r + 8) * Math.cos(a);
        const oy = cy + (r + 8) * Math.sin(a);
        return (
          <line
            key={t}
            x1={ix}
            y1={iy}
            x2={ox}
            y2={oy}
            stroke="rgba(255,255,255,0.4)"
            strokeWidth={2}
          />
        );
      })}
      {/* Direction arrow hint */}
      <text
        x={cx}
        y={cy + 30}
        textAnchor="middle"
        fill="rgba(255,255,255,0.5)"
        fontSize={16}
        fontFamily="'Inter', sans-serif"
      >
        {declining ? "▼" : "▲"}
      </text>
    </svg>
  );
};

/* ─── Animated Counter ───────────────────────────────────────────── */
const AnimatedCounter: React.FC<{
  value: number;
  prefix: string;
  suffix: string;
  color: string;
}> = ({ value, prefix, suffix, color }) => {
  return (
    <div
      style={{
        fontFamily: "'Inter', sans-serif",
        fontWeight: 700,
        fontSize: 48,
        color,
        textAlign: "center",
        lineHeight: 1.1,
      }}
    >
      {prefix}
      {Math.round(value)}
      {suffix}
    </div>
  );
};

/* ─── Bug Count Bars ─────────────────────────────────────────────── */
const BugBars: React.FC<{ progress: number }> = ({ progress }) => {
  const bars = [0.3, 0.5, 0.7, 0.85, 1.0];
  return (
    <div
      style={{
        display: "flex",
        alignItems: "flex-end",
        justifyContent: "center",
        gap: 6,
        height: 50,
        marginTop: 8,
      }}
    >
      {bars.map((h, i) => {
        const barProgress = Math.min(1, progress * 1.5 - i * 0.15);
        const barHeight = Math.max(0, h * 50 * Math.max(0, barProgress));
        return (
          <div
            key={i}
            style={{
              width: 14,
              height: barHeight,
              backgroundColor: "#EF4444",
              borderRadius: 3,
              opacity: 0.7 + 0.3 * barProgress,
            }}
          />
        );
      })}
    </div>
  );
};

/* ─── Positive Metric Bars ───────────────────────────────────────── */
const PositiveBars: React.FC<{ progress: number }> = ({ progress }) => {
  const bars = [0.5, 0.65, 0.8, 0.9, 1.0];
  return (
    <div
      style={{
        display: "flex",
        alignItems: "flex-end",
        justifyContent: "center",
        gap: 6,
        height: 50,
        marginTop: 8,
      }}
    >
      {bars.map((h, i) => {
        const barProgress = Math.min(1, progress * 1.5 - i * 0.1);
        const barHeight = Math.max(0, h * 50 * Math.max(0, barProgress));
        return (
          <div
            key={i}
            style={{
              width: 14,
              height: barHeight,
              backgroundColor: "#22C55E",
              borderRadius: 3,
              opacity: 0.7 + 0.3 * barProgress,
            }}
          />
        );
      })}
    </div>
  );
};

/* ─── Main Component ─────────────────────────────────────────────── */
export const Part1EconomicsSplitPerceptionVsReality: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps, durationInFrames } = useVideoConfig();

  // Animation progress (0→1 over first 3 seconds)
  const animProgress = interpolate(frame, [0, fps * 3], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Panel slide-in
  const leftSlide = interpolate(frame, [0, fps * 0.6], [-100, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const rightSlide = interpolate(frame, [0, fps * 0.6], [100, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Panel opacity (visible from frame 0)
  const panelOpacity = interpolate(frame, [0, fps * 0.4], [0.6, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Fade-out at end
  const fadeOut = interpolate(
    frame,
    [durationInFrames - 20, durationInFrames],
    [1, 0],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  // Counter values
  const leftCounter = interpolate(frame, [fps * 0.5, fps * 2.5], [0, 20], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const rightCounter = interpolate(frame, [fps * 0.5, fps * 2.5], [0, 19], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Gap reveal (after counters finish)
  const gapOpacity = interpolate(frame, [fps * 2.8, fps * 3.5], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const gapScale = interpolate(frame, [fps * 2.8, fps * 3.5], [0.8, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Pulsing glow for gap indicator
  const glowIntensity = interpolate(
    frame % (fps * 1.5),
    [0, fps * 0.75, fps * 1.5],
    [0.4, 1, 0.4],
    { extrapolateRight: "clamp" }
  );

  // Speedometer progress
  const leftSpeedometer = interpolate(
    frame,
    [fps * 0.3, fps * 2.5],
    [0.3, 0.75],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );
  const rightSpeedometer = interpolate(
    frame,
    [fps * 0.3, fps * 2.5],
    [0.65, 0.3],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  // Divider line grow
  const dividerHeight = interpolate(frame, [0, fps * 0.8], [0, 100], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        fontFamily: "'Inter', sans-serif",
        opacity: fadeOut,
      }}
    >
      {/* Left Panel — Perception */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "50%",
          height: "100%",
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
          transform: `translateX(${leftSlide}px)`,
          opacity: panelOpacity,
        }}
      >
        {/* Panel background */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 40,
            right: 20,
            bottom: 40,
            backgroundColor: "rgba(34, 197, 94, 0.06)",
            border: "1px solid rgba(34, 197, 94, 0.2)",
            borderRadius: 16,
          }}
        />

        {/* Header label */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.6)",
            letterSpacing: "0.08em",
            textTransform: "uppercase",
            marginBottom: 8,
            zIndex: 1,
          }}
        >
          What It Feels Like
        </div>

        {/* Label */}
        <div
          style={{
            fontSize: 28,
            fontWeight: 600,
            color: "#22C55E",
            marginBottom: 24,
            zIndex: 1,
          }}
        >
          Perceived: 20% faster
        </div>

        {/* Speedometer */}
        <div style={{ zIndex: 1 }}>
          <Speedometer
            progress={leftSpeedometer}
            color="#22C55E"
            declining={false}
          />
        </div>

        {/* Counter */}
        <div style={{ marginTop: 16, zIndex: 1 }}>
          <AnimatedCounter
            value={leftCounter}
            prefix="+"
            suffix="%"
            color="#22C55E"
          />
        </div>

        {/* Positive bars */}
        <div style={{ zIndex: 1 }}>
          <PositiveBars progress={animProgress} />
        </div>

        {/* Descriptor */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.6)",
            marginTop: 12,
            zIndex: 1,
          }}
        >
          Optimistic self-report
        </div>
      </div>

      {/* Right Panel — Reality */}
      <div
        style={{
          position: "absolute",
          right: 0,
          top: 0,
          width: "50%",
          height: "100%",
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
          transform: `translateX(${rightSlide}px)`,
          opacity: panelOpacity,
        }}
      >
        {/* Panel background */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 20,
            right: 40,
            bottom: 40,
            backgroundColor: "rgba(239, 68, 68, 0.06)",
            border: "1px solid rgba(239, 68, 68, 0.2)",
            borderRadius: 16,
          }}
        />

        {/* Header label */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.6)",
            letterSpacing: "0.08em",
            textTransform: "uppercase",
            marginBottom: 8,
            zIndex: 1,
          }}
        >
          What Actually Happens
        </div>

        {/* Label */}
        <div
          style={{
            fontSize: 28,
            fontWeight: 600,
            color: "#EF4444",
            marginBottom: 24,
            zIndex: 1,
          }}
        >
          Measured: 19% slower
        </div>

        {/* Speedometer */}
        <div style={{ zIndex: 1 }}>
          <Speedometer
            progress={rightSpeedometer}
            color="#EF4444"
            declining={true}
          />
        </div>

        {/* Counter */}
        <div style={{ marginTop: 16, zIndex: 1 }}>
          <AnimatedCounter
            value={rightCounter}
            prefix="-"
            suffix="%"
            color="#EF4444"
          />
        </div>

        {/* Bug count bars */}
        <div style={{ zIndex: 1 }}>
          <BugBars progress={animProgress} />
        </div>

        {/* Descriptor */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.6)",
            marginTop: 12,
            zIndex: 1,
          }}
        >
          Measured benchmarks
        </div>
      </div>

      {/* Center Divider */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 0,
          width: 2,
          height: `${dividerHeight}%`,
          background:
            "linear-gradient(to bottom, transparent, rgba(255,255,255,0.3), transparent)",
          transform: "translateX(-50%)",
        }}
      />

      {/* Gap Indicator */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          transform: `translate(-50%, -50%) scale(${gapScale})`,
          opacity: gapOpacity,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          zIndex: 10,
        }}
      >
        <div
          style={{
            backgroundColor: "rgba(10, 22, 40, 0.9)",
            border: "1px solid rgba(255, 255, 255, 0.3)",
            borderRadius: 12,
            padding: "16px 28px",
            boxShadow: `0 0 ${20 + 20 * glowIntensity}px rgba(255, 255, 255, ${0.1 * glowIntensity})`,
          }}
        >
          <div
            style={{
              fontSize: 48,
              fontWeight: 700,
              color: "#FFFFFF",
              textAlign: "center",
              textShadow: `0 0 ${12 * glowIntensity}px rgba(255, 255, 255, ${0.5 * glowIntensity})`,
              lineHeight: 1.1,
            }}
          >
            39-point gap
          </div>
          <div
            style={{
              fontSize: 18,
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.6)",
              textAlign: "center",
              marginTop: 4,
            }}
          >
            Developer Perception Gap
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part1EconomicsSplitPerceptionVsReality;
