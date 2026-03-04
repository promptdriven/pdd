import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  spring,
} from "remotion";

const LINE_HEIGHT = 6;
const LINE_GAP = 4;

const PromptLine: React.FC<{
  width: number;
  y: number;
  opacity: number;
  color: string;
}> = ({ width, y, opacity, color }) => (
  <div
    style={{
      position: "absolute",
      top: y,
      left: 24,
      width,
      height: LINE_HEIGHT,
      borderRadius: 3,
      backgroundColor: color,
      opacity,
    }}
  />
);

const TestDot: React.FC<{
  x: number;
  y: number;
  size: number;
  opacity: number;
  delay: number;
  frame: number;
  fps: number;
}> = ({ x, y, size, opacity, delay, frame, fps }) => {
  const scale = spring({
    frame: frame - delay,
    fps,
    config: { damping: 12, stiffness: 120 },
  });
  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: size,
        height: size,
        borderRadius: 3,
        backgroundColor: "#22C55E",
        opacity: opacity * scale,
        transform: `scale(${scale})`,
      }}
    />
  );
};

const RollingNumber: React.FC<{
  value: number;
  prefix?: string;
  suffix?: string;
  frame: number;
  startFrame: number;
  duration: number;
  color: string;
  fontSize: number;
}> = ({ value, prefix, suffix, frame, startFrame, duration, color, fontSize }) => {
  const current = Math.round(
    interpolate(frame, [startFrame, startFrame + duration], [0, value], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    })
  );
  return (
    <span
      style={{
        fontFamily: "Inter, sans-serif",
        fontWeight: 700,
        fontSize,
        color,
        lineHeight: 1,
      }}
    >
      {prefix}
      {current}
      {suffix}
    </span>
  );
};

export const Part4PrecisionSplitPromptDetailVsTests: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Panel slide-in
  const panelProgress = spring({
    frame,
    fps,
    config: { damping: 14, stiffness: 80 },
  });

  // Center divider
  const dividerOpacity = interpolate(frame, [30, 50], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const glowPulse =
    0.6 +
    0.4 * Math.sin((frame / fps) * Math.PI * 2);
  const arrowSlide = interpolate(frame, [60, 90], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Left panel: 50 dense prompt lines
  const leftLines = Array.from({ length: 50 }, (_, i) => {
    const widthSeed = ((i * 7 + 13) % 17) / 17;
    const w = 120 + widthSeed * 200;
    const yPos = 60 + i * (LINE_HEIGHT + LINE_GAP);
    const lineOpacity = interpolate(
      frame,
      [10 + i * 0.4, 15 + i * 0.4],
      [0, 0.7],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    return { width: w, y: yPos, opacity: lineOpacity };
  });

  // Right panel: 10 clean prompt lines
  const rightLines = Array.from({ length: 10 }, (_, i) => {
    const widthSeed = ((i * 11 + 7) % 13) / 13;
    const w = 160 + widthSeed * 180;
    const yPos = 60 + i * (LINE_HEIGHT + LINE_GAP + 4);
    const lineOpacity = interpolate(
      frame,
      [10 + i * 1.5, 20 + i * 1.5],
      [0, 0.85],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    return { width: w, y: yPos, opacity: lineOpacity };
  });

  // Left tests: 3-5 dots below prompt
  const leftTests = Array.from({ length: 5 }, (_, i) => ({
    x: 24 + i * 28,
    y: 580,
    size: 18,
    delay: 80 + i * 6,
  }));

  // Right tests: 47 dots in dense grid
  const rightTests = Array.from({ length: 47 }, (_, i) => {
    const cols = 8;
    const col = i % cols;
    const row = Math.floor(i / cols);
    return {
      x: 24 + col * 44,
      y: 260 + row * 38,
      size: 28,
      delay: 60 + i * 2,
    };
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* LEFT PANEL */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "50%",
          height: "100%",
          transform: `translateX(${(1 - panelProgress) * -100}px)`,
          opacity: panelProgress,
        }}
      >
        {/* Label */}
        <div
          style={{
            position: "absolute",
            top: 36,
            left: 24,
            display: "flex",
            flexDirection: "column",
            gap: 4,
          }}
        >
          <span
            style={{
              fontWeight: 600,
              fontSize: 28,
              color: "#F59E0B",
              lineHeight: 1.2,
            }}
          >
            Few tests: specify everything
          </span>
          <span
            style={{
              fontWeight: 400,
              fontSize: 20,
              color: "rgba(255,255,255,0.6)",
            }}
          >
            Every edge case spelled out
          </span>
        </div>

        {/* Prompt document area */}
        <div
          style={{
            position: "absolute",
            top: 120,
            left: 24,
            width: 420,
            height: 520,
            backgroundColor: "rgba(245,158,11,0.06)",
            borderRadius: 12,
            border: "1px solid rgba(245,158,11,0.15)",
            overflow: "hidden",
          }}
        >
          {leftLines.map((line, i) => (
            <PromptLine
              key={i}
              width={line.width}
              y={line.y}
              opacity={line.opacity}
              color="#F59E0B"
            />
          ))}

          {/* Line count overlay */}
          <div
            style={{
              position: "absolute",
              bottom: 16,
              right: 20,
              display: "flex",
              alignItems: "baseline",
              gap: 6,
            }}
          >
            <span
              style={{
                fontSize: 20,
                color: "rgba(255,255,255,0.5)",
                fontWeight: 400,
              }}
            >
              ~
            </span>
            <RollingNumber
              value={50}
              suffix=" lines"
              frame={frame}
              startFrame={20}
              duration={60}
              color="#F59E0B"
              fontSize={48}
            />
          </div>
        </div>

        {/* Test indicators */}
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 24,
            display: "flex",
            flexDirection: "column",
            gap: 8,
          }}
        >
          <span
            style={{
              fontWeight: 700,
              fontSize: 32,
              color: "#22C55E",
            }}
          >
            <RollingNumber
              value={5}
              suffix=" tests"
              frame={frame}
              startFrame={80}
              duration={30}
              color="#22C55E"
              fontSize={32}
            />
          </span>
          <div style={{ position: "relative", width: 200, height: 30 }}>
            {leftTests.map((t, i) => (
              <TestDot
                key={i}
                x={t.x}
                y={0}
                size={t.size}
                opacity={1}
                delay={t.delay}
                frame={frame}
                fps={fps}
              />
            ))}
          </div>
        </div>
      </div>

      {/* RIGHT PANEL */}
      <div
        style={{
          position: "absolute",
          right: 0,
          top: 0,
          width: "50%",
          height: "100%",
          transform: `translateX(${(1 - panelProgress) * 100}px)`,
          opacity: panelProgress,
        }}
      >
        {/* Label */}
        <div
          style={{
            position: "absolute",
            top: 36,
            left: 24,
            display: "flex",
            flexDirection: "column",
            gap: 4,
          }}
        >
          <span
            style={{
              fontWeight: 600,
              fontSize: 28,
              color: "#22C55E",
              lineHeight: 1.2,
            }}
          >
            Many tests: specify intent
          </span>
          <span
            style={{
              fontWeight: 400,
              fontSize: 20,
              color: "rgba(255,255,255,0.6)",
            }}
          >
            Clean, focused prompt
          </span>
        </div>

        {/* Prompt document area */}
        <div
          style={{
            position: "absolute",
            top: 120,
            left: 24,
            width: 420,
            height: 180,
            backgroundColor: "rgba(34,197,94,0.06)",
            borderRadius: 12,
            border: "1px solid rgba(34,197,94,0.15)",
            overflow: "hidden",
          }}
        >
          {rightLines.map((line, i) => (
            <PromptLine
              key={i}
              width={line.width}
              y={line.y}
              opacity={line.opacity}
              color="#22C55E"
            />
          ))}

          {/* Line count overlay */}
          <div
            style={{
              position: "absolute",
              bottom: 12,
              right: 20,
              display: "flex",
              alignItems: "baseline",
              gap: 6,
            }}
          >
            <span
              style={{
                fontSize: 20,
                color: "rgba(255,255,255,0.5)",
                fontWeight: 400,
              }}
            >
              ~
            </span>
            <RollingNumber
              value={10}
              suffix=" lines"
              frame={frame}
              startFrame={20}
              duration={40}
              color="#22C55E"
              fontSize={48}
            />
          </div>
        </div>

        {/* Dense test wall */}
        <div
          style={{
            position: "absolute",
            top: 320,
            left: 0,
            width: "100%",
            height: 320,
          }}
        >
          <span
            style={{
              position: "absolute",
              top: -8,
              left: 24,
              fontWeight: 700,
              fontSize: 32,
              color: "#22C55E",
            }}
          >
            <RollingNumber
              value={47}
              suffix=" tests"
              frame={frame}
              startFrame={60}
              duration={50}
              color="#22C55E"
              fontSize={32}
            />
          </span>
          <div style={{ position: "relative", width: 400, height: 280, top: 30 }}>
            {rightTests.map((t, i) => (
              <TestDot
                key={i}
                x={t.x}
                y={t.y - 260}
                size={t.size}
                opacity={1}
                delay={t.delay}
                frame={frame}
                fps={fps}
              />
            ))}
          </div>
        </div>
      </div>

      {/* CENTER DIVIDER */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 0,
          width: 2,
          height: "100%",
          backgroundColor: "rgba(255,255,255,0.15)",
          opacity: dividerOpacity,
          transform: "translateX(-1px)",
        }}
      />

      {/* Center label + arrow */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          transform: "translate(-50%, -50%)",
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          gap: 12,
          opacity: dividerOpacity,
        }}
      >
        <div
          style={{
            backgroundColor: "rgba(10,22,40,0.9)",
            padding: "10px 20px",
            borderRadius: 8,
            border: "1px solid rgba(255,255,255,0.2)",
            boxShadow: `0 0 ${20 * glowPulse}px rgba(255,255,255,${0.15 * glowPulse})`,
          }}
        >
          <span
            style={{
              fontWeight: 600,
              fontSize: 22,
              color: "white",
              whiteSpace: "nowrap",
              textShadow: `0 0 ${10 * glowPulse}px rgba(255,255,255,${0.4 * glowPulse})`,
            }}
          >
            Tests absorb precision
          </span>
        </div>

        {/* Arrow */}
        <div
          style={{
            opacity: arrowSlide,
            transform: `translateX(${(1 - arrowSlide) * -20}px)`,
            display: "flex",
            alignItems: "center",
            gap: 4,
          }}
        >
          <div
            style={{
              width: 60,
              height: 2,
              backgroundColor: "white",
              borderRadius: 1,
            }}
          />
          <div
            style={{
              width: 0,
              height: 0,
              borderTop: "6px solid transparent",
              borderBottom: "6px solid transparent",
              borderLeft: "10px solid white",
            }}
          />
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionSplitPromptDetailVsTests;
