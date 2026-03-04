import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

/* ─── Fake Code Lines ───────────────────────────────────────────── */
const CodeLines: React.FC<{
  lineCount: number;
  color: string;
  type: "prompt" | "code";
}> = ({ lineCount, color, type }) => {
  const widths =
    type === "prompt"
      ? [85, 60, 72, 90, 45, 80, 55, 68, 92, 50, 78, 65, 88, 42, 70, 58, 82, 75, 48, 62]
      : [70, 45, 88, 52, 30, 75, 60, 82, 40, 65, 90, 35, 72, 55, 80, 48, 68, 85, 42, 58];

  const visible = Math.min(lineCount, 20);

  return (
    <div
      style={{
        display: "flex",
        flexDirection: "column",
        gap: type === "prompt" ? 5 : 3,
        width: "100%",
        overflow: "hidden",
      }}
    >
      {Array.from({ length: visible }).map((_, i) => (
        <div
          key={i}
          style={{
            display: "flex",
            alignItems: "center",
            gap: 8,
          }}
        >
          <span
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: type === "prompt" ? 11 : 9,
              color: "rgba(255,255,255,0.25)",
              width: 24,
              textAlign: "right",
              flexShrink: 0,
            }}
          >
            {i + 1}
          </span>
          <div
            style={{
              height: type === "prompt" ? 8 : 6,
              width: `${widths[i % widths.length]}%`,
              backgroundColor: color,
              opacity: 0.3 + 0.15 * ((i % 3) / 2),
              borderRadius: 3,
            }}
          />
        </div>
      ))}
    </div>
  );
};

/* ─── Rolling Counter ───────────────────────────────────────────── */
const RollingCounter: React.FC<{
  value: number;
  suffix?: string;
  color: string;
}> = ({ value, suffix = "", color }) => {
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
      ~{Math.round(value)}
      {suffix}
    </div>
  );
};

/* ─── Main Component ─────────────────────────────────────────────── */
export const Part3MoldSplitPromptVsCode: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps, durationInFrames } = useVideoConfig();

  // Panel slide-in
  const leftSlide = interpolate(frame, [0, fps * 0.5], [-80, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const rightSlide = interpolate(frame, [0, fps * 0.5], [80, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Panel opacity (visible from frame 0)
  const panelOpacity = interpolate(frame, [0, fps * 0.3], [0.7, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Left counter: rolls up to ~50 lines over 1–3s
  const leftCount = interpolate(frame, [fps * 0.5, fps * 3], [0, 50], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Right counter: rolls up to ~375 (midpoint of 250–500) over 1–4s
  const rightCount = interpolate(frame, [fps * 0.5, fps * 4], [0, 375], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Code lines visible (proportional reveal)
  const leftLinesVisible = interpolate(frame, [fps * 0.3, fps * 2.5], [2, 20], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const rightLinesVisible = interpolate(frame, [fps * 0.3, fps * 3], [2, 20], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Center ratio reveal (after counters mostly done)
  const ratioOpacity = interpolate(frame, [fps * 3.5, fps * 4.5], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const ratioScale = interpolate(frame, [fps * 3.5, fps * 4.5], [0.8, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Pulsing glow for ratio text
  const glowIntensity = interpolate(
    frame % (fps * 1.5),
    [0, fps * 0.75, fps * 1.5],
    [0.4, 1, 0.4],
    { extrapolateRight: "clamp" }
  );

  // Divider line grow
  const dividerHeight = interpolate(frame, [0, fps * 0.7], [0, 100], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Arrow opacity (appears with ratio)
  const arrowOpacity = interpolate(frame, [fps * 4, fps * 5], [0, 1], {
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

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        fontFamily: "'Inter', sans-serif",
        opacity: fadeOut,
      }}
    >
      {/* Left Panel — The Prompt */}
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
        {/* Panel background with gold border */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 40,
            right: 20,
            bottom: 40,
            backgroundColor: "rgba(245, 158, 11, 0.06)",
            border: "1px solid rgba(245, 158, 11, 0.3)",
            borderRadius: 16,
            boxShadow: `0 0 ${12 + 8 * glowIntensity}px rgba(245, 158, 11, ${0.08 * glowIntensity})`,
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
          The Prompt
        </div>

        {/* Label */}
        <div
          style={{
            fontSize: 28,
            fontWeight: 600,
            color: "#F59E0B",
            marginBottom: 20,
            zIndex: 1,
          }}
        >
          Prompt specification
        </div>

        {/* Code preview area */}
        <div
          style={{
            width: 320,
            height: 200,
            backgroundColor: "rgba(0, 0, 0, 0.3)",
            borderRadius: 8,
            border: "1px solid rgba(245, 158, 11, 0.2)",
            padding: "12px 16px",
            overflow: "hidden",
            zIndex: 1,
          }}
        >
          <CodeLines
            lineCount={Math.floor(leftLinesVisible)}
            color="#F59E0B"
            type="prompt"
          />
        </div>

        {/* Line count */}
        <div style={{ marginTop: 20, zIndex: 1 }}>
          <RollingCounter
            value={leftCount}
            suffix=" lines"
            color="#F59E0B"
          />
        </div>

        {/* Descriptor */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.6)",
            marginTop: 8,
            zIndex: 1,
          }}
        >
          Compact NL document
        </div>
      </div>

      {/* Right Panel — Generated Code */}
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
        {/* Panel background with blue border */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 20,
            right: 40,
            bottom: 40,
            backgroundColor: "rgba(59, 130, 246, 0.06)",
            border: "1px solid rgba(59, 130, 246, 0.2)",
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
          Generated Code
        </div>

        {/* Label */}
        <div
          style={{
            fontSize: 28,
            fontWeight: 600,
            color: "#3B82F6",
            marginBottom: 20,
            zIndex: 1,
          }}
        >
          Generated implementation
        </div>

        {/* Code preview area */}
        <div
          style={{
            width: 320,
            height: 200,
            backgroundColor: "rgba(0, 0, 0, 0.3)",
            borderRadius: 8,
            border: "1px solid rgba(59, 130, 246, 0.2)",
            padding: "12px 16px",
            overflow: "hidden",
            zIndex: 1,
          }}
        >
          <CodeLines
            lineCount={Math.floor(rightLinesVisible)}
            color="#3B82F6"
            type="code"
          />
        </div>

        {/* Line count */}
        <div style={{ marginTop: 20, zIndex: 1 }}>
          <RollingCounter
            value={rightCount}
            suffix=" lines"
            color="#3B82F6"
          />
        </div>

        {/* Descriptor */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.6)",
            marginTop: 8,
            zIndex: 1,
          }}
        >
          Dense code listing
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

      {/* Center Ratio Indicator */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          transform: `translate(-50%, -50%) scale(${ratioScale})`,
          opacity: ratioOpacity,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          zIndex: 10,
        }}
      >
        <div
          style={{
            backgroundColor: "rgba(10, 22, 40, 0.95)",
            border: "1px solid rgba(245, 158, 11, 0.4)",
            borderRadius: 12,
            padding: "16px 28px",
            boxShadow: `0 0 ${20 + 20 * glowIntensity}px rgba(245, 158, 11, ${0.15 * glowIntensity})`,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            gap: 8,
          }}
        >
          {/* Arrow */}
          <div
            style={{
              fontSize: 24,
              color: "#F59E0B",
              opacity: arrowOpacity,
              marginBottom: 4,
            }}
          >
            ← prompt → code →
          </div>

          {/* Ratio text */}
          <div
            style={{
              fontSize: 32,
              fontWeight: 700,
              color: "#F59E0B",
              textAlign: "center",
              textShadow: `0 0 ${14 * glowIntensity}px rgba(245, 158, 11, ${0.5 * glowIntensity})`,
              lineHeight: 1.2,
            }}
          >
            1/5 to 1/10 the size
          </div>

          <div
            style={{
              fontSize: 18,
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.6)",
              textAlign: "center",
              marginTop: 2,
            }}
          >
            Prompt-to-code expansion ratio
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldSplitPromptVsCode;
