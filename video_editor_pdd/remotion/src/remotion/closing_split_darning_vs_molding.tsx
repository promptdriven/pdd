import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  staticFile,
  Video,
} from "remotion";

/* ─── Icon Components ──────────────────────────────────────────── */
const NeedleIcon: React.FC<{ opacity: number }> = ({ opacity }) => (
  <svg
    width="64"
    height="64"
    viewBox="0 0 64 64"
    fill="none"
    style={{ opacity }}
  >
    {/* Darning needle */}
    <line
      x1="12"
      y1="52"
      x2="52"
      y2="12"
      stroke="#EF4444"
      strokeWidth="3"
      strokeLinecap="round"
    />
    <circle cx="54" cy="10" r="4" stroke="#EF4444" strokeWidth="2" fill="none" />
    {/* Thread */}
    <path
      d="M12 52 Q8 48, 14 42 Q20 36, 16 30 Q12 24, 18 18"
      stroke="#EF4444"
      strokeWidth="1.5"
      strokeLinecap="round"
      fill="none"
      opacity={0.5}
    />
  </svg>
);

const MoldIcon: React.FC<{ opacity: number; glow: number }> = ({
  opacity,
  glow,
}) => (
  <svg
    width="64"
    height="64"
    viewBox="0 0 64 64"
    fill="none"
    style={{ opacity }}
  >
    {/* Three-part mold shape */}
    <rect
      x="8"
      y="8"
      width="48"
      height="14"
      rx="3"
      stroke="#22C55E"
      strokeWidth="2"
      fill={`rgba(34, 197, 94, ${0.1 + 0.15 * glow})`}
    />
    <rect
      x="8"
      y="25"
      width="48"
      height="14"
      rx="3"
      stroke="#22C55E"
      strokeWidth="2"
      fill={`rgba(34, 197, 94, ${0.1 + 0.15 * glow})`}
    />
    <rect
      x="8"
      y="42"
      width="48"
      height="14"
      rx="3"
      stroke="#22C55E"
      strokeWidth="2"
      fill={`rgba(34, 197, 94, ${0.1 + 0.15 * glow})`}
    />
    {/* Glow effect */}
    <rect
      x="4"
      y="4"
      width="56"
      height="56"
      rx="6"
      stroke="#22C55E"
      strokeWidth="1"
      fill="none"
      opacity={0.3 * glow}
    />
  </svg>
);

/* ─── Fake Diff Lines ──────────────────────────────────────────── */
const DiffLines: React.FC<{ lineCount: number }> = ({ lineCount }) => {
  const widths = [72, 55, 88, 40, 65, 80, 48, 90, 35, 60, 75, 50, 82, 45, 68];
  const types = ["+", "-", " ", "-", "+", " ", "-", "+", " ", "+", "-", " ", "+", "-", "+"];
  const visible = Math.min(Math.floor(lineCount), 15);

  return (
    <div style={{ display: "flex", flexDirection: "column", gap: 2, width: "100%" }}>
      {Array.from({ length: visible }).map((_, i) => {
        const t = types[i % types.length];
        const color =
          t === "+" ? "rgba(239, 68, 68, 0.4)" :
          t === "-" ? "rgba(239, 68, 68, 0.25)" :
          "rgba(255, 255, 255, 0.12)";
        return (
          <div key={i} style={{ display: "flex", alignItems: "center", gap: 6 }}>
            <span
              style={{
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 9,
                color: t === "+" ? "#EF4444" : t === "-" ? "rgba(239,68,68,0.6)" : "rgba(255,255,255,0.3)",
                width: 12,
                textAlign: "center",
                flexShrink: 0,
              }}
            >
              {t}
            </span>
            <div
              style={{
                height: 5,
                width: `${widths[i % widths.length]}%`,
                backgroundColor: color,
                borderRadius: 2,
              }}
            />
          </div>
        );
      })}
    </div>
  );
};

/* ─── Terminal Lines ───────────────────────────────────────────── */
const TerminalLines: React.FC<{ progress: number }> = ({ progress }) => {
  const lines = [
    { text: "$ pdd generate", color: "#22C55E", delay: 0 },
    { text: "  Reading prompt.md...", color: "rgba(255,255,255,0.6)", delay: 0.15 },
    { text: "  Generating module...", color: "rgba(255,255,255,0.6)", delay: 0.3 },
    { text: "  Running tests...", color: "rgba(255,255,255,0.6)", delay: 0.45 },
    { text: "  ✓ All 12 tests passed", color: "#22C55E", delay: 0.6 },
    { text: "  ✓ Module written", color: "#22C55E", delay: 0.75 },
  ];

  return (
    <div style={{ display: "flex", flexDirection: "column", gap: 4, width: "100%" }}>
      {lines.map((line, i) => {
        const visible = progress > line.delay ? 1 : 0;
        return (
          <span
            key={i}
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 11,
              color: line.color,
              opacity: visible,
              whiteSpace: "nowrap",
            }}
          >
            {line.text}
          </span>
        );
      })}
    </div>
  );
};

/* ─── Main Component ───────────────────────────────────────────── */
export const ClosingSplitDarningVsMolding: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps, durationInFrames } = useVideoConfig();

  /* ── Animation Timings ── */

  // Divider appears first (0–0.3s)
  const dividerOpacity = interpolate(frame, [0, fps * 0.3], [0.3, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const dividerHeight = interpolate(frame, [0, fps * 0.3], [0, 100], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Left panel fades in (0.1s–0.6s)
  const leftOpacity = interpolate(frame, [fps * 0.1, fps * 0.6], [0.3, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const leftSlide = interpolate(frame, [fps * 0.1, fps * 0.6], [-40, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Right panel fades in 0.4s later (0.5s–1.0s)
  const rightOpacity = interpolate(frame, [fps * 0.5, fps * 1.0], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const rightSlide = interpolate(frame, [fps * 0.5, fps * 1.0], [40, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Right panel glow pulse on arrival
  const rightGlow = interpolate(
    frame,
    [fps * 0.8, fps * 1.5, fps * 2.5],
    [0, 1, 0.3],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  // Diff lines reveal on left
  const diffLineCount = interpolate(frame, [fps * 0.6, fps * 3], [0, 15], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Terminal progress on right
  const terminalProgress = interpolate(frame, [fps * 1.2, fps * 5], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Arrow: pulses twice then holds
  const arrowPulse1 = interpolate(
    frame,
    [fps * 1.5, fps * 2.0, fps * 2.5],
    [0, 1, 0.4],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );
  const arrowPulse2 = interpolate(
    frame,
    [fps * 2.8, fps * 3.3, fps * 3.8],
    [0.4, 1, 0.7],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );
  const arrowOpacity = frame < fps * 1.5 ? 0 : frame < fps * 2.8 ? arrowPulse1 : arrowPulse2;
  const arrowTranslateX = interpolate(
    frame,
    [fps * 1.5, fps * 2.0, fps * 2.5, fps * 3.0],
    [0, 6, 0, 6],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  // Fade-out at end
  const fadeOut = interpolate(
    frame,
    [durationInFrames - 15, durationInFrames],
    [1, 0],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  // Subtext fade-in
  const leftSubOpacity = interpolate(frame, [fps * 1.5, fps * 2.2], [0, 0.7], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const rightSubOpacity = interpolate(frame, [fps * 2.0, fps * 2.7], [0, 0.7], {
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
      {/* Background video — closing.mp4 */}
      <Video
        src={staticFile("veo/closing.mp4")}
        style={{
          position: "absolute",
          width: "100%",
          height: "100%",
          objectFit: "cover",
          opacity: 0.12,
        }}
      />

      {/* ── Left Panel — Keep Darning ── */}
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
          opacity: leftOpacity,
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
            backgroundColor: "rgba(239, 68, 68, 0.04)",
            border: "1px solid rgba(239, 68, 68, 0.2)",
            borderRadius: 16,
          }}
        />

        {/* Needle icon */}
        <div style={{ zIndex: 1, marginBottom: 16 }}>
          <NeedleIcon opacity={leftOpacity} />
        </div>

        {/* Header */}
        <div
          style={{
            fontSize: 36,
            fontWeight: 700,
            color: "#EF4444",
            marginBottom: 24,
            zIndex: 1,
          }}
        >
          Keep Darning
        </div>

        {/* Diff visualization area */}
        <div
          style={{
            width: 320,
            height: 160,
            backgroundColor: "rgba(0, 0, 0, 0.3)",
            borderRadius: 8,
            border: "1px solid rgba(239, 68, 68, 0.2)",
            padding: "10px 14px",
            overflow: "hidden",
            zIndex: 1,
          }}
        >
          <DiffLines lineCount={diffLineCount} />
        </div>

        {/* Subtext */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.7)",
            marginTop: 28,
            maxWidth: 340,
            textAlign: "center",
            lineHeight: 1.5,
            opacity: leftSubOpacity,
            zIndex: 1,
          }}
        >
          Patches get faster.
          <br />
          Debt still compounds.
        </div>
      </div>

      {/* ── Right Panel — Build the Mold ── */}
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
          opacity: rightOpacity,
        }}
      >
        {/* Panel background with glow */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 20,
            right: 40,
            bottom: 40,
            backgroundColor: `rgba(34, 197, 94, ${0.04 + 0.04 * rightGlow})`,
            border: "1px solid rgba(34, 197, 94, 0.3)",
            borderRadius: 16,
            boxShadow: `0 0 ${16 + 20 * rightGlow}px rgba(34, 197, 94, ${0.06 * rightGlow})`,
          }}
        />

        {/* Mold icon */}
        <div style={{ zIndex: 1, marginBottom: 16 }}>
          <MoldIcon opacity={rightOpacity} glow={rightGlow} />
        </div>

        {/* Header */}
        <div
          style={{
            fontSize: 36,
            fontWeight: 700,
            color: "#22C55E",
            marginBottom: 24,
            zIndex: 1,
            textShadow: `0 0 ${10 * rightGlow}px rgba(34, 197, 94, ${0.4 * rightGlow})`,
          }}
        >
          Build the Mold
        </div>

        {/* Terminal visualization area */}
        <div
          style={{
            width: 320,
            height: 160,
            backgroundColor: "rgba(0, 0, 0, 0.4)",
            borderRadius: 8,
            border: "1px solid rgba(34, 197, 94, 0.2)",
            padding: "10px 14px",
            overflow: "hidden",
            zIndex: 1,
          }}
        >
          <TerminalLines progress={terminalProgress} />
        </div>

        {/* Subtext */}
        <div
          style={{
            fontSize: 20,
            fontWeight: 400,
            color: "rgba(255, 255, 255, 0.7)",
            marginTop: 28,
            maxWidth: 380,
            textAlign: "center",
            lineHeight: 1.5,
            opacity: rightSubOpacity,
            zIndex: 1,
          }}
        >
          Tests lock behavior. Prompt specifies intent.
          <br />
          Regenerate at will.
        </div>
      </div>

      {/* ── Center Divider ── */}
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
          opacity: dividerOpacity,
        }}
      />

      {/* ── Center Arrow (pointing right, pulsing) ── */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          transform: `translate(-50%, -50%) translateX(${arrowTranslateX}px)`,
          opacity: arrowOpacity,
          zIndex: 10,
        }}
      >
        <svg width="40" height="40" viewBox="0 0 40 40" fill="none">
          <path
            d="M12 20 L28 20 M22 13 L29 20 L22 27"
            stroke="white"
            strokeWidth="2.5"
            strokeLinecap="round"
            strokeLinejoin="round"
            opacity={0.8}
          />
        </svg>
      </div>
    </AbsoluteFill>
  );
};

export default ClosingSplitDarningVsMolding;
