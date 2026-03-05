import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
} from "remotion";

/* ─── Row Data ────────────────────────────────────────────────── */
const ROWS = [
  {
    label: "Fix a bug",
    left: "One place, once",
    right: "Impossible forever",
  },
  {
    label: "Improve code",
    left: "One version",
    right: "All future versions",
  },
  {
    label: "Document intent",
    left: "One snapshot",
    right: "Living specification",
  },
];

/* ─── Main Component ──────────────────────────────────────────── */
export const Part5CompoundSplitPatchingVsPdd: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps, durationInFrames } = useVideoConfig();

  /* ── Animation Timings ── */
  // Table frame appears (0–0.3s)
  const tableOpacity = interpolate(frame, [0, fps * 0.3], [0.8, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });
  const tableBorderOpacity = interpolate(frame, [0, fps * 0.3], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Header fade-in
  const headerOpacity = interpolate(frame, [0, fps * 0.25], [0.6, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // Fade-out at end
  const fadeOut = interpolate(
    frame,
    [durationInFrames - 15, durationInFrames],
    [1, 0],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  // Row label cascade (0.3s base, 0.2s stagger per row)
  const rowLabelOpacities = ROWS.map((_, i) => {
    const start = fps * 0.3 + i * fps * 0.2;
    return interpolate(frame, [start, start + fps * 0.25], [0, 0.8], {
      extrapolateRight: "clamp",
      extrapolateLeft: "clamp",
    });
  });

  // Left column values (appear after labels, slight downward motion)
  const leftValueAnimations = ROWS.map((_, i) => {
    const start = fps * 0.5 + i * fps * 0.2;
    const opacity = interpolate(frame, [start, start + fps * 0.3], [0, 0.9], {
      extrapolateRight: "clamp",
      extrapolateLeft: "clamp",
    });
    const translateY = interpolate(frame, [start, start + fps * 0.3], [-12, 0], {
      extrapolateRight: "clamp",
      extrapolateLeft: "clamp",
    });
    return { opacity, translateY };
  });

  // Right column values (0.3s after left, slight upward motion + glow)
  const rightValueAnimations = ROWS.map((_, i) => {
    const start = fps * 0.8 + i * fps * 0.2;
    const opacity = interpolate(frame, [start, start + fps * 0.3], [0, 0.9], {
      extrapolateRight: "clamp",
      extrapolateLeft: "clamp",
    });
    const translateY = interpolate(frame, [start, start + fps * 0.3], [12, 0], {
      extrapolateRight: "clamp",
      extrapolateLeft: "clamp",
    });
    // Glow pulse on arrival (peaks ~0.2s after appearing, then settles)
    const glowProgress = interpolate(
      frame,
      [start + fps * 0.2, start + fps * 0.5, start + fps * 1.2],
      [0, 1, 0.3],
      { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
    );
    return { opacity, translateY, glowProgress };
  });

  const TABLE_WIDTH = 860;
  const ROW_HEIGHT = 72;
  const HEADER_HEIGHT = 64;
  const LEFT_COL_WIDTH = 280;
  const CENTER_COL_WIDTH = 200;
  const RIGHT_COL_WIDTH = 280;
  const TABLE_LEFT = (1920 - TABLE_WIDTH) / 2;
  const TABLE_TOP = (1080 - (HEADER_HEIGHT + ROW_HEIGHT * 3 + 4)) / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        fontFamily: "'Inter', sans-serif",
        opacity: fadeOut,
      }}
    >
      {/* Table Container */}
      <div
        style={{
          position: "absolute",
          left: TABLE_LEFT,
          top: TABLE_TOP,
          width: TABLE_WIDTH,
          opacity: tableOpacity,
        }}
      >
        {/* ── Header Row ── */}
        <div
          style={{
            display: "flex",
            height: HEADER_HEIGHT,
            borderBottom: `1px solid rgba(51, 65, 85, ${tableBorderOpacity})`,
          }}
        >
          {/* Left Header: Patching */}
          <div
            style={{
              width: LEFT_COL_WIDTH,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              opacity: headerOpacity,
            }}
          >
            <span
              style={{
                fontWeight: 700,
                fontSize: 36,
                color: "#EF4444",
              }}
            >
              Patching
            </span>
          </div>

          {/* Center spacer */}
          <div
            style={{
              width: CENTER_COL_WIDTH,
              borderLeft: `1px solid rgba(51, 65, 85, ${tableBorderOpacity})`,
              borderRight: `1px solid rgba(51, 65, 85, ${tableBorderOpacity})`,
            }}
          />

          {/* Right Header: PDD */}
          <div
            style={{
              width: RIGHT_COL_WIDTH,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              opacity: headerOpacity,
            }}
          >
            <span
              style={{
                fontWeight: 700,
                fontSize: 36,
                color: "#22C55E",
              }}
            >
              PDD
            </span>
          </div>
        </div>

        {/* ── Data Rows ── */}
        {ROWS.map((row, i) => (
          <div
            key={row.label}
            style={{
              display: "flex",
              height: ROW_HEIGHT,
              borderBottom:
                i < ROWS.length - 1
                  ? `1px solid rgba(51, 65, 85, ${tableBorderOpacity})`
                  : "none",
            }}
          >
            {/* Left Value (red, downward motion) */}
            <div
              style={{
                width: LEFT_COL_WIDTH,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                padding: "0 16px",
              }}
            >
              <span
                style={{
                  fontWeight: 400,
                  fontSize: 22,
                  color: "#EF4444",
                  opacity: leftValueAnimations[i].opacity,
                  transform: `translateY(${leftValueAnimations[i].translateY}px)`,
                  textAlign: "center",
                  lineHeight: 1.3,
                }}
              >
                {row.left}
              </span>
            </div>

            {/* Center Label (white 80% opacity) */}
            <div
              style={{
                width: CENTER_COL_WIDTH,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                borderLeft: `1px solid rgba(51, 65, 85, ${tableBorderOpacity})`,
                borderRight: `1px solid rgba(51, 65, 85, ${tableBorderOpacity})`,
                padding: "0 12px",
              }}
            >
              <span
                style={{
                  fontWeight: 600,
                  fontSize: 24,
                  color: `rgba(255, 255, 255, ${0.8 * rowLabelOpacities[i]})`,
                  textAlign: "center",
                  lineHeight: 1.3,
                }}
              >
                {row.label}
              </span>
            </div>

            {/* Right Value (green, upward motion + glow) */}
            <div
              style={{
                width: RIGHT_COL_WIDTH,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                padding: "0 16px",
              }}
            >
              <span
                style={{
                  fontWeight: 400,
                  fontSize: 22,
                  color: "#22C55E",
                  opacity: rightValueAnimations[i].opacity,
                  transform: `translateY(${rightValueAnimations[i].translateY}px)`,
                  textShadow: `0 0 ${12 * rightValueAnimations[i].glowProgress}px rgba(34, 197, 94, ${0.6 * rightValueAnimations[i].glowProgress})`,
                  textAlign: "center",
                  lineHeight: 1.3,
                }}
              >
                {row.right}
              </span>
            </div>
          </div>
        ))}
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundSplitPatchingVsPdd;
