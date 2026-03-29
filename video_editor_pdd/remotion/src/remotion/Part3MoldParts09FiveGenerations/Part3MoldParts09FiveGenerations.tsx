import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import { CodePanel } from "./CodePanel";
import { StatusOverlay } from "./StatusOverlay";
import {
  BG_COLOR,
  LABEL_TEXT_COLOR,
  GENERATIONS,
  PANEL_START_X,
  PANEL_W,
  PANEL_GAP,
  PANEL_Y,
  PANEL_FIRST_FRAME,
  PANEL_STAGGER,
  LABEL_Y,
  LABEL_FRAME,
  LABEL_FADE_DURATION,
  BOTTOM_LABEL,
} from "./constants";

// ── Default props (required by export contract) ─────────────────────────────
export const defaultPart3MoldParts09FiveGenerationsProps = {};

// ── Main component ──────────────────────────────────────────────────────────
export const Part3MoldParts09FiveGenerations: React.FC = () => {
  const frame = useCurrentFrame();

  // Label fade-in
  const labelOpacity = interpolate(
    frame,
    [LABEL_FRAME, LABEL_FRAME + LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Subtle title at top
  const titleOpacity = interpolate(frame, [0, 20], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Top section title */}
      <div
        style={{
          position: "absolute",
          top: 60,
          width: "100%",
          textAlign: "center",
          opacity: titleOpacity,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 500,
            color: "#64748B",
            letterSpacing: "0.12em",
            textTransform: "uppercase",
          }}
        >
          Multi-Generation Selection
        </span>
      </div>

      {/* ── Five code panels ── */}
      {GENERATIONS.map((gen, i) => {
        const panelX = PANEL_START_X + i * (PANEL_W + PANEL_GAP);
        const appearFrame = PANEL_FIRST_FRAME + i * PANEL_STAGGER;

        return (
          <React.Fragment key={i}>
            <CodePanel
              gen={gen}
              index={i}
              x={panelX}
              y={PANEL_Y}
              appearFrame={appearFrame}
            />
            <StatusOverlay
              panelIndex={i}
              status={gen.status}
              x={panelX}
              y={PANEL_Y}
            />
          </React.Fragment>
        );
      })}

      {/* ── Bottom label ── */}
      <div
        style={{
          position: "absolute",
          top: LABEL_Y,
          width: "100%",
          textAlign: "center",
          opacity: labelOpacity,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 20,
            fontWeight: 600,
            color: LABEL_TEXT_COLOR,
            lineHeight: 1.4,
          }}
        >
          {BOTTOM_LABEL}
        </span>
      </div>

      {/* ── Subtle divider line above label ── */}
      <div
        style={{
          position: "absolute",
          top: LABEL_Y - 24,
          left: "50%",
          transform: "translateX(-50%)",
          width: 200,
          height: 2,
          backgroundColor: "#334155",
          opacity: interpolate(
            frame,
            [LABEL_FRAME, LABEL_FRAME + LABEL_FADE_DURATION],
            [0, 0.7],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
          borderRadius: 1,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part3MoldParts09FiveGenerations;
