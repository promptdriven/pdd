import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import MoldCrossSection from "./MoldCrossSection";
import AnnotationPanel from "./AnnotationPanel";
import ConnectorLines from "./ConnectorLines";

// ── Timing constants ───────────────────────────────────────
// Panel slide in: 0..30
const SLIDE_IN_START = 0;
const SLIDE_IN_END = 30;

// Word-by-word text: 30..90  (handled inside AnnotationPanel)
// Emphasis: 90..110           (handled inside AnnotationPanel)
// Italic: 150..170            (handled inside AnnotationPanel)
// Badges: 210..230            (handled inside AnnotationPanel)

// Connectors + wall transition: 270..360
const CONNECTORS_START = 270;
const CONNECTORS_END = 300;
const WALL_TRANSITION_START = 270;
const WALL_TRANSITION_END = 360;

// Panel slide out: 720..750
const SLIDE_OUT_START = 720;
const SLIDE_OUT_END = 750;

// Mold restore: 720..780
const MOLD_DIM_END = 30;         // mold dims over first 30 frames
const MOLD_RESTORE_START = 720;
const MOLD_RESTORE_END = 780;

// ── Proven wall connector targets ──────────────────────────
const CONNECTOR_TARGETS = [
  { wallX: 350, wallY: 500 },  // wall index 1
  { wallX: 650, wallY: 500 },  // wall index 3
];

// ── Props ──────────────────────────────────────────────────
export const defaultPart3MoldParts10Z3FormalProofProps = {};

export const Part3MoldParts10Z3FormalProof: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Mold opacity ─────────────────────────────────────────
  // Dims to 0.3 over first 30 frames, restores 720..780
  const moldDimProgress = interpolate(frame, [0, MOLD_DIM_END], [1, 0.3], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });
  const moldRestoreProgress = interpolate(
    frame,
    [MOLD_RESTORE_START, MOLD_RESTORE_END],
    [0.3, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const moldOpacity = frame < MOLD_RESTORE_START ? moldDimProgress : moldRestoreProgress;

  // ── Panel slide-in ───────────────────────────────────────
  const slideInProgress = interpolate(
    frame,
    [SLIDE_IN_START, SLIDE_IN_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Panel slide-out ──────────────────────────────────────
  const slideOutProgress = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  // ── Connector draw progress ──────────────────────────────
  const connectorDraw = interpolate(
    frame,
    [CONNECTORS_START, CONNECTORS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Wall transition (blue → purple) ──────────────────────
  const wallProvenProgress = interpolate(
    frame,
    [WALL_TRANSITION_START, WALL_TRANSITION_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    }
  );

  // After slide-out, walls retain purple
  const retainPurple = frame >= SLIDE_OUT_START;

  // Should connectors be visible?
  const connectorsVisible = frame >= CONNECTORS_START && frame < SLIDE_OUT_END;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A0F1A",
        overflow: "hidden",
      }}
    >
      {/* Dimmed mold cross-section on left side */}
      <MoldCrossSection
        moldOpacity={moldOpacity}
        provenProgress={wallProvenProgress}
        retainPurple={retainPurple}
      />

      {/* Annotation panel (slides in from right) */}
      <AnnotationPanel
        slideInProgress={slideInProgress}
        slideOutProgress={slideOutProgress}
        localFrame={frame}
      />

      {/* Connector lines from panel to proven walls */}
      {connectorsVisible && (
        <ConnectorLines
          drawProgress={connectorDraw}
          originX={1000}
          originY={490}
          targets={CONNECTOR_TARGETS}
        />
      )}
    </AbsoluteFill>
  );
};

export default Part3MoldParts10Z3FormalProof;
