import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Sequence,
} from "remotion";
import MaterialStream from "./MaterialStream";
import CodePanel from "./CodePanel";
import DatabaseFeedback from "./DatabaseFeedback";
import {
  BG_COLOR,
  TEAL,
  OOP_BLUE,
  FUNC_AMBER,
  SLATE,
  MATERIAL_STREAMS,
  STREAM_Y_START,
  STREAM_Y_SPACING,
  STREAM_WIDTH,
  STREAM_HEIGHT,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  PANEL_LEFT_X,
  PANEL_RIGHT_X,
  PANEL_Y,
  OOP_CODE,
  FUNCTIONAL_CODE,
  TOTAL_FRAMES,
  HEADER_FADE_END,
  PHASE2_START,
  CROSSFADE_END,
  OOP_TYPE_START,
  FUNC_TYPE_START,
  BOTH_GLOW_START,
  BOTH_GLOW_END,
  SELECT_GLOW_START,
  SELECT_GLOW_END,
  PHASE3_START,
  ARROW_ANIM_END,
  DB_APPEAR,
  DB_APPEAR_END,
  DASHED_ARROW_START,
  DASHED_ARROW_END,
} from "./constants";

export const defaultPart3MoldParts15GroundingStylesProps = {};

export const Part3MoldParts15GroundingStyles: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Phase 1: Header + Material Streams ---

  // "Grounding" header fade in (frame 0-30)
  const headerOpacity = interpolate(frame, [0, HEADER_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Header fades out as Phase 2 starts
  const headerFadeOut = interpolate(
    frame,
    [PHASE2_START, CROSSFADE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // --- Phase 2: "Same prompt. Same tests." label ---
  const samePromptOpacity = interpolate(
    frame,
    [PHASE2_START, PHASE2_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Phase 2 overall fade out for Phase 3 transition
  const phase2FadeOut = interpolate(
    frame,
    [PHASE3_START + 60, PHASE3_START + 90],
    [1, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Subtle gradient overlay
  const gradientOpacity = interpolate(frame, [0, 60], [0, 0.15], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Wall indicators during glow phase
  const wallOpacity = interpolate(
    frame,
    [BOTH_GLOW_START, BOTH_GLOW_START + 15],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Subtle radial gradient overlay */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: 1920,
          height: 1080,
          background: `radial-gradient(ellipse at 50% 40%, ${TEAL}08 0%, transparent 70%)`,
          opacity: gradientOpacity,
        }}
      />

      {/* Phase 1: "Grounding" Header */}
      <div
        style={{
          position: "absolute",
          top: 100,
          left: 0,
          width: 1920,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 24,
          fontWeight: 700,
          color: TEAL,
          opacity: headerOpacity * headerFadeOut,
        }}
      >
        Grounding
      </div>

      {/* Phase 1: Material Streams */}
      {MATERIAL_STREAMS.map((stream, i) => (
        <MaterialStream
          key={stream.label}
          color={stream.color}
          label={stream.label}
          y={STREAM_Y_START + i * STREAM_Y_SPACING}
          width={STREAM_WIDTH}
          height={STREAM_HEIGHT}
          streamStyle={stream.style}
          animStartFrame={30 + i * 20}
          fadeOutStart={PHASE2_START}
          fadeOutEnd={CROSSFADE_END}
        />
      ))}

      {/* Phase 2: "Same prompt. Same tests." label */}
      {frame >= PHASE2_START && (
        <div
          style={{
            position: "absolute",
            top: 220,
            left: 0,
            width: 1920,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            color: SLATE,
            opacity: samePromptOpacity * phase2FadeOut * 0.85,
          }}
        >
          Same prompt. Same tests.
        </div>
      )}

      {/* Phase 2: OOP Code Panel (left) */}
      {frame >= PHASE2_START && (
        <Sequence from={PHASE2_START} durationInFrames={TOTAL_FRAMES - PHASE2_START}>
          <div style={{ opacity: phase2FadeOut }}>
            <CodePanel
              x={PANEL_LEFT_X}
              y={PANEL_Y}
              width={PANEL_WIDTH}
              height={PANEL_HEIGHT}
              header="OOP Grounding"
              headerColor={OOP_BLUE}
              borderColor={OOP_BLUE}
              code={OOP_CODE}
              typeInStart={OOP_TYPE_START - PHASE2_START}
              glowStart={BOTH_GLOW_START - PHASE2_START}
              glowEnd={BOTH_GLOW_END - PHASE2_START}
              fadeInStart={0}
              fadeInEnd={30}
            />
          </div>
        </Sequence>
      )}

      {/* Phase 2: Functional Code Panel (right) */}
      {frame >= PHASE2_START && (
        <Sequence from={PHASE2_START} durationInFrames={TOTAL_FRAMES - PHASE2_START}>
          <div style={{ opacity: phase2FadeOut }}>
            <CodePanel
              x={PANEL_RIGHT_X}
              y={PANEL_Y}
              width={PANEL_WIDTH}
              height={PANEL_HEIGHT}
              header="Functional Grounding"
              headerColor={FUNC_AMBER}
              borderColor={FUNC_AMBER}
              code={FUNCTIONAL_CODE}
              typeInStart={FUNC_TYPE_START - PHASE2_START}
              glowStart={BOTH_GLOW_START - PHASE2_START}
              glowEnd={BOTH_GLOW_END - PHASE2_START}
              selectGlowStart={SELECT_GLOW_START - PHASE2_START}
              selectGlowEnd={SELECT_GLOW_END - PHASE2_START}
              isSelected
              fadeInStart={0}
              fadeInEnd={30}
            />
          </div>
        </Sequence>
      )}

      {/* Wall indicators (left and right edges) during glow phase */}
      {frame >= BOTH_GLOW_START && (
        <>
          {/* Left wall */}
          <div
            style={{
              position: "absolute",
              left: PANEL_LEFT_X - 20,
              top: PANEL_Y + 40,
              width: 4,
              height: PANEL_HEIGHT - 80,
              backgroundColor: "#22C55E",
              borderRadius: 2,
              opacity: wallOpacity * phase2FadeOut,
              boxShadow: "0 0 8px #22C55E40",
            }}
          />
          {/* Right wall (after right panel) */}
          <div
            style={{
              position: "absolute",
              left: PANEL_RIGHT_X + PANEL_WIDTH + 16,
              top: PANEL_Y + 40,
              width: 4,
              height: PANEL_HEIGHT - 80,
              backgroundColor: "#22C55E",
              borderRadius: 2,
              opacity: wallOpacity * phase2FadeOut,
              boxShadow: "0 0 8px #22C55E40",
            }}
          />
        </>
      )}

      {/* Phase 3: Database Feedback Loop */}
      {frame >= PHASE3_START && (
        <Sequence from={PHASE3_START} durationInFrames={TOTAL_FRAMES - PHASE3_START}>
          <DatabaseFeedback
            arrowStart={0}
            arrowEnd={ARROW_ANIM_END - PHASE3_START}
            dbAppearStart={DB_APPEAR - PHASE3_START}
            dbAppearEnd={DB_APPEAR_END - PHASE3_START}
            dashedArrowStart={DASHED_ARROW_START - PHASE3_START}
            dashedArrowEnd={DASHED_ARROW_END - PHASE3_START}
          />
        </Sequence>
      )}

      {/* Persistent "Grounding" label that returns in Phase 3 */}
      {frame >= PHASE3_START + 60 && (
        <div
          style={{
            position: "absolute",
            top: 100,
            left: 0,
            width: 1920,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 24,
            fontWeight: 700,
            color: TEAL,
            opacity: interpolate(
              frame,
              [PHASE3_START + 60, PHASE3_START + 80],
              [0, 0.8],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
          }}
        >
          Grounding
        </div>
      )}

      {/* Horizontal divider rule below header */}
      <div
        style={{
          position: "absolute",
          top: 150,
          left: 760,
          width: 400,
          height: 2,
          backgroundColor: TEAL,
          opacity: interpolate(frame, [10, 30], [0, 0.7], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          borderRadius: 1,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part3MoldParts15GroundingStyles;
