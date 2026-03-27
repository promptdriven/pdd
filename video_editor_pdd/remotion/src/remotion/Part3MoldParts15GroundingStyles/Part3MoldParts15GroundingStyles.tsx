import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Sequence,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  MATERIAL_STREAMS,
  OOP_CODE,
  FUNCTIONAL_CODE,
  OOP_COLOR,
  FUNC_COLOR,
  TEAM_COLOR,
  SUBTITLE_COLOR,
  STREAM_Y_CENTER,
  STREAM_SPACING,
  PANEL_LEFT_X,
  PANEL_RIGHT_X,
  PANEL_Y,
} from "./constants";
import MaterialStream from "./MaterialStream";
import CodePanel from "./CodePanel";
import {
  FlowArrow,
  DashedArrow,
  DatabaseIcon,
  TerminalNote,
} from "./DatabaseFeedback";

export const defaultPart3MoldParts15GroundingStylesProps = {};

export const Part3MoldParts15GroundingStyles: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Phase 1 opacity: fade out during crossfade (frames 120-150) ───
  const phase1Opacity = interpolate(frame, [120, 150], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ─── Phase 2 opacity: fade in during crossfade (frames 120-150) ───
  const phase2Opacity = interpolate(frame, [120, 150], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ─── Header "Grounding" fade-in ───
  const headerOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Header stays visible across all phases, just repositions
  const headerY = interpolate(frame, [120, 150], [120, 60], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ─── "Same prompt. Same tests." label ───
  const samePromptOpacity = interpolate(frame, [130, 155], [0, 1], {
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
      {/* ─── Header: "Grounding" ─── */}
      <div
        style={{
          position: "absolute",
          left: 0,
          right: 0,
          top: headerY,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 24,
          fontWeight: 700,
          color: TEAM_COLOR,
          opacity: headerOpacity,
          zIndex: 10,
        }}
      >
        Grounding
      </div>

      {/* ─── Phase 1: Material Streams (frames 0-180) ─── */}
      <div style={{ opacity: phase1Opacity }}>
        <Sequence from={0} durationInFrames={180}>
          {MATERIAL_STREAMS.map((stream, i) => (
            <MaterialStream
              key={stream.label}
              stream={stream}
              y={STREAM_Y_CENTER - STREAM_SPACING + i * STREAM_SPACING}
              delayFrames={30 + i * 20}
            />
          ))}
        </Sequence>
      </div>

      {/* ─── Phase 2: OOP vs Functional Split (frames 120+) ─── */}
      <div style={{ opacity: phase2Opacity }}>
        {/* "Same prompt. Same tests." */}
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            top: 220,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            color: SUBTITLE_COLOR,
            opacity: samePromptOpacity,
            zIndex: 5,
          }}
        >
          Same prompt. Same tests.
        </div>

        {/* Code panels use absolute frame references */}
        <Sequence from={120}>
          {/* OOP Panel — type-in starts at frame 180 absolute = 60 relative */}
          <CodePanel
            x={PANEL_LEFT_X}
            y={PANEL_Y}
            header="OOP Grounding"
            headerColor={OOP_COLOR}
            borderColor={OOP_COLOR}
            code={OOP_CODE}
            typeInStart={60}
            glowStart={240}
            glowBrightStart={undefined}
          />

          {/* Functional Panel — type-in starts at frame 270 absolute = 150 relative */}
          <CodePanel
            x={PANEL_RIGHT_X}
            y={PANEL_Y}
            header="Functional Grounding"
            headerColor={FUNC_COLOR}
            borderColor={FUNC_COLOR}
            code={FUNCTIONAL_CODE}
            typeInStart={150}
            glowStart={240}
            glowBrightStart={300}
          />
        </Sequence>

        {/* Walls indicator at edges during glow phase */}
        {frame >= 360 && (
          <WallIndicators
            startFrame={360}
          />
        )}
      </div>

      {/* ─── Phase 3: Database Feedback (frames 480+) ─── */}
      {frame >= 480 && (
        <>
          {/* Arrow from right panel to database */}
          <FlowArrow
            fromX={1100}
            fromY={630}
            toX={960}
            toY={790}
            startFrame={480}
            durationFrames={40}
            label="(prompt, code)"
          />

          {/* Database icon */}
          <DatabaseIcon fadeStartFrame={510} pulseStartFrame={520} />

          {/* Terminal note */}
          <TerminalNote startFrame={530} />
        </>
      )}

      {/* ─── Dashed arrow to Future Generations (frames 600+) ─── */}
      {frame >= 600 && (
        <DashedArrow
          fromX={960}
          fromY={880}
          toX={960}
          toY={960}
          startFrame={600}
          label="Future Generations"
        />
      )}
    </AbsoluteFill>
  );
};

// ─── Wall Indicators Sub-component ───
interface WallIndicatorsProps {
  startFrame: number;
}

const WallIndicators: React.FC<WallIndicatorsProps> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - startFrame);

  const opacity = interpolate(localFrame, [0, 15], [0, 0.75], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const wallStyle: React.CSSProperties = {
    position: "absolute",
    width: 3,
    backgroundColor: "#22C55E",
    opacity,
    borderRadius: 2,
  };

  return (
    <>
      {/* Left wall - left panel */}
      <div style={{ ...wallStyle, left: 164, top: 280, height: 350 }} />
      {/* Right wall - left panel */}
      <div style={{ ...wallStyle, left: 754, top: 280, height: 350 }} />
      {/* Left wall - right panel */}
      <div style={{ ...wallStyle, left: 804, top: 280, height: 350 }} />
      {/* Right wall - right panel */}
      <div style={{ ...wallStyle, left: 1394, top: 280, height: 350 }} />
    </>
  );
};

export default Part3MoldParts15GroundingStyles;
