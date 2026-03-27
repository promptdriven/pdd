import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import {
  BACKGROUND_COLOR,
  TOTAL_FRAMES,
  WALLS_COLOR,
  WALLS_GLOW_RADIUS,
  WALLS_GLOW_OPACITY,
  WALLS_HIGHLIGHT_FRAME,
  NOZZLE_COLOR,
  NOZZLE_GLOW_RADIUS,
  NOZZLE_GLOW_OPACITY,
  NOZZLE_HIGHLIGHT_FRAME,
  CAVITY_COLOR,
  CAVITY_GLOW_RADIUS,
  CAVITY_GLOW_OPACITY,
  CAVITY_HIGHLIGHT_FRAME,
  LABEL_FADE_DELAY,
} from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { MoldOutline } from "./MoldOutline";
import { GlowRegion } from "./GlowRegion";
import { ConnectorLabel } from "./ConnectorLabel";

export const defaultPart3MoldParts02MoldCrossSectionProps = {};

export const Part3MoldParts02MoldCrossSection: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BACKGROUND_COLOR }}>
      {/* Blueprint grid — visible from frame 0 */}
      <BlueprintGrid />

      {/* Mold outline — draws in from frame 0-30 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <MoldOutline />
      </Sequence>

      {/* ── Region 1: Walls (Tests) ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <GlowRegion
          region="walls"
          color={WALLS_COLOR}
          glowRadius={WALLS_GLOW_RADIUS}
          glowOpacity={WALLS_GLOW_OPACITY}
          startFrame={WALLS_HIGHLIGHT_FRAME}
        />
      </Sequence>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ConnectorLabel
          text="TESTS"
          color={WALLS_COLOR}
          position="left"
          startFrame={WALLS_HIGHLIGHT_FRAME + LABEL_FADE_DELAY}
        />
      </Sequence>

      {/* ── Region 2: Nozzle (Prompt) ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <GlowRegion
          region="nozzle"
          color={NOZZLE_COLOR}
          glowRadius={NOZZLE_GLOW_RADIUS}
          glowOpacity={NOZZLE_GLOW_OPACITY}
          startFrame={NOZZLE_HIGHLIGHT_FRAME}
        />
      </Sequence>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ConnectorLabel
          text="PROMPT"
          color={NOZZLE_COLOR}
          position="top"
          startFrame={NOZZLE_HIGHLIGHT_FRAME + LABEL_FADE_DELAY}
        />
      </Sequence>

      {/* ── Region 3: Cavity (Grounding) ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <GlowRegion
          region="cavity"
          color={CAVITY_COLOR}
          glowRadius={CAVITY_GLOW_RADIUS}
          glowOpacity={CAVITY_GLOW_OPACITY}
          startFrame={CAVITY_HIGHLIGHT_FRAME}
        />
      </Sequence>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ConnectorLabel
          text="GROUNDING"
          color={CAVITY_COLOR}
          position="bottom"
          startFrame={CAVITY_HIGHLIGHT_FRAME + LABEL_FADE_DELAY}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldParts02MoldCrossSection;
