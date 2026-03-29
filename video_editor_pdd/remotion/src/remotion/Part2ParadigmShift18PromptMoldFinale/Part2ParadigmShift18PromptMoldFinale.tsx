import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { PulsingDocument } from "./PulsingDocument";
import { TestWalls } from "./TestWalls";
import { CodeFlow } from "./CodeFlow";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  WALLS_START,
  CODE_FLOW_START,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  REGEN_INTERVAL,
  DISSOLVE_DURATION,
  WALL_FLASH_DURATION,
} from "./constants";

export const defaultPart2ParadigmShift18PromptMoldFinaleProps = {};

export const Part2ParadigmShift18PromptMoldFinale: React.FC = () => {
  const frame = useCurrentFrame();

  // Final fade to black (frames 300-360)
  const fadeToBlack = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // Determine if walls should flash (during regeneration dissolve phase)
  const codeFrame = frame - CODE_FLOW_START;
  const isCodeActive = codeFrame >= 0;
  let wallFlashActive = false;
  if (isCodeActive) {
    const genIndex = Math.floor(codeFrame / REGEN_INTERVAL);
    const localFrame = codeFrame - genIndex * REGEN_INTERVAL;
    // Flash on regeneration transitions (gen > 0, during dissolve)
    if (genIndex > 0 && localFrame < DISSOLVE_DURATION + WALL_FLASH_DURATION) {
      wallFlashActive = true;
    }
  }

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Subtle radial gradient background */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          background:
            "radial-gradient(ellipse 80% 60% at 50% 45%, rgba(217,148,74,0.04), transparent 70%)",
          pointerEvents: "none",
        }}
      />

      {/* Prompt document — visible from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <PulsingDocument />
      </Sequence>

      {/* Test walls — draw starting at frame 45 */}
      <Sequence from={WALLS_START} durationInFrames={TOTAL_FRAMES - WALLS_START}>
        <TestWalls flashActive={wallFlashActive} />
      </Sequence>

      {/* Code flow with regeneration — starts at frame 90 */}
      <Sequence
        from={CODE_FLOW_START}
        durationInFrames={TOTAL_FRAMES - CODE_FLOW_START}
      >
        <CodeFlow />
      </Sequence>

      {/* Fade to black overlay */}
      {fadeToBlack > 0 && (
        <AbsoluteFill
          style={{
            backgroundColor: "#000000",
            opacity: fadeToBlack,
          }}
        />
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift18PromptMoldFinale;
