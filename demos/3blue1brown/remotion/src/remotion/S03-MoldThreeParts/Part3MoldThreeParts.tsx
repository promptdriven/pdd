import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part3MoldThreePartsPropsType } from "./constants";
import { AddTestWall, defaultAddTestWallProps } from "../26-AddTestWall";
import { CodeOutputMoldGlows, defaultCodeOutputMoldGlowsProps } from "../38-CodeOutputMoldGlows";
import { CrossSectionIntro, defaultCrossSectionIntroProps } from "../21-CrossSectionIntro";
import { GroundingPanel, defaultGroundingPanelProps } from "../34-GroundingPanel";
import { LiquidInjection, defaultLiquidInjectionProps } from "../23-LiquidInjection";
import { PromptGovernsCode, defaultPromptGovernsCodeProps } from "../33-PromptGovernsCode";
import { PromptTextFlows, defaultPromptTextFlowsProps } from "../31-PromptTextFlows";
import { PromptVariations, defaultPromptVariationsProps } from "../32-PromptVariations";
import { RatchetTimelapse, defaultRatchetTimelapseProps } from "../28-RatchetTimelapse";
import { ThreeComponents, defaultThreeComponentsProps } from "../37-ThreeComponents";
import { TraditionalVsPdd, defaultTraditionalVsPddProps } from "../29-TraditionalVsPdd";
import { WallsIlluminate, defaultWallsIlluminateProps } from "../22-WallsIlluminate";

export const Part3MoldThreeParts: React.FC<Part3MoldThreePartsPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      {/* Narration audio */}
      <Audio src={staticFile("part3_mold_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: CrossSectionIntro - Intro: three components, three types of capital */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <CrossSectionIntro {...defaultCrossSectionIntroProps} />
        </Sequence>
      )}

      {/* Visual 1: WallsIlluminate - Tests are walls, constraint, boundary */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <WallsIlluminate {...defaultWallsIlluminateProps} />
        </Sequence>
      )}

      {/* Visual 2: LiquidInjection - Model sees tests, cannot violate walls */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <LiquidInjection {...defaultLiquidInjectionProps} />
        </Sequence>
      )}

      {/* Visual 3: AddTestWall - Bug: add wall, permanent, never again */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <AddTestWall {...defaultAddTestWallProps} />
        </Sequence>
      )}

      {/* Visual 4: RatchetTimelapse - Ratchet effect: tests accumulate */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <RatchetTimelapse {...defaultRatchetTimelapseProps} />
        </Sequence>
      )}

      {/* Visual 5: TraditionalVsPdd - Traditional vs PDD comparison */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START} durationInFrames={BEATS.VISUAL_05_END - BEATS.VISUAL_05_START}>
          <TraditionalVsPdd {...defaultTraditionalVsPddProps} />
        </Sequence>
      )}

      {/* Visual 6: PromptTextFlows - Second: prompt, specification of what you want */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START} durationInFrames={BEATS.VISUAL_06_END - BEATS.VISUAL_06_START}>
          <PromptTextFlows {...defaultPromptTextFlowsProps} />
        </Sequence>
      )}

      {/* Visual 7: PromptVariations - Implementation varies, behavior locked */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START} durationInFrames={BEATS.VISUAL_07_END - BEATS.VISUAL_07_START}>
          <PromptVariations {...defaultPromptVariationsProps} />
        </Sequence>
      )}

      {/* Visual 8: PromptGovernsCode - Good prompt smaller than code */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START} durationInFrames={BEATS.VISUAL_08_END - BEATS.VISUAL_08_START}>
          <PromptGovernsCode {...defaultPromptGovernsCodeProps} />
        </Sequence>
      )}

      {/* Visual 9: GroundingPanel - Third: grounding, style, patterns, conventions */}
      {activeVisual === 9 && (
        <Sequence from={BEATS.VISUAL_09_START} durationInFrames={BEATS.VISUAL_09_END - BEATS.VISUAL_09_START}>
          <GroundingPanel {...defaultGroundingPanelProps} />
        </Sequence>
      )}

      {/* Visual 10: ThreeComponents - Prompt+tests+grounding, complete specification */}
      {activeVisual === 10 && (
        <Sequence from={BEATS.VISUAL_10_START} durationInFrames={BEATS.VISUAL_10_END - BEATS.VISUAL_10_START}>
          <ThreeComponents {...defaultThreeComponentsProps} />
        </Sequence>
      )}

      {/* Visual 11: CodeOutputMoldGlows - Code is output, mold is what matters */}
      {activeVisual === 11 && (
        <Sequence from={BEATS.VISUAL_11_START} durationInFrames={BEATS.VISUAL_11_END - BEATS.VISUAL_11_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
