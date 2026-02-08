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
import { BugDiscovered, defaultBugDiscoveredProps } from "../25-BugDiscovered";
import { CodeOutputMoldGlows, defaultCodeOutputMoldGlowsProps } from "../38-CodeOutputMoldGlows";
import { CrossSectionIntro, defaultCrossSectionIntroProps } from "../21-CrossSectionIntro";
import { FocusSingleWall, defaultFocusSingleWallProps } from "../24-FocusSingleWall";
import { GroundingComparison, defaultGroundingComparisonProps } from "../35-GroundingComparison";
import { GroundingDatabase, defaultGroundingDatabaseProps } from "../36-GroundingDatabase";
import { GroundingPanel, defaultGroundingPanelProps } from "../34-GroundingPanel";
import { InjectionNozzle, defaultInjectionNozzleProps } from "../30-InjectionNozzle";
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
      
      {/* Visual 0: CrossSectionIntro - Get precise, mold has three components, three capi */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <CrossSectionIntro {...defaultCrossSectionIntroProps} />
        </Sequence>
      )}

      {/* Visual 1: WallsIlluminate - First tests, tests are walls, constraint, boundary */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <WallsIlluminate {...defaultWallsIlluminateProps} />
        </Sequence>
      )}

      {/* Visual 2: LiquidInjection - Walls matter, CodeRabbit 1.7x issues, DORA confirm */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <LiquidInjection {...defaultLiquidInjectionProps} />
        </Sequence>
      )}

      {/* Visual 3: FocusSingleWall - Walls not optional, model sees tests, cannot viola */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <FocusSingleWall {...defaultFocusSingleWallProps} />
        </Sequence>
      )}

      {/* Visual 4: BugDiscovered - Bug found, you don't patch the code */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <BugDiscovered {...defaultBugDiscoveredProps} />
        </Sequence>
      )}

      {/* Visual 5: AddTestWall - Add a wall, permanent, bug can never occur again */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <AddTestWall {...defaultAddTestWallProps} />
        </Sequence>
      )}

      {/* Visual 6: RatchetTimelapse - Ratchet effect, tests only accumulate, mold more p */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <RatchetTimelapse {...defaultRatchetTimelapseProps} />
        </Sequence>
      )}

      {/* Visual 7: TraditionalVsPdd - Traditional fix one place, PDD prevents bug everyw */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START}>
          <TraditionalVsPdd {...defaultTraditionalVsPddProps} />
        </Sequence>
      )}

      {/* Visual 8: TraditionalVsPdd - Synopsys uses SAT/SMT, PDD uses Z3, same class sol */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START}>
          <TraditionalVsPdd {...defaultTraditionalVsPddProps} />
        </Sequence>
      )}

      {/* Visual 9: TraditionalVsPdd - Z3 proves for all inputs, symbolic reasoning, same */}
      {activeVisual === 9 && (
        <Sequence from={BEATS.VISUAL_09_START}>
          <TraditionalVsPdd {...defaultTraditionalVsPddProps} />
        </Sequence>
      )}

      {/* Visual 10: InjectionNozzle - Second the prompt, specification of what you want */}
      {activeVisual === 10 && (
        <Sequence from={BEATS.VISUAL_10_START}>
          <InjectionNozzle {...defaultInjectionNozzleProps} />
        </Sequence>
      )}

      {/* Visual 11: PromptTextFlows - Prompt defines what and why, implementation can va */}
      {activeVisual === 11 && (
        <Sequence from={BEATS.VISUAL_11_START}>
          <PromptTextFlows {...defaultPromptTextFlowsProps} />
        </Sequence>
      )}

      {/* Visual 12: PromptVariations - Behavior locked, code flexible, contract fixed */}
      {activeVisual === 12 && (
        <Sequence from={BEATS.VISUAL_12_START}>
          <PromptVariations {...defaultPromptVariationsProps} />
        </Sequence>
      )}

      {/* Visual 13: PromptGovernsCode - Good prompt 1/5 to 1/10 size, what and why not how */}
      {activeVisual === 13 && (
        <Sequence from={BEATS.VISUAL_13_START}>
          <PromptGovernsCode {...defaultPromptGovernsCodeProps} />
        </Sequence>
      )}

      {/* Visual 14: PromptGovernsCode - Context window: prompts are NL, 30x more training  */}
      {activeVisual === 14 && (
        <Sequence from={BEATS.VISUAL_14_START}>
          <PromptGovernsCode {...defaultPromptGovernsCodeProps} />
        </Sequence>
      )}

      {/* Visual 15: GroundingPanel - Third grounding, determines properties of what fil */}
      {activeVisual === 15 && (
        <Sequence from={BEATS.VISUAL_15_START}>
          <GroundingPanel {...defaultGroundingPanelProps} />
        </Sequence>
      )}

      {/* Visual 16: GroundingComparison - Grounding learned from past generations */}
      {activeVisual === 16 && (
        <Sequence from={BEATS.VISUAL_16_START}>
          <GroundingComparison {...defaultGroundingComparisonProps} />
        </Sequence>
      )}

      {/* Visual 17: GroundingDatabase - Style patterns conventions, feeds back into system */}
      {activeVisual === 17 && (
        <Sequence from={BEATS.VISUAL_17_START}>
          <GroundingDatabase {...defaultGroundingDatabaseProps} />
        </Sequence>
      )}

      {/* Visual 18: ThreeComponents - Prompt+tests+grounding, complete specification */}
      {activeVisual === 18 && (
        <Sequence from={BEATS.VISUAL_18_START}>
          <ThreeComponents {...defaultThreeComponentsProps} />
        </Sequence>
      )}

      {/* Visual 19: CodeOutputMoldGlows - Code is output, mold is what matters */}
      {activeVisual === 19 && (
        <Sequence from={BEATS.VISUAL_19_START}>
          <CodeOutputMoldGlows {...defaultCodeOutputMoldGlowsProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
