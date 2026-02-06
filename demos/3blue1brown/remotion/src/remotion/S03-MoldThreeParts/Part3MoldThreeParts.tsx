import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part3MoldThreePartsPropsType } from "./constants";
import { GroundingPanel, defaultGroundingPanelProps } from "../34-GroundingPanel";
import { LongPrompt, defaultLongPromptProps } from "../43-LongPrompt";
import { PrecisionGraph, defaultPrecisionGraphProps } from "../41-PrecisionGraph";
import { PromptGovernsCode, defaultPromptGovernsCodeProps } from "../33-PromptGovernsCode";
import { PromptTextFlows, defaultPromptTextFlowsProps } from "../31-PromptTextFlows";
import { PromptVariations, defaultPromptVariationsProps } from "../32-PromptVariations";
import { ShortPromptTests, defaultShortPromptTestsProps } from "../44-ShortPromptTests";
import { ThreeComponents, defaultThreeComponentsProps } from "../37-ThreeComponents";

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
      
      {/* Visual 0: PromptTextFlows - Prompt capital: specification → doesn't define wal */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <PromptTextFlows {...defaultPromptTextFlowsProps} />
        </Sequence>
      )}

      {/* Visual 1: PromptVariations - Subtle: implementation varies → behavior locked →  */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <PromptVariations {...defaultPromptVariationsProps} />
        </Sequence>
      )}

      {/* Visual 2: PromptGovernsCode - Compression: smaller than code → what and why not  */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <PromptGovernsCode {...defaultPromptGovernsCodeProps} />
        </Sequence>
      )}

      {/* Visual 3: GroundingPanel - Grounding: properties → learned → style → conventi */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <GroundingPanel {...defaultGroundingPanelProps} />
        </Sequence>
      )}

      {/* Visual 4: ThreeComponents - Integration: prompt+tests+grounding → complete spe */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <ThreeComponents {...defaultThreeComponentsProps} />
        </Sequence>
      )}

      {/* Visual 5: Veo clip - Precision tradeoff: 3D printing → no mold → every  */}
      {activeVisual === 5 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("split_3d_vs_mold.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 6: PrecisionGraph - PDD mapping: few tests → specify everything → many */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START} durationInFrames={BEATS.VISUAL_06_END - BEATS.VISUAL_06_START}>
          <PrecisionGraph {...defaultPrecisionGraphProps} />
        </Sequence>
      )}

      {/* Visual 7: LongPrompt - Compound returns: patch → local returns → one bug  */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START} durationInFrames={BEATS.VISUAL_07_END - BEATS.VISUAL_07_START}>
          <LongPrompt {...defaultLongPromptProps} />
        </Sequence>
      )}

      {/* Visual 8: ShortPromptTests - PDD returns: test today → constrains tomorrow → pe */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START} durationInFrames={BEATS.VISUAL_08_END - BEATS.VISUAL_08_START}>
          <ShortPromptTests {...defaultShortPromptTestsProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
