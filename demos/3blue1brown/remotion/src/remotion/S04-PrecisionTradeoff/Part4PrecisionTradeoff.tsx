import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part4PrecisionTradeoffPropsType } from "./constants";
import { BothGenerateFinal, defaultBothGenerateFinalProps } from "../45-BothGenerateFinal";
import { GraphAnimateCurve, defaultGraphAnimateCurveProps } from "../42-GraphAnimateCurve";
import { LongPrompt, defaultLongPromptProps } from "../43-LongPrompt";
import { MoldFlowFocus, defaultMoldFlowFocusProps } from "../40-MoldFlowFocus";
import { PrecisionGraph, defaultPrecisionGraphProps } from "../41-PrecisionGraph";
import { PrinterFocus, defaultPrinterFocusProps } from "../39-3DPrinterFocus";
import { ShortPromptTests, defaultShortPromptTestsProps } from "../44-ShortPromptTests";

export const Part4PrecisionTradeoff: React.FC<Part4PrecisionTradeoffPropsType> = () => {
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
      <Audio src={staticFile("part4_precision_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: Veo clip - Something subtle that changes how you think about  */}
      {activeVisual === 0 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("split_3d_vs_mold.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 1: PrinterFocus - 3D printing no mold, every point precise, specific */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <PrinterFocus {...defaultPrinterFocusProps} />
        </Sequence>
      )}

      {/* Visual 2: MoldFlowFocus - Injection molding precision comes from walls, flow */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <MoldFlowFocus {...defaultMoldFlowFocusProps} />
        </Sequence>
      )}

      {/* Visual 3: PrecisionGraph - This maps directly to PDD */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <PrecisionGraph {...defaultPrecisionGraphProps} />
        </Sequence>
      )}

      {/* Visual 4: LongPrompt - Few tests prompt specifies everything, edge cases, */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <LongPrompt {...defaultLongPromptProps} />
        </Sequence>
      )}

      {/* Visual 5: ShortPromptTests - Many tests prompt only needs intent, tests handle  */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START} durationInFrames={BEATS.VISUAL_05_END - BEATS.VISUAL_05_START}>
          <ShortPromptTests {...defaultShortPromptTestsProps} />
        </Sequence>
      )}

      {/* Visual 6: GraphAnimateCurve - Test accumulation not just catching bugs, simpler  */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START} durationInFrames={BEATS.VISUAL_06_END - BEATS.VISUAL_06_START}>
          <GraphAnimateCurve {...defaultGraphAnimateCurveProps} />
        </Sequence>
      )}

      {/* Visual 7: BothGenerateFinal - More walls less to specify, mold does precision wo */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START} durationInFrames={BEATS.VISUAL_07_END - BEATS.VISUAL_07_START}>
          <BothGenerateFinal {...defaultBothGenerateFinalProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
