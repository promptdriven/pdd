import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { Part4PrecisionTradeoff01SectionTitleCard } from "../Part4PrecisionTradeoff01SectionTitleCard";
import { Part4PrecisionTradeoff02PrinterVsMoldSplit } from "../Part4PrecisionTradeoff02PrinterVsMoldSplit";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "../Part4PrecisionTradeoff03PrecisionTradeoffCurve";
import { Part4PrecisionTradeoff04PromptComparisonSplit } from "../Part4PrecisionTradeoff04PromptComparisonSplit";
import { Part4PrecisionTradeoff05TestAccumulationInsight } from "../Part4PrecisionTradeoff05TestAccumulationInsight";
import { Part4PrecisionTradeoff06TakeawayCallout } from "../Part4PrecisionTradeoff06TakeawayCallout";
import { Part4PrecisionTradeoff07EmbeddedCodeDocument } from "../Part4PrecisionTradeoff07EmbeddedCodeDocument";
import { Part4PrecisionTradeoff08PromptCodeSpectrum } from "../Part4PrecisionTradeoff08PromptCodeSpectrum";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part4PrecisionTradeoff01SectionTitleCard,
  "02_printer_vs_mold_split": Part4PrecisionTradeoff02PrinterVsMoldSplit,
  "03_precision_tradeoff_curve": Part4PrecisionTradeoff03PrecisionTradeoffCurve,
  "04_prompt_comparison_split": Part4PrecisionTradeoff04PromptComparisonSplit,
  "05_test_accumulation_insight": Part4PrecisionTradeoff05TestAccumulationInsight,
  "06_takeaway_callout": Part4PrecisionTradeoff06TakeawayCallout,
  "07_embedded_code_document": Part4PrecisionTradeoff07EmbeddedCodeDocument,
  "08_prompt_code_spectrum": Part4PrecisionTradeoff08PromptCodeSpectrum,
};

const VISUAL_DURATIONS: Record<string, number> = {
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "08_prompt_code_spectrum": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": null, "overlayConfig": null},
  "03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": null, "overlayConfig": null},
  "04_prompt_comparison_split": {"specBaseName": "04_prompt_comparison_split", "dataPoints": null, "overlayConfig": null},
  "05_test_accumulation_insight": {"specBaseName": "05_test_accumulation_insight", "dataPoints": null, "overlayConfig": null},
  "06_takeaway_callout": {"specBaseName": "06_takeaway_callout", "dataPoints": null, "overlayConfig": null},
  "07_embedded_code_document": {"specBaseName": "07_embedded_code_document", "dataPoints": null, "overlayConfig": null},
  "08_prompt_code_spectrum": {"specBaseName": "08_prompt_code_spectrum", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
};

export const Part4PrecisionTradeoffSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 112.085333;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part4_precision_tradeoff/narration.wav")} />
      {activeVisuals.map((visual) => {
        const VisualComponent = COMPONENT_MAP[visual.id] ?? null;
        const visualDuration = Math.max(1, visual.end - visual.start);
        const intrinsicDurationInFrames = VISUAL_DURATIONS[visual.id] ?? visualDuration;
        const visualMedia = VISUAL_MEDIA[visual.id] ?? null;
        const visualOverlayConfig = VISUAL_OVERLAYS[visual.id] ?? null;
        const visualContract = VISUAL_CONTRACTS[visual.id] ?? null;

        return (
          <Sequence key={visual.id} from={visual.start} durationInFrames={visualDuration}>
            {VisualComponent ? (
              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
                <VisualContractProvider contract={visualContract}>
                  <VisualMediaProvider media={visualMedia}>
                    <VisualComponent />
                  </VisualMediaProvider>
                </VisualContractProvider>
              </SlotScaledSequence>
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part4PrecisionTradeoffSection;
