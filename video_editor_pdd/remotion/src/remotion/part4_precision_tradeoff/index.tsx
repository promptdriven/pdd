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
  "01_section_title_card": 120,
  "02_printer_vs_mold_split": 600,
  "03_precision_tradeoff_curve": 450,
  "04_prompt_comparison_split": 420,
  "05_test_accumulation_insight": 300,
  "06_takeaway_callout": 180,
  "07_embedded_code_document": 480,
  "08_prompt_code_spectrum": 360,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "08_prompt_code_spectrum": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "dot_matrix", "color": "#94A3B8", "component": "coordinate_precision"}, {"shape": "mold_outline", "color": "#D9944A", "component": "wall_precision"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "3D PRINTING", "concept": "Specify every point — exhaustive precision", "grid": {"rows": 20, "cols": 20, "totalPoints": 400}, "background": "#0F172A", "accentColor": "#94A3B8"}, "rightPanel": {"label": "INJECTION MOLDING", "concept": "Define walls — constraint-based precision", "wallCount": 4, "background": "#0A0F1A", "accentColor": "#D9944A"}, "callout": "Precision through specification vs. precision through constraint", "backgroundColor": "#000000", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]}, "overlayConfig": null, "renderMode": "component"},
  "03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartType": "inverse_curve", "title": "THE PRECISION TRADEOFF", "xAxis": {"label": "Number of Tests", "range": [0, 50], "ticks": [0, 10, 20, 30, 40, 50]}, "yAxis": {"label": "Required Prompt Precision", "range": ["Low", "High"]}, "curve": {"type": "inverse_hyperbola", "color": "#4A90D9", "equation": "y = 180 + 580 * (1 / (1 + 0.08 * x))"}, "zones": [{"label": "Detailed prompt required", "range": [0, 10], "color": "#D9944A"}, {"label": "Intent is enough", "range": [35, 50], "color": "#5AAA6E"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
  "04_prompt_comparison_split": {"specBaseName": "04_prompt_comparison_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "FEW TESTS", "filename": "parser_v1.prompt", "lineCount": 50, "concept": "Prompt must specify everything — edge cases, errors, constraints", "background": "#0F172A", "accentColor": "#D9944A"}, "rightPanel": {"label": "MANY TESTS", "filename": "parser_v2.prompt", "lineCount": 10, "testCount": 47, "concept": "Prompt only needs intent — tests carry the precision", "background": "#0A0F1A", "accentColor": "#5AAA6E", "terminalCommand": "pdd test parser"}, "callout": "Same output. Different specification strategy.", "backgroundColor": "#000000", "narrationSegments": ["part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
  "05_test_accumulation_insight": {"specBaseName": "05_test_accumulation_insight", "dataPoints": {"type": "stage_progression", "title": "TEST ACCUMULATION OVER TIME", "stages": [{"label": "DAY 1", "promptLines": 30, "wallCount": 3, "description": "Prompt carries the weight", "color": "#D9944A"}, {"label": "MONTH 1", "promptLines": 15, "wallCount": 15, "description": "Tests take over", "color": "#94A3B8"}, {"label": "MONTH 6", "promptLines": 5, "wallCount": 40, "description": "Intent is enough", "color": "#5AAA6E"}], "callout": "Not just about catching bugs. It's about making prompts simpler and regeneration safer over time.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_007"]}, "overlayConfig": null, "renderMode": "component"},
  "06_takeaway_callout": {"specBaseName": "06_takeaway_callout", "dataPoints": {"type": "callout_text", "lines": [{"text": "The more walls you have,", "emphasis": {"word": "walls", "color": "#D9944A"}}, {"text": "the less you need to specify.", "emphasis": {"word": "less", "scale": 1.1}}, {"text": "The mold does the precision work.", "emphasis": {"word": "mold", "color": "#D9944A", "glow": true}}], "miniAnimation": {"promptLines": {"from": 20, "to": 5}, "wallCount": {"from": 3, "to": 15}}, "backgroundColor": "#080C14", "narrationSegments": ["part4_precision_tradeoff_008"]}, "overlayConfig": null, "renderMode": "component"},
  "07_embedded_code_document": {"specBaseName": "07_embedded_code_document", "dataPoints": {"type": "document_visualization", "filename": "ad_latency_optimizer.prompt", "sections": [{"type": "natural_language", "lines": "1-8", "label": "Intent (natural language)", "color": "#4A90D9"}, {"type": "embedded_code", "lines": "9-18", "label": "Critical algorithm (code)", "color": "#94A3B8", "language": "python"}, {"type": "natural_language", "lines": "19-24", "label": "Constraints (natural language)", "color": "#4A90D9"}], "annotation": "Stay in prompt space as long as possible. Dip into code when you must.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_009"]}, "overlayConfig": null, "renderMode": "component"},
  "08_prompt_code_spectrum": {"specBaseName": "08_prompt_code_spectrum", "dataPoints": {"type": "spectrum_visualization", "title": "Prompt-Code Spectrum", "spectrum": {"leftLabel": "Pure natural language", "leftColor": "#4A90D9", "rightLabel": "Pure code", "rightColor": "#94A3B8", "sliderPosition": 0.25}, "regions": [{"label": "Architecture, intent, constraints", "position": 0.12, "color": "#4A90D9"}, {"label": "Edge cases, error handling", "position": 0.35, "color": "#6B8AB5"}, {"label": "Algorithm choice, tuning", "position": 0.66, "color": "#8094A8"}, {"label": "Bit-level ops, inner loops", "position": 0.91, "color": "#94A3B8"}], "codeDipNotches": [0.7, 0.83, 0.95], "keyQuestion": "The question isn't prompts OR code. It's how far into prompt space can you stay?", "answer": "For most of the specification — further than you'd think.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_010"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
};

export const Part4PrecisionTradeoffSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 111.84;
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
                  <VisualMediaProvider media={visualContract?.renderMode === "component" ? null : visualMedia}>
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
