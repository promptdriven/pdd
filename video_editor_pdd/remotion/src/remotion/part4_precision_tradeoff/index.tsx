import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part4PrecisionTradeoff01SectionTitleCard } from "../Part4PrecisionTradeoff01SectionTitleCard";
import { Part4PrecisionTradeoff02PrinterVsMoldSplit } from "../Part4PrecisionTradeoff02PrinterVsMoldSplit";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "../Part4PrecisionTradeoff03PrecisionTradeoffCurve";
import { Part4PrecisionTradeoff07EmbeddedCodeDocument } from "../Part4PrecisionTradeoff07EmbeddedCodeDocument";
import { Part4PrecisionTradeoff08PromptCodeSpectrum } from "../Part4PrecisionTradeoff08PromptCodeSpectrum";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part4PrecisionTradeoff01SectionTitleCard,
  "02_printer_vs_mold_split": Part4PrecisionTradeoff02PrinterVsMoldSplit,
  "03_precision_tradeoff_curve": Part4PrecisionTradeoff03PrecisionTradeoffCurve,
  "05_embedded_code_document": Part4PrecisionTradeoff07EmbeddedCodeDocument,
  "06_prompt_code_spectrum": Part4PrecisionTradeoff08PromptCodeSpectrum,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "02_printer_vs_mold_split": 600,
  "03_precision_tradeoff_curve": 450,
  "05_embedded_code_document": 480,
  "06_prompt_code_spectrum": 360,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "printer_nozzle", "color": "#60A5FA", "side": "left"}, {"shape": "coordinate_grid", "color": "#60A5FA", "side": "left"}, {"shape": "mold_outline", "color": "#D9944A", "side": "right"}, {"shape": "flow_curves", "color": "#A78BFA", "side": "right"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "3D PRINTING", "headerColor": "#60A5FA", "elements": [{"type": "coordinate_grid", "spacing": 40, "color": "#60A5FA"}, {"type": "printer_nozzle", "layers": 3, "pointsPerLayer": 8}, {"type": "coordinate_labels", "font": "JetBrains Mono", "size": 8}], "caption": "Every point must be specified", "thematicRole": "explicit_precision"}, "rightPanel": {"header": "INJECTION MOLDING", "headerColor": "#D9944A", "elements": [{"type": "mold_walls", "strokeWidth": 4, "color": "#D9944A"}, {"type": "liquid_flow", "color": "#A78BFA"}, {"type": "wall_glow_on_impact", "glowColor": "#D9944A"}], "caption": "Walls do the precision work", "thematicRole": "emergent_precision"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]}, "overlayConfig": null, "renderMode": "component"},
  "03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartId": "precision_tradeoff_curve", "axes": {"x": {"label": "Number of Tests", "range": [0, 50], "ticks": ["0", "10", "20", "30", "40", "50+"]}, "y": {"label": "Required Prompt Precision", "range": ["Low", "High"], "ticks": ["Low", "Medium", "High"]}}, "curve": {"type": "inverse_hyperbolic", "color": "#2DD4BF", "strokeWidth": 3}, "annotations": {"left": {"label": "parser_v1.prompt — 50 lines", "description": "Dense prompt, few tests", "position": "high_precision"}, "right": {"label": "parser_v2.prompt — 10 lines", "description": "Minimal prompt, 47 tests", "testCount": 47, "position": "low_precision"}}, "introText": "This maps directly to PDD.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
  "04_code_generation_comparison": {"specBaseName": "04_code_generation_comparison", "dataPoints": {"type": "animated_diagram", "diagramId": "code_generation_comparison", "scenarios": [{"side": "left", "promptFile": "parser_v1.prompt", "promptLines": 50, "testCount": 5, "result": "correct", "emphasis": "prompt_heavy"}, {"side": "right", "promptFile": "parser_v2.prompt", "promptLines": 10, "testCount": 47, "result": "correct", "emphasis": "test_heavy", "preferred": true}], "takeaway": {"line1": "More tests, less prompt.", "line2": "The walls do the precision work."}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_007", "part4_precision_tradeoff_008"]}, "overlayConfig": null, "renderMode": "component"},
  "05_embedded_code_document": {"specBaseName": "05_embedded_code_document", "dataPoints": {"type": "animated_diagram", "diagramId": "embedded_code_document", "document": {"naturalLanguageBlocks": 5, "embeddedCodeBlocks": 1, "totalLines": 18, "codeLines": 4, "nlLines": 14}, "codeBlock": {"language": "python", "function": "hash_id", "purpose": "Performance-critical hashing implementation"}, "annotations": {"nlLabel": "Architecture, intent, constraints → natural language", "codeLabel": "Algorithm choice, performance-critical logic → code"}, "bottomLabel": "The boundary between prompt and code is fluid.", "colors": {"naturalLanguage": "#2DD4BF", "code": "#60A5FA", "background": "#0A0F1A"}, "narrationSegments": ["part4_precision_tradeoff_009"]}, "overlayConfig": null, "renderMode": "component"},
  "06_prompt_code_spectrum": {"specBaseName": "06_prompt_code_spectrum", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_code_spectrum", "spectrum": {"leftEnd": {"label": "Pure natural language", "color": "#2DD4BF"}, "rightEnd": {"label": "Pure code", "color": "#475569"}, "width": 1520}, "slider": {"position": 0.25, "label": "Most work lives here"}, "notches": [{"position": 0.6, "label": "Algorithm choice"}, {"position": 0.75, "label": "Bit-level ops"}, {"position": 0.9, "label": "Performance loops"}], "annotations": [{"position": 0.15, "label": "Architecture", "color": "#2DD4BF"}, {"position": 0.25, "label": "Intent", "color": "#2DD4BF"}, {"position": 0.35, "label": "Constraints / Edge cases", "color": "#2DD4BF"}, {"position": 0.65, "label": "Algorithm choice", "color": "#94A3B8"}, {"position": 0.85, "label": "Bit-level ops / Perf. loops", "color": "#64748B"}], "bottomLabel": {"line1": "Stay in prompt space as long as possible.", "line2": "Dip into code when you must."}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_010"]}, "overlayConfig": null, "renderMode": "component"},
};

export const Part4PrecisionTradeoffSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 111.84;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

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
