import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "../Part4PrecisionTradeoff03PrecisionTradeoffCurve";
import { Part4PrecisionTradeoff07EmbeddedCodeDocument } from "../Part4PrecisionTradeoff07EmbeddedCodeDocument";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "03_precision_tradeoff_curve": Part4PrecisionTradeoff03PrecisionTradeoffCurve,
  "06_embedded_code_document": Part4PrecisionTradeoff07EmbeddedCodeDocument,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "03_precision_tradeoff_curve": 450,
  "06_embedded_code_document": 480,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "04_prompt_detail_comparison": { leftSrc: "veo/developer_prompt_shift.mp4", defaultSrc: "veo/developer_prompt_shift.mp4", rightSrc: "veo/developer_prompt_shift.mp4", backgroundSrc: "veo/developer_prompt_shift.mp4", outputSrc: "veo/developer_prompt_shift.mp4", baseSrc: "veo/developer_prompt_shift.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 39 },
  "03_precision_tradeoff_curve": { fadeInFrames: 60 },
  "07_prompt_code_spectrum": { fadeInFrames: 30 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "dot_matrix_grid", "color": "#F59E0B", "role": "3d_printing_precision"}, {"shape": "mold_flow_walls", "color": "#2DD4BF", "role": "injection_molding_walls"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 39}, "renderMode": "component"},
  "02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "3D PRINTING", "headerColor": "#F59E0B", "content": "coordinate_grid_with_nozzle_path", "pointCount": 2847, "caption": "Every point must be defined.", "thematicRole": "exhaustive_specification"}, "rightPanel": {"header": "INJECTION MOLDING", "headerColor": "#2DD4BF", "content": "mold_walls_with_liquid_flow", "wallCount": 6, "liquidCurves": 10, "caption": "The walls do the precision work.", "thematicRole": "wall_based_precision"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003", "part4_precision_tradeoff_004"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartType": "inverse_curve", "axes": {"x": {"label": "Number of Tests", "range": [0, 100], "unit": "count"}, "y": {"label": "Required Prompt Precision", "range": [0, 100], "unit": "percent"}}, "curve": {"function": "y = 200 + 600 * exp(-0.04 * x)", "color": "#A78BFA", "interpretation": "inverse_relationship"}, "regions": [{"position": "above_curve", "label": "Prompt does the work", "color": "#F59E0B"}, {"position": "below_curve", "label": "Tests do the work", "color": "#2DD4BF"}], "callouts": [{"position": "left", "label": "Few tests → detailed prompt", "promptLines": 5}, {"position": "right", "label": "Many tests → minimal prompt", "promptLines": 2, "testCount": 6}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "04_prompt_detail_comparison": {"specBaseName": "04_prompt_detail_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "DETAILED PROMPT", "headerColor": "#F59E0B", "filename": "parser_v1.prompt", "lineCount": 50, "testCount": 3, "thematicRole": "verbose_specification"}, "rightPanel": {"header": "MINIMAL PROMPT", "headerColor": "#2DD4BF", "filename": "parser_v2.prompt", "lineCount": 10, "testCount": 47, "thematicRole": "test_driven_specification"}, "outcome": {"both_correct": true, "promptReduction": "5×", "summary": "Same result. 5× less prompt."}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_007", "part4_precision_tradeoff_008"]}, "mediaAliases": {"leftSrc": "veo/developer_prompt_shift.mp4", "defaultSrc": "veo/developer_prompt_shift.mp4", "rightSrc": "veo/developer_prompt_shift.mp4", "backgroundSrc": "veo/developer_prompt_shift.mp4", "outputSrc": "veo/developer_prompt_shift.mp4", "baseSrc": "veo/developer_prompt_shift.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "05_walls_precision_callout": {"specBaseName": "05_walls_precision_callout", "dataPoints": {"type": "kinetic_typography", "primaryText": ["More tests,", "less prompt."], "secondaryText": "The walls do the precision work.", "visualElements": {"testWalls": {"count": 8, "color": "#2DD4BF"}, "promptDocument": {"initialLines": 12, "finalLines": 3, "color": "#F59E0B"}, "checkmark": {"color": "#22C55E"}}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_embedded_code_document": {"specBaseName": "06_embedded_code_document", "dataPoints": {"type": "document_visualization", "document": {"width": 720, "height": 700, "sections": [{"type": "natural_language", "lines": 8, "topic": "parser_requirements"}, {"type": "natural_language", "lines": 6, "topic": "edge_cases"}, {"type": "code_block", "lines": 5, "language": "python", "topic": "token_validation"}, {"type": "natural_language", "lines": 6, "topic": "error_handling"}]}, "annotations": [{"target": "natural_language", "label": "Architecture, intent, constraints", "color": "#A78BFA"}, {"target": "code_block", "label": "Precision where it matters", "color": "#2DD4BF"}], "labels": ["The boundary between prompt and code is fluid.", "Stay in prompt space. Dip into code when you must."], "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_prompt_code_spectrum": {"specBaseName": "07_prompt_code_spectrum", "dataPoints": {"type": "spectrum_visualization", "spectrum": {"left": {"label": "Pure natural language", "color": "#4A90D9"}, "right": {"label": "Pure code", "color": "#475569"}, "width": 1520}, "notches": [{"position": 0.1, "label": "Architecture", "color": "#4A90D9"}, {"position": 0.2, "label": "Intent & constraints", "color": "#4A90D9"}, {"position": 0.3, "label": "Edge cases", "color": "#6B7DB0"}, {"position": 0.6, "label": "Critical algorithms", "color": "#8B9AB0"}, {"position": 0.8, "label": "Performance paths", "color": "#475569"}], "slider": {"restPosition": 0.25, "dipPosition": 0.6, "label": "PDD sweet spot"}, "bottomLabel": "Stay in prompt space as long as possible. Dip into code when you must.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_010"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "generated-media"},
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
            ) : visualContract?.renderMode === "component" ? (
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                  <GeneratedContractVisual />
                </VisualMediaProvider>
              </VisualContractProvider>
            ) : visualMedia?.defaultSrc ? (
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                {visualOverlayConfig || visualMedia?.leftSrc || visualMedia?.rightSrc ? (
                  <GeneratedMediaVisual config={visualOverlayConfig} />
                ) : (
                  <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
                )}
                </VisualMediaProvider>
              </VisualContractProvider>
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part4PrecisionTradeoffSection;
