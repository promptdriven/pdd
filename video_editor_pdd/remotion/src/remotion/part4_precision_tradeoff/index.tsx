import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part4PrecisionTradeoff04DetailedPromptFile } from "../Part4PrecisionTradeoff04DetailedPromptFile";
import { Part4PrecisionTradeoff05MinimalPromptWithTests } from "../Part4PrecisionTradeoff05MinimalPromptWithTests";
import { Part4PrecisionTradeoff06DualGenerationComparison } from "../Part4PrecisionTradeoff06DualGenerationComparison";
import { Part4PrecisionTradeoff07KeyInsightWalls } from "../Part4PrecisionTradeoff07KeyInsightWalls";
import { Part4PrecisionTradeoff08EmbeddedCodeDocument } from "../Part4PrecisionTradeoff08EmbeddedCodeDocument";
import { Part4PrecisionTradeoff09PromptCodeSpectrum } from "../Part4PrecisionTradeoff09PromptCodeSpectrum";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "04_detailed_prompt_file": Part4PrecisionTradeoff04DetailedPromptFile,
  "05_minimal_prompt_with_tests": Part4PrecisionTradeoff05MinimalPromptWithTests,
  "06_dual_generation_comparison": Part4PrecisionTradeoff06DualGenerationComparison,
  "07_key_insight_walls": Part4PrecisionTradeoff07KeyInsightWalls,
  "08_embedded_code_document": Part4PrecisionTradeoff08EmbeddedCodeDocument,
  "09_prompt_code_spectrum": Part4PrecisionTradeoff09PromptCodeSpectrum,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "04_detailed_prompt_file": 240,
  "05_minimal_prompt_with_tests": 240,
  "06_dual_generation_comparison": 240,
  "07_key_insight_walls": 120,
  "08_embedded_code_document": 840,
  "09_prompt_code_spectrum": 480,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 60 },
  "02_split_printer_vs_mold": { fadeOutFrames: 60 },
  "03_precision_tradeoff_curve": { fadeInFrames: 45 },
  "06_dual_generation_comparison": { fadeOutFrames: 30 },
  "07_key_insight_walls": { fadeOutFrames: 20 },
  "08_embedded_code_document": { fadeOutFrames: 60 },
  "09_prompt_code_spectrum": { fadeInFrames: 60, fadeOutFrames: 30 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "inverse_curve", "color": "#D9944A", "role": "precision_tradeoff_preview"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "02_split_printer_vs_mold": {"specBaseName": "02_split_printer_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.4}, "panels": {"left": {"label": "3D Printer", "animation": "printer_nozzle_grid", "accentColor": "#4A90D9", "description": "Nozzle deposits material point-by-point on coordinate grid"}, "right": {"label": "Injection Mold", "animation": "liquid_flow_walls", "accentColor": "#D9944A", "description": "Liquid flows freely until walls constrain it into shape"}}, "narrationSegments": ["part4_precision_tradeoff_001"], "durationSeconds": 16.0}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "line_chart", "chartId": "precision_tradeoff_curve", "xAxis": {"label": "Number of Tests", "range": [0, 50], "tickInterval": 10}, "yAxis": {"label": "Required Prompt Precision", "range": [0, 1], "tickLabels": ["Low", "High"]}, "series": [{"id": "precision_curve", "label": "Required Prompt Precision", "color": "#E2E8F0", "data": [{"x": 0, "y": 0.95}, {"x": 5, "y": 0.7}, {"x": 10, "y": 0.45}, {"x": 15, "y": 0.32}, {"x": 20, "y": 0.25}, {"x": 30, "y": 0.18}, {"x": 40, "y": 0.14}, {"x": 50, "y": 0.12}]}], "annotations": [{"type": "callout", "x": 3, "text": "50-line prompt\nEvery edge case specified", "color": "#D9944A"}, {"type": "callout", "x": 45, "text": "10-line prompt\nTests handle constraints", "color": "#4A90D9"}], "zones": [{"range": [0, 20], "color": "#D9944A", "label": "High prompt effort"}, {"range": [20, 50], "color": "#4A90D9", "label": "Test-driven precision"}], "narrationSegments": ["part4_precision_tradeoff_002"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 45}, "renderMode": "component"},
  "04_detailed_prompt_file": {"specBaseName": "04_detailed_prompt_file", "dataPoints": {"type": "code_editor", "chartId": "detailed_prompt_file", "file": {"name": "parser_v1.prompt", "lineCount": 50, "sections": [{"range": [1, 3], "label": "Module description", "type": "header"}, {"range": [4, 12], "label": "Input format specification", "type": "spec"}, {"range": [13, 22], "label": "Edge case handling", "type": "edge_case", "highlight": true}, {"range": [23, 35], "label": "Error handling rules", "type": "error"}, {"range": [36, 45], "label": "Output format constraints", "type": "format"}, {"range": [46, 50], "label": "Performance requirements", "type": "perf"}]}, "accentColor": "#D9944A", "label": "Without tests: prompt must specify everything", "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_minimal_prompt_with_tests": {"specBaseName": "05_minimal_prompt_with_tests", "dataPoints": {"type": "code_editor_with_terminal", "chartId": "minimal_prompt_with_tests", "promptFile": {"name": "parser_v2.prompt", "lineCount": 10, "accentColor": "#4A90D9"}, "terminal": {"command": "pdd test parser", "testCount": 47, "allPassing": true, "accentColor": "#5AAA6E"}, "testWalls": {"count": 10, "color": "#4A90D9", "metaphor": "Tests as constraining walls around prompt"}, "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_dual_generation_comparison": {"specBaseName": "06_dual_generation_comparison", "dataPoints": {"type": "side_by_side_comparison", "chartId": "dual_generation_comparison", "panels": {"left": {"label": "High Prompt Effort", "promptLines": 50, "testCount": 0, "accentColor": "#D9944A", "result": "correct_code"}, "right": {"label": "Low Prompt + Tests", "promptLines": 10, "testCount": 47, "accentColor": "#4A90D9", "result": "correct_code"}}, "comparison": {"metric": "prompt_lines", "ratio": "5:1", "insight": "Same output, 5× less prompt effort"}, "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 30}, "renderMode": "component"},
  "07_key_insight_walls": {"specBaseName": "07_key_insight_walls", "dataPoints": {"type": "key_insight", "chartId": "key_insight_walls", "primaryText": "More tests, less prompt.", "secondaryText": "The walls do the precision work.", "accentColors": {"tests": "#4A90D9", "walls": "#D9944A"}, "narrationSegments": ["part4_precision_tradeoff_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 20}, "renderMode": "component"},
  "08_embedded_code_document": {"specBaseName": "08_embedded_code_document", "dataPoints": {"type": "document_visualization", "chartId": "embedded_code_document", "document": {"title": "Parser Module", "sections": [{"type": "prose", "content": "Parse incoming JSON payloads according to schema...", "lines": 8}, {"type": "prose", "content": "Handle malformed input by returning structured errors...", "lines": 6}, {"type": "code_embed", "content": "comparison_function", "lines": 8, "language": "python"}, {"type": "prose", "content": "For all other formatting, follow standard conventions...", "lines": 4}]}, "annotations": [{"target": "prose", "label": "Natural language", "color": "#D9944A"}, {"target": "code_embed", "label": "Embedded code", "color": "#4A90D9"}], "label": "The boundary between prompt and code is fluid.", "narrationSegments": ["part4_precision_tradeoff_004"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "09_prompt_code_spectrum": {"specBaseName": "09_prompt_code_spectrum", "dataPoints": {"type": "spectrum_slider", "chartId": "prompt_code_spectrum", "spectrum": {"leftLabel": "Pure natural language", "leftColor": "#4A90D9", "rightLabel": "Pure code", "rightColor": "#64748B", "width": 1600}, "slider": {"position": 0.2, "label": "Typical PDD sweet spot"}, "notches": [{"position": 0.46, "label": "algorithm"}, {"position": 0.59, "label": "hash fn"}, {"position": 0.71, "label": "bit ops"}, {"position": 0.84, "label": "perf loop"}], "insight": {"primary": "Stay in prompt space as long as possible.", "secondary": "Dip into code when you must."}, "narrationSegments": ["part4_precision_tradeoff_005"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60, "fadeOutFrames": 30}, "renderMode": "component"},
};

export const Part4PrecisionTradeoffSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 108.3;
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
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part4PrecisionTradeoffSection;
