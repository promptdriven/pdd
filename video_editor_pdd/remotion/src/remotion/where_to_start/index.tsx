import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { WhereToStart01SectionTitleCard } from "../WhereToStart01SectionTitleCard";
import { WhereToStart03ModuleHighlightTerminal } from "../WhereToStart03ModuleHighlightTerminal";
import { WhereToStart04SourceOfTruthLabel } from "../WhereToStart04SourceOfTruthLabel";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": WhereToStart01SectionTitleCard,
  "03_module_highlight_terminal": WhereToStart03ModuleHighlightTerminal,
  "04_source_of_truth_label": WhereToStart04SourceOfTruthLabel,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 546,
  "03_module_highlight_terminal": 270,
  "04_source_of_truth_label": 150,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 60 },
  "03_module_highlight_terminal": { fadeInFrames: 30 },
  "07_gradual_migration_insight": { fadeInFrames: 30 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 6, "sectionLabel": "WHERE TO START", "titleLine1": "WHERE TO", "titleLine2": "START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "module_grid", "rows": 4, "cols": 6, "highlightCell": [2, 3], "role": "one_module_preview"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "code_editor_animation", "editorId": "legacy_codebase_reveal", "files": ["auth_handler.py", "payment_processor.py", "legacy_utils.py", "config_v2_final_FINAL.py"], "warningComments": [{"line": 15, "text": "# don't touch"}, {"line": 42, "text": "# here be dragons"}, {"line": 78, "text": "# TODO: fix this (2019)"}, {"line": 105, "text": "# nobody knows why this works"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_module_highlight_terminal": {"specBaseName": "03_module_highlight_terminal", "dataPoints": {"type": "code_transformation", "transformId": "module_to_prompt", "sourceFile": "auth_handler.py", "generatedFile": "auth_handler.prompt.md", "command": "pdd update auth_handler.py", "states": [{"id": "code_highlighted", "label": "Module selected"}, {"id": "command_typed", "label": "PDD update executed"}, {"id": "prompt_extracted", "label": "Prompt materialized"}, {"id": "code_grayed", "label": "Code becomes artifact"}, {"id": "prompt_glowing", "label": "Prompt is source of truth"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "component"},
  "04_source_of_truth_label": {"specBaseName": "04_source_of_truth_label", "dataPoints": {"type": "validation_sequence", "sequenceId": "regenerate_and_verify", "steps": [{"command": "pdd generate auth_handler.py", "description": "Regenerate code from prompt"}, {"command": "pdd test", "description": "Run test suite"}, {"result": "✓ All tests pass", "description": "Validation complete"}], "badge": {"text": "SOURCE OF TRUTH", "target": "auth_handler.prompt.md"}, "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_module_glow_spread": {"specBaseName": "05_module_glow_spread", "dataPoints": {"type": "module_migration_animation", "animationId": "gradual_glow_spread", "totalModules": 12, "migratedModules": [{"id": "auth_handler", "order": 1, "frameStart": 0}, {"id": "user_service", "order": 2, "frameStart": 30}, {"id": "payment_proc", "order": 3, "frameStart": 75}, {"id": "email_templates", "order": 4, "frameStart": 120}, {"id": "api_routes", "order": 5, "frameStart": 140}, {"id": "config_mgr", "order": 6, "frameStart": 165}], "unmigrated": ["db_models", "test_utils", "middleware", "validators", "cache_layer", "logging_setup"], "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_no_big_bang_callout": {"specBaseName": "06_no_big_bang_callout", "dataPoints": {"type": "key_insight_card", "insightId": "no_big_bang", "statements": [{"text": "No big bang.", "color": "#E2E8F0", "weight": 700}, {"text": "No rewrite.", "color": "#E2E8F0", "weight": 700}, {"text": "Just gradual migration.", "color": "#5AAA6E", "weight": 600}], "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_gradual_migration_insight": {"specBaseName": "07_gradual_migration_insight", "dataPoints": {"type": "value_flow_animation", "animationId": "code_to_specification", "containers": [{"id": "code", "label": "CODE", "color": "#64748B", "fillColor": "#94A3B8", "startLevel": 0.7, "endLevel": 0.4}, {"id": "specification", "label": "SPECIFICATION", "color": "#5AAA6E", "fillColor": "#5AAA6E", "startLevel": 0.3, "endLevel": 0.6}], "thesisText": "from code to specification", "narrationSegments": ["where_to_start_003"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 30}, "renderMode": "component"},
};

export const WhereToStartSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 33.18;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("where_to_start/narration.wav")} />
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
              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
                <VisualContractProvider contract={visualContract}>
                  <VisualMediaProvider media={visualMedia}>
                    <GeneratedContractVisual />
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

export default WhereToStartSection;
