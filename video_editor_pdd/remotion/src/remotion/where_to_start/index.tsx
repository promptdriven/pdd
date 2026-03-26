import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { WhereToStart02LegacyCodebaseReveal } from "../WhereToStart02LegacyCodebaseReveal";
import { WhereToStart07NoBigBangCallout } from "../WhereToStart07NoBigBangCallout";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "../Part5CompoundReturns07EconomicsCrossingCallback";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "02_legacy_codebase_reveal": WhereToStart02LegacyCodebaseReveal,
  "06_no_big_bang_callout": WhereToStart07NoBigBangCallout,
  "07_economics_callback": Part5CompoundReturns07EconomicsCrossingCallback,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "02_legacy_codebase_reveal": 150,
  "06_no_big_bang_callout": 180,
  "07_economics_callback": 300,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "03_module_highlight_terminal": { defaultSrc: "veo/developer_prompt_shift.mp4", backgroundSrc: "veo/developer_prompt_shift.mp4", outputSrc: "veo/developer_prompt_shift.mp4", baseSrc: "veo/developer_prompt_shift.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "04_source_of_truth_label": { fadeInFrames: 20 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 6, "sectionLabel": "PART 6", "titleLine1": "WHERE TO", "titleLine2": "START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "module_grid", "rows": 4, "cols": 6, "highlightIndex": 13, "highlightColor": "#4A90D9"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "code_wall", "layout": "stacked_panes", "paneCount": 3, "dangerComments": [{"pane": 1, "line": 12, "text": "// don't touch", "glowFrame": 30}, {"pane": 1, "line": 28, "text": "// here be dragons", "glowFrame": 60}, {"pane": 2, "line": 8, "text": "// TODO: refactor this someday", "glowFrame": 100}, {"pane": 2, "line": 22, "text": "// nobody knows why this works", "glowFrame": 115}, {"pane": 3, "line": 15, "text": "// legacy — do not modify", "glowFrame": 140}], "scrollRate": 0.5, "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_module_highlight_terminal": {"specBaseName": "03_module_highlight_terminal", "dataPoints": {"type": "interactive_demo", "command": "pdd update auth_handler.py", "targetModule": "auth_handler.py", "outputFile": "auth_handler.prompt.md", "phases": [{"id": "highlight", "frames": [0, 30], "description": "Module highlights in codebase"}, {"id": "terminal", "frames": [30, 120], "description": "Terminal command executes"}, {"id": "materialize", "frames": [120, 180], "description": "Prompt file materializes from code"}, {"id": "shift", "frames": [180, 270], "description": "Code dims, prompt glows — source of truth shifts"}], "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {"defaultSrc": "veo/developer_prompt_shift.mp4", "backgroundSrc": "veo/developer_prompt_shift.mp4", "outputSrc": "veo/developer_prompt_shift.mp4", "baseSrc": "veo/developer_prompt_shift.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_source_of_truth_label": {"specBaseName": "04_source_of_truth_label", "dataPoints": {"type": "comparison_diagram", "left": {"label": "auth_handler.py", "category": "ARTIFACT", "borderStyle": "dashed", "borderColor": "#475569", "watermark": "ARTIFACT"}, "right": {"label": "auth_handler.prompt.md", "category": "SOURCE OF TRUTH", "borderStyle": "solid", "borderColor": "#8B5CF6", "glow": true}, "relationships": [{"direction": "right_to_left", "label": "generates →"}, {"direction": "left_to_right", "label": "← extracts"}], "annotation": "When the regenerated version passes all tests, the prompt is your new source of truth.", "narrationSegments": ["where_to_start_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 20}, "renderMode": "generated-media"},
  "05_module_glow_spread": {"specBaseName": "05_module_glow_spread", "dataPoints": {"type": "progressive_migration", "grid": {"cols": 5, "rows": 4, "totalModules": 20}, "conversionOrder": [{"id": "auth_handler", "label": "auth_handler.py", "col": 2, "row": 1, "frame": 0, "preConverted": true}, {"id": "user_model", "label": "user_model.py", "col": 4, "row": 0, "frame": 30}, {"id": "payment_processor", "label": "payment_processor.py", "col": 1, "row": 2, "frame": 70}, {"id": "api_routes", "label": "api_routes.py", "col": 3, "row": 3, "frame": 110}, {"id": "email_service", "label": "email_service.py", "col": 0, "row": 1, "frame": 150}, {"id": "config_loader", "label": "config_loader.py", "col": 4, "row": 3, "frame": 170}, {"id": "search_index", "label": "search_index.py", "col": 2, "row": 0, "frame": 190}, {"id": "notification_hub", "label": "notification_hub.py", "col": 0, "row": 3, "frame": 210}], "unconverted": ["db_connection.py", "cache_manager.py", "logger.py", "middleware.py", "rate_limiter.py", "session_store.py", "file_upload.py", "webhook_handler.py", "scheduler.py", "analytics.py", "admin_panel.py", "test_runner.py"], "counterSteps": [1, 2, 3, 4, 5, 6, 7, 8], "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_no_big_bang_callout": {"specBaseName": "06_no_big_bang_callout", "dataPoints": {"type": "text_manifesto", "statements": [{"text": "No big bang.", "frame": 20, "style": "bold"}, {"text": "No rewrite.", "frame": 50, "style": "bold"}, {"text": "Just a gradual migration of where value lives.", "frame": 80, "highlight": "value"}], "migrationBar": {"from": "code", "to": "specification", "startSplit": 0.2, "endSplit": 0.5, "leftColor": "#475569", "rightColor": "#8B5CF6"}, "narrationSegments": ["where_to_start_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_economics_callback": {"specBaseName": "07_economics_callback", "dataPoints": {"type": "metaphor_callback", "comparison": {"left": {"label": "patch it?", "icon": "holey_sock", "color": "#D9944A", "status": "deprecated"}, "right": {"label": "replace it.", "icon": "fresh_sock", "color": "#10B981", "status": "preferred"}}, "closingStatements": ["You don't patch socks because socks got cheap.", "The economics made patching irrational."], "narrationSegments": ["where_to_start_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const WhereToStartSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 32.08;
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
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                  <GeneratedContractVisual />
                </VisualMediaProvider>
              </VisualContractProvider>
            ) : visualMedia?.defaultSrc ? (
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
                </VisualMediaProvider>
              </VisualContractProvider>
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default WhereToStartSection;
