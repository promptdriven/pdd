import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { ColdOpen07CodeCursorBlink } from "../ColdOpen07CodeCursorBlink";
import { ColdOpen08PromptFileGenerate } from "../ColdOpen08PromptFileGenerate";
import { ColdOpen09TestFixRegenerate } from "../ColdOpen09TestFixRegenerate";
import { ColdOpen10TransitionOverlay } from "../ColdOpen10TransitionOverlay";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "07_code_cursor_blink": ColdOpen07CodeCursorBlink,
  "10_prompt_file_generate": ColdOpen08PromptFileGenerate,
  "11_test_fix_regenerate": ColdOpen09TestFixRegenerate,
  "12_transition_overlay": ColdOpen10TransitionOverlay,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "07_code_cursor_blink": 48,
  "10_prompt_file_generate": 150,
  "11_test_fix_regenerate": 300,
  "12_transition_overlay": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_developer_grandmother": { leftSrc: "veo/developer_cursor_edit.mp4", defaultSrc: "veo/developer_cursor_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
  "02_veo_developer_cursor_edit": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "03_veo_grandmother_darning": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "04_veo_developer_codebase_zoomout": { defaultSrc: "veo/developer_codebase_zoomout.mp4", backgroundSrc: "veo/developer_codebase_zoomout.mp4", outputSrc: "veo/developer_codebase_zoomout.mp4", baseSrc: "veo/developer_codebase_zoomout.mp4" },
  "05_veo_grandmother_drawer_zoomout": { defaultSrc: "veo/grandmother_drawer_zoomout.mp4", backgroundSrc: "veo/grandmother_drawer_zoomout.mp4", outputSrc: "veo/grandmother_drawer_zoomout.mp4", baseSrc: "veo/grandmother_drawer_zoomout.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_developer_grandmother": {"specBaseName": "01_split_developer_grandmother", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.6}, "panels": {"left": {"clips": ["developer_cursor_edit_co", "developer_codebase_zoomout_co"], "label": "Developer with Cursor"}, "right": {"clips": ["grandmother_darning_co", "grandmother_drawer_zoomout_co"], "label": "Grandmother darning"}}, "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"], "durationSeconds": 14.0}, "mediaAliases": {"leftSrc": "veo/developer_cursor_edit.mp4", "defaultSrc": "veo/developer_cursor_edit.mp4", "rightSrc": "veo/grandmother_darning.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4", "revealSrc": "veo/grandmother_darning.mp4", "leftBaseSrc": "veo/developer_cursor_edit.mp4", "leftRevealSrc": "veo/developer_codebase_zoomout.mp4", "rightBaseSrc": "veo/grandmother_darning.mp4", "rightRevealSrc": "veo/grandmother_drawer_zoomout.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "02_veo_developer_cursor_edit": {"specBaseName": "02_veo_developer_cursor_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_edit_co", "durationSeconds": 6, "usedIn": "01_split_developer_grandmother (left panel)", "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "Software developer, early 30s, focused expression, modern office setting, cool monitor glow on face"}]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_veo_grandmother_darning": {"specBaseName": "03_veo_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning_co", "durationSeconds": 6, "usedIn": "01_split_developer_grandmother (right panel)", "characters": [{"id": "grandmother", "label": "Grandmother", "referencePrompt": "Elderly grandmother, warm lamplight, skilled hands, cozy interior, darning a wool sock"}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning.mp4", "backgroundSrc": "veo/grandmother_darning.mp4", "outputSrc": "veo/grandmother_darning.mp4", "baseSrc": "veo/grandmother_darning.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_veo_developer_codebase_zoomout": {"specBaseName": "04_veo_developer_codebase_zoomout", "dataPoints": {"type": "veo_clip", "clipId": "developer_codebase_zoomout_co", "durationSeconds": 8, "usedIn": "01_split_developer_grandmother (left panel)", "camera": {"framing": "medium_to_wide", "movement": "dolly_back", "dof": "deepening", "angle": "eye_level"}, "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "Software developer, early 30s, focused expression, modern office setting, cool monitor glow on face"}]}, "mediaAliases": {"defaultSrc": "veo/developer_codebase_zoomout.mp4", "backgroundSrc": "veo/developer_codebase_zoomout.mp4", "outputSrc": "veo/developer_codebase_zoomout.mp4", "baseSrc": "veo/developer_codebase_zoomout.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_veo_grandmother_drawer_zoomout": {"specBaseName": "05_veo_grandmother_drawer_zoomout", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_drawer_zoomout_co", "durationSeconds": 8, "usedIn": "01_split_developer_grandmother (right panel)", "camera": {"framing": "medium_closeup_to_medium", "movement": "pull_back", "dof": "sharpening_on_drawer"}, "characters": [{"id": "grandmother", "label": "Grandmother", "referencePrompt": "Elderly grandmother, warm lamplight, skilled hands, cozy interior, darning a wool sock"}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_drawer_zoomout.mp4", "backgroundSrc": "veo/grandmother_drawer_zoomout.mp4", "outputSrc": "veo/grandmother_drawer_zoomout.mp4", "baseSrc": "veo/grandmother_drawer_zoomout.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_veo_sock_discard": {"specBaseName": "06_veo_sock_discard", "dataPoints": {"type": "veo_clip", "clipId": "sock_discard_co", "durationSeconds": 4, "narrationSegments": ["cold_open_004"], "characters": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_code_cursor_blink": {"specBaseName": "07_code_cursor_blink", "dataPoints": {"type": "code_editor", "editorTheme": "dark", "language": "python", "functionName": "validate_email", "lineCount": 30, "patchComments": [{"line": 4, "text": "// patched for unicode"}, {"line": 8, "text": "// edge case fix #247"}, {"line": 12, "text": "// temporary workaround"}, {"line": 15, "text": "// patched: null check"}, {"line": 18, "text": "// fix: RFC 5321 compliance"}, {"line": 21, "text": "// workaround for legacy domains"}, {"line": 24, "text": "// TODO: refactor this block"}, {"line": 27, "text": "// patched again (2024-03)"}], "cursorPosition": {"line": 28, "column": "end"}, "narrationSegments": ["cold_open_005", "cold_open_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_code_regeneration": {"specBaseName": "08_code_regeneration", "dataPoints": {"type": "code_editor_animation", "editorTheme": "dark", "language": "python", "functionName": "validate_email", "phases": [{"phase": "select", "frames": [0, 15], "description": "Selection sweep over patched code"}, {"phase": "delete", "frames": [15, 25], "description": "All code deletes"}, {"phase": "empty", "frames": [25, 35], "description": "Brief empty editor beat"}, {"phase": "regenerate", "frames": [35, 90], "description": "Clean code flows in"}, {"phase": "terminal", "frames": [70, 150], "description": "pdd generate overlay"}], "terminalCommand": "pdd generate email_validator", "narrationSegments": ["cold_open_007", "cold_open_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_title_card_pdd": {"specBaseName": "09_title_card_pdd", "dataPoints": {"type": "title_card", "titleLine1": "Prompt-Driven", "titleLine2": "Development", "backgroundColor": "rgba(10, 15, 26, 0.8)", "accentColor": "#4A90D9", "overlayOnPrevious": true, "narrationSegments": ["cold_open_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_prompt_file_generate": {"specBaseName": "10_prompt_file_generate", "dataPoints": {"type": "code_generation_demo", "layout": "split_pane", "leftPane": {"file": "email_validator.prompt", "lineCount": 15, "contentType": "natural_language"}, "rightPane": {"file": "email_validator.py", "lineCount": 200, "contentType": "python"}, "ratio": "15:200", "terminal": {"command": "pdd generate email_validator", "result": "Generated 200 lines (0.8s)"}, "narrationSegments": ["cold_open_008", "cold_open_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "11_test_fix_regenerate": {"specBaseName": "11_test_fix_regenerate", "dataPoints": {"type": "test_fix_cycle", "tests": [{"name": "test_basic_email", "initialStatus": "pass", "finalStatus": "pass"}, {"name": "test_invalid_format", "initialStatus": "pass", "finalStatus": "pass"}, {"name": "test_missing_domain", "initialStatus": "pass", "finalStatus": "pass"}, {"name": "test_unicode_domain", "initialStatus": "fail", "finalStatus": "pass"}], "terminal": {"command": "pdd fix email_validator", "result": "Fixed and regenerated (1.2s)"}, "keyInsight": "Bug is gone, not patched. Test is a permanent wall.", "narrationSegments": ["cold_open_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "12_transition_overlay": {"specBaseName": "12_transition_overlay", "dataPoints": {"type": "transition_overlay", "text": "Now let me show you WHY this matters.", "emphasis": {"word": "WHY", "color": "#4A90D9", "weight": 700}, "transitionTo": "part1_economics", "narrationSegments": ["cold_open_010"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 49.18;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("cold_open/narration.wav")} />
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

export default ColdOpenSection;
