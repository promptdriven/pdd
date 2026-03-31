import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { ColdOpen05CodeCursorBlink } from "../ColdOpen05CodeCursorBlink";
import { ColdOpen06CodeRegeneration } from "../ColdOpen06CodeRegeneration";
import { ColdOpen08PromptFileGenerate } from "../ColdOpen08PromptFileGenerate";
import { ColdOpen09TestFixCycle } from "../ColdOpen09TestFixCycle";
import { ColdOpen10TransitionOverlay } from "../ColdOpen10TransitionOverlay";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "05_code_cursor_blink": ColdOpen05CodeCursorBlink,
  "06_code_regeneration": ColdOpen06CodeRegeneration,
  "08_prompt_file_generate": ColdOpen08PromptFileGenerate,
  "09_test_fix_cycle": ColdOpen09TestFixCycle,
  "10_transition_overlay": ColdOpen10TransitionOverlay,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "05_code_cursor_blink": 210,
  "06_code_regeneration": 150,
  "08_prompt_file_generate": 150,
  "09_test_fix_cycle": 390,
  "10_transition_overlay": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_screen_darning": { leftSrc: "veo/developer_cursor_edit.mp4", defaultSrc: "veo/developer_cursor_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
  "02_veo_developer_cursor_edit": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "03_veo_grandmother_darning": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "04_veo_sock_toss": { defaultSrc: "veo/sock_toss_modern.mp4", backgroundSrc: "veo/sock_toss_modern.mp4", outputSrc: "veo/sock_toss_modern.mp4", baseSrc: "veo/sock_toss_modern.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_darning": {"specBaseName": "01_split_screen_darning", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.3}, "panels": {"left": {"clips": ["developer_cursor_edit"], "label": "Developer — AI-assisted code patching", "zoomOut": {"startFrame": 180, "from": 1.0, "to": 0.35}}, "right": {"clips": ["grandmother_darning"], "label": "Grandmother — careful sock darning", "zoomOut": {"startFrame": 180, "from": 1.0, "to": 0.35}}}, "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"], "durationSeconds": 14.0}, "mediaAliases": {"leftSrc": "veo/developer_cursor_edit.mp4", "defaultSrc": "veo/developer_cursor_edit.mp4", "rightSrc": "veo/grandmother_darning.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4", "revealSrc": "veo/grandmother_darning.mp4", "leftBaseSrc": "veo/developer_cursor_edit.mp4", "rightBaseSrc": "veo/grandmother_darning.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "02_veo_developer_cursor_edit": {"specBaseName": "02_veo_developer_cursor_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_edit", "durationSeconds": 14, "usedIn": "01_split_screen_darning (left panel)", "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Young developer, late 20s, casual hoodie, modern desk setup with ultrawide monitor, dark-themed code editor, ambient RGB lighting"}]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_veo_grandmother_darning": {"specBaseName": "03_veo_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "durationSeconds": 14, "usedIn": "01_split_screen_darning (right panel)", "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "Elderly woman in her 70s, 1950s attire, cardigan sweater, reading glasses, warm lamplight, domestic setting, kind weathered hands"}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning.mp4", "backgroundSrc": "veo/grandmother_darning.mp4", "outputSrc": "veo/grandmother_darning.mp4", "baseSrc": "veo/grandmother_darning.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_veo_sock_toss": {"specBaseName": "04_veo_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss_modern", "durationSeconds": 5}, "mediaAliases": {"defaultSrc": "veo/sock_toss_modern.mp4", "backgroundSrc": "veo/sock_toss_modern.mp4", "outputSrc": "veo/sock_toss_modern.mp4", "baseSrc": "veo/sock_toss_modern.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_code_cursor_blink": {"specBaseName": "05_code_cursor_blink", "dataPoints": {"type": "remotion_animation", "componentId": "code_cursor_blink", "durationFrames": 210, "fps": 30, "narrationSegments": ["cold_open_005", "cold_open_006"], "codeFile": "process_order.py", "patchComments": 6, "visibleLines": 40}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_code_regeneration": {"specBaseName": "06_code_regeneration", "dataPoints": {"type": "remotion_animation", "componentId": "code_regeneration", "durationFrames": 150, "fps": 30, "narrationSegments": ["cold_open_007", "cold_open_008"], "codeFile": "process_order.py", "deletedLines": 40, "regeneratedLines": 25, "pddCommand": "pdd generate process_order"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_title_card_pdd": {"specBaseName": "07_title_card_pdd", "dataPoints": {"type": "title_card", "componentId": "title_card_pdd", "durationFrames": 60, "fps": 30, "narrationSegments": ["cold_open_008"], "title": "Prompt-Driven Development", "overlayOpacity": 0.7, "inheritsBackground": "06_code_regeneration"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_prompt_file_generate": {"specBaseName": "08_prompt_file_generate", "dataPoints": {"type": "remotion_animation", "componentId": "prompt_file_generate", "durationFrames": 150, "fps": 30, "narrationSegments": ["cold_open_008"], "promptFile": "email_validator.prompt", "promptLines": 15, "outputLines": 200, "pddCommand": "pdd generate email_validator"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_test_fix_cycle": {"specBaseName": "09_test_fix_cycle", "dataPoints": {"type": "remotion_animation", "componentId": "test_fix_cycle", "durationFrames": 390, "fps": 30, "narrationSegments": ["cold_open_009"], "phases": ["initial_failure", "add_test", "pdd_fix", "regenerate", "all_pass"], "failingTest": "test_unicode_domain", "pddCommand": "pdd fix email_validator", "testResults": ["test_basic_format", "test_invalid_domain", "test_empty_string", "test_special_chars", "test_unicode_domain"], "totalPassed": 5}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_transition_overlay": {"specBaseName": "10_transition_overlay", "dataPoints": {"type": "title_card", "componentId": "transition_overlay_why", "durationFrames": 90, "fps": 30, "narrationSegments": ["cold_open_010"], "text": "Now let me show you WHY this matters.", "emphasis": {"word": "WHY", "weight": 700, "color": "#E2E8F0"}, "inheritsBackground": "09_test_fix_cycle", "transitionsTo": "part1_economics"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
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
