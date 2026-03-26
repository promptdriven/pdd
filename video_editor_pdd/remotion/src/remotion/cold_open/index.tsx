import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { ColdOpen07CodeRegeneration } from "../ColdOpen07CodeRegeneration";
import { ColdOpen01SplitScreenHook } from "../ColdOpen01SplitScreenHook";
import { ColdOpen07PddTitleCard } from "../ColdOpen07PddTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "08_code_regeneration": ColdOpen07CodeRegeneration,
  "01_split_screen_hook": ColdOpen01SplitScreenHook,
  "07_pdd_title_card": ColdOpen07PddTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "08_code_regeneration": 270,
  "01_split_screen_hook": 240,
  "07_pdd_title_card": 150,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_screen_darning": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "02_developer_cursor_edit": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "03_grandmother_darning": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "04_developer_codebase_zoomout": { defaultSrc: "veo/developer_codebase_zoomout.mp4", backgroundSrc: "veo/developer_codebase_zoomout.mp4", outputSrc: "veo/developer_codebase_zoomout.mp4", baseSrc: "veo/developer_codebase_zoomout.mp4" },
  "05_grandmother_drawer_zoomout": { defaultSrc: "veo/grandmother_drawer_zoomout.mp4", backgroundSrc: "veo/grandmother_drawer_zoomout.mp4", outputSrc: "veo/grandmother_drawer_zoomout.mp4", baseSrc: "veo/grandmother_drawer_zoomout.mp4" },
  "06_sock_toss": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "10_transition_beat": { lowerThirdText: "But here's what your great-grandmother figured out sixty years ago." },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_darning": {"specBaseName": "01_split_screen_darning", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.8}, "panels": {"left": {"clips": ["developer_cursor_edit", "developer_codebase_zoomout"], "crossfadeAt": 5.8}, "right": {"clips": ["grandmother_darning", "grandmother_drawer_zoomout"], "crossfadeAt": 5.8}}, "durationSeconds": 11.0}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "02_developer_cursor_edit": {"specBaseName": "02_developer_cursor_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_edit", "durationSeconds": 6, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "A developer in their late 20s wearing a dark henley shirt, sitting at a modern desk with a mechanical keyboard and ultrawide monitor. Relaxed posture, warm desk lamp nearby."}]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_grandmother_darning": {"specBaseName": "03_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "durationSeconds": 6, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "An elderly woman in her 70s with silver hair pinned up, wearing a floral housedress and reading glasses on a chain. 1950s appearance, kind face, sitting in a cushioned armchair under warm lamplight."}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning.mp4", "backgroundSrc": "veo/grandmother_darning.mp4", "outputSrc": "veo/grandmother_darning.mp4", "baseSrc": "veo/grandmother_darning.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_developer_codebase_zoomout": {"specBaseName": "04_developer_codebase_zoomout", "dataPoints": {"type": "veo_clip", "clipId": "developer_codebase_zoomout", "durationSeconds": 5, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "A developer in their late 20s wearing a dark henley shirt, sitting at a modern desk with a mechanical keyboard and ultrawide monitor. Relaxed posture, warm desk lamp nearby."}]}, "mediaAliases": {"defaultSrc": "veo/developer_codebase_zoomout.mp4", "backgroundSrc": "veo/developer_codebase_zoomout.mp4", "outputSrc": "veo/developer_codebase_zoomout.mp4", "baseSrc": "veo/developer_codebase_zoomout.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_grandmother_drawer_zoomout": {"specBaseName": "05_grandmother_drawer_zoomout", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_drawer_zoomout", "durationSeconds": 5, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "An elderly woman in her 70s with silver hair pinned up, wearing a floral housedress and reading glasses on a chain. 1950s appearance, kind face, sitting in a cushioned armchair under warm lamplight."}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_drawer_zoomout.mp4", "backgroundSrc": "veo/grandmother_drawer_zoomout.mp4", "outputSrc": "veo/grandmother_drawer_zoomout.mp4", "baseSrc": "veo/grandmother_drawer_zoomout.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_sock_toss": {"specBaseName": "06_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss", "durationSeconds": 3}, "mediaAliases": {"defaultSrc": "veo/sock_toss.mp4", "backgroundSrc": "veo/sock_toss.mp4", "outputSrc": "veo/sock_toss.mp4", "baseSrc": "veo/sock_toss.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_code_cursor_blink": {"specBaseName": "07_code_cursor_blink", "dataPoints": {"type": "code_editor", "language": "typescript", "lineCount": 30, "patchIndicators": ["// HACK:", "// TODO: refactor", "// patch for #1247"], "gutterPlusLines": [3, 7, 12, 18, 22, 25], "cursorPosition": {"line": 14, "column": 4}, "theme": "vscode-dark"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_code_regeneration": {"specBaseName": "08_code_regeneration", "dataPoints": {"type": "code_editor_animation", "phases": [{"name": "cascade_delete", "direction": "bottom-to-top", "durationFrames": 15}, {"name": "empty_beat", "durationFrames": 3}, {"name": "cascade_generate", "direction": "top-to-bottom", "durationFrames": 30}, {"name": "terminal_overlay", "text": "$ pdd generate ✓", "durationFrames": 12}], "theme": "vscode-dark", "cleanCode": true, "terminalCommand": "pdd generate"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_title_card_pdd": {"specBaseName": "09_title_card_pdd", "dataPoints": {"type": "title_card", "title": "Prompt-Driven Development", "tagline": "Why You're Still Darning Socks", "titleFont": "Inter Bold", "titleSize": 72, "titleColor": "#FFFFFF", "glowColor": "rgba(79, 193, 255, 0.3)", "backgroundCodeOpacity": 0.2, "vignetteOpacity": 0.6}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_transition_beat": {"specBaseName": "10_transition_beat", "dataPoints": {"type": "lower_third_overlay", "position": {"x": 660, "y": 780}, "bars": [{"label": "Patches Applied", "color": "#F59E0B", "targetPercent": 105, "counterEnd": 2847, "suffix": " patches"}, {"label": "Time Spent Repairing", "color": "#EF4444", "targetPercent": 102, "counterEnd": 1240, "suffix": " hrs"}], "containerWidth": 600, "containerHeight": 160, "bgOpacity": 0.7}, "mediaAliases": {}, "overlayConfig": {"lowerThirdText": "But here's what your great-grandmother figured out sixty years ago."}, "renderMode": "generated-media"},
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": null, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": null, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 17.54;
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

export default ColdOpenSection;
