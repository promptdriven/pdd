import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { ColdOpen07CodeCursorBlink } from "../ColdOpen07CodeCursorBlink";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "07_code_cursor_blink": ColdOpen07CodeCursorBlink,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "07_code_cursor_blink": 48,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_screen_darning": { leftSrc: "veo/developer_cursor_edit.mp4", defaultSrc: "veo/developer_cursor_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
  "02_developer_cursor_edit": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "03_grandmother_darning": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "04_developer_codebase_zoomout": { defaultSrc: "veo/developer_codebase_zoomout.mp4", backgroundSrc: "veo/developer_codebase_zoomout.mp4", outputSrc: "veo/developer_codebase_zoomout.mp4", baseSrc: "veo/developer_codebase_zoomout.mp4" },
  "05_grandmother_drawer_zoomout": { defaultSrc: "veo/grandmother_drawer_zoomout.mp4", backgroundSrc: "veo/grandmother_drawer_zoomout.mp4", outputSrc: "veo/grandmother_drawer_zoomout.mp4", baseSrc: "veo/grandmother_drawer_zoomout.mp4" },
  "06_sock_toss": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_darning": {"specBaseName": "01_split_screen_darning", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.4}, "panels": {"left": {"clips": ["developer_cursor_edit", "developer_codebase_zoomout"], "label": "Developer patching code"}, "right": {"clips": ["grandmother_darning", "grandmother_drawer_zoomout"], "label": "Grandmother darning socks"}}, "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"], "durationSeconds": 9.0}, "mediaAliases": {"leftSrc": "veo/developer_cursor_edit.mp4", "defaultSrc": "veo/developer_cursor_edit.mp4", "rightSrc": "veo/grandmother_darning.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4", "revealSrc": "veo/grandmother_darning.mp4", "leftBaseSrc": "veo/developer_cursor_edit.mp4", "leftRevealSrc": "veo/developer_codebase_zoomout.mp4", "rightBaseSrc": "veo/grandmother_darning.mp4", "rightRevealSrc": "veo/grandmother_drawer_zoomout.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "02_developer_cursor_edit": {"specBaseName": "02_developer_cursor_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_edit", "durationSeconds": 5, "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "A 30-something software developer, gender-neutral, wearing a dark henley shirt. Modern desk with mechanical keyboard and single ultrawide monitor. Warm office lighting."}]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_grandmother_darning": {"specBaseName": "03_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "durationSeconds": 5, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "An elderly woman in her 70s, 1950s era. Weathered but steady hands, wearing a simple cotton dress with rolled sleeves. Warm golden lamplight on her face and hands. Modest 1950s living room setting."}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning.mp4", "backgroundSrc": "veo/grandmother_darning.mp4", "outputSrc": "veo/grandmother_darning.mp4", "baseSrc": "veo/grandmother_darning.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_developer_codebase_zoomout": {"specBaseName": "04_developer_codebase_zoomout", "dataPoints": {"type": "veo_clip", "clipId": "developer_codebase_zoomout", "durationSeconds": 4, "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "A 30-something software developer, gender-neutral, wearing a dark henley shirt. Modern desk with mechanical keyboard and single ultrawide monitor. Warm office lighting."}]}, "mediaAliases": {"defaultSrc": "veo/developer_codebase_zoomout.mp4", "backgroundSrc": "veo/developer_codebase_zoomout.mp4", "outputSrc": "veo/developer_codebase_zoomout.mp4", "baseSrc": "veo/developer_codebase_zoomout.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_grandmother_drawer_zoomout": {"specBaseName": "05_grandmother_drawer_zoomout", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_drawer_zoomout", "durationSeconds": 4, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "An elderly woman in her 70s, 1950s era. Weathered but steady hands, wearing a simple cotton dress with rolled sleeves. Warm golden lamplight on her face and hands. Modest 1950s living room setting."}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_drawer_zoomout.mp4", "backgroundSrc": "veo/grandmother_drawer_zoomout.mp4", "outputSrc": "veo/grandmother_drawer_zoomout.mp4", "baseSrc": "veo/grandmother_drawer_zoomout.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_sock_toss": {"specBaseName": "06_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss", "durationSeconds": 4}, "mediaAliases": {"defaultSrc": "veo/sock_toss.mp4", "backgroundSrc": "veo/sock_toss.mp4", "outputSrc": "veo/sock_toss.mp4", "baseSrc": "veo/sock_toss.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_code_cursor_blink": {"specBaseName": "07_code_cursor_blink", "dataPoints": {"type": "code_editor", "language": "python", "theme": "catppuccin-mocha", "functionName": "process_order", "totalLines": 40, "patchComments": [{"line": 5, "text": "// PATCH: fixed null check", "age": "old"}, {"line": 12, "text": "// TODO: refactor this block", "age": "old"}, {"line": 18, "text": "// HOTFIX: edge case #1247", "age": "medium"}, {"line": 23, "text": "// PATCH: handle empty list", "age": "recent"}, {"line": 31, "text": "// PATCH: timezone fix", "age": "medium"}, {"line": 37, "text": "// HOTFIX: race condition", "age": "recent"}], "cursor": {"line": 23, "column": 4, "blinkMs": 500}, "narrationSegments": ["cold_open_005"], "durationSeconds": 1.6}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_code_regeneration": {"specBaseName": "08_code_regeneration", "dataPoints": {"type": "code_regeneration", "language": "python", "theme": "catppuccin-mocha", "functionName": "process_order", "originalLines": 40, "regeneratedLines": 30, "patchCommentsRemoved": 6, "terminalCommand": "pdd generate process_order", "phases": [{"name": "select", "startFrame": 0, "endFrame": 8}, {"name": "delete", "startFrame": 8, "endFrame": 12}, {"name": "void", "startFrame": 12, "endFrame": 14}, {"name": "regenerate", "startFrame": 14, "endFrame": 44}, {"name": "terminal", "startFrame": 38, "endFrame": 48}, {"name": "hold", "startFrame": 48, "endFrame": 60}], "narrationSegments": ["cold_open_006"], "durationSeconds": 2.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_title_card_pdd": {"specBaseName": "09_title_card_pdd", "dataPoints": {"type": "title_card", "sectionNumber": 0, "titleLine1": "PROMPT-DRIVEN", "titleLine2": "DEVELOPMENT", "backgroundColor": "#1E1E2E", "backgroundLayer": "regenerated_code_at_15_percent", "accentColor": "#89B4FA", "narrationSegments": ["cold_open_006"], "durationSeconds": 2.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 20.42;
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
