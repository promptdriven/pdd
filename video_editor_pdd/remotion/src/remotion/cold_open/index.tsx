import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { ColdOpen01SplitScreenHook } from "../ColdOpen01SplitScreenHook";
import { ColdOpen04ZoomOutAccumulated } from "../ColdOpen04ZoomOutAccumulated";
import { ColdOpen06CodeBlinkPatched } from "../ColdOpen06CodeBlinkPatched";
import { ColdOpen07CodeRegeneration } from "../ColdOpen07CodeRegeneration";
import { ColdOpen08PddTitleCard } from "../ColdOpen08PddTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_split_screen_hook": ColdOpen01SplitScreenHook,
  "04_zoom_out_accumulated": ColdOpen04ZoomOutAccumulated,
  "06_code_blink_patched": ColdOpen06CodeBlinkPatched,
  "07_code_regeneration": ColdOpen07CodeRegeneration,
  "08_pdd_title_card": ColdOpen08PddTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_split_screen_hook": 240,
  "04_zoom_out_accumulated": 164,
  "06_code_blink_patched": 150,
  "07_code_regeneration": 270,
  "08_pdd_title_card": 75,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_screen_hook": { leftSrc: "veo/developer_ai_edit.mp4", defaultSrc: "veo/developer_ai_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
  "02_developer_ai_edit": { defaultSrc: "veo/developer_ai_edit.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4" },
  "03_grandmother_darning": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "04_zoom_out_accumulated": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "05_sock_toss": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "06_code_blink_patched": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "07_code_regeneration": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "08_pdd_title_card": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "01_split_screen_hook": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "AI-Assisted Edit", "labelColor": "#4A90D9", "content": "veo_clip", "clipId": "developer_ai_edit", "colorGrade": {"color": "#4A90D9", "opacity": 0.04}, "zoomOutAt": 175, "zoomOutContent": "accumulated_codebase"}, "rightPanel": {"label": "Darning by Lamplight", "labelColor": "#D9944A", "content": "veo_clip", "clipId": "grandmother_darning", "colorGrade": {"color": "#D9944A", "opacity": 0.04}, "zoomOutAt": 175, "zoomOutContent": "mended_garments_drawer"}, "backgroundColor": "#000000", "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "02_developer_ai_edit": {"specBaseName": "02_developer_ai_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_ai_edit", "camera": {"framing": "medium_close_hands_and_screen", "movement": "static", "dof": "shallow", "aperture": "f/1.8", "angle": "slight_downward_desk_level"}, "lighting": {"key": {"color": "#C8D6E5", "position": "front_monitor", "type": "screen_glow"}, "fill": {"color": "#0D1117", "opacity": 0.1, "type": "ambient"}, "rim": "faint_backlight_edge", "grade": "cool_clean_modern"}, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Software developer, mid-30s, hands visible on mechanical keyboard, wearing casual professional attire. Lit by cool blue-white monitor glow in a dark home office. Large monitor with dark-theme IDE visible."}], "narrationSegments": ["cold_open_001", "cold_open_002"], "parentSplit": "01_split_screen_hook", "panelPosition": "left"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_grandmother_darning": {"specBaseName": "03_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "camera": {"framing": "close_up_to_medium_pullback", "movement": "slow_dolly_back", "dof": "moderate", "aperture": "f/2.8", "angle": "slightly_above_looking_down"}, "lighting": {"key": {"color": "#D9944A", "position": "frame_right_lamp", "type": "warm_lamp"}, "fill": {"color": "#2A1F14", "opacity": 0.2, "type": "ambient"}, "rim": "none", "grade": "warm_golden_nostalgic"}, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "Elderly woman in her 70s, silver hair, wearing a 1950s house dress or cardigan. Warm lamplight illuminates her face and skilled hands. Seated in a period-appropriate armchair in a domestic interior."}], "props": ["darning_needle", "wool_sock", "darning_egg", "mending_basket"], "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"], "parentSplit": "01_split_screen_hook", "panelPosition": "right"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_zoom_out_accumulated": {"specBaseName": "04_zoom_out_accumulated", "dataPoints": {"type": "remotion_animation", "animationType": "zoom_out_reveal", "initialFile": "UserService.ts", "editHighlight": {"line": 14, "color": "#5AAA6E"}, "zoomLevels": [{"scale": 1.0, "frame": 0, "content": "single_file_edit"}, {"scale": 0.6, "frame": 15, "content": "adjacent_files"}, {"scale": 0.3, "frame": 50, "content": "file_tree_diffs"}, {"scale": 0.15, "frame": 90, "content": "multi_pane_labels"}, {"scale": 0.1, "frame": 120, "content": "full_workspace"}], "markers": {"diffCount": 25, "todoLabels": ["// HACK", "// temporary fix (2019)", "// don't touch this", "// TODO: refactor someday"], "totalFiles": 42}, "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_003"], "parentSplit": "01_split_screen_hook", "panelPosition": "left"}, "overlayConfig": null, "renderMode": "component"},
  "05_sock_toss": {"specBaseName": "05_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss", "camera": {"framing": "medium_shot_waist_up", "movement": "static", "dof": "medium", "aperture": "f/4.0", "angle": "eye_level"}, "lighting": {"key": {"color": "#F0EDE8", "position": "window_left", "type": "natural_daylight"}, "fill": {"color": "#F0EDE8", "opacity": 0.6, "type": "ambient"}, "rim": "none", "grade": "bright_clean_contemporary"}, "props": ["worn_sock_with_hole", "trash_can", "sock_multi_pack"], "narrationSegments": ["cold_open_004"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_code_blink_patched": {"specBaseName": "06_code_blink_patched", "dataPoints": {"type": "remotion_animation", "animationType": "static_code_display", "file": "UserService.ts", "functionName": "processUserData", "lineRange": [127, 171], "patchComments": [{"line": 131, "text": "// patched for edge case #247"}, {"line": 139, "text": "// TODO: this shouldn't be here"}, {"line": 145, "text": "// workaround for legacy API"}, {"line": 152, "text": "// HACK: don't ask"}, {"line": 158, "text": "// temporary fix, see ticket PD-1892"}], "cursorPosition": {"line": 145, "column": 42}, "gitGutterDensity": "heavy_modified", "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_005"]}, "overlayConfig": null, "renderMode": "component"},
  "07_code_regeneration": {"specBaseName": "07_code_regeneration", "dataPoints": {"type": "remotion_animation", "animationType": "delete_and_regenerate", "file": "UserService.ts", "functionName": "processUserData", "deletePhase": {"lineRange": [128, 171], "lineCount": 44, "selectionColor": "#264F78", "cascadeDirection": "up", "durationFrames": 10}, "regeneratePhase": {"lineCount": 18, "startLine": 128, "wipeDirection": "left-to-right", "flashColor": "#5AAA6E", "durationFrames": 23}, "terminal": {"command": "pdd generate", "output": "✓ UserService.ts regenerated (18 lines, 3 tests passing)", "position": "bottom-right"}, "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "component"},
  "08_pdd_title_card": {"specBaseName": "08_pdd_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 0, "sectionLabel": null, "title": "Prompt-Driven Development", "titleColor": "#4A90D9", "titleSize": 56, "subtitle": null, "codeUnderlay": true, "codeUnderlayOpacity": 0.12, "terminalPersist": true, "terminalOpacity": 0.5, "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "component"},
};

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 17.54;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

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
