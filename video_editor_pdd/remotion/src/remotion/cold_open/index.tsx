import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
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
  "04_zoom_out_accumulated": 210,
  "06_code_blink_patched": 150,
  "07_code_regeneration": 270,
  "08_pdd_title_card": 60,
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
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip", "clipId": "developer_ai_edit", "colorGrade": "cool_blue", "gradeColor": "#4A90D9"}, "rightPanel": {"content": "veo_clip", "clipId": "grandmother_darning", "colorGrade": "warm_amber", "gradeColor": "#D9944A"}, "backgroundColor": "#000000", "narrationSegments": ["cold_open_001", "cold_open_002"]}, "overlayConfig": null, "renderMode": "component"},
  "02_developer_ai_edit": {"specBaseName": "02_developer_ai_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_ai_edit", "camera": {"framing": "medium_close_hands_and_monitor", "movement": "static", "dof": "moderate", "aperture": "f/2.8", "angle": "slightly_elevated_15deg"}, "lighting": {"key": {"color": "#B8D4F0", "position": "front_monitor", "type": "screen_glow"}, "fill": {"color": "#1A1A2E", "opacity": 0.1, "type": "ambient"}, "grade": "cool_modern"}, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Software developer, mid-30s, casual professional attire. Only hands and partial face visible. Lit by cool blue-white monitor glow in dark office. Modern keyboard and large monitor with dark-themed IDE."}], "narrationSegments": ["cold_open_001"], "narrationTimingSeconds": {"start": 0, "end": 5}}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_grandmother_darning": {"specBaseName": "03_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "camera": {"framing": "medium_close_hands_and_sock", "movement": "static", "dof": "shallow", "aperture": "f/2.0", "angle": "slightly_elevated_15deg"}, "lighting": {"key": {"color": "#F5D6A8", "position": "camera_right_lamp", "type": "incandescent"}, "fill": {"color": "#3D2B1A", "opacity": 0.15, "type": "ambient"}, "grade": "warm_amber_nostalgic"}, "props": ["dark_wool_sock", "darning_needle", "thread", "wooden_darning_mushroom"], "narrationSegments": ["cold_open_001", "cold_open_002"], "narrationTimingSeconds": {"start": 0, "end": 5}}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_zoom_out_accumulated": {"specBaseName": "04_zoom_out_accumulated", "dataPoints": {"type": "animated_infographic", "layout": "split_screen_zoom_out", "splitPosition": 960, "leftPanel": {"content": "code_accumulation_grid", "fileCount": 200, "patchCounter": {"values": [1, 47, 312, 1847], "label": "patches"}, "scatteredLabels": ["// TODO", "// HACK", "// temporary fix", "// don't touch"], "colors": {"recentEdit": "#5AAA6E", "olderPatch": "#D9944A", "problematicPatch": "#E74C3C", "fileBlock": "#1E293B"}}, "rightPanel": {"content": "garment_drawer_illustration", "garments": [{"type": "sock", "count": 6}, {"type": "shirt", "count": 4}, {"type": "trousers", "count": 3}], "repairColor": "#D9944A", "drawerColor": "#8B6F47"}, "zoomFactor": {"from": 1.0, "to": 0.15}, "backgroundColor": "#000000", "narrationSegments": ["cold_open_003"]}, "overlayConfig": null, "renderMode": "component"},
  "05_sock_toss": {"specBaseName": "05_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss", "camera": {"framing": "medium_shot", "movement": "static", "dof": "moderate", "aperture": "f/3.5", "angle": "eye_level"}, "lighting": {"key": {"color": "#F5F0E8", "position": "window", "type": "natural_daylight"}, "fill": {"color": "#E8E0D4", "type": "ambient"}, "grade": "bright_neutral_modern"}, "props": ["sock_with_hole", "wastebasket"], "narrationSegments": ["cold_open_004"], "narrationTimingSeconds": {"start": 11.46, "end": 13.94}}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_code_blink_patched": {"specBaseName": "06_code_blink_patched", "dataPoints": {"type": "code_animation", "animation": "delete_and_regenerate", "oldCode": {"lines": 25, "hackComments": ["// patched", "// workaround", "// TODO: refactor"], "style": "complex_patched_function"}, "newCode": {"lines": 25, "style": "clean_regenerated", "noHackComments": true}, "deleteAnimation": {"direction": "top_to_bottom", "flashColor": "#D9944A", "stagger": "1_frame"}, "regenerateAnimation": {"direction": "top_to_bottom", "flashColor": "#4A90D9", "stagger": "1_frame"}, "terminalSnippet": {"command": "pdd generate", "status": "success", "checkColor": "#5AAA6E"}, "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_005"]}, "overlayConfig": null, "renderMode": "component"},
  "07_code_regeneration": {"specBaseName": "07_code_regeneration", "dataPoints": {"type": "code_hold", "content": "clean_regenerated_code", "cursor": {"blinking": true, "position": "end_of_last_line"}, "transition": {"type": "fade_to_background", "codeOpacity": {"from": 1.0, "to": 0.5}, "backgroundColor": {"from": "#0D1117", "to": "#111827"}}, "terminalSnippet": {"command": "pdd generate", "status": "success"}, "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "component"},
  "08_pdd_title_card": {"specBaseName": "08_pdd_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 0, "sectionLabel": "Cold Open", "title": "Prompt-Driven Development", "titleColor": "#4A90D9", "subtitle": "The code is just plastic. The mold is what matters.", "subtitleColor": "#94A3B8", "backgroundColor": "#111827", "codeUnderlayer": {"content": "clean_regenerated_code", "opacity": {"from": 0.5, "to": 0.2}}, "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "component"},
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
