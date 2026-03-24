import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { ColdOpen01SplitScreenHook } from "../ColdOpen01SplitScreenHook";
import { ColdOpen07PddTitleCard } from "../ColdOpen07PddTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_split_screen_hook": ColdOpen01SplitScreenHook,
  "07_pdd_title_card": ColdOpen07PddTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_split_screen_hook": 240,
  "07_pdd_title_card": 150,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_screen_hook": { leftSrc: "veo/developer_ai_edit.mp4", defaultSrc: "veo/developer_ai_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
  "02_developer_ai_edit": { defaultSrc: "veo/developer_ai_edit.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4" },
  "03_grandmother_darning": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "04_sock_toss": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "05_code_blink_patched": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "06_code_regeneration": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "07_pdd_title_card": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "03_grandmother_darning": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip_then_zoom_out", "clipId": "developer_ai_edit", "zoomOutReveals": "massive_codebase_with_patches", "thematicRole": "modern_developer_patching"}, "rightPanel": {"content": "veo_clip_then_zoom_out", "clipId": "grandmother_darning", "zoomOutReveals": "drawer_of_mended_garments", "thematicRole": "grandmother_darning_socks"}, "backgroundColor": "#000000", "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"]}, "overlayConfig": null, "renderMode": "component"},
  "02_developer_ai_edit": {"specBaseName": "02_developer_ai_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_ai_edit", "camera": {"framing": "close_up_hands_to_medium", "movement": "subtle_drift_right", "dof": "moderate", "aperture": "f/2.8", "angle": "eye_level"}, "lighting": {"key": {"color": "#B8C9E0", "position": "front_monitor", "type": "screen_glow"}, "fill": {"color": "#3D2F1F", "opacity": 0.1, "type": "desk_lamp"}, "rim": {"color": "#4A90D9", "opacity": 0.15, "type": "keyboard_backlight"}, "grade": "cool_modern"}, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Software developer, mid-20s to mid-30s, casual attire, confident and focused. Hands on mechanical keyboard. Lit by cool blue-white monitor glow in a dim modern home office."}], "usedIn": "01_split_screen_hook (left panel)", "narrationSegments": ["cold_open_001"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_grandmother_darning": {"specBaseName": "03_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "camera": {"framing": "extreme_close_up_hands", "movement": "very_slow_push_in", "dof": "very_shallow", "aperture": "f/1.8", "angle": "slightly_elevated"}, "lighting": {"key": {"color": "#D9944A", "position": "frame_right_lamp", "type": "lamplight"}, "fill": {"color": "#2A1F14", "opacity": 0.08, "type": "ambient"}, "rim": "none", "grade": "warm_golden_nostalgic"}, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "Elderly woman in her 70s-80s, weathered hands with visible age spots, seated in a wooden chair. 1950s domestic attire. Lit by warm amber lamplight. Darning a wool sock over a wooden darning egg."}], "props": ["darning_egg", "wool_sock", "darning_needle", "sewing_basket"], "usedIn": "01_split_screen_hook (right panel)", "narrationSegments": ["cold_open_001"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "generated-media"},
  "04_sock_toss": {"specBaseName": "04_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss", "camera": {"framing": "medium_shot", "movement": "static_handheld", "dof": "moderate", "aperture": "f/4.0", "angle": "eye_level"}, "lighting": {"key": {"color": "#E8E0D4", "position": "window", "type": "natural_daylight"}, "fill": {"color": "#F5F0E8", "opacity": 0.6, "type": "bounced_ambient"}, "rim": "none", "grade": "bright_casual_modern"}, "props": ["holey_sock", "trash_can", "sock_multipack"], "narrationSegments": ["cold_open_004"], "narrationTimingSeconds": {"start": 11.46, "end": 13.94}}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_code_blink_patched": {"specBaseName": "05_code_blink_patched", "dataPoints": {"type": "code_display", "language": "python", "filename": "auth_handler.py", "lineCount": 24, "patchComments": [{"line": 3, "text": "# patched 2024-01 — handle None case"}, {"line": 8, "text": "# workaround: upstream API sometimes returns 403"}, {"line": 14, "text": "# TODO: clean this up after migration"}, {"line": 19, "text": "# edge case fix (see ticket #4721)"}], "cursorPosition": {"line": 14, "column": 48}, "theme": "dark_ide", "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_005"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_code_regeneration": {"specBaseName": "06_code_regeneration", "dataPoints": {"type": "code_regeneration", "filename": "auth_handler.py", "deletedLines": 24, "generatedLines": 16, "deletionDurationFrames": 36, "generationDurationFrames": 16, "terminal": {"command": "pdd generate auth_handler", "result": "Generated in 0.8s", "position": "bottom_right"}, "theme": "dark_ide", "backgroundColor": "#0D1117", "narrationSegments": ["cold_open_005"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 0, "sectionLabel": "Cold Open", "title": "Prompt-Driven Development", "titleColor": "#4A90D9", "subtitle": "So why are we still patching?", "subtitleColor": "#94A3B8", "backgroundColor": "#0D1117", "codeUnderlay": true, "underlayOpacity": 0.15, "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "component"},
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
