import React from "react";
import { Sequence, useCurrentFrame, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { ColdOpen01SplitScreenHook } from "../ColdOpen01SplitScreenHook";
import { ColdOpen02ZoomOutAccumulated } from "../ColdOpen02ZoomOutAccumulated";
import { ColdOpen05CodeBlink } from "../ColdOpen05CodeBlink";
import { ColdOpen06StillPatchingBeat } from "../ColdOpen06StillPatchingBeat";
import { ColdOpen07PddTitleCard } from "../ColdOpen07PddTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_split_screen_hook": ColdOpen01SplitScreenHook,
  "02_zoom_out_accumulated": ColdOpen02ZoomOutAccumulated,
  "05_code_blink": ColdOpen05CodeBlink,
  "06_still_patching_beat": ColdOpen06StillPatchingBeat,
  "07_pdd_title_card": ColdOpen07PddTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_split_screen_hook": 240,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "03_grandmother_lamplight": { defaultSrc: "veo/grandmother_darning_lamplight.mp4", backgroundSrc: "veo/grandmother_darning_lamplight.mp4", outputSrc: "veo/grandmother_darning_lamplight.mp4", baseSrc: "veo/grandmother_darning_lamplight.mp4" },
  "04_sock_toss": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "05_code_blink": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "06_still_patching_beat": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "07_pdd_title_card": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "01_split_screen_hook": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "2025", "content": "developer_cursor_edit_veo", "colorGrade": {"color": "#4A90D9", "opacity": 0.02}, "background": "#000000"}, "rightPanel": {"label": "1955", "content": "grandmother_darning_hook_veo", "colorGrade": {"color": "#D4A043", "opacity": 0.04}, "background": "#000000"}, "embeddedVeoClips": ["developer_cursor_edit", "grandmother_darning_hook"], "backgroundColor": "#000000", "narrationSegments": ["cold_open_001"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "generated-media"},
  "02_zoom_out_accumulated": {"specBaseName": "02_zoom_out_accumulated", "dataPoints": {"type": "animated_zoom_split", "chartId": "accumulated_weight_reveal", "leftPanel": {"label": "Codebase", "gridSize": [8, 8], "tileSize": [110, 90], "diffMarkerPercent": 0.6, "counter": {"label": "patches", "finalValue": 1247}, "inlineComments": ["// fixed null case", "// workaround for #412", "// TODO: refactor", "// temporary fix (2019)", "// don't touch this", "// legacy"]}, "rightPanel": {"label": "Mended garments", "itemCount": 47, "counter": {"label": "mended", "finalValue": 47}, "itemTypes": ["socks", "shirts", "trousers"]}, "zoomConfig": {"startScale": 1.0, "endScale": 0.15, "startFrame": 15, "duration": 105}, "backgroundColor": "#000000", "narrationSegments": ["cold_open_002"]}, "overlayConfig": null, "renderMode": "component"},
  "03_grandmother_lamplight": {"specBaseName": "03_grandmother_lamplight", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning_lamplight", "camera": {"framing": "medium_closeup_to_extreme_closeup", "movement": "push_in", "travelPercent": 12, "dof": "shallow", "angle": "slightly_overhead"}, "lighting": {"key": {"color": "#E8A040", "position": "upper_left", "type": "practical_lamp"}, "fill": "minimal", "rim": "warm_edge", "grade": "rembrandt_warm"}, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "Elderly woman, 70s-80s, weathered hands with visible age spots, wearing a dark cardigan. Warm domestic setting, 1950s era. Skilled and practiced with needle and thread."}], "intercutWith": "02_zoom_out_accumulated", "panel": "right", "narrationSegments": ["cold_open_002"], "narrationTimingSeconds": {"start": 8.0, "end": 13.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_sock_toss": {"specBaseName": "04_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "modern_sock_toss", "camera": {"framing": "medium_shot", "movement": "static", "dof": "moderate", "angle": "eye_level", "drift": false}, "lighting": {"key": {"color": "#F0ECE4", "position": "overhead", "type": "LED"}, "fill": {"color": "#D4E0EC", "position": "side_window", "type": "daylight"}, "grade": "neutral_cool"}, "props": {"sock": "white cotton ankle sock with hole in toe", "multiPack": "cellophane-wrapped, $4.99 sticker visible", "trashCan": "small modern waste bin"}, "narrationSegments": ["cold_open_003"], "narrationTimingSeconds": {"start": 15.0, "end": 20.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_code_blink": {"specBaseName": "05_code_blink", "dataPoints": {"type": "code_animation", "chartId": "code_blink_regenerate", "ide": {"theme": "github-dark", "background": "#0D1117", "font": "JetBrains Mono", "fontSize": 14}, "oldCode": {"lineCount": 18, "filename": "user_parser.py", "maintenanceComments": [{"line": 3, "text": "# fixed null case"}, {"line": 7, "text": "# workaround for #412"}, {"line": 10, "text": "# TODO: refactor this"}, {"line": 13, "text": "# temporary fix (2019)"}, {"line": 16, "text": "# don't remove — breaks prod"}]}, "newCode": {"lineCount": 14, "commentCount": 0, "revealBlocks": [[1, 5], [6, 10], [11, 14]]}, "dissolution": {"particleCount": 200, "gravity": 0.3, "fadeDuration": 45}, "terminalCommand": "pdd generate ✓", "narrationSegments": ["cold_open_004"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_still_patching_beat": {"specBaseName": "06_still_patching_beat", "dataPoints": {"type": "text_beat", "chartId": "still_patching_question", "questionText": "So why are we still patching?", "accentWord": "patching?", "accentColor": "#D9944A", "textColor": "#E2E8F0", "backgroundColor": "#0D1117", "codeUnderlayOpacity": 0.08, "holdDuration": 60, "narrationSegments": ["cold_open_005"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 0, "sectionLabel": null, "titleLine1": "Prompt-Driven", "titleLine2": "Development", "titleColor": "#4A90D9", "subtitle": "Writing the mold, not the plastic.", "subtitleColor": "#94A3B8", "backgroundColor": "#0D1117", "codeUnderlayOpacity": 0.04, "glow": {"blur": 12, "color": "#4A90D9", "opacity": 0.08}, "terminalBreadcrumb": "pdd generate", "narrationSegments": ["cold_open_006"]}, "overlayConfig": null, "renderMode": "raw-media"},
};

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 17.54;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
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
                  <VisualMediaProvider media={visualMedia}>
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
