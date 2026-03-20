import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { ColdOpen01SplitScreenHook } from "../ColdOpen01SplitScreenHook";
import { ColdOpen03ZoomOutAccumulated } from "../ColdOpen03ZoomOutAccumulated";
import { ColdOpen06CodeBlinkPatched } from "../ColdOpen06CodeBlinkPatched";
import { ColdOpen07CodeRegeneration } from "../ColdOpen07CodeRegeneration";
import { ColdOpen08StillPatchingBeat } from "../ColdOpen08StillPatchingBeat";
import { ColdOpen09PddTitleCard } from "../ColdOpen09PddTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_split_screen_hook": ColdOpen01SplitScreenHook,
  "03_zoom_out_accumulated": ColdOpen03ZoomOutAccumulated,
  "06_code_blink_patched": ColdOpen06CodeBlinkPatched,
  "07_code_regeneration": ColdOpen07CodeRegeneration,
  "08_still_patching_beat": ColdOpen08StillPatchingBeat,
  "09_pdd_title_card": ColdOpen09PddTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_split_screen_hook": 240,
  "03_zoom_out_accumulated": 210,
  "06_code_blink_patched": 150,
  "07_code_regeneration": 270,
  "08_still_patching_beat": 120,
  "09_pdd_title_card": 180,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_screen_hook": { leftSrc: "veo/developer_cursor_edit.mp4", defaultSrc: "veo/developer_cursor_edit.mp4", rightSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4", revealSrc: "veo/grandmother_darning.mp4" },
  "02_grandmother_lamplight": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "03_zoom_out_accumulated": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "04_sock_toss": { defaultSrc: "veo/sock_toss_modern.mp4", backgroundSrc: "veo/sock_toss_modern.mp4", outputSrc: "veo/sock_toss_modern.mp4", baseSrc: "veo/sock_toss_modern.mp4" },
  "05_developer_cursor_broll": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "06_code_blink_patched": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "07_code_regeneration": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "08_still_patching_beat": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
  "09_pdd_title_card": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical", "divider": {"x": 960, "color": "#334155", "opacity": 0.4, "width": 2}, "panels": {"left": {"label": "2025", "veoClipId": "developer_cursor_edit", "colorGrade": {"tint": "#4A90D9", "opacity": 0.02}, "vignette": {"color": "#000000", "opacity": 0.15}}, "right": {"label": "1955", "veoClipId": "grandmother_darning", "colorGrade": {"tint": "#D4A043", "opacity": 0.04}, "filmGrain": {"opacity": 0.06, "fps": 12}}}, "embeddedVeoClips": ["developer_cursor_edit", "grandmother_darning"], "narrationSegments": ["cold_open_001", "cold_open_002"]}, "overlayConfig": null, "renderMode": "generated-media"},
  "02_grandmother_lamplight": {"specBaseName": "02_grandmother_lamplight", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "duration": 10, "frames": 300, "camera": "static_close_up", "colorTemperature": "3200K", "era": "1950s", "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "Elderly woman in her 70s, silver hair in a low bun, wire-rimmed reading glasses, cotton floral housedress, simple gold wedding band, gentle weathered hands. Warm and practiced demeanor."}], "setting": "1950s_living_room", "props": ["darning_egg", "wool_sock", "ceramic_lamp", "sewing_basket"], "narrationSegments": ["cold_open_001", "cold_open_002"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_zoom_out_accumulated": {"specBaseName": "03_zoom_out_accumulated", "dataPoints": {"type": "animated_infographic", "layout": "split_screen", "left": {"label": "Codebase Patches", "blockCount": 80, "diffMarkerPercent": 60, "floatingComments": ["// TODO: refactor", "// HACK", "// fixed null case", "// workaround for #412", "// legacy — do not touch", "// temporary fix 2023-04"], "counter": {"from": 0, "to": 1247, "suffix": " patches", "color": "#F85149"}}, "right": {"label": "Mended Garments", "garmentCount": 47, "garmentTypes": ["sock", "shirt", "trouser", "sock", "sweater"], "counter": {"from": 0, "to": 47, "suffix": " mended garments", "color": "#D9944A"}}, "zoom": {"from": 1.0, "to": 0.15, "startFrame": 10, "durationFrames": 80}, "narrationSegments": ["cold_open_003", "cold_open_004"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_sock_toss": {"specBaseName": "04_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss_modern", "duration": 6, "frames": 180, "camera": "medium_tracking_rack_focus", "colorTemperature": "5600K", "era": "modern", "setting": "minimalist_apartment_bedroom", "props": ["holey_sock", "wastebasket", "sock_multipack", "price_tag_4_99"], "keyAction": "toss_and_replace", "narrationSegments": ["cold_open_005", "cold_open_006"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_developer_cursor_broll": {"specBaseName": "05_developer_cursor_broll", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_edit", "duration": 10, "frames": 300, "camera": "over_the_shoulder_static", "colorTemperature": "mixed_6500K_3500K", "era": "modern", "setting": "modern_tech_workspace", "props": ["mechanical_keyboard", "widescreen_monitor", "code_editor", "desk_lamp", "coffee_mug"], "keyAction": "accept_ai_suggestion", "narrationSegments": ["cold_open_001", "cold_open_002"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_code_blink_patched": {"specBaseName": "06_code_blink_patched", "dataPoints": {"type": "code_editor", "function": {"name": "processUserInput", "lineCount": 18, "language": "typescript", "code": ["function processUserInput(raw: string): ProcessedInput {", "  const sanitized = raw.trim().toLowerCase();", "  let result: ProcessedInput;", "", "  // fixed null case", "  if (!sanitized || sanitized === 'undefined') {", "    return { valid: false, value: '', error: 'empty input' };", "  }", "", "  // workaround for #412", "  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, '');", "  if (cleaned !== sanitized) {", "    result = { valid: true, value: cleaned, warning: 'chars stripped' };", "  // TODO: refactor this", "  } else if (cleaned.length > MAX_INPUT_LENGTH) {", "    result = { valid: true, value: cleaned.slice(0, MAX_INPUT_LENGTH) };", "  // legacy — do not touch", "  } else { result = { valid: true, value: cleaned }; }", "  return result;", "}"]}, "patchScars": [{"line": 5, "text": "// fixed null case", "highlightColor": "#F85149", "opacity": 0.5}, {"line": 9, "text": "// workaround for #412", "highlightColor": "#F85149", "opacity": 0.5}, {"line": 13, "text": "// TODO: refactor this", "highlightColor": "#D29922", "opacity": 0.4}, {"line": 16, "text": "// legacy — do not touch", "highlightColor": "#F85149", "opacity": 0.5}], "cursor": {"line": 1, "column": 0, "color": "#58A6FF", "blinkMs": 530}, "narrationSegments": ["cold_open_007"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_code_regeneration": {"specBaseName": "07_code_regeneration", "dataPoints": {"type": "code_editor_animation", "phases": [{"name": "selection", "frames": [0, 20], "lineRange": [1, 18], "highlightColor": "#388BFD", "highlightOpacity": 0.15}, {"name": "dissolution", "frames": [20, 75], "effect": "particle_scatter", "direction": "bottom_to_top", "staggerFramesPerLine": 3, "particleSize": 2}, {"name": "empty_beat", "frames": [75, 105], "description": "Empty editor with blinking cursor"}, {"name": "regeneration", "frames": [105, 210], "effect": "typewriter", "charsPerSecond": 60, "lineCount": 14}, {"name": "terminal_confirm", "frames": [210, 270], "command": "pdd generate processUserInput", "result": "✓"}], "oldCode": {"functionName": "processUserInput", "lineCount": 18, "patchComments": 4}, "newCode": {"functionName": "processUserInput", "lineCount": 14, "patchComments": 0, "code": ["function processUserInput(raw: string): ProcessedInput {", "  const sanitized = raw.trim().toLowerCase();", "", "  if (!sanitized) {", "    return { valid: false, value: '', error: 'empty input' };", "  }", "", "  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, '');", "  const truncated = cleaned.slice(0, MAX_INPUT_LENGTH);", "", "  return {", "    valid: true,", "    value: truncated,", "    ...(cleaned !== sanitized && { warning: 'chars stripped' }),", "  };", "}"]}, "narrationSegments": ["cold_open_008"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_still_patching_beat": {"specBaseName": "08_still_patching_beat", "dataPoints": {"type": "title_card", "text": "So why are we still patching?", "font": {"family": "Inter", "weight": 600, "size": 52}, "color": "#C9D1D9", "opacity": 0.92, "position": {"x": 960, "y": 520}, "background": "#0D1117", "ambientGlow": {"color": "#4A90D9", "opacity": 0.03, "radius": 400}, "timing": {"fadeInFrames": 20, "holdFrames": 60, "fadeOutFrames": 40}, "narrationSegments": ["cold_open_009"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "09_pdd_title_card": {"specBaseName": "09_pdd_title_card", "dataPoints": {"type": "title_card", "title": {"text": "Prompt-Driven Development", "font": {"family": "Inter", "weight": 700, "size": 64}, "color": "#E6EDF3", "opacity": 0.95, "position": {"x": 960, "y": 460}, "letterSpacing": -1}, "subtitle": {"text": "WHY YOU'RE STILL DARNING SOCKS", "font": {"family": "Inter", "weight": 400, "size": 24}, "color": "#8B949E", "opacity": 0.7, "position": {"x": 960, "y": 568}, "letterSpacing": 2}, "rule": {"y": 510, "xRange": [460, 1460], "color": "#4A90D9", "glow": {"opacity": 0.12, "blur": 4}}, "background": {"color": "#0A0F1A", "dots": {"count": 50, "color": "#4A90D9", "opacity": 0.06, "speed": 0.3}}, "timing": {"ruleDrawFrames": [0, 30], "titleRiseFrames": [30, 60], "subtitleFadeFrames": [50, 80], "holdFrames": [80, 150], "fadeOutFrames": [150, 180]}, "narrationSegments": ["cold_open_010"]}, "overlayConfig": null, "renderMode": "raw-media"},
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
                  <VisualMediaProvider media={visualMedia}>
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
