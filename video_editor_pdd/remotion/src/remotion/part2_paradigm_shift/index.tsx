import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part2ParadigmShift01SectionTitleCard } from "../Part2ParadigmShift01SectionTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part2ParadigmShift01SectionTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "03_factory_floor_intro": { defaultSrc: "veo/factory_floor_intro.mp4", backgroundSrc: "veo/factory_floor_intro.mp4", outputSrc: "veo/factory_floor_intro.mp4", baseSrc: "veo/factory_floor_intro.mp4" },
  "04_injection_molding_process": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "06_craftsman_vs_mold": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "07_craftsman_carving": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "08_mold_producing_parts": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "09_1980s_chip_lab": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "10_verilog_synthesis_triple": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_nozzle", "color": "#4A90D9", "component": "injection_nozzle"}, {"shape": "mold_cavity", "color": "#4A90D9", "component": "rectangular_cavity"}, {"shape": "mold_walls", "color": "#D9944A", "component": "constraint_walls"}], "narrationSegments": ["part2_paradigm_shift_001"]}, "overlayConfig": null, "renderMode": "component"},
  "03_factory_floor_intro": {"specBaseName": "03_factory_floor_intro", "dataPoints": {"type": "veo_clip", "clipId": "factory_floor_intro", "camera": {"framing": "wide_establishing", "movement": "slow_dolly_forward", "dof": "deep", "aperture": "f/5.6", "angle": "eye_level_to_low"}, "lighting": {"key": {"color": "#F0F0EC", "type": "overhead_fluorescent"}, "fill": {"color": "#FFB347", "opacity": 0.2, "type": "machinery_indicators"}, "accent": {"color": "#4A90D9", "opacity": 0.1, "type": "status_leds"}, "atmosphere": "light_haze"}, "narrationSegments": ["part2_paradigm_shift_005", "part2_paradigm_shift_006"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_injection_molding_process": {"specBaseName": "04_injection_molding_process", "dataPoints": {"type": "veo_clip", "clipId": "injection_molding_process", "camera": {"framing": "extreme_close_up", "movement": "slow_pan_then_hold", "dof": "shallow", "aperture": "f/2.8", "angle": "slightly_elevated"}, "lighting": {"key": {"color": "#FFD699", "type": "warm_industrial"}, "fill": {"color": "#B8C9E0", "opacity": 0.3, "type": "overhead_cool"}, "rim": {"color": "#C0C0C0", "opacity": 0.4, "type": "mold_edge_highlight"}, "materialGlow": {"color": "#FF8C42", "opacity": 0.2, "type": "molten_plastic"}}, "narrationSegments": ["part2_paradigm_shift_006", "part2_paradigm_shift_007"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_craftsman_vs_mold": {"specBaseName": "06_craftsman_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"content": "veo_clip_with_aura", "clipId": "craftsman_carving", "aura": {"color": "#FFB347", "target": "wooden_chair"}, "label": "Value lives in the object", "thematicRole": "crafting_value_in_object"}, "rightPanel": {"content": "veo_clip_with_aura", "clipId": "mold_producing_parts", "aura": {"color": "#4A90D9", "target": "injection_mold"}, "label": "Value lives in the specification", "partDissolves": true, "thematicRole": "molding_value_in_spec"}, "backgroundColor": "#000000", "narrationSegments": ["part2_paradigm_shift_010", "part2_paradigm_shift_011", "part2_paradigm_shift_012"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_craftsman_carving": {"specBaseName": "07_craftsman_carving", "dataPoints": {"type": "veo_clip", "clipId": "craftsman_carving", "camera": {"framing": "close_up_hands", "movement": "near_static", "dof": "moderate", "aperture": "f/3.5", "angle": "eye_level"}, "lighting": {"key": {"color": "#FFD699", "type": "afternoon_sun"}, "fill": {"color": "#8B6914", "opacity": 0.15, "type": "workshop_ambient"}, "rim": {"color": "#DAA520", "opacity": 0.2, "type": "shaving_edge_light"}, "grade": "warm_artisanal"}, "usedIn": "06_craftsman_vs_mold (left panel)", "narrationSegments": ["part2_paradigm_shift_011"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_mold_producing_parts": {"specBaseName": "08_mold_producing_parts", "dataPoints": {"type": "veo_clip", "clipId": "mold_producing_parts", "camera": {"framing": "close_up_cavity", "movement": "near_static", "dof": "moderate", "aperture": "f/4", "angle": "slightly_elevated"}, "lighting": {"key": {"color": "#D4E5F7", "type": "industrial_overhead"}, "fill": {"color": "#FF8C42", "opacity": 0.2, "type": "molten_plastic_glow"}, "rim": {"color": "#C0C0C0", "opacity": 0.5, "type": "steel_specular"}, "grade": "cool_precision"}, "usedIn": "06_craftsman_vs_mold (right panel)", "narrationSegments": ["part2_paradigm_shift_012"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "09_1980s_chip_lab": {"specBaseName": "09_1980s_chip_lab", "dataPoints": {"type": "veo_clip", "clipId": "1980s_chip_lab", "camera": {"framing": "over_shoulder_medium", "movement": "slow_drift_forward", "dof": "moderate", "aperture": "f/3.5", "angle": "elevated_over_shoulder"}, "lighting": {"key": {"color": "#F5F5DC", "type": "overhead_fluorescent"}, "fill": {"color": "#FFD699", "opacity": 0.3, "type": "desk_lamp"}, "accent": {"color": "#00FF41", "opacity": 0.05, "type": "oscilloscope_crt"}, "grade": "1980s_institutional"}, "characters": [{"id": "chip_engineer", "label": "1980s Chip Engineer", "referencePrompt": "Electronics engineer, male, 30s-40s, short-sleeve button-down shirt, 1980s style. Hunched over drafting desk drawing circuits with mechanical pencil under fluorescent lighting."}], "narrationSegments": ["part2_paradigm_shift_013", "part2_paradigm_shift_014"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "10_verilog_synthesis_triple": {"specBaseName": "10_verilog_synthesis_triple", "dataPoints": {"type": "animated_diagram", "diagramId": "verilog_synthesis_triple", "phases": [{"id": "single_synthesis", "elements": ["verilog_code", "synthesis_icon", "gate_netlist"]}, {"id": "triple_synthesis", "elements": ["three_code_blocks", "three_netlists", "three_checkmarks"]}], "netlists": [{"id": "run_1", "layout": "diamond", "color": "#4ADE80"}, {"id": "run_2", "layout": "grid", "color": "#38BDF8"}, {"id": "run_3", "layout": "tree", "color": "#FBBF24"}], "equivalenceLabel": "Functionally equivalent", "equivalenceColor": "#4ADE80", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_paradigm_shift_015", "part2_paradigm_shift_016"]}, "overlayConfig": null, "renderMode": "raw-media"},
};

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 227.48;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part2_paradigm_shift/narration.wav")} />
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

export default Part2ParadigmShiftSection;
