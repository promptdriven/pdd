import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part4PrecisionTradeoff01SectionTitleCard } from "../Part4PrecisionTradeoff01SectionTitleCard";
import { Part4PrecisionTradeoff02PrinterVsMoldSplit } from "../Part4PrecisionTradeoff02PrinterVsMoldSplit";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "../Part4PrecisionTradeoff03PrecisionTradeoffCurve";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part4PrecisionTradeoff01SectionTitleCard,
  "02_printer_vs_mold_split": Part4PrecisionTradeoff02PrinterVsMoldSplit,
  "03_precision_tradeoff_curve": Part4PrecisionTradeoff03PrecisionTradeoffCurve,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "02_printer_vs_mold_split": 600,
  "03_precision_tradeoff_curve": 450,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 4, "sectionLabel": "PART 4", "titleLine1": "THE PRECISION", "titleLine2": "TRADEOFF", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "printer_nozzle", "color": "#60A5FA", "side": "left"}, {"shape": "coordinate_grid", "color": "#60A5FA", "side": "left"}, {"shape": "mold_outline", "color": "#D9944A", "side": "right"}, {"shape": "flow_curves", "color": "#A78BFA", "side": "right"}], "narrationSegments": ["part4_precision_tradeoff_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_printer_vs_mold_split": {"specBaseName": "02_printer_vs_mold_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "3D PRINTING", "headerColor": "#60A5FA", "elements": [{"type": "coordinate_grid", "spacing": 40, "color": "#60A5FA"}, {"type": "printer_nozzle", "layers": 3, "pointsPerLayer": 8}, {"type": "coordinate_labels", "font": "JetBrains Mono", "size": 8}], "caption": "Every point must be specified", "thematicRole": "explicit_precision"}, "rightPanel": {"header": "INJECTION MOLDING", "headerColor": "#D9944A", "elements": [{"type": "mold_walls", "strokeWidth": 4, "color": "#D9944A"}, {"type": "liquid_flow", "color": "#A78BFA"}, {"type": "wall_glow_on_impact", "glowColor": "#D9944A"}], "caption": "Walls do the precision work", "thematicRole": "emergent_precision"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]}, "overlayConfig": null, "renderMode": "component"},
  "03_precision_tradeoff_curve": {"specBaseName": "03_precision_tradeoff_curve", "dataPoints": {"type": "animated_chart", "chartId": "precision_tradeoff_curve", "axes": {"x": {"label": "Number of Tests", "range": [0, 50], "ticks": ["0", "10", "20", "30", "40", "50+"]}, "y": {"label": "Required Prompt Precision", "range": ["Low", "High"], "ticks": ["Low", "Medium", "High"]}}, "curve": {"type": "inverse_hyperbolic", "color": "#2DD4BF", "strokeWidth": 3}, "annotations": {"left": {"label": "parser_v1.prompt — 50 lines", "description": "Dense prompt, few tests", "position": "high_precision"}, "right": {"label": "parser_v2.prompt — 10 lines", "description": "Minimal prompt, 47 tests", "testCount": 47, "position": "low_precision"}}, "introText": "This maps directly to PDD.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]}, "overlayConfig": null, "renderMode": "component"},
};

export const Part4PrecisionTradeoffSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 111.84;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part4_precision_tradeoff/narration.wav")} />
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
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part4PrecisionTradeoffSection;
