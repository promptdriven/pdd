import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { Part5CompoundReturns01SectionTitleCard } from "../Part5CompoundReturns01SectionTitleCard";
import { Part5CompoundReturns02MaintenancePieChart } from "../Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "../Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "../Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "../Part5CompoundReturns05InvestmentComparisonTable";
import { Part5CompoundReturns06SockCallbackSplit } from "../Part5CompoundReturns06SockCallbackSplit";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "../Part5CompoundReturns07EconomicsCrossingCallback";
import { Part5CompoundReturns08ContrarianQuoteCard } from "../Part5CompoundReturns08ContrarianQuoteCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part5CompoundReturns01SectionTitleCard,
  "02_maintenance_pie_chart": Part5CompoundReturns02MaintenancePieChart,
  "03_compound_debt_curve": Part5CompoundReturns03CompoundDebtCurve,
  "04_diverging_cost_curves": Part5CompoundReturns04DivergingCostCurves,
  "05_investment_comparison_table": Part5CompoundReturns05InvestmentComparisonTable,
  "06_sock_callback_split": Part5CompoundReturns06SockCallbackSplit,
  "07_economics_crossing_callback": Part5CompoundReturns07EconomicsCrossingCallback,
  "08_contrarian_quote_card": Part5CompoundReturns08ContrarianQuoteCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "02_maintenance_pie_chart": 420,
  "03_compound_debt_curve": 360,
  "04_diverging_cost_curves": 420,
  "05_investment_comparison_table": 420,
  "06_sock_callback_split": 360,
  "07_economics_crossing_callback": 300,
  "08_contrarian_quote_card": 300,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "09_grandmother_realization": { defaultSrc: "veo/grandmother_realization.mp4", backgroundSrc: "veo/grandmother_realization.mp4", outputSrc: "veo/grandmother_realization.mp4", baseSrc: "veo/grandmother_realization.mp4" },
  "10_developer_prompt_shift": { defaultSrc: "veo/developer_prompt_shift.mp4", backgroundSrc: "veo/developer_prompt_shift.mp4", outputSrc: "veo/developer_prompt_shift.mp4", baseSrc: "veo/developer_prompt_shift.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "06_sock_callback_split": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 5, "sectionLabel": "PART 5", "titleLine1": "COMPOUND", "titleLine2": "RETURNS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "exponential_curve", "color": "#D9944A", "component": "debt_growth"}, {"shape": "flat_curve", "color": "#4A90D9", "component": "pdd_flat"}], "narrationSegments": ["part5_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "animated_chart", "chartId": "maintenance_pie", "chartType": "donut", "segments": [{"label": "Initial Development", "percentage": [10, 20], "color": "#4A90D9"}, {"label": "Maintenance", "percentage": [80, 90], "color": "#D9944A"}], "researchCallouts": [{"source": "McKinsey Digital, 2024", "stat": "+40% maintenance cost", "context": "organizations with high technical debt"}, {"source": "Stripe Developer Coefficient, 2018", "stat": "33% of work week", "context": "spent on technical debt"}], "backgroundColor": "#0F172A", "narrationSegments": ["part5_002"]}, "overlayConfig": null, "renderMode": "component"},
  "03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "animated_chart", "chartId": "compound_debt_curve", "curves": [{"name": "Technical Debt (exponential)", "color": "#D9944A", "formula": "Debt × (1 + Rate)^Time", "dataPoints": [{"x": 1, "y": 1.0}, {"x": 2, "y": 1.4}, {"x": 3, "y": 2.1}, {"x": 5, "y": 4.2}, {"x": 7, "y": 8.5}, {"x": 10, "y": 24.0}]}, {"name": "Regeneration cost (sawtooth)", "color": "#4A90D9", "pattern": "sawtooth", "baseline": 1.0, "peakHeight": 1.5, "resetCycles": 5}], "callout": {"stat": "$1.52T", "context": "annual US tech debt cost", "source": "CISQ, 2022"}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_003"]}, "overlayConfig": null, "renderMode": "component"},
  "04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "animated_chart", "chartId": "diverging_cost_curves", "xAxis": {"label": "Time (years)", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost", "range": [0, 25]}, "series": [{"name": "Patching", "color": "#D9944A", "pattern": "exponential", "dataPoints": [{"x": 0, "y": 1.0}, {"x": 1, "y": 1.5}, {"x": 2, "y": 2.3}, {"x": 3, "y": 3.5}, {"x": 4, "y": 5.5}, {"x": 5, "y": 8.5}, {"x": 6, "y": 12.0}, {"x": 7, "y": 16.0}, {"x": 8, "y": 20.0}, {"x": 10, "y": 24.0}], "annotation": "Each patch adds debt"}, {"name": "PDD", "color": "#4A90D9", "pattern": "flat_declining", "dataPoints": [{"x": 0, "y": 1.0}, {"x": 1, "y": 1.1}, {"x": 2, "y": 1.0}, {"x": 3, "y": 0.95}, {"x": 5, "y": 0.85}, {"x": 7, "y": 0.8}, {"x": 10, "y": 0.75}], "annotation": "Each test constrains all future generations"}], "gapLabel": "The compounding gap", "origin": {"x": 0, "y": 1.0, "label": "Today"}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_004"]}, "overlayConfig": null, "renderMode": "component"},
  "05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "chartId": "investment_comparison", "columns": ["Investment", "Patching", "PDD"], "rows": [{"investment": "Fix a bug", "icon": "bug", "patching": "One place, once", "pdd": "Impossible forever", "pddGlowIntensity": 0.04}, {"investment": "Improve code", "icon": "code_arrow", "patching": "One version", "pdd": "All future versions", "pddGlowIntensity": 0.06}, {"investment": "Document intent", "icon": "document", "patching": "One snapshot", "pdd": "Living specification", "pddGlowIntensity": 0.08}], "summary": "One side compounds against you. The other compounds for you.", "colors": {"patching": "#D9944A", "pdd": "#4A90D9", "text": "#E2E8F0"}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_005"]}, "overlayConfig": null, "renderMode": "component"},
  "06_sock_callback_split": {"specBaseName": "06_sock_callback_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "1960", "content": "grandmother_callback_veo", "colorGrade": {"color": "#D4A043", "opacity": 0.04}, "caption": "The economics made it rational.", "crossedOutIcon": "darning_needle", "background": "#000000"}, "rightPanel": {"label": "NOW", "content": "developer_callback_veo", "colorGrade": {"color": "#4A90D9", "opacity": 0.03}, "caption": "Until now, the economics made it rational.", "crossedOutIcon": "patch", "background": "#000000"}, "sharedMoment": {"type": "realization_flash", "frame": 180, "peakOpacity": 0.03}, "embeddedVeoClips": ["grandmother_callback", "developer_callback"], "backgroundColor": "#000000", "narrationSegments": ["part5_006"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "07_economics_crossing_callback": {"specBaseName": "07_economics_crossing_callback", "dataPoints": {"type": "animated_chart", "chartId": "economics_crossing_callback", "callback_from": "sock_economics", "morphSequence": {"initial": {"xRange": [1950, 2020], "line1": {"label": "Labor cost (per hour)", "color": "#D9944A"}, "line2": {"label": "Sock cost", "color": "#4A90D9"}, "crossingYear": 1962, "crossingLabel": "The Threshold"}, "final": {"xRange": [2020, 2030], "line1": {"label": "Patching cost (per fix)", "color": "#D9944A"}, "line2": {"label": "Generation cost", "color": "#4A90D9"}, "crossingYear": 2024, "crossingLabel": "Now"}}, "punchlineIcon": {"type": "darning_needle_strikethrough", "position": [1400, 600]}, "backgroundColor": "#0F172A", "narrationSegments": ["part5_007"]}, "overlayConfig": null, "renderMode": "component"},
  "08_contrarian_quote_card": {"specBaseName": "08_contrarian_quote_card", "dataPoints": {"type": "quote_card", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time", "highlightedPhrases": [{"text": "the way of the future", "color": "#4A90D9", "sentiment": "positive"}, {"text": "crash and burn", "color": "#D9944A", "sentiment": "negative"}, {"text": "spectacularly", "color": "#D9944A", "sentiment": "negative_emphasis"}], "reframe": "He's right — it's a contrarian bet. But the economics are on our side.", "reframeHighlight": {"word": "economics", "color": "#4A90D9"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_008"]}, "overlayConfig": null, "renderMode": "component"},
  "09_grandmother_realization": {"specBaseName": "09_grandmother_realization", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_realization", "characters": [{"id": "grandmother", "label": "Grandmother", "referencePrompt": "Elderly woman with weathered hands, 1950s domestic setting, warm amber lamplight, same character from cold open darning sequence"}], "camera": {"framing": "close_up", "movement": "static", "dof": "shallow", "drift": false}, "lighting": {"key": {"color": "#D4A043", "position": "upper_left", "type": "practical_lamp"}, "fill": "minimal", "grade": "warm_sepia"}, "embeddedIn": "06_sock_callback_split", "panel": "left", "narrationSegments": ["part5_006a"], "narrationTimingSeconds": {"start": 1318.0, "end": 1324.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "10_developer_prompt_shift": {"specBaseName": "10_developer_prompt_shift", "dataPoints": {"type": "veo_clip", "clipId": "developer_prompt_shift", "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Modern software developer at desk with large monitor, dark room lit by screen glow, mechanical keyboard, minimal home office setup"}], "camera": {"framing": "medium_close_up", "movement": "static", "dof": "moderate", "drift": false}, "lighting": {"key": {"color": "#B8D4E8", "position": "front", "type": "monitor_glow"}, "fill": "minimal_ambient", "grade": "cool_blue"}, "screenContent": {"initial": "cursor_ide_diff_view", "final": "prompt_md_file_with_pdd_generate"}, "embeddedIn": "06_sock_callback_split", "panel": "right", "narrationSegments": ["part5_006b"], "narrationTimingSeconds": {"start": 1324.0, "end": 1330.0}}, "overlayConfig": null, "renderMode": "raw-media"},
};

export const Part5CompoundReturnsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 115.08;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part5_compound_returns/narration.wav")} />
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

export default Part5CompoundReturnsSection;
