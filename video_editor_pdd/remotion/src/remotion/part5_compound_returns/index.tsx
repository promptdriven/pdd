import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part5CompoundReturns04DivergingCostCurves } from "../Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "../Part5CompoundReturns05InvestmentComparisonTable";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "../Part5CompoundReturns07EconomicsCrossingCallback";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "04_diverging_cost_curves": Part5CompoundReturns04DivergingCostCurves,
  "05_investment_comparison_table": Part5CompoundReturns05InvestmentComparisonTable,
  "08_economics_crossing_callback": Part5CompoundReturns07EconomicsCrossingCallback,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "04_diverging_cost_curves": 420,
  "05_investment_comparison_table": 420,
  "08_economics_crossing_callback": 300,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "06_grandmother_socks_callback": { defaultSrc: "veo/grandmother_darning_lamplight.mp4", backgroundSrc: "veo/grandmother_darning_lamplight.mp4", outputSrc: "veo/grandmother_darning_lamplight.mp4", baseSrc: "veo/grandmother_darning_lamplight.mp4" },
  "07_developer_cursor_callback": { defaultSrc: "veo/developer_cursor_edit.mp4", backgroundSrc: "veo/developer_cursor_edit.mp4", outputSrc: "veo/developer_cursor_edit.mp4", baseSrc: "veo/developer_cursor_edit.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "03_compound_debt_curve": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionId": "part5_compound_returns", "title": "COMPOUND RETURNS", "tagline": "Why the economics compound for you.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_001"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "pie_chart", "chartId": "maintenance_cost_pie", "slices": [{"label": "Maintenance", "range": "80-90%", "color": "#F59E0B", "pullOut": 8}, {"label": "Initial Development", "range": "10-20%", "color": "#4ADE80"}], "callouts": [{"text": "40% more on maintenance", "source": "McKinsey", "color": "#F59E0B"}, {"text": "⅓ of dev time on debt", "source": "Stripe", "color": "#F59E0B"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "animated_chart", "chartId": "compound_debt_curve", "morphFrom": "maintenance_cost_pie", "curves": [{"id": "debt_exponential", "formula": "base * (1 + 0.25)^x", "color": "#F59E0B", "strokeWidth": 3, "label": "Debt × (1 + Rate)^Time", "fill": true}, {"id": "regeneration_flat", "formula": "constant", "color": "#4ADE80", "strokeWidth": 2.5, "dashed": true, "label": "Regeneration cost (debt resets each cycle)"}], "stats": [{"value": "$1.52T", "label": "annually", "source": "CISQ", "color": "#F59E0B"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_003"]}, "mediaAliases": {}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "animated_chart", "chartId": "diverging_cost_curves", "curves": [{"id": "patching_exponential", "label": "Patching", "color": "#F59E0B", "type": "exponential", "direction": "up", "annotations": ["+debt", "+debt", "+debt", "+debt", "+debt"]}, {"id": "pdd_flat", "label": "PDD", "color": "#4ADE80", "type": "flat", "annotations": ["+test", "+test", "+test", "+test", "+test", "+test", "+test", "+test"]}], "xAxis": ["Now", "6 months", "1 year", "2 years", "5 years"], "pivotLabel": "Tests accrue compound returns", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_004", "part5_compound_returns_005"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "tableId": "investment_comparison", "columns": ["Investment", "Patching", "PDD"], "columnColors": ["#E2E8F0", "#F59E0B", "#4ADE80"], "rows": [{"investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever"}, {"investment": "Improve code", "patching": "One version", "pdd": "All future versions"}, {"investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_grandmother_socks_callback": {"specBaseName": "06_grandmother_socks_callback", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_socks_callback", "camera": {"framing": "medium_close_up", "movement": "static", "dof": "moderate", "drift": false}, "lighting": {"key": {"color": "#D4A043", "position": "upper_left", "type": "table_lamp"}, "fill": "minimal", "grade": "warm_amber"}, "characters": [{"id": "grandmother_darner", "label": "Grandmother", "referencePrompt": "Elderly woman with weathered skilled hands, domestic setting, warm lamplight"}], "callbackTo": "part1_economics/14_grandmother_darning_expert", "narrationSegments": ["part5_compound_returns_007"]}, "mediaAliases": {"defaultSrc": "veo/grandmother_darning_lamplight.mp4", "backgroundSrc": "veo/grandmother_darning_lamplight.mp4", "outputSrc": "veo/grandmother_darning_lamplight.mp4", "baseSrc": "veo/grandmother_darning_lamplight.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_developer_cursor_callback": {"specBaseName": "07_developer_cursor_callback", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_callback", "camera": {"framing": "medium_close_up", "movement": "static", "dof": "shallow", "drift": false}, "lighting": {"key": {"color": "#B8D4E8", "position": "monitor", "type": "cool_blue"}, "fill": {"color": "#E8D5B8", "position": "side", "type": "ambient"}, "grade": "cool_professional"}, "callbackTo": "part1_economics/13_developer_cursor_coding", "narrationSegments": ["part5_compound_returns_008"]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_edit.mp4", "backgroundSrc": "veo/developer_cursor_edit.mp4", "outputSrc": "veo/developer_cursor_edit.mp4", "baseSrc": "veo/developer_cursor_edit.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_economics_crossing_callback": {"specBaseName": "08_economics_crossing_callback", "dataPoints": {"type": "chart_callback", "chartId": "code_cost_triple_line", "callbackTo": "part1_economics/11_crossing_lines_moment", "event": "crossing_reprise", "crossingPoint": {"radius": 12, "glowRadius": 24, "pulseRange": [0.85, 1.15], "pulsePeriod": 45}, "newAnnotation": "When economics change, rational behavior changes.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_contrarian_quote_card": {"specBaseName": "09_contrarian_quote_card", "dataPoints": {"type": "quote_card", "cardId": "contrarian_quote", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time", "accentColor": "#4A90D9", "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_010"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_transition_out": {"specBaseName": "10_transition_out", "dataPoints": {"type": "transition", "transitionId": "compound_returns_out", "echoes": [{"source": "diverging_cost_curves", "opacity": 0.08}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part5_compound_returns_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const Part5CompoundReturnsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 115.08;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

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

export default Part5CompoundReturnsSection;
