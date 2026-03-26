import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part5CompoundReturns02MaintenancePieChart } from "../Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "../Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "../Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "../Part5CompoundReturns05InvestmentComparisonTable";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "../Part5CompoundReturns07EconomicsCrossingCallback";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "02_maintenance_pie_chart": Part5CompoundReturns02MaintenancePieChart,
  "03_compound_debt_curve": Part5CompoundReturns03CompoundDebtCurve,
  "04_diverging_cost_curves": Part5CompoundReturns04DivergingCostCurves,
  "05_investment_comparison_table": Part5CompoundReturns05InvestmentComparisonTable,
  "08_economics_crossing_callback": Part5CompoundReturns07EconomicsCrossingCallback,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "02_maintenance_pie_chart": 420,
  "03_compound_debt_curve": 360,
  "04_diverging_cost_curves": 420,
  "05_investment_comparison_table": 420,
  "08_economics_crossing_callback": 300,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "06_grandmother_socks_callback": { defaultSrc: "veo/grandmother_socks_callback.mp4", backgroundSrc: "veo/grandmother_socks_callback.mp4", outputSrc: "veo/grandmother_socks_callback.mp4", baseSrc: "veo/grandmother_socks_callback.mp4" },
  "07_developer_cursor_callback": { defaultSrc: "veo/developer_cursor_callback.mp4", backgroundSrc: "veo/developer_cursor_callback.mp4", outputSrc: "veo/developer_cursor_callback.mp4", baseSrc: "veo/developer_cursor_callback.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 30 },
  "02_maintenance_pie_chart": { fadeInFrames: 90 },
  "04_diverging_cost_curves": { fadeInFrames: 45 },
  "09_contrarian_quote_card": { fadeOutFrames: 90 },
  "10_transition_out": { fadeOutFrames: 20 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionLabel": "PART 5", "title": "Compound Returns", "accentStyle": "exponential_curve", "accentColor": "#D9944A", "backgroundColor": "#0A0F1A", "durationSeconds": 8, "narrationSegments": ["part5_compound_returns_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 30}, "renderMode": "component"},
  "02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "animated_pie_chart", "center": [960, 460], "radius": 280, "wedges": [{"id": "initial_development", "label": "Initial Development", "value": "10-20%", "midpointPct": 15, "color": "#4A90D9", "sweepAngle": 54}, {"id": "maintenance", "label": "Maintenance", "value": "80-90%", "midpointPct": 85, "color": "#D9944A", "sweepAngle": 306}], "citations": ["McKinsey: +40% maintenance overhead from tech debt", "Stripe: 33% of dev week on debt"], "narrationSegments": ["part5_compound_returns_002"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 90}, "renderMode": "component"},
  "03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "animated_line_chart", "morphFrom": "maintenance_pie_chart", "xAxis": {"label": "Time (years)", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost", "range": [0, 100]}, "series": [{"id": "debt_curve", "label": "Debt × (1 + Rate)^Time", "color": "#D9944A", "formula": "C₀ × (1 + 0.3)^t", "data": [[0, 1], [1, 1.3], [2, 1.7], [3, 2.2], [4, 2.9], [5, 3.7], [6, 4.8], [7, 6.3], [8, 8.2], [9, 10.6], [10, 13.8]]}, {"id": "regeneration_line", "label": "Regeneration cost (resets each cycle)", "color": "#4A90D9", "style": "dashed", "data": [[0, 1], [2, 1.1], [4, 1.0], [6, 1.1], [8, 1.0], [10, 1.1]]}], "callout": {"value": "$1.52 trillion / year", "source": "US technical debt — CISQ", "anchorPoint": [8, 8.2]}, "narrationSegments": ["part5_compound_returns_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "diverging_line_chart", "xAxis": {"label": "Years", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost", "range": [0, 100]}, "series": [{"id": "patching_curve", "label": "Patching", "color": "#D9944A", "style": "solid", "data": [[0, 2], [1, 3], [2, 4.5], [3, 7], [4, 11], [5, 17], [6, 26], [7, 39], [8, 55], [9, 72], [10, 90]]}, {"id": "pdd_curve", "label": "PDD", "color": "#4A90D9", "style": "solid", "data": [[0, 2], [1, 3.5], [1.5, 2.2], [3, 3.8], [3.5, 2.3], [5, 3.9], [5.5, 2.2], [7, 3.7], [7.5, 2.1], [9, 3.6], [10, 4.0]]}], "annotations": [{"text": "Each patch adds debt", "anchorYear": 6, "target": "patching_curve"}, {"text": "Each test constrains forever", "anchorYear": 6, "target": "pdd_curve"}], "impactText": "Over time, it's everything.", "narrationSegments": ["part5_compound_returns_004", "part5_compound_returns_005", "part5_compound_returns_006"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 45}, "renderMode": "component"},
  "05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "columns": [{"id": "investment", "label": "Investment", "color": "#64748B"}, {"id": "patching", "label": "Patching", "color": "#D9944A"}, {"id": "pdd", "label": "PDD", "color": "#4A90D9"}], "rows": [{"investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever"}, {"investment": "Improve code", "patching": "One version", "pdd": "All future versions"}, {"investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification"}], "narrationSegments": ["part5_compound_returns_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_grandmother_socks_callback": {"specBaseName": "06_grandmother_socks_callback", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_socks_callback", "durationSeconds": 7, "characters": [{"id": "grandmother", "label": "Great-Grandmother", "referencePrompt": "An elderly woman in her 70s with silver hair pinned up, wearing a floral housedress and reading glasses on a chain. 1950s appearance, kind face, sitting in a cushioned armchair under warm lamplight."}], "narrationSegments": ["part5_compound_returns_007"]}, "mediaAliases": {"defaultSrc": "veo/grandmother_socks_callback.mp4", "backgroundSrc": "veo/grandmother_socks_callback.mp4", "outputSrc": "veo/grandmother_socks_callback.mp4", "baseSrc": "veo/grandmother_socks_callback.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_developer_cursor_callback": {"specBaseName": "07_developer_cursor_callback", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_callback", "durationSeconds": 6, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "A developer in their late 20s wearing a dark henley shirt, sitting at a modern desk with a mechanical keyboard and ultrawide monitor. Relaxed posture, warm desk lamp nearby."}], "narrationSegments": ["part5_compound_returns_008"]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_callback.mp4", "backgroundSrc": "veo/developer_cursor_callback.mp4", "outputSrc": "veo/developer_cursor_callback.mp4", "baseSrc": "veo/developer_cursor_callback.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_economics_crossing_callback": {"specBaseName": "08_economics_crossing_callback", "dataPoints": {"type": "callback_chart", "referencesSpec": "part1_economics/02_sock_price_chart", "crossingPoint": {"x": 1962, "y": 0.85}, "pulseEffect": {"rings": 3, "maxRadius": 100, "color": "#D9944A", "cycleDuration": 90}, "newLabel": "The economics changed.", "narrationSegments": ["part5_compound_returns_009"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_contrarian_quote_card": {"specBaseName": "09_contrarian_quote_card", "dataPoints": {"type": "quote_card", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time", "quoteFont": "Georgia", "quoteSize": 36, "accentColor": "#D9944A", "backgroundColor": "#0A0F1A", "durationSeconds": 18, "narrationSegments": ["part5_compound_returns_010"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 90}, "renderMode": "component"},
  "10_transition_out": {"specBaseName": "10_transition_out", "dataPoints": {"type": "transition_card", "text": "Now, you don't work on socks.", "backgroundColor": "#0A0F1A", "durationSeconds": 4, "narrationSegments": ["part5_compound_returns_011"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 20}, "renderMode": "generated-media"},
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
