import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part5CompoundReturns02MaintenancePieChart } from "../Part5CompoundReturns02MaintenancePieChart";
import { Part5CompoundReturns03CompoundDebtCurve } from "../Part5CompoundReturns03CompoundDebtCurve";
import { Part5CompoundReturns04DivergingCostCurves } from "../Part5CompoundReturns04DivergingCostCurves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "../Part5CompoundReturns05InvestmentComparisonTable";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "02_maintenance_pie_chart": Part5CompoundReturns02MaintenancePieChart,
  "03_compound_debt_curve": Part5CompoundReturns03CompoundDebtCurve,
  "04_diverging_cost_curves": Part5CompoundReturns04DivergingCostCurves,
  "05_investment_comparison_table": Part5CompoundReturns05InvestmentComparisonTable,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "02_maintenance_pie_chart": 420,
  "03_compound_debt_curve": 360,
  "04_diverging_cost_curves": 420,
  "05_investment_comparison_table": 420,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "06_veo_grandmother_socks_callback": { defaultSrc: "veo/grandmother_socks_callback.mp4", backgroundSrc: "veo/grandmother_socks_callback.mp4", outputSrc: "veo/grandmother_socks_callback.mp4", baseSrc: "veo/grandmother_socks_callback.mp4" },
  "07_veo_developer_cursor_callback": { defaultSrc: "veo/developer_cursor_callback.mp4", backgroundSrc: "veo/developer_cursor_callback.mp4", outputSrc: "veo/developer_cursor_callback.mp4", baseSrc: "veo/developer_cursor_callback.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 62 },
  "02_maintenance_pie_chart": { fadeInFrames: 120 },
  "04_diverging_cost_curves": { gradientOverlay: "bottom" },
  "05_investment_comparison_table": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 5, "sectionLabel": "PART 5", "titleLine1": "COMPOUND", "titleLine2": "RETURNS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "diverging_curves", "colors": ["#D9944A", "#5AAA6E"], "role": "compound_cost_preview"}], "narrationSegments": ["part5_compound_returns_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 62}, "renderMode": "component"},
  "02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": {"type": "pie_chart", "chartId": "maintenance_cost_split", "segments": [{"id": "maintenance", "label": "Maintenance", "percentage": "80-90%", "color": "#D9944A", "degrees": 306}, {"id": "initial_development", "label": "Initial Development", "percentage": "10-20%", "color": "#4A90D9", "degrees": 54}], "statistics": [{"source": "McKinsey", "finding": "40% more on maintenance with high technical debt"}, {"source": "Stripe", "finding": "1/3 of developer work week lost to debt"}, {"source": "CISQ", "finding": "$1.52 trillion annually in US"}], "narrationSegments": ["part5_compound_returns_001"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 120}, "renderMode": "component"},
  "03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": {"type": "dual_curve_chart", "chartId": "compound_debt_vs_regeneration", "xAxis": {"label": "Time (maintenance cycles)", "range": [0, 20]}, "yAxis": {"label": "Cumulative Cost"}, "series": [{"id": "debt_exponential", "label": "Debt × (1 + Rate)^Time", "color": "#D9944A", "type": "exponential", "data": [{"x": 0, "y": 0.05}, {"x": 2, "y": 0.07}, {"x": 4, "y": 0.1}, {"x": 6, "y": 0.14}, {"x": 8, "y": 0.2}, {"x": 10, "y": 0.3}, {"x": 12, "y": 0.42}, {"x": 14, "y": 0.58}, {"x": 16, "y": 0.72}, {"x": 18, "y": 0.85}, {"x": 20, "y": 0.95}]}, {"id": "regeneration_flat", "label": "Regeneration cost (debt resets each cycle)", "color": "#5AAA6E", "type": "flat", "data": [{"x": 0, "y": 0.08}, {"x": 20, "y": 0.08}]}], "annotations": [{"type": "callout", "text": "$1.52 trillion/year", "source": "CISQ", "position": "steep_section"}], "narrationSegments": ["part5_compound_returns_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": {"type": "diverging_curves", "chartId": "patching_vs_pdd_compounding", "xAxis": {"label": "Time (years)", "range": [0, 10]}, "yAxis": {"label": "Cumulative Cost"}, "series": [{"id": "patching_exponential", "label": "Patching", "color": "#D9944A", "type": "exponential", "data": [{"x": 0, "y": 0.1}, {"x": 1, "y": 0.13}, {"x": 2, "y": 0.17}, {"x": 3, "y": 0.23}, {"x": 4, "y": 0.31}, {"x": 5, "y": 0.42}, {"x": 6, "y": 0.55}, {"x": 7, "y": 0.68}, {"x": 8, "y": 0.8}, {"x": 9, "y": 0.88}, {"x": 10, "y": 0.95}]}, {"id": "pdd_flat", "label": "PDD", "color": "#5AAA6E", "type": "flat_sawtooth", "baseline": 0.1, "sawtoothAmplitude": 0.03, "data": [{"x": 0, "y": 0.1}, {"x": 1, "y": 0.1}, {"x": 2, "y": 0.1}, {"x": 3, "y": 0.1}, {"x": 4, "y": 0.1}, {"x": 5, "y": 0.1}, {"x": 6, "y": 0.1}, {"x": 7, "y": 0.1}, {"x": 8, "y": 0.1}, {"x": 9, "y": 0.1}, {"x": 10, "y": 0.1}]}], "gap": {"label": "The Gap", "gradient": {"top": "#D9944A", "bottom": "#5AAA6E"}}, "thesisStatements": [{"text": "Patching accrues compound costs.", "color": "#D9944A"}, {"text": "Tests accrue compound returns.", "color": "#5AAA6E"}], "narrationSegments": ["part5_compound_returns_003"]}, "mediaAliases": {}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": {"type": "comparison_table", "chartId": "investment_patching_vs_pdd", "columns": ["Investment", "Patching", "PDD"], "columnColors": ["#E2E8F0", "#D9944A", "#5AAA6E"], "rows": [{"investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever"}, {"investment": "Improve code", "patching": "One version", "pdd": "All future versions"}, {"investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification"}], "narrationSegments": ["part5_compound_returns_004"]}, "mediaAliases": {}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "06_veo_grandmother_socks_callback": {"specBaseName": "06_veo_grandmother_socks_callback", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_socks_callback", "durationSeconds": 6, "characters": [{"id": "grandmother", "label": "1950s Grandmother", "referencePrompt": "Elderly woman in 1950s domestic setting, warm lamplight, wooden chair, period-appropriate clothing and furnishings"}]}, "mediaAliases": {"defaultSrc": "veo/grandmother_socks_callback.mp4", "backgroundSrc": "veo/grandmother_socks_callback.mp4", "outputSrc": "veo/grandmother_socks_callback.mp4", "baseSrc": "veo/grandmother_socks_callback.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_veo_developer_cursor_callback": {"specBaseName": "07_veo_developer_cursor_callback", "dataPoints": {"type": "veo_clip", "clipId": "developer_cursor_callback", "durationSeconds": 6, "characters": [{"id": "developer", "label": "Modern Developer", "referencePrompt": "Software developer at modern desk with large monitor showing code editor, cool blue-white lighting, mechanical keyboard, minimalist workspace"}]}, "mediaAliases": {"defaultSrc": "veo/developer_cursor_callback.mp4", "backgroundSrc": "veo/developer_cursor_callback.mp4", "outputSrc": "veo/developer_cursor_callback.mp4", "baseSrc": "veo/developer_cursor_callback.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_economics_crossing_callback": {"specBaseName": "08_economics_crossing_callback", "dataPoints": {"type": "chart_callback", "chartRef": "code_cost_generate_vs_patch", "sourceSpec": "part1_economics/13_crossing_lines_moment", "crossingPoint": {"id": "generate_crosses_immediate", "year": 2025.6, "pulse": true}, "reframeText": "The economics changed.", "narrationSegments": ["part5_compound_returns_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_contrarian_quote_card": {"specBaseName": "09_contrarian_quote_card", "dataPoints": {"type": "quote_card", "quote": "This is either the way of the future or it's going to crash and burn spectacularly.", "attribution": "Research engineer, after seeing PDD for the first time.", "backgroundColor": "#0A0F1A", "accentWord": "spectacularly", "accentGlow": {"color": "#D9944A", "opacity": 0.03}, "narrationSegments": ["part5_compound_returns_007", "part5_compound_returns_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const Part5CompoundReturnsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 119.18;
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
