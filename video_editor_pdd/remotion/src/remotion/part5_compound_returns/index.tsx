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
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "09_grandmother_realization": { defaultSrc: "veo/grandmother_realization.mp4", backgroundSrc: "veo/grandmother_realization.mp4", outputSrc: "veo/grandmother_realization.mp4", baseSrc: "veo/grandmother_realization.mp4" },
  "10_developer_prompt_shift": { defaultSrc: "veo/developer_prompt_shift.mp4", backgroundSrc: "veo/developer_prompt_shift.mp4", outputSrc: "veo/developer_prompt_shift.mp4", baseSrc: "veo/developer_prompt_shift.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "06_sock_callback_split": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "02_maintenance_pie_chart": {"specBaseName": "02_maintenance_pie_chart", "dataPoints": null, "overlayConfig": null},
  "03_compound_debt_curve": {"specBaseName": "03_compound_debt_curve", "dataPoints": null, "overlayConfig": null},
  "04_diverging_cost_curves": {"specBaseName": "04_diverging_cost_curves", "dataPoints": null, "overlayConfig": null},
  "05_investment_comparison_table": {"specBaseName": "05_investment_comparison_table", "dataPoints": null, "overlayConfig": null},
  "06_sock_callback_split": {"specBaseName": "06_sock_callback_split", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "07_economics_crossing_callback": {"specBaseName": "07_economics_crossing_callback", "dataPoints": null, "overlayConfig": null},
  "08_contrarian_quote_card": {"specBaseName": "08_contrarian_quote_card", "dataPoints": null, "overlayConfig": null},
  "09_grandmother_realization": {"specBaseName": "09_grandmother_realization", "dataPoints": null, "overlayConfig": null},
  "10_developer_prompt_shift": {"specBaseName": "10_developer_prompt_shift", "dataPoints": null, "overlayConfig": null},
};

export const Part5CompoundReturnsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 115.392;
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

export default Part5CompoundReturnsSection;
