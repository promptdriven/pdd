import React from "react";
import { Sequence } from "remotion";

import { Part4PrecisionTradeoff01SectionTitleCard } from "../01_section_title_card";
import { Part4PrecisionTradeoff02PrinterVsMoldSplit } from "../02_printer_vs_mold_split";
import { Part4PrecisionTradeoff03PrecisionTradeoffCurve } from "../03_precision_tradeoff_curve";
import { Part4PrecisionTradeoff04PromptComparisonSplit } from "../04_prompt_comparison_split";
import { Part4PrecisionTradeoff05TestAccumulationInsight } from "../05_test_accumulation_insight";
import { Part4PrecisionTradeoff06TakeawayCallout } from "../06_takeaway_callout";
import { Part4PrecisionTradeoff07EmbeddedCodeDocument } from "../07_embedded_code_document";
import { Part4PrecisionTradeoff08PromptCodeSpectrum } from "../08_prompt_code_spectrum";

export const Part4PrecisionTradeoffSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 573.2392090000001;
  const durationSeconds = 112.000667;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Part4PrecisionTradeoff01SectionTitleCard />
      <Part4PrecisionTradeoff02PrinterVsMoldSplit />
      <Part4PrecisionTradeoff03PrecisionTradeoffCurve />
      <Part4PrecisionTradeoff04PromptComparisonSplit />
      <Part4PrecisionTradeoff05TestAccumulationInsight />
      <Part4PrecisionTradeoff06TakeawayCallout />
      <Part4PrecisionTradeoff07EmbeddedCodeDocument />
      <Part4PrecisionTradeoff08PromptCodeSpectrum />
    </Sequence>
  );
};

export default Part4PrecisionTradeoffSection;
