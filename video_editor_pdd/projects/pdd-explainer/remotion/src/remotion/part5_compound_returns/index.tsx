import React from "react";
import { Sequence } from "remotion";

import { Part5CompoundReturns01SectionTitleCard } from "../01_section_title_card";
import { Part5CompoundReturns02MaintenancePieChart } from "../02_maintenance_pie_chart";
import { Part5CompoundReturns03CompoundDebtCurve } from "../03_compound_debt_curve";
import { Part5CompoundReturns04DivergingCostCurves } from "../04_diverging_cost_curves";
import { Part5CompoundReturns05InvestmentComparisonTable } from "../05_investment_comparison_table";
import { Part5CompoundReturns06SockCallbackSplit } from "../06_sock_callback_split";
import { Part5CompoundReturns07EconomicsCrossingCallback } from "../07_economics_crossing_callback";
import { Part5CompoundReturns08ContrarianQuoteCard } from "../08_contrarian_quote_card";

export const Part5CompoundReturnsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 684.813208;
  const durationSeconds = 115.321625;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Part5CompoundReturns01SectionTitleCard />
      <Part5CompoundReturns02MaintenancePieChart />
      <Part5CompoundReturns03CompoundDebtCurve />
      <Part5CompoundReturns04DivergingCostCurves />
      <Part5CompoundReturns05InvestmentComparisonTable />
      <Part5CompoundReturns06SockCallbackSplit />
      <Part5CompoundReturns07EconomicsCrossingCallback />
      <Part5CompoundReturns08ContrarianQuoteCard />
    </Sequence>
  );
};

export default Part5CompoundReturnsSection;
