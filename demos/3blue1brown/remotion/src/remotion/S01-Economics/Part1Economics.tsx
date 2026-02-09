import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part1EconomicsPropsType } from "./constants";
import { AIMilestones, defaultAIMilestonesProps } from "../06-AIMilestones";
import { CodeCostChart, defaultCodeCostChartProps } from "../05-CodeCostChart";
import { CodeCostChartMini, defaultCodeCostChartMiniProps } from "../05a-CodeCostChartMini";
import { ContextRot, defaultContextRotProps } from "../07-ContextRot";
import { CrossingPoint, defaultCrossingPointProps } from "../08-CrossingPoint";
import { LinesDiverge, defaultLinesDivergeProps } from "../04-LinesDiverge";
import { ContextWindowComparison } from "../14a-ContextWindowComparison";
import { PieChart, defaultPieChartProps } from "../12-PieChart";
import { PieToCurve, defaultPieToCurveProps } from "../13-PieToCurve";
import { SockPriceChart, defaultSockPriceChartProps } from "../02-SockPriceChart";
import { PatchCycle, defaultPatchCycleProps } from "../10-PatchCycle";
import { ThresholdHighlight, defaultThresholdHighlightProps } from "../03-ThresholdHighlight";

export const Part1Economics: React.FC<Part1EconomicsPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      {/* Narration audio */}
      <Audio src={staticFile("part1_economics_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: SockPriceChart - This isn't nostalgia, it's economics */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <SockPriceChart {...defaultSockPriceChartProps} />
        </Sequence>
      )}

      {/* Visual 1: ThresholdHighlight - In 1950 wool sock cost real money, darning made se */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <ThresholdHighlight {...defaultThresholdHighlightProps} />
        </Sequence>
      )}

      {/* Visual 2: LinesDiverge - Mid-1960s math flipped, darning became irrational */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <LinesDiverge {...defaultLinesDivergeProps} />
        </Sequence>
      )}

      {/* Visual 3: CodeCostChart - Now look at code */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <Sequence from={-540}>
            <CodeCostChart {...defaultCodeCostChartProps} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 4: AIMilestones - For decades generating expensive, you patched, rat */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <AIMilestones {...defaultAIMilestonesProps} />
        </Sequence>
      )}

      {/* Visual 5: CodeCostChart - AI made patching faster too, Cursor Claude Copilot */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <Sequence from={-1800}>
            <CodeCostChart {...defaultCodeCostChartProps} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 6: CodeCostChartMini - Each patch getting faster, that's real, you feel i */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <Sequence from={-938}>
            <CodeCostChartMini {...defaultCodeCostChartMiniProps} showAudio={false} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 7: CrossingPoint - But watch dashed line, debt accumulates faster */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 8: CrossingPoint - GitHub 55% speedup, Uplevel 800 devs no change */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START}>
          <CrossingPoint {...defaultCrossingPointProps} startAtFullView={true} />
        </Sequence>
      )}

      {/* Visual 9: CrossingPoint - GitClear 44% churn, refactoring -60%, piling on */}
      {activeVisual === 9 && (
        <Sequence from={BEATS.VISUAL_09_START}>
          <CrossingPoint {...defaultCrossingPointProps} startAtFullView={true} />
        </Sequence>
      )}

      {/* Visual 10: ContextRot - Something else hiding in debt, AI-specific */}
      {activeVisual === 10 && (
        <Sequence from={BEATS.VISUAL_10_START}>
          <ContextRot {...defaultContextRotProps} />
        </Sequence>
      )}

      {/* Visual 11: ContextRot - Small codebase AI brilliant, context covers everyt */}
      {activeVisual === 11 && (
        <Sequence from={BEATS.VISUAL_11_START}>
          <Sequence from={-240}>
            <ContextRot {...defaultContextRotProps} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 12: ContextRot - Codebases grow, window stays same, millions of tok */}
      {activeVisual === 12 && (
        <Sequence from={BEATS.VISUAL_12_START}>
          <Sequence from={-630}>
            <ContextRot {...defaultContextRotProps} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 13: ContextRot - AI guesses relevance, vector search fails, agentic */}
      {activeVisual === 13 && (
        <Sequence from={BEATS.VISUAL_13_START}>
          <Sequence from={-870}>
            <ContextRot {...defaultContextRotProps} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 14: ContextRot - EMNLP: performance degrades with length, context r */}
      {activeVisual === 14 && (
        <Sequence from={BEATS.VISUAL_14_START}>
          <Sequence from={-1350}>
            <ContextRot {...defaultContextRotProps} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 15: CrossingPoint - AI patching two stories, small codebase transforma */}
      {activeVisual === 15 && (
        <Sequence from={BEATS.VISUAL_15_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 16: CrossingPoint - Large codebase 19% slower, 39-point perception gap */}
      {activeVisual === 16 && (
        <Sequence from={BEATS.VISUAL_16_START}>
          <CrossingPoint {...defaultCrossingPointProps} startAtFullView={true} />
        </Sequence>
      )}

      {/* Visual 17: PatchCycle - Every patch makes codebase bigger, pushes to worse */}
      {activeVisual === 17 && (
        <Sequence from={BEATS.VISUAL_17_START}>
          <PatchCycle {...defaultPatchCycleProps} />
        </Sequence>
      )}

      {/* Visual 18: Veo clip - Regeneration no problem, prompt fits, no retrieval */}
      {activeVisual === 18 && (
        <Sequence from={BEATS.VISUAL_18_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("veo_developer_edit.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 19: ContextWindowComparison - NL is models deepest fluency, room to think */}
      {activeVisual === 19 && (
        <Sequence from={BEATS.VISUAL_19_START}>
          <ContextWindowComparison variant="efficiency" showKnowledgeIndicator={true} />
        </Sequence>
      )}

      {/* Visual 20: CrossingPoint - Generation crossed below both lines, debt resets */}
      {activeVisual === 20 && (
        <Sequence from={BEATS.VISUAL_20_START}>
          <CrossingPoint {...defaultCrossingPointProps} showOverlayText={true} />
        </Sequence>
      )}

      {/* Visual 21: Veo clip - Best darning needles ever, still accumulation */}
      {activeVisual === 21 && (
        <Sequence from={BEATS.VISUAL_21_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("07_split_screen_sepia.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 22: PieChart - 80-90% cost is maintenance, McKinsey Stripe tech d */}
      {activeVisual === 22 && (
        <Sequence from={BEATS.VISUAL_22_START}>
          <Sequence from={-120}>
            <PieChart {...defaultPieChartProps} />
          </Sequence>
        </Sequence>
      )}

      {/* Visual 23: PieToCurve - Costs compound literally, unless you regenerate */}
      {activeVisual === 23 && (
        <Sequence from={BEATS.VISUAL_23_START}>
          <Sequence from={-90}>
            <PieToCurve {...defaultPieToCurveProps} />
          </Sequence>
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
