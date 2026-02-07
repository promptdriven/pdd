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
import { PieChart, defaultPieChartProps } from "../12-PieChart";
import { PieToCurve, defaultPieToCurveProps } from "../13-PieToCurve";
import { SockPriceChart, defaultSockPriceChartProps } from "../02-SockPriceChart";
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
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <SockPriceChart {...defaultSockPriceChartProps} />
        </Sequence>
      )}

      {/* Visual 1: ThresholdHighlight - In 1950 wool sock cost real money, darning made se */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <ThresholdHighlight {...defaultThresholdHighlightProps} />
        </Sequence>
      )}

      {/* Visual 2: LinesDiverge - Mid-1960s math flipped, darning became irrational */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <LinesDiverge {...defaultLinesDivergeProps} />
        </Sequence>
      )}

      {/* Visual 3: CodeCostChart - Now look at code */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <CodeCostChart {...defaultCodeCostChartProps} />
        </Sequence>
      )}

      {/* Visual 4: AIMilestones - For decades generating expensive, you patched, rat */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <AIMilestones {...defaultAIMilestonesProps} />
        </Sequence>
      )}

      {/* Visual 5: CodeCostChart - AI made patching faster too, Cursor Claude Copilot */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START} durationInFrames={BEATS.VISUAL_05_END - BEATS.VISUAL_05_START}>
          <CodeCostChart {...defaultCodeCostChartProps} />
        </Sequence>
      )}

      {/* Visual 6: CodeCostChartMini - Each patch getting faster, that's real, you feel i */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START} durationInFrames={BEATS.VISUAL_06_END - BEATS.VISUAL_06_START}>
          <CodeCostChartMini {...defaultCodeCostChartMiniProps} />
        </Sequence>
      )}

      {/* Visual 7: CrossingPoint - But watch dashed line, debt accumulates faster */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START} durationInFrames={BEATS.VISUAL_07_END - BEATS.VISUAL_07_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 8: CrossingPoint - GitHub 55% speedup, Uplevel 800 devs no change */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START} durationInFrames={BEATS.VISUAL_08_END - BEATS.VISUAL_08_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 9: CrossingPoint - GitClear 44% churn, refactoring -60%, piling on */}
      {activeVisual === 9 && (
        <Sequence from={BEATS.VISUAL_09_START} durationInFrames={BEATS.VISUAL_09_END - BEATS.VISUAL_09_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 10: ContextRot - Something else hiding in debt, AI-specific */}
      {activeVisual === 10 && (
        <Sequence from={BEATS.VISUAL_10_START} durationInFrames={BEATS.VISUAL_10_END - BEATS.VISUAL_10_START}>
          <ContextRot {...defaultContextRotProps} />
        </Sequence>
      )}

      {/* Visual 11: ContextRot - Small codebase AI brilliant, context covers everyt */}
      {activeVisual === 11 && (
        <Sequence from={BEATS.VISUAL_11_START} durationInFrames={BEATS.VISUAL_11_END - BEATS.VISUAL_11_START}>
          <ContextRot {...defaultContextRotProps} />
        </Sequence>
      )}

      {/* Visual 12: ContextRot - Codebases grow, window stays same, millions of tok */}
      {activeVisual === 12 && (
        <Sequence from={BEATS.VISUAL_12_START} durationInFrames={BEATS.VISUAL_12_END - BEATS.VISUAL_12_START}>
          <ContextRot {...defaultContextRotProps} />
        </Sequence>
      )}

      {/* Visual 13: ContextRot - AI guesses relevance, vector search fails, agentic */}
      {activeVisual === 13 && (
        <Sequence from={BEATS.VISUAL_13_START} durationInFrames={BEATS.VISUAL_13_END - BEATS.VISUAL_13_START}>
          <ContextRot {...defaultContextRotProps} />
        </Sequence>
      )}

      {/* Visual 14: ContextRot - EMNLP: performance degrades with length, context r */}
      {activeVisual === 14 && (
        <Sequence from={BEATS.VISUAL_14_START} durationInFrames={BEATS.VISUAL_14_END - BEATS.VISUAL_14_START}>
          <ContextRot {...defaultContextRotProps} />
        </Sequence>
      )}

      {/* Visual 15: CrossingPoint - AI patching two stories, small codebase transforma */}
      {activeVisual === 15 && (
        <Sequence from={BEATS.VISUAL_15_START} durationInFrames={BEATS.VISUAL_15_END - BEATS.VISUAL_15_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 16: CrossingPoint - Large codebase 19% slower, 39-point perception gap */}
      {activeVisual === 16 && (
        <Sequence from={BEATS.VISUAL_16_START} durationInFrames={BEATS.VISUAL_16_END - BEATS.VISUAL_16_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 17: CrossingPoint - Every patch makes codebase bigger, pushes to worse */}
      {activeVisual === 17 && (
        <Sequence from={BEATS.VISUAL_17_START} durationInFrames={BEATS.VISUAL_17_END - BEATS.VISUAL_17_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 18: Veo clip - Regeneration no problem, prompt fits, no retrieval */}
      {activeVisual === 18 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("veo_developer_edit.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 19: Veo clip - NL is models deepest fluency, 250 lines lowest def */}
      {activeVisual === 19 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("veo_developer_edit.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 20: CrossingPoint - Generation crossed below both lines, debt resets */}
      {activeVisual === 20 && (
        <Sequence from={BEATS.VISUAL_20_START} durationInFrames={BEATS.VISUAL_20_END - BEATS.VISUAL_20_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}

      {/* Visual 21: Veo clip - Best darning needles ever, still accumulation */}
      {activeVisual === 21 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 22: PieChart - 80-90% cost is maintenance, McKinsey Stripe tech d */}
      {activeVisual === 22 && (
        <Sequence from={BEATS.VISUAL_22_START} durationInFrames={BEATS.VISUAL_22_END - BEATS.VISUAL_22_START}>
          <PieChart {...defaultPieChartProps} />
        </Sequence>
      )}

      {/* Visual 23: PieToCurve - Costs compound literally, unless you regenerate */}
      {activeVisual === 23 && (
        <Sequence from={BEATS.VISUAL_23_START} durationInFrames={BEATS.VISUAL_23_END - BEATS.VISUAL_23_START}>
          <PieToCurve {...defaultPieToCurveProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
