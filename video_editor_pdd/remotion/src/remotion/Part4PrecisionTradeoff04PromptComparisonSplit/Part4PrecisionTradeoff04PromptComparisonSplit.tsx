import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import {
  COLORS,
  CANVAS_WIDTH,
  SPLIT_X,
  LEFT_WIDTH,
  RIGHT_WIDTH,
  SANS_FONT,
  DENSE_PROMPT_LINES,
  MINIMAL_PROMPT_LINES,
  TEST_RESULTS,
  GENERATED_CODE_LINES,
} from './constants';
import SplitDivider from './SplitDivider';
import FileHeader from './FileHeader';
import ScrollingCode from './ScrollingCode';
import TerminalWindow from './TerminalWindow';
import CodeOutput from './CodeOutput';
import Badge from './Badge';

export const defaultPart4PrecisionTradeoff04PromptComparisonSplitProps = {};

export const Part4PrecisionTradeoff04PromptComparisonSplit: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel header fade-in (frames 0-20)
  const headerOpacity = interpolate(frame, [0, 20], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        overflow: 'hidden',
      }}
    >
      {/* ===== LEFT PANEL — Dense Prompt ===== */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: LEFT_WIDTH,
          height: 1080,
          backgroundColor: COLORS.leftPanelBg,
        }}
      >
        {/* Panel header: "FEW TESTS" */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 8,
            width: LEFT_WIDTH,
            textAlign: 'center',
            opacity: headerOpacity,
          }}
        >
          <span
            style={{
              fontFamily: SANS_FONT,
              fontSize: 14,
              fontWeight: 600,
              color: COLORS.leftAccent,
              letterSpacing: 2,
            }}
          >
            FEW TESTS
          </span>
        </div>

        {/* File header bar */}
        <FileHeader
          filename="parser_v1.prompt"
          x={0}
          y={30}
          width={LEFT_WIDTH}
          appearFrame={5}
        />

        {/* Scrolling dense prompt content */}
        <ScrollingCode
          lines={DENSE_PROMPT_LINES}
          x={0}
          y={62}
          width={LEFT_WIDTH}
          maxHeight={770}
          scrollSpeed={1.5}
          startFrame={20}
          showLineNumbers
        />

        {/* "50 lines" badge */}
        <Badge
          text="50 lines"
          color={COLORS.leftAccent}
          x={LEFT_WIDTH - 120}
          y={820}
          startFrame={90}
        />
      </div>

      {/* ===== SPLIT DIVIDER ===== */}
      <SplitDivider x={SPLIT_X} color={COLORS.splitLine} drawDuration={15} />

      {/* ===== RIGHT PANEL — Minimal Prompt + Tests ===== */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X + 2,
          top: 0,
          width: RIGHT_WIDTH,
          height: 1080,
          backgroundColor: COLORS.rightPanelBg,
        }}
      >
        {/* Panel header: "MANY TESTS" */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 8,
            width: RIGHT_WIDTH,
            textAlign: 'center',
            opacity: headerOpacity,
          }}
        >
          <span
            style={{
              fontFamily: SANS_FONT,
              fontSize: 14,
              fontWeight: 600,
              color: COLORS.rightAccent,
              letterSpacing: 2,
            }}
          >
            MANY TESTS
          </span>
        </div>

        {/* File header bar */}
        <FileHeader
          filename="parser_v2.prompt"
          x={0}
          y={30}
          width={RIGHT_WIDTH}
          appearFrame={5}
        />

        {/* Minimal prompt content (instant reveal, not scrolling) */}
        <ScrollingCode
          lines={MINIMAL_PROMPT_LINES}
          x={0}
          y={62}
          width={RIGHT_WIDTH}
          maxHeight={180}
          scrollSpeed={10}
          startFrame={20}
          showLineNumbers
        />

        {/* "10 lines" badge */}
        <Badge
          text="10 lines"
          color={COLORS.rightAccent}
          x={RIGHT_WIDTH - 120}
          y={240}
          startFrame={90}
        />

        {/* Terminal window with scrolling test results */}
        <TerminalWindow
          x={20}
          y={290}
          width={RIGHT_WIDTH - 40}
          height={540}
          command="pdd test parser"
          testResults={TEST_RESULTS}
          startFrame={150}
          scrollSpeed={3}
        />
      </div>

      {/* ===== BOTTOM — Identical Code Output ===== */}
      <CodeOutput
        codeLines={GENERATED_CODE_LINES}
        startFrame={330}
        y={870}
      />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff04PromptComparisonSplit;
