import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  COLORS,
  CANVAS_WIDTH,
  PANEL_WIDTH,
  SPLIT_X,
  DENSE_PROMPT_LINES,
  MINIMAL_PROMPT_LINES,
  TEST_RESULTS,
} from './constants';
import { SplitDivider } from './SplitDivider';
import { PanelHeader } from './PanelHeader';
import { FileHeaderBar } from './FileHeaderBar';
import { ScrollingCodeBlock } from './ScrollingCodeBlock';
import { LineBadge } from './LineBadge';
import { TerminalWindow } from './TerminalWindow';
import { CodeOutput } from './CodeOutput';

export const defaultPart4PrecisionTradeoff04PromptComparisonSplitProps = {};

export const Part4PrecisionTradeoff04PromptComparisonSplit: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* ── Left Panel Background ── */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: SPLIT_X - 2,
          height: '100%',
          backgroundColor: COLORS.leftPanelBg,
        }}
      />

      {/* ── Right Panel Background ── */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X + 2,
          top: 0,
          width: CANVAS_WIDTH - SPLIT_X - 2,
          height: '100%',
          backgroundColor: COLORS.rightPanelBg,
        }}
      />

      {/* ── Split Divider (frames 0-15) ── */}
      <SplitDivider />

      {/* ── Panel Headers (frames 0-20 fade in) ── */}
      <PanelHeader
        text="FEW TESTS"
        color={COLORS.leftAccent}
        panelX={0}
        panelWidth={PANEL_WIDTH}
      />
      <PanelHeader
        text="MANY TESTS"
        color={COLORS.rightAccent}
        panelX={SPLIT_X + 2}
        panelWidth={PANEL_WIDTH}
      />

      {/* ── Left File Header (frames 20+) ── */}
      <FileHeaderBar
        filename="parser_v1.prompt"
        panelX={0}
        panelWidth={PANEL_WIDTH}
        y={42}
        startFrame={20}
      />

      {/* ── Left Scrolling Code (frames 20-150+) ── */}
      <ScrollingCodeBlock
        lines={DENSE_PROMPT_LINES}
        panelX={0}
        panelWidth={PANEL_WIDTH}
        y={74}
        startFrame={20}
        scrollSpeed={1.5}
        maxHeight={750}
      />

      {/* ── Left "50 lines" badge (frame 90+) ── */}
      <LineBadge
        text="50 lines"
        color={COLORS.leftAccent}
        x={860}
        y={830}
        startFrame={90}
      />

      {/* ── Right File Header (frames 20+) ── */}
      <FileHeaderBar
        filename="parser_v2.prompt"
        panelX={SPLIT_X + 2}
        panelWidth={PANEL_WIDTH}
        y={42}
        startFrame={20}
      />

      {/* ── Right Minimal Code (frames 20+, instant reveal) ── */}
      <ScrollingCodeBlock
        lines={MINIMAL_PROMPT_LINES}
        panelX={SPLIT_X + 2}
        panelWidth={PANEL_WIDTH}
        y={74}
        startFrame={20}
        scrollSpeed={10}
        maxHeight={200}
      />

      {/* ── Right "10 lines" badge (frame 90+) ── */}
      <LineBadge
        text="10 lines"
        color={COLORS.rightAccent}
        x={SPLIT_X + 860}
        y={270}
        startFrame={90}
      />

      {/* ── Right Terminal Window (frame 150+) ── */}
      <TerminalWindow
        panelX={SPLIT_X + 2}
        panelWidth={PANEL_WIDTH}
        y={310}
        command="pdd test parser"
        testResults={TEST_RESULTS}
        startFrame={150}
        scrollSpeed={3}
      />

      {/* ── Bottom Code Output (frame 330+) ── */}
      <CodeOutput startFrame={330} />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff04PromptComparisonSplit;
