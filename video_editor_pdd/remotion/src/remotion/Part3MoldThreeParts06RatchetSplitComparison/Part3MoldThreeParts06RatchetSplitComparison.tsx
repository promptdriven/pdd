import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import {
  BG_COLOR,
  LEFT_BG,
  RIGHT_BG,
  SPLIT_X,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  RIGHT_PANEL_WIDTH,
  ROW_START_Y,
  ROW_HEIGHT,
  TRADITIONAL_ROWS,
  PDD_ROWS,
  FONT_SANS,
  GREEN,
  RED,
  FRAMES,
} from './constants';
import { SplitLine } from './SplitLine';
import { PanelHeader } from './PanelHeader';
import { TraditionalRow } from './TraditionalRow';
import { PddRow } from './PddRow';
import { EffortCounter } from './EffortCounter';
import { MiniMold } from './MiniMold';
import { TimelineBar } from './TimelineBar';
import { CalloutText } from './CalloutText';

export const defaultPart3MoldThreeParts06RatchetSplitComparisonProps = {};

// Frame at which each traditional row appears
const TRADITIONAL_APPEAR_FRAMES = [
  FRAMES.leftRow1, // 20
  FRAMES.leftRow2, // 60
  FRAMES.leftRow3, // 80
  FRAMES.leftRow4, // 120
  FRAMES.leftRow5, // 140
  FRAMES.leftRow6, // 160
  180, // row 7
  200, // row 8
  230, // row 9
  260, // row 10
];

// Frame at which each PDD row appears
const PDD_APPEAR_FRAMES = [
  FRAMES.rightRow1, // 20
  FRAMES.rightRow2, // 60
  FRAMES.rightRow3, // 120
];

export const Part3MoldThreeParts06RatchetSplitComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // After frame 200, the left panel slowly scrolls to show the overwhelming nature
  const scrollOffset =
    frame > FRAMES.autoScrollStart
      ? (frame - FRAMES.autoScrollStart) * 0.5
      : 0;

  // PDD subtitle
  const subtitleOpacity = interpolate(frame, [FRAMES.pddSubtitle, FRAMES.pddSubtitle + 20], [0, 0.8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* ========== LEFT PANEL — Traditional ========== */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: 1080,
          backgroundColor: LEFT_BG,
          overflow: 'hidden',
        }}
      >
        <PanelHeader text="TRADITIONAL" color={RED} centerX={LEFT_PANEL_WIDTH / 2} />

        {/* Scrolling rows container */}
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: '100%',
            height: '100%',
            transform: `translateY(-${scrollOffset}px)`,
          }}
        >
          {TRADITIONAL_ROWS.map((row, i) => (
            <TraditionalRow
              key={i}
              bug={row.bug}
              fix={row.fix}
              icon={row.icon}
              appearFrame={TRADITIONAL_APPEAR_FRAMES[i] ?? 200 + i * 30}
              y={ROW_START_Y + i * ROW_HEIGHT}
            />
          ))}
        </div>

        {/* Effort counter */}
        <EffortCounter rowAppearFrames={TRADITIONAL_APPEAR_FRAMES} />
      </div>

      {/* ========== SPLIT DIVIDER ========== */}
      <SplitLine />

      {/* ========== RIGHT PANEL — PDD ========== */}
      <div
        style={{
          position: 'absolute',
          left: RIGHT_PANEL_X,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: 1080,
          backgroundColor: RIGHT_BG,
          overflow: 'hidden',
        }}
      >
        <PanelHeader text="PDD" color={GREEN} centerX={RIGHT_PANEL_WIDTH / 2} />

        {/* PDD rows */}
        {PDD_ROWS.map((row, i) => (
          <PddRow
            key={i}
            text={row.text}
            icon={row.icon}
            color={row.color}
            isMono={row.isMono}
            appearFrame={PDD_APPEAR_FRAMES[i]}
            y={ROW_START_Y + i * ROW_HEIGHT}
          />
        ))}

        {/* "Bug impossible forever" subtitle */}
        <div
          style={{
            position: 'absolute',
            top: ROW_START_Y + 3 * ROW_HEIGHT + 20,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: FONT_SANS,
            fontSize: 14,
            fontWeight: 700,
            color: GREEN,
            opacity: subtitleOpacity,
          }}
        >
          Bug impossible forever ∞
        </div>

        {/* Mini mold icon */}
        <MiniMold
          appearFrame={FRAMES.moldIcon}
          x={RIGHT_PANEL_WIDTH / 2}
          y={ROW_START_Y + 3 * ROW_HEIGHT + 110}
        />
      </div>

      {/* ========== TIMELINE BAR ========== */}
      <TimelineBar appearFrame={FRAMES.timelineStart} />

      {/* ========== CALLOUT TEXT ========== */}
      <CalloutText appearFrame={FRAMES.calloutStart} />
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts06RatchetSplitComparison;
