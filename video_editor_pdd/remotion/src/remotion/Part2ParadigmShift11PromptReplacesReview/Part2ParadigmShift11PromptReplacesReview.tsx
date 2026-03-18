import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { COLORS, SPLIT_X } from './constants';
import { FrozenCodeDiff } from './FrozenCodeDiff';
import { PulsingQuestionMark } from './PulsingQuestionMark';
import { PromptDocument } from './PromptDocument';
import { TestSuitePanel } from './TestSuitePanel';
import { CognitiveLoadMeter } from './CognitiveLoadMeter';

export const defaultPart2ParadigmShift11PromptReplacesReviewProps = {};

export const Part2ParadigmShift11PromptReplacesReview: React.FC = () => {
  const frame = useCurrentFrame();

  // Split line draws from frame 0-15
  const splitLineHeight = interpolate(frame, [0, 15], [0, 1080], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Panel headers fade in from frame 0-20
  const leftHeaderOpacity = interpolate(frame, [0, 20], [0, 0.4], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const rightHeaderOpacity = interpolate(frame, [0, 20], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Strikethrough animation for LEFT header
  const strikethroughWidth = interpolate(frame, [5, 20], [0, 100], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* LEFT PANEL — Old: Review the Code */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: SPLIT_X - 2,
          height: 1080,
          backgroundColor: COLORS.leftPanelBg,
          overflow: 'hidden',
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: 'absolute',
            top: 40,
            left: 0,
            width: '100%',
            display: 'flex',
            justifyContent: 'center',
            alignItems: 'center',
          }}
        >
          <div style={{ position: 'relative', display: 'inline-block' }}>
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: 14,
                fontWeight: 600,
                color: COLORS.red,
                opacity: leftHeaderOpacity,
                letterSpacing: 2,
                textTransform: 'uppercase',
              }}
            >
              REVIEW THE CODE
            </span>
            {/* Strikethrough */}
            <div
              style={{
                position: 'absolute',
                top: '50%',
                left: 0,
                width: `${strikethroughWidth}%`,
                height: 2,
                backgroundColor: COLORS.red,
                opacity: leftHeaderOpacity * 0.8,
                transform: 'translateY(-50%)',
              }}
            />
          </div>
        </div>

        {/* Frozen code diff — faded, overwhelming */}
        <FrozenCodeDiff fadeInStart={20} />

        {/* Red question mark overlay */}
        <PulsingQuestionMark fadeInStart={60} />

        {/* Cognitive load meter */}
        <CognitiveLoadMeter
          x={480}
          y={950}
          width={300}
          fillPercent={100}
          color={COLORS.red}
          label="Cognitive load"
          status="OVERLOADED"
          appearStart={220}
        />
      </div>

      {/* SPLIT DIVIDER */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X - 1,
          top: 0,
          width: 2,
          height: splitLineHeight,
          backgroundColor: COLORS.splitLine,
          opacity: 0.25,
        }}
      />

      {/* RIGHT PANEL — New: Review the Spec */}
      <div
        style={{
          position: 'absolute',
          left: SPLIT_X + 1,
          top: 0,
          width: 1920 - SPLIT_X - 1,
          height: 1080,
          backgroundColor: COLORS.rightPanelBg,
          overflow: 'hidden',
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: 'absolute',
            top: 40,
            left: 0,
            width: '100%',
            display: 'flex',
            justifyContent: 'center',
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 14,
              fontWeight: 600,
              color: COLORS.green,
              opacity: rightHeaderOpacity,
              letterSpacing: 2,
              textTransform: 'uppercase',
            }}
          >
            REVIEW THE SPEC
          </span>
        </div>

        {/* Prompt document */}
        <PromptDocument fadeInStart={20} highlightStart={60} />

        {/* Test suite with checkmarks */}
        <TestSuitePanel appearStart={120} checkInterval={15} />

        {/* Cognitive load meter */}
        <CognitiveLoadMeter
          x={480}
          y={950}
          width={300}
          fillPercent={25}
          color={COLORS.green}
          label="Cognitive load"
          status="MANAGEABLE"
          appearStart={220}
        />
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift11PromptReplacesReview;
