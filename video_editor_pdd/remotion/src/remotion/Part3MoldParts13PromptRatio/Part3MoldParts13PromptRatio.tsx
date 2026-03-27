import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import {
  BG_COLOR,
  PHASE1_START,
  CODE_BLOCK_START,
  RATIO_START,
  CROSSFADE_START,
  CROSSFADE_DURATION,
  LEFT_FILL_START,
  RIGHT_FILL_START,
  EMPHASIS_START,
  LEFT_WINDOW_X,
  RIGHT_WINDOW_X,
  WINDOW_Y,
} from './constants';
import { PromptBlock } from './PromptBlock';
import { CodeBlock } from './CodeBlock';
import { RatioLabel } from './RatioLabel';
import { ContextWindow } from './ContextWindow';

export const defaultPart3MoldParts13PromptRatioProps = {};

const CANVAS_CENTER_X = 960;

export const Part3MoldParts13PromptRatio: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Phase 1 opacity: fully visible, then crossfade out ──
  const phase1Opacity = interpolate(
    frame,
    [CROSSFADE_START, CROSSFADE_START + CROSSFADE_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── Phase 2 opacity: crossfade in ──
  const phase2Opacity = interpolate(
    frame,
    [CROSSFADE_START, CROSSFADE_START + CROSSFADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── Phase 1 title fade in (quick, from frame 0) ──
  const phase1TitleProgress = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // ── Phase 2 title fade in ──
  const phase2TitleProgress = interpolate(
    frame,
    [CROSSFADE_START + 10, CROSSFADE_START + CROSSFADE_DURATION + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Divider opacity: fade in with title, but minimum 0.7 once visible
  const phase1DividerOpacity =
    phase1TitleProgress < 0.01 ? 0 : Math.max(phase1TitleProgress, 0.7);
  const phase2DividerOpacity =
    phase2TitleProgress < 0.01 ? 0 : Math.max(phase2TitleProgress, 0.7);

  // Bottom label
  const bottomLabelOpacity = interpolate(
    frame,
    [LEFT_FILL_START + 30, LEFT_FILL_START + 50],
    [0, 0.78],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* ═══════════════════════════════════════════════
          PHASE 1: Prompt vs Code Size Comparison
          Frames 0–270
         ═══════════════════════════════════════════════ */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          opacity: phase1Opacity,
        }}
      >
        {/* Section title */}
        <div
          style={{
            position: 'absolute',
            top: 60,
            left: 0,
            right: 0,
            textAlign: 'center',
            opacity: phase1TitleProgress * 0.9,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 22,
              fontWeight: 700,
              color: '#E2E8F0',
              letterSpacing: 1,
            }}
          >
            Prompt Compression Ratio
          </span>
        </div>

        {/* Horizontal divider */}
        <div
          style={{
            position: 'absolute',
            top: 100,
            left: 200,
            right: 200,
            height: 2,
            backgroundColor: '#334155',
            opacity: phase1DividerOpacity,
          }}
        />

        {/* Prompt block - appears at frame 0 */}
        <PromptBlock startFrame={PHASE1_START} />

        {/* Code block - appears at frame 30 */}
        <CodeBlock startFrame={CODE_BLOCK_START} />

        {/* Ratio label - appears at frame 90 */}
        <RatioLabel startFrame={RATIO_START} />
      </div>

      {/* ═══════════════════════════════════════════════
          PHASE 2: Context Window Comparison
          Frames 210–540
         ═══════════════════════════════════════════════ */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          opacity: phase2Opacity,
        }}
      >
        {/* Phase 2 title */}
        <div
          style={{
            position: 'absolute',
            top: 60,
            left: 0,
            right: 0,
            textAlign: 'center',
            opacity: phase2TitleProgress * 0.9,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 22,
              fontWeight: 700,
              color: '#E2E8F0',
              letterSpacing: 1,
            }}
          >
            Context Window Advantage
          </span>
        </div>

        {/* Horizontal divider */}
        <div
          style={{
            position: 'absolute',
            top: 100,
            left: 200,
            right: 200,
            height: 2,
            backgroundColor: '#334155',
            opacity: phase2DividerOpacity,
          }}
        />

        {/* "vs" label in center */}
        <div
          style={{
            position: 'absolute',
            left: CANVAS_CENTER_X - 20,
            top: WINDOW_Y + 250,
            width: 40,
            height: 40,
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            opacity: phase2Opacity * 0.62,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 18,
              fontWeight: 600,
              color: '#64748B',
            }}
          >
            vs
          </span>
        </div>

        {/* Left context window: Raw code */}
        <ContextWindow
          side="left"
          x={LEFT_WINDOW_X}
          y={WINDOW_Y}
          fillStartFrame={LEFT_FILL_START}
          emphasisFrame={EMPHASIS_START}
        />

        {/* Right context window: Prompts */}
        <ContextWindow
          side="right"
          x={RIGHT_WINDOW_X}
          y={WINDOW_Y}
          fillStartFrame={RIGHT_FILL_START}
          emphasisFrame={EMPHASIS_START}
        />

        {/* Bottom summary label */}
        <div
          style={{
            position: 'absolute',
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: 'center',
            opacity: bottomLabelOpacity,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 18,
              fontWeight: 600,
              color: '#94A3B8',
            }}
          >
            Same context window — vastly different information density
          </span>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldParts13PromptRatio;
