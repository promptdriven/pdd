import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import { FlowStep } from './FlowStep';
import { FlowArrow } from './FlowArrow';
import { PulsingEllipsis } from './PulsingEllipsis';
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  DIVIDER_COLOR,
  DIVIDER_WIDTH,
  DIVIDER_OPACITY,
  PANEL_WIDTH,
  HEADER_FONT_SIZE,
  HEADER_FONT_WEIGHT,
  HEADER_Y,
  TRAD_HEADER_COLOR,
  TRAD_BORDER_COLOR,
  TRAD_ARROW_COLOR,
  TRAD_ELLIPSIS_COLOR,
  PDD_HEADER_COLOR,
  PDD_BORDER_COLOR,
  PDD_ARROW_COLOR,
  TRAD_STEP_WIDTH,
  PDD_STEP_WIDTH,
  FLOWCHART_START_Y,
  FADE_IN_DURATION,
  TRADITIONAL_STEPS,
  PDD_STEPS,
  ELLIPSIS_APPEAR,
} from './constants';

export const defaultPart3MoldParts07SplitTraditionalVsPddProps = {};

export const Part3MoldParts07SplitTraditionalVsPdd: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Global fade-in (frames 0-20) — starts at 0.15 so content is visible from frame 0 ──
  const globalOpacity = interpolate(
    frame,
    [0, 20],
    [0.15, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // ── Header fade-in (frames 0-15) ──
  const headerOpacity = interpolate(
    frame,
    [0, FADE_IN_DURATION],
    [0.2, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          width: CANVAS_WIDTH,
          height: CANVAS_HEIGHT,
          position: 'relative',
          opacity: globalOpacity,
        }}
      >
        {/* ─── Center Divider ─── */}
        <div
          style={{
            position: 'absolute',
            left: CANVAS_WIDTH / 2 - DIVIDER_WIDTH / 2,
            top: 80,
            width: DIVIDER_WIDTH,
            height: CANVAS_HEIGHT - 160,
            backgroundColor: DIVIDER_COLOR,
            opacity: DIVIDER_OPACITY,
          }}
        />

        {/* ═══════════════════════════════════════
            LEFT PANEL — Traditional
           ═══════════════════════════════════════ */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            width: PANEL_WIDTH,
            height: CANVAS_HEIGHT,
          }}
        >
          {/* Header */}
          <div
            style={{
              position: 'absolute',
              top: HEADER_Y,
              width: '100%',
              textAlign: 'center',
              opacity: headerOpacity,
            }}
          >
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: HEADER_FONT_SIZE,
                fontWeight: HEADER_FONT_WEIGHT,
                color: TRAD_HEADER_COLOR,
                letterSpacing: 2,
              }}
            >
              TRADITIONAL
            </span>
          </div>

          {/* Flowchart Steps */}
          <div
            style={{
              position: 'absolute',
              top: FLOWCHART_START_Y,
              left: 0,
              width: '100%',
              display: 'flex',
              flexDirection: 'column',
              alignItems: 'center',
            }}
          >
            {TRADITIONAL_STEPS.map((step, i) => (
              <React.Fragment key={i}>
                <FlowStep
                  text={step.text}
                  width={TRAD_STEP_WIDTH}
                  borderColor={TRAD_BORDER_COLOR}
                  appearFrame={step.appearFrame}
                  hasBandaid={step.hasBandaid}
                  hasCode={false}
                  isFinal={false}
                />
                {/* Arrow after each step except the last (ellipsis follows instead) */}
                {i < TRADITIONAL_STEPS.length - 1 && (
                  <FlowArrow
                    color={TRAD_ARROW_COLOR}
                    appearFrame={step.appearFrame}
                  />
                )}
              </React.Fragment>
            ))}

            {/* Trailing ellipsis */}
            <div style={{ marginTop: 8 }}>
              <PulsingEllipsis
                color={TRAD_ELLIPSIS_COLOR}
                appearFrame={ELLIPSIS_APPEAR}
              />
            </div>
          </div>
        </div>

        {/* ═══════════════════════════════════════
            RIGHT PANEL — PDD
           ═══════════════════════════════════════ */}
        <div
          style={{
            position: 'absolute',
            left: CANVAS_WIDTH / 2 + DIVIDER_WIDTH / 2,
            top: 0,
            width: PANEL_WIDTH,
            height: CANVAS_HEIGHT,
          }}
        >
          {/* Header */}
          <div
            style={{
              position: 'absolute',
              top: HEADER_Y,
              width: '100%',
              textAlign: 'center',
              opacity: headerOpacity,
            }}
          >
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: HEADER_FONT_SIZE,
                fontWeight: HEADER_FONT_WEIGHT,
                color: PDD_HEADER_COLOR,
                letterSpacing: 2,
              }}
            >
              PDD
            </span>
          </div>

          {/* Flowchart Steps */}
          <div
            style={{
              position: 'absolute',
              top: FLOWCHART_START_Y,
              left: 0,
              width: '100%',
              display: 'flex',
              flexDirection: 'column',
              alignItems: 'center',
            }}
          >
            {PDD_STEPS.map((step, i) => (
              <React.Fragment key={i}>
                <FlowStep
                  text={step.text}
                  width={PDD_STEP_WIDTH}
                  borderColor={PDD_BORDER_COLOR}
                  appearFrame={step.appearFrame}
                  hasBandaid={false}
                  hasCode={step.hasCode}
                  codeText={step.codeText}
                  isFinal={step.isFinal}
                />
                {/* Arrow between steps (not after final) */}
                {i < PDD_STEPS.length - 1 && (
                  <FlowArrow
                    color={PDD_ARROW_COLOR}
                    appearFrame={step.appearFrame}
                  />
                )}
              </React.Fragment>
            ))}

            {/* "Complete" label below final step */}
            <CompleteBadge appearFrame={PDD_STEPS[PDD_STEPS.length - 1].appearFrame + FADE_IN_DURATION + 10} />
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};

// ── Small "Complete" badge below the PDD chain ──
const CompleteBadge: React.FC<{ appearFrame: number }> = ({ appearFrame }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [appearFrame, appearFrame + 20],
    [0, 0.85],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        marginTop: 14,
        opacity,
        fontFamily: 'Inter, sans-serif',
        fontSize: 13,
        fontWeight: 600,
        color: '#4ADE80',
        letterSpacing: 1.5,
        textTransform: 'uppercase',
      }}
    >
      ● Resolved
    </div>
  );
};

export default Part3MoldParts07SplitTraditionalVsPdd;
