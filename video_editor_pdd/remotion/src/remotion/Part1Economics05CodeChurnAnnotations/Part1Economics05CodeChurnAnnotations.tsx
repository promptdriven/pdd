import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';

// ─── Inline constants (no cross-file imports) ──────────────────────
const BG_COLOR = '#0A0F1A';
const FONT_FAMILY = 'Inter, system-ui, sans-serif';
const COLOR_RED = '#EF4444';
const COLOR_AMBER = '#F59E0B';
const COLOR_SLATE = '#94A3B8';
const COLOR_SLATE_DARK = '#1E293B';
const COLOR_WHITE = '#FFFFFF';
const COLOR_LINE_SOLID = '#3B82F6';
const COLOR_LINE_DASHED = '#F59E0B';
const COLOR_DEBT_FILL = '#F59E0B';
const COLOR_INDIGO = '#6366F1';

const TOTAL_FRAMES = 840;

// Chart
const CHART_LEFT = 120;
const CHART_RIGHT = 1300;
const CHART_TOP = 160;
const CHART_BOTTOM = 820;
const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;
const CHART_YEARS = [2020, 2021, 2022, 2023, 2024, 2025];

// Synthetic chart data
const solidLineY = [0.65, 0.60, 0.55, 0.42, 0.28, 0.18];
const dashedLineY = [0.65, 0.62, 0.58, 0.52, 0.48, 0.44];

// Timing
const PREV_FADE_DURATION = 30;
const PULSE_START = 60;
const PULSE_MIN_OPACITY = 0.12;
const PULSE_MAX_OPACITY = 0.20;
const PULSE_CYCLE_FRAMES = 45;
const ANNOTATION1_START = 60;
const ANNOTATION2_START = 360;
const CONNECTOR_DRAW_DURATION = 30;
const CALLOUT_SCALE_DURATION = 20;
const TEXT_TYPE_DURATION = 30;

// Annotations layout
const CALLOUT_WIDTH = 380;
const CALLOUT_BORDER_RADIUS = 8;

// ─── Helpers ───────────────────────────────────────────────────────
function yearToX(index: number): number {
  return CHART_LEFT + (index / (CHART_YEARS.length - 1)) * CHART_WIDTH;
}

function fractionToY(f: number): number {
  return CHART_TOP + f * CHART_HEIGHT;
}

function buildPolylinePoints(yFractions: number[]): string {
  return yFractions.map((f, i) => `${yearToX(i)},${fractionToY(f)}`).join(' ');
}

function buildDebtAreaPath(): string {
  const startIdx = 2;
  const forwardPoints = solidLineY
    .slice(startIdx)
    .map((f, i) => `${yearToX(i + startIdx)},${fractionToY(f)}`)
    .join(' L');
  const backwardPoints = dashedLineY
    .slice(startIdx)
    .map((f, i) => `${yearToX(i + startIdx)},${fractionToY(f)}`)
    .reverse()
    .join(' L');
  return `M${forwardPoints} L${backwardPoints} Z`;
}

// ─── Sub-component: Annotation Callout ─────────────────────────────
interface CalloutProps {
  startFrame: number;
  accentColor: string;
  mainText: string;
  sourceText: string;
  boxX: number;
  boxY: number;
  connectorTargetX: number;
  connectorTargetY: number;
}

const AnnotationCallout: React.FC<CalloutProps> = ({
  startFrame,
  accentColor,
  mainText,
  sourceText,
  boxX,
  boxY,
  connectorTargetX,
  connectorTargetY,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const connectorProgress = interpolate(
    localFrame,
    [0, CONNECTOR_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) },
  );

  const scaleStart = CONNECTOR_DRAW_DURATION * 0.5;
  const calloutScale = interpolate(
    localFrame,
    [scaleStart, scaleStart + CALLOUT_SCALE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.back(1.4)) },
  );

  const textStart = scaleStart + CALLOUT_SCALE_DURATION * 0.5;
  const textProgress = interpolate(
    localFrame,
    [textStart, textStart + TEXT_TYPE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) },
  );

  const visibleMainChars = Math.floor(textProgress * mainText.length);
  const visibleSourceChars = Math.floor(
    interpolate(textProgress, [0.4, 1], [0, sourceText.length], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }),
  );

  const connectorOriginX = boxX;
  const connectorOriginY = boxY + 40;
  const currentX = connectorOriginX + (connectorTargetX - connectorOriginX) * connectorProgress;
  const currentY = connectorOriginY + (connectorTargetY - connectorOriginY) * connectorProgress;

  return (
    <>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', left: 0, top: 0, pointerEvents: 'none' }}
      >
        <line
          x1={connectorOriginX}
          y1={connectorOriginY}
          x2={currentX}
          y2={currentY}
          stroke={accentColor}
          strokeWidth={1}
          opacity={0.5}
        />
        {connectorProgress > 0.9 && (
          <circle
            cx={connectorTargetX}
            cy={connectorTargetY}
            r={3.5}
            fill={accentColor}
            opacity={connectorProgress}
          />
        )}
      </svg>

      <div
        style={{
          position: 'absolute',
          left: boxX,
          top: boxY,
          width: CALLOUT_WIDTH,
          background: COLOR_SLATE_DARK,
          border: `1.5px solid ${accentColor}`,
          borderRadius: CALLOUT_BORDER_RADIUS,
          padding: '14px 20px',
          transform: `scale(${calloutScale})`,
          transformOrigin: 'left center',
          opacity: calloutScale,
        }}
      >
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 18,
            fontWeight: 700,
            color: accentColor,
            lineHeight: 1.3,
            minHeight: 24,
          }}
        >
          {mainText.slice(0, visibleMainChars)}
          {visibleMainChars < mainText.length && (
            <span
              style={{
                display: 'inline-block',
                width: 2,
                height: 18,
                background: accentColor,
                marginLeft: 1,
                verticalAlign: 'text-bottom',
                opacity: frame % 16 < 8 ? 1 : 0,
              }}
            />
          )}
        </div>
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 12,
            fontWeight: 400,
            color: COLOR_SLATE,
            marginTop: 4,
            minHeight: 16,
            opacity: 0.85,
          }}
        >
          {sourceText.slice(0, visibleSourceChars)}
        </div>
      </div>
    </>
  );
};

// ─── Sub-component: Previous Annotations ───────────────────────────
const PreviousAnnotations: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, PREV_FADE_DURATION], [1.0, 0.3], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const prevAnns = [
    { x: 1400, y: 180, text: 'Bugs: +41% post-Copilot', source: '(Uplevel, 2024)' },
    { x: 1400, y: 270, text: 'PR revert rate: 2× baseline', source: '(GitHub internal)' },
  ];

  return (
    <div style={{ position: 'absolute', left: 0, top: 0, width: 1920, height: 1080, opacity, pointerEvents: 'none' }}>
      <svg width={1920} height={1080} viewBox="0 0 1920 1080" style={{ position: 'absolute', left: 0, top: 0 }}>
        <line x1={1400} y1={215} x2={1050} y2={380} stroke={COLOR_INDIGO} strokeWidth={1} opacity={0.4} />
        <line x1={1400} y1={305} x2={1080} y2={480} stroke={COLOR_INDIGO} strokeWidth={1} opacity={0.4} />
      </svg>
      {prevAnns.map((ann, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            left: ann.x,
            top: ann.y,
            width: 350,
            background: COLOR_SLATE_DARK,
            border: `1.5px solid ${COLOR_INDIGO}`,
            borderRadius: CALLOUT_BORDER_RADIUS,
            padding: '12px 18px',
          }}
        >
          <div style={{ fontFamily: FONT_FAMILY, fontSize: 16, fontWeight: 700, color: COLOR_INDIGO, lineHeight: 1.3 }}>
            {ann.text}
          </div>
          <div style={{ fontFamily: FONT_FAMILY, fontSize: 11, fontWeight: 400, color: COLOR_SLATE, marginTop: 3 }}>
            {ann.source}
          </div>
        </div>
      ))}
    </div>
  );
};

// ─── Sub-component: Chart ──────────────────────────────────────────
const DebtAreaChart: React.FC = () => {
  const frame = useCurrentFrame();

  const pulseFrame = Math.max(0, frame - PULSE_START);
  const cyclePosition = (pulseFrame % PULSE_CYCLE_FRAMES) / PULSE_CYCLE_FRAMES;
  const pulseOpacity =
    frame < PULSE_START
      ? PULSE_MIN_OPACITY
      : interpolate(
          Math.sin(cyclePosition * Math.PI * 2),
          [-1, 1],
          [PULSE_MIN_OPACITY, PULSE_MAX_OPACITY],
        );

  const solidPoints = buildPolylinePoints(solidLineY);
  const dashedPoints = buildPolylinePoints(dashedLineY);
  const debtPath = buildDebtAreaPath();

  return (
    <svg width={1920} height={1080} viewBox="0 0 1920 1080" style={{ position: 'absolute', left: 0, top: 0 }}>
      {/* Chart title */}
      <text x={CHART_LEFT} y={CHART_TOP - 40} fill={COLOR_WHITE} fontFamily={FONT_FAMILY} fontSize={22} fontWeight={700}>
        Code Generation vs. Maintenance Cost
      </text>

      {/* Horizontal grid lines */}
      {[0, 0.25, 0.5, 0.75, 1].map((f) => (
        <line
          key={f}
          x1={CHART_LEFT}
          y1={fractionToY(f)}
          x2={CHART_RIGHT}
          y2={fractionToY(f)}
          stroke={COLOR_SLATE}
          strokeOpacity={0.15}
          strokeWidth={1}
        />
      ))}

      {/* Vertical grid lines */}
      {CHART_YEARS.map((_, i) => (
        <line
          key={i}
          x1={yearToX(i)}
          y1={CHART_TOP}
          x2={yearToX(i)}
          y2={CHART_BOTTOM}
          stroke={COLOR_SLATE}
          strokeOpacity={0.1}
          strokeWidth={1}
        />
      ))}

      {/* Year labels */}
      {CHART_YEARS.map((year, i) => (
        <text key={year} x={yearToX(i)} y={CHART_BOTTOM + 30} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={13} textAnchor="middle">
          {year}
        </text>
      ))}

      {/* Y-axis labels */}
      {['High', 'Med', 'Low'].map((label, i) => (
        <text key={label} x={CHART_LEFT - 16} y={fractionToY(i * 0.5) + 4} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={13} textAnchor="end">
          {label}
        </text>
      ))}

      {/* AI arrival marker */}
      <line x1={yearToX(3)} y1={CHART_TOP} x2={yearToX(3)} y2={CHART_BOTTOM} stroke={COLOR_WHITE} strokeOpacity={0.25} strokeWidth={1} strokeDasharray="6,4" />
      <text x={yearToX(3)} y={CHART_TOP - 10} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={11} textAnchor="middle">
        AI assistants arrive
      </text>

      {/* Debt shaded area */}
      <path d={debtPath} fill={COLOR_DEBT_FILL} opacity={pulseOpacity} />

      {/* Dashed line (expected) */}
      <polyline points={dashedPoints} fill="none" stroke={COLOR_LINE_DASHED} strokeWidth={2.5} strokeDasharray="8,5" opacity={0.8} />

      {/* Solid line (actual) */}
      <polyline points={solidPoints} fill="none" stroke={COLOR_LINE_SOLID} strokeWidth={2.5} opacity={0.9} />

      {/* Data points — solid */}
      {solidLineY.map((f, i) => (
        <circle key={`s-${i}`} cx={yearToX(i)} cy={fractionToY(f)} r={4} fill={COLOR_LINE_SOLID} stroke={BG_COLOR} strokeWidth={2} />
      ))}

      {/* Data points — dashed */}
      {dashedLineY.map((f, i) => (
        <circle key={`d-${i}`} cx={yearToX(i)} cy={fractionToY(f)} r={4} fill={COLOR_LINE_DASHED} stroke={BG_COLOR} strokeWidth={2} />
      ))}

      {/* Legend */}
      <line x1={CHART_LEFT} y1={CHART_BOTTOM + 56} x2={CHART_LEFT + 30} y2={CHART_BOTTOM + 56} stroke={COLOR_LINE_SOLID} strokeWidth={2.5} />
      <text x={CHART_LEFT + 38} y={CHART_BOTTOM + 60} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={12}>
        Actual cost trajectory
      </text>

      <line x1={CHART_LEFT + 240} y1={CHART_BOTTOM + 56} x2={CHART_LEFT + 270} y2={CHART_BOTTOM + 56} stroke={COLOR_LINE_DASHED} strokeWidth={2.5} strokeDasharray="8,5" />
      <text x={CHART_LEFT + 278} y={CHART_BOTTOM + 60} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={12}>
        Expected trajectory
      </text>

      <rect x={CHART_LEFT + 480} y={CHART_BOTTOM + 48} width={16} height={16} fill={COLOR_DEBT_FILL} opacity={0.16} rx={2} />
      <text x={CHART_LEFT + 504} y={CHART_BOTTOM + 60} fill={COLOR_SLATE} fontFamily={FONT_FAMILY} fontSize={12}>
        Technical debt area
      </text>
    </svg>
  );
};

// ─── Main Component ────────────────────────────────────────────────
export const defaultPart1Economics05CodeChurnAnnotationsProps = {};

export const Part1Economics05CodeChurnAnnotations: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: FONT_FAMILY,
      }}
    >
      {/* Background chart — always visible */}
      <DebtAreaChart />

      {/* Previous annotations — fade from 1.0 to 0.3 over frames 0-30 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <PreviousAnnotations />
      </Sequence>

      {/* Annotation 1: Code churn +44% — appears at frame 60 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AnnotationCallout
          startFrame={ANNOTATION1_START}
          accentColor={COLOR_RED}
          mainText="Code churn: +44%"
          sourceText="(GitClear, 2025, 211M lines analyzed)"
          boxX={1400}
          boxY={380}
          connectorTargetX={1100}
          connectorTargetY={500}
        />
      </Sequence>

      {/* Annotation 2: Refactoring −60% — appears at frame 360 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AnnotationCallout
          startFrame={ANNOTATION2_START}
          accentColor={COLOR_AMBER}
          mainText="Refactoring: −60%"
          sourceText="(GitClear, 2025, code revised within 2 weeks)"
          boxX={1400}
          boxY={520}
          connectorTargetX={1100}
          connectorTargetY={650}
        />
      </Sequence>

      {/* Subtle vignette overlay for depth */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: 1920,
          height: 1080,
          background:
            'radial-gradient(ellipse at center, transparent 50%, rgba(0,0,0,0.3) 100%)',
          pointerEvents: 'none',
        }}
      />
    </AbsoluteFill>
  );
};

export default Part1Economics05CodeChurnAnnotations;
