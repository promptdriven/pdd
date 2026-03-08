import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  TYPOGRAPHY,
  PANEL,
  ANIMATION,
  METRICS,
  PIPELINE_STAGES,
  HEADING_TEXT,
} from './constants';
import { MetricCard } from './MetricCard';
import { PipelineBar } from './PipelineBar';
import { WaveformVisual } from './WaveformVisual';
import { StatusIndicator } from './StatusIndicator';
import { GridBackground } from './GridBackground';

export const VeoSection08VeoTechnologyCallout: React.FC = () => {
  const frame = useCurrentFrame();

  // Panel reveal: slide up + fade in, frames 0-12
  const panelOpacity = interpolate(
    frame,
    [0, ANIMATION.panelRevealEnd],
    [0.5, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const panelTranslateY = interpolate(
    frame,
    [0, ANIMATION.panelRevealEnd],
    [ANIMATION.panelSlideDistance, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Heading fade in
  const headingOpacity = interpolate(
    frame,
    [0, ANIMATION.headingEnd],
    [0.3, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    },
  );

  // Accent line width
  const accentWidth = interpolate(
    frame,
    [0, ANIMATION.headingEnd + 5],
    [20, 120],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Global fade out
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(3)),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        opacity: fadeOutOpacity,
      }}
    >
      {/* Subtle grid background */}
      <GridBackground />

      {/* Top-right decorative glow */}
      <div
        style={{
          position: 'absolute',
          right: 100,
          top: 60,
          width: 500,
          height: 500,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${COLORS.panelGlow} 0%, transparent 70%)`,
          opacity: interpolate(frame, [0, 15], [0.2, 0.7], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }),
        }}
      />

      {/* Main bottom panel */}
      <div
        style={{
          position: 'absolute',
          left: PANEL.x,
          top: PANEL.y,
          width: PANEL.width,
          height: PANEL.height,
          borderRadius: PANEL.borderRadius,
          backgroundColor: COLORS.panelBg,
          border: `1px solid ${COLORS.panelBorder}`,
          boxShadow: `0 -4px 40px ${COLORS.panelGlow}, inset 0 1px 0 rgba(255,255,255,0.04)`,
          opacity: panelOpacity,
          transform: `translateY(${panelTranslateY}px)`,
          overflow: 'hidden',
        }}
      >
        {/* Panel content */}
        <div
          style={{
            position: 'relative',
            padding: PANEL.padding,
            width: '100%',
            height: '100%',
            display: 'flex',
            flexDirection: 'column',
          }}
        >
          {/* Header row */}
          <div
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 14,
              opacity: headingOpacity,
              marginBottom: 6,
            }}
          >
            <StatusIndicator />
            <span
              style={{
                color: COLORS.headingText,
                fontSize: TYPOGRAPHY.heading.fontSize,
                fontFamily: TYPOGRAPHY.heading.fontFamily,
                fontWeight: TYPOGRAPHY.heading.fontWeight,
                letterSpacing: TYPOGRAPHY.heading.letterSpacing,
                marginLeft: 12,
              }}
            >
              {HEADING_TEXT}
            </span>
          </div>

          {/* Accent line */}
          <div
            style={{
              width: accentWidth,
              height: 2,
              borderRadius: 1,
              background: `linear-gradient(90deg, ${COLORS.accentBlue}, ${COLORS.accentCyan})`,
              marginBottom: 24,
            }}
          />

          {/* Two-column layout */}
          <div
            style={{
              display: 'flex',
              gap: 40,
              flex: 1,
            }}
          >
            {/* Left: Metrics row + waveform */}
            <div
              style={{
                display: 'flex',
                flexDirection: 'column',
                gap: 24,
                width: 740,
                flexShrink: 0,
              }}
            >
              {/* Metrics cards row */}
              <div
                style={{
                  display: 'flex',
                  gap: 20,
                  justifyContent: 'space-between',
                }}
              >
                {METRICS.map((metric, i) => (
                  <MetricCard
                    key={metric.label}
                    label={metric.label}
                    value={metric.value}
                    unit={metric.unit}
                    suffix={metric.suffix}
                    index={i}
                  />
                ))}
              </div>

              {/* Waveform visual */}
              <div
                style={{
                  display: 'flex',
                  alignItems: 'center',
                  gap: 16,
                }}
              >
                <span
                  style={{
                    color: COLORS.metricLabel,
                    fontSize: 11,
                    fontFamily: 'Inter, sans-serif',
                    fontWeight: 500,
                    letterSpacing: '1px',
                    textTransform: 'uppercase' as const,
                    whiteSpace: 'nowrap',
                  }}
                >
                  SIGNAL
                </span>
                <WaveformVisual />
              </div>
            </div>

            {/* Vertical divider */}
            <div
              style={{
                width: 1,
                backgroundColor: COLORS.divider,
                flexShrink: 0,
              }}
            />

            {/* Right: Pipeline progress bars */}
            <div
              style={{
                flex: 1,
                display: 'flex',
                flexDirection: 'column',
                justifyContent: 'center',
                gap: 2,
              }}
            >
              <span
                style={{
                  color: COLORS.labelText,
                  fontSize: 11,
                  fontFamily: 'Inter, sans-serif',
                  fontWeight: 600,
                  letterSpacing: '1.5px',
                  textTransform: 'uppercase' as const,
                  marginBottom: 10,
                  opacity: interpolate(
                    frame,
                    [ANIMATION.pipelineStart, ANIMATION.pipelineStart + 8],
                    [0, 1],
                    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
                  ),
                }}
              >
                PIPELINE STATUS
              </span>
              {PIPELINE_STAGES.map((stage, i) => (
                <PipelineBar
                  key={stage.label}
                  label={stage.label}
                  progress={stage.progress}
                  color={stage.color}
                  index={i}
                />
              ))}
            </div>
          </div>
        </div>
      </div>

      {/* Top decorative concentric arcs (right side) */}
      {[120, 200, 280].map((radius, i) => {
        const ringOpacity = interpolate(
          frame,
          [5 + i * 4, 20 + i * 4],
          [0, 0.1 - i * 0.02],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );
        const rotation = frame * (0.2 + i * 0.1);
        return (
          <div
            key={radius}
            style={{
              position: 'absolute',
              right: 300 - radius,
              top: 150 - radius,
              width: radius * 2,
              height: radius * 2,
              borderRadius: '50%',
              border: `1px solid ${COLORS.accentCyan}`,
              opacity: ringOpacity,
              transform: `rotate(${rotation}deg)`,
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};

export const defaultVeoSection08VeoTechnologyCalloutProps = {};

export default VeoSection08VeoTechnologyCallout;
