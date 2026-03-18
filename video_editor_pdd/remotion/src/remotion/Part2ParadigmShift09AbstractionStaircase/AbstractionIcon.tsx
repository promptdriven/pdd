// AbstractionIcon.tsx — SVG icons for each abstraction level
import React from 'react';
import { useCurrentFrame, interpolate, spring } from 'remotion';
import type { StepData } from './constants';
import { OPACITIES, STEP_WIDTH } from './constants';

interface AbstractionIconProps {
  step: StepData;
  startFrame: number;
  fps: number;
}

/** BJT transistor symbol */
const TransistorIcon: React.FC<{ color: string; opacity: number }> = ({
  color,
  opacity,
}) => (
  <g opacity={opacity}>
    {/* Base line */}
    <line x1={0} y1={-12} x2={0} y2={12} stroke={color} strokeWidth={2} />
    {/* Emitter */}
    <line x1={0} y1={-6} x2={12} y2={-14} stroke={color} strokeWidth={1.5} />
    {/* Collector */}
    <line x1={0} y1={6} x2={12} y2={14} stroke={color} strokeWidth={1.5} />
    {/* Base connection */}
    <line x1={-10} y1={0} x2={0} y2={0} stroke={color} strokeWidth={1.5} />
    {/* Arrowhead on emitter */}
    <polygon
      points="10,-12 14,-14 11,-9"
      fill={color}
    />
  </g>
);

/** Schematic gates fragment */
const SchematicIcon: React.FC<{ color: string; opacity: number }> = ({
  color,
  opacity,
}) => (
  <g opacity={opacity}>
    {/* AND gate body */}
    <path
      d="M -16,-10 L 0,-10 A 10,10 0 0,1 0,10 L -16,10 Z"
      fill="none"
      stroke={color}
      strokeWidth={1.5}
    />
    {/* Inputs */}
    <line x1={-24} y1={-5} x2={-16} y2={-5} stroke={color} strokeWidth={1} />
    <line x1={-24} y1={5} x2={-16} y2={5} stroke={color} strokeWidth={1} />
    {/* Output */}
    <line x1={10} y1={0} x2={20} y2={0} stroke={color} strokeWidth={1} />
    {/* OR gate nearby */}
    <path
      d="M -8,16 Q 4,22 -8,28"
      fill="none"
      stroke={color}
      strokeWidth={1}
      opacity={0.6}
    />
  </g>
);

/** RTL / Verilog code snippet */
const RTLIcon: React.FC<{ color: string; opacity: number }> = ({
  color,
  opacity,
}) => (
  <g opacity={opacity} fontFamily="monospace" fontSize={7} fill={color}>
    <text x={-22} y={-8}>always @(</text>
    <text x={-18} y={0}>posedge clk</text>
    <text x={-22} y={8}>)</text>
    <rect x={-26} y={-14} width={54} height={28} fill="none" stroke={color} strokeWidth={0.8} rx={2} opacity={0.3} />
  </g>
);

/** HLS / Behavioral code block */
const HLSIcon: React.FC<{ color: string; opacity: number }> = ({
  color,
  opacity,
}) => (
  <g opacity={opacity} fontFamily="monospace" fontSize={7} fill={color}>
    <text x={-22} y={-8}>void filter(</text>
    <text x={-18} y={0}>  stream &amp;in</text>
    <text x={-22} y={8}>);</text>
    <rect x={-26} y={-14} width={58} height={28} fill="none" stroke={color} strokeWidth={0.8} rx={2} opacity={0.3} />
  </g>
);

/** Natural Language / Prompt document icon */
const NLPIcon: React.FC<{ color: string; opacity: number; frame: number }> = ({
  color,
  opacity,
  frame,
}) => {
  // Pulsing glow on border
  const pulsePhase = Math.sin((frame / 40) * Math.PI * 2);
  const borderOpacity = 0.3 + pulsePhase * 0.15;

  return (
    <g opacity={opacity}>
      {/* Document body */}
      <rect
        x={-20}
        y={-18}
        width={40}
        height={36}
        rx={3}
        fill={color}
        fillOpacity={0.12}
        stroke={color}
        strokeWidth={2}
        strokeOpacity={borderOpacity}
      />
      {/* Text lines representing a prompt */}
      <line x1={-14} y1={-10} x2={14} y2={-10} stroke={color} strokeWidth={1.5} opacity={0.6} />
      <line x1={-14} y1={-3} x2={10} y2={-3} stroke={color} strokeWidth={1.5} opacity={0.5} />
      <line x1={-14} y1={4} x2={6} y2={4} stroke={color} strokeWidth={1.5} opacity={0.4} />
      {/* Arrow */}
      <polygon points="-2,11 4,14 -2,17" fill={color} opacity={0.5} />
    </g>
  );
};

const AbstractionIcon: React.FC<AbstractionIconProps> = ({
  step,
  startFrame,
  fps,
}) => {
  const frame = useCurrentFrame();

  // Pop-in using spring (simulates easeOut(back))
  const iconDelay = startFrame + 10;
  const scaleSpring = spring({
    frame: frame - iconDelay,
    fps,
    config: {
      damping: 12,
      stiffness: 180,
      mass: 0.8,
    },
  });
  const scale = frame >= iconDelay ? scaleSpring : 0;

  // Label and decade fade-in
  const labelOpacity = interpolate(
    frame,
    [iconDelay + 5, iconDelay + 15],
    [0, step.active ? OPACITIES.amberLabel : OPACITIES.iconDefault],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const decadeOpacity = interpolate(
    frame,
    [iconDelay + 8, iconDelay + 18],
    [0, step.active ? OPACITIES.amberDecade : OPACITIES.decadeLabel],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const iconOpacity = step.active ? OPACITIES.amberIcon : OPACITIES.iconDefault;

  // Icon center position on the step
  const iconCx = step.x + STEP_WIDTH / 2;
  const iconCy = step.y + 40;

  const renderIcon = () => {
    switch (step.iconType) {
      case 'transistor':
        return <TransistorIcon color={step.color} opacity={iconOpacity} />;
      case 'schematic':
        return <SchematicIcon color={step.color} opacity={iconOpacity} />;
      case 'rtl':
        return <RTLIcon color={step.color} opacity={iconOpacity} />;
      case 'hls':
        return <HLSIcon color={step.color} opacity={iconOpacity} />;
      case 'nlp':
        return <NLPIcon color={step.color} opacity={iconOpacity} frame={frame} />;
      default:
        return null;
    }
  };

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      {/* Icon with spring pop-in */}
      <g transform={`translate(${iconCx}, ${iconCy}) scale(${scale})`}>
        {renderIcon()}
      </g>

      {/* Step label */}
      <text
        x={iconCx}
        y={step.y + 85}
        fill={step.color}
        fontSize={14}
        fontFamily="Inter, sans-serif"
        fontWeight={step.active ? 600 : 400}
        textAnchor="middle"
        opacity={labelOpacity}
      >
        {step.label}
      </text>

      {/* Decade label */}
      <text
        x={iconCx}
        y={step.y + 104}
        fill={step.active ? step.color : '#475569'}
        fontSize={10}
        fontFamily="Inter, sans-serif"
        textAnchor="middle"
        opacity={decadeOpacity}
      >
        {step.decade}
      </text>
    </svg>
  );
};

export default AbstractionIcon;
