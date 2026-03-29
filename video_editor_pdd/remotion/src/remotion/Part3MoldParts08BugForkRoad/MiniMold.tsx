import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface MiniMoldProps {
  action: 'addWall' | 'reshapeNozzle';
  x: number;
  y: number;
  accentColor: string;
  animStartFrame: number;
  animDuration: number;
}

const MOLD_WIDTH = 120;
const MOLD_HEIGHT = 100;

export const MiniMold: React.FC<MiniMoldProps> = ({
  action,
  x,
  y,
  accentColor,
  animStartFrame,
  animDuration,
}) => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(frame, [animStartFrame, animStartFrame + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const animProgress = interpolate(
    frame,
    [animStartFrame + 10, animStartFrame + 10 + animDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.4)),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x - MOLD_WIDTH / 2,
        top: y - MOLD_HEIGHT / 2,
        width: MOLD_WIDTH,
        height: MOLD_HEIGHT,
        opacity: fadeIn,
      }}
    >
      <svg width={MOLD_WIDTH} height={MOLD_HEIGHT} viewBox="0 0 120 100">
        {action === 'addWall' ? (
          <AddWallMold progress={animProgress} color={accentColor} />
        ) : (
          <ReshapeNozzleMold progress={animProgress} color={accentColor} />
        )}
      </svg>
    </div>
  );
};

const AddWallMold: React.FC<{ progress: number; color: string }> = ({
  progress,
  color,
}) => {
  // Mold outline (U-shape)
  const wallX = 55 + 5 * progress; // Wall slides in from center-right
  const wallHeight = 50 * progress;

  return (
    <>
      {/* Mold outline */}
      <rect
        x={10}
        y={15}
        width={100}
        height={70}
        rx={4}
        fill="none"
        stroke="#374151"
        strokeWidth={2}
        opacity={0.6}
      />
      {/* Mold cavity (U-shape) */}
      <path
        d="M 25 25 L 25 70 L 95 70 L 95 25"
        fill="none"
        stroke="#4B5563"
        strokeWidth={2}
      />
      {/* Existing left wall */}
      <line
        x1={25}
        y1={25}
        x2={25}
        y2={70}
        stroke="#6B7280"
        strokeWidth={3}
      />
      {/* NEW wall being added */}
      <line
        x1={wallX}
        y1={70 - wallHeight}
        x2={wallX}
        y2={70}
        stroke={color}
        strokeWidth={3}
        opacity={progress}
        strokeLinecap="round"
      />
      {/* Glow on new wall */}
      <line
        x1={wallX}
        y1={70 - wallHeight}
        x2={wallX}
        y2={70}
        stroke={color}
        strokeWidth={8}
        opacity={progress * 0.2}
        strokeLinecap="round"
        filter="url(#moldGlow)"
      />
      {/* Liquid pooling */}
      <rect
        x={26}
        y={72 - 8 * Math.min(progress * 1.5, 1)}
        width={wallX - 26}
        height={8 * Math.min(progress * 1.5, 1)}
        fill={color}
        opacity={0.25 * progress}
        rx={2}
      />
      {/* Label */}
      <text
        x={60}
        y={95}
        textAnchor="middle"
        fill={color}
        fontSize={10}
        fontFamily="Inter, sans-serif"
        fontWeight={600}
        opacity={progress}
      >
        + wall
      </text>
      <defs>
        <filter id="moldGlow">
          <feGaussianBlur stdDeviation="3" />
        </filter>
      </defs>
    </>
  );
};

const ReshapeNozzleMold: React.FC<{ progress: number; color: string }> = ({
  progress,
  color,
}) => {
  // The nozzle/top part of the mold morphs shape
  const nozzleOffset = 12 * progress;
  const sideShift = 8 * progress;

  return (
    <>
      {/* Mold outline */}
      <rect
        x={10}
        y={15}
        width={100}
        height={70}
        rx={4}
        fill="none"
        stroke="#374151"
        strokeWidth={2}
        opacity={0.6}
      />
      {/* Original mold shape (fading out) */}
      <path
        d="M 30 25 L 30 70 L 90 70 L 90 25 L 70 25 L 60 15 L 50 25 Z"
        fill="none"
        stroke="#4B5563"
        strokeWidth={2}
        opacity={1 - progress * 0.7}
      />
      {/* Morphed mold shape (fading in) */}
      <path
        d={`M ${30 - sideShift} 25 L ${30 - sideShift} 70 L ${90 + sideShift} 70 L ${90 + sideShift} 25 L ${75 + sideShift} 25 L 60 ${15 - nozzleOffset} L ${45 - sideShift} 25 Z`}
        fill="none"
        stroke={color}
        strokeWidth={2}
        opacity={progress}
      />
      {/* Glow on morphed shape */}
      <path
        d={`M ${30 - sideShift} 25 L ${30 - sideShift} 70 L ${90 + sideShift} 70 L ${90 + sideShift} 25 L ${75 + sideShift} 25 L 60 ${15 - nozzleOffset} L ${45 - sideShift} 25 Z`}
        fill="none"
        stroke={color}
        strokeWidth={6}
        opacity={progress * 0.15}
        filter="url(#nozzleGlow)"
      />
      {/* Arrows indicating reshape */}
      <line
        x1={30}
        y1={48}
        x2={30 - sideShift}
        y2={48}
        stroke={color}
        strokeWidth={1.5}
        opacity={progress}
        markerEnd="url(#arrowHead)"
      />
      <line
        x1={90}
        y1={48}
        x2={90 + sideShift}
        y2={48}
        stroke={color}
        strokeWidth={1.5}
        opacity={progress}
        markerEnd="url(#arrowHead)"
      />
      {/* Label */}
      <text
        x={60}
        y={95}
        textAnchor="middle"
        fill={color}
        fontSize={10}
        fontFamily="Inter, sans-serif"
        fontWeight={600}
        opacity={progress}
      >
        reshape
      </text>
      <defs>
        <filter id="nozzleGlow">
          <feGaussianBlur stdDeviation="3" />
        </filter>
        <marker
          id="arrowHead"
          markerWidth="6"
          markerHeight="4"
          refX="5"
          refY="2"
          orient="auto"
        >
          <path d="M 0 0 L 6 2 L 0 4 Z" fill={color} />
        </marker>
      </defs>
    </>
  );
};
