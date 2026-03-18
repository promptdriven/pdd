import React from 'react';
import { useCurrentFrame, interpolate, spring, Easing } from 'remotion';
import { COLORS, FONT } from './constants';

interface SubStatItem {
  text: string;
  color: string;
}

interface DataCardProps {
  x: number;
  y: number;
  width: number;
  height: number;
  borderColor: string;
  headerText: string;
  mainStat: string;
  mainColor: string;
  subStats: SubStatItem[];
  sourceText: string;
  /** Frame at which this card starts animating (relative to component start) */
  startFrame: number;
  fps: number;
}

export const DataCard: React.FC<DataCardProps> = ({
  x,
  y,
  width,
  height,
  borderColor,
  headerText,
  mainStat,
  mainColor,
  subStats,
  sourceText,
  startFrame,
  fps,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Border draw progress (0→1 over 20 frames)
  const borderProgress = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Background fade (starts at frame 5, over 15 frames)
  const bgOpacity = interpolate(localFrame, [5, 20], [0, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Header type in (starts at frame 8)
  const headerOpacity = interpolate(localFrame, [8, 23], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Main stat spring scale (starts at frame 20)
  const mainStatLocalFrame = Math.max(0, localFrame - 20);
  const mainStatScale = spring({
    frame: mainStatLocalFrame,
    fps,
    config: { stiffness: 200, damping: 12 },
    from: 0.8,
    to: 1,
  });
  const mainStatOpacity = interpolate(localFrame, [20, 32], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Sub-stats stagger (15 frames apart, each takes 12 frames)
  const subStatOpacities = subStats.map((_, i) => {
    const subStart = 30 + i * 15;
    return interpolate(localFrame, [subStart, subStart + 12], [0, 1], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });
  });
  const subStatTranslateYs = subStats.map((_, i) => {
    const subStart = 30 + i * 15;
    return interpolate(localFrame, [subStart, subStart + 12], [8, 0], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });
  });

  // Source text
  const sourceOpacity = interpolate(
    localFrame,
    [30 + subStats.length * 15, 30 + subStats.length * 15 + 12],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Calculate border dash for draw effect
  const perimeter = 2 * (width + height);
  const dashOffset = perimeter * (1 - borderProgress);

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
      }}
    >
      {/* Card border (animated draw) */}
      <svg
        width={width}
        height={height}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <rect
          x={0.5}
          y={0.5}
          width={width - 1}
          height={height - 1}
          rx={8}
          fill="none"
          stroke={borderColor}
          strokeWidth={1}
          strokeOpacity={0.3}
          strokeDasharray={perimeter}
          strokeDashoffset={dashOffset}
        />
      </svg>

      {/* Card background */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width,
          height,
          borderRadius: 8,
          backgroundColor: COLORS.cardBg,
          opacity: bgOpacity,
        }}
      />

      {/* Card content */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width,
          height,
          padding: '20px 24px',
          display: 'flex',
          flexDirection: 'column',
          gap: 6,
        }}
      >
        {/* Header */}
        <div
          style={{
            fontFamily: FONT.family,
            fontSize: 10,
            fontWeight: 600,
            color: COLORS.muted,
            opacity: headerOpacity * 0.5,
            letterSpacing: 2,
          }}
        >
          {headerText}
        </div>

        {/* Main stat */}
        <div
          style={{
            fontFamily: FONT.family,
            fontSize: 28,
            fontWeight: 700,
            color: mainColor,
            opacity: mainStatOpacity,
            transform: `scale(${mainStatScale})`,
            transformOrigin: 'left center',
            marginTop: 4,
            marginBottom: 4,
          }}
        >
          {mainStat}
        </div>

        {/* Sub-stats */}
        {subStats.map((stat, i) => (
          <div
            key={i}
            style={{
              fontFamily: FONT.family,
              fontSize: 14,
              color: stat.color,
              opacity: subStatOpacities[i] * 0.7,
              transform: `translateY(${subStatTranslateYs[i]}px)`,
            }}
          >
            {stat.text}
          </div>
        ))}

        {/* Source */}
        <div
          style={{
            fontFamily: FONT.family,
            fontSize: 11,
            color: COLORS.muted,
            opacity: sourceOpacity * 0.5,
            marginTop: 'auto',
          }}
        >
          {sourceText}
        </div>
      </div>
    </div>
  );
};
