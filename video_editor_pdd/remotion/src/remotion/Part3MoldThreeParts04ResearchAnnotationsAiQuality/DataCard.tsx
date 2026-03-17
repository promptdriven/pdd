import React from 'react';
import { useCurrentFrame, interpolate, spring, Easing } from 'remotion';
import { COLORS, FONTS } from './constants';

interface SubStatItem {
  text: string;
  color: string;
}

interface DataCardProps {
  /** Frame at which this card starts animating in */
  startFrame: number;
  /** Position [x, y] */
  position: [number, number];
  /** Card dimensions [width, height] */
  size: [number, number];
  /** Border accent color */
  borderColor: string;
  /** Category header text */
  header: string;
  /** Main stat text */
  mainStat: string;
  /** Main stat color */
  mainStatColor: string;
  /** Sub-stats to stagger in */
  subStats: SubStatItem[];
  /** Source citation text */
  source: string;
  /** FPS for spring calculations */
  fps?: number;
}

export const DataCard: React.FC<DataCardProps> = ({
  startFrame,
  position,
  size,
  borderColor,
  header,
  mainStat,
  mainStatColor,
  subStats,
  source,
  fps = 30,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Border draw: easeOut(cubic) over 20 frames
  const borderProgress = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Background fade: easeOut(quad) over 15 frames, starts at frame 5
  const bgOpacity = interpolate(localFrame, [5, 20], [0, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Header types in
  const headerOpacity = interpolate(localFrame, [10, 22], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Main stat: spring scale from 0.8
  const statSpring = spring({
    frame: Math.max(0, localFrame - 20),
    fps,
    config: { stiffness: 200, damping: 12 },
  });
  const statScale = interpolate(statSpring, [0, 1], [0.8, 1]);
  const statOpacity = interpolate(localFrame, [20, 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Source fade
  const sourceOpacity = interpolate(localFrame, [35, 45], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Border perimeter for dash animation
  const perimeter = 2 * (size[0] + size[1]);
  const dashOffset = perimeter * (1 - borderProgress);

  return (
    <div
      style={{
        position: 'absolute',
        left: position[0],
        top: position[1],
        width: size[0],
        height: size[1],
      }}
    >
      {/* Card background + border via SVG */}
      <svg
        width={size[0]}
        height={size[1]}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Background fill */}
        <rect
          x={1}
          y={1}
          width={size[0] - 2}
          height={size[1] - 2}
          rx={8}
          ry={8}
          fill={COLORS.cardBg}
          opacity={bgOpacity}
        />
        {/* Animated border */}
        <rect
          x={1}
          y={1}
          width={size[0] - 2}
          height={size[1] - 2}
          rx={8}
          ry={8}
          fill="none"
          stroke={borderColor}
          strokeWidth={1}
          opacity={0.3 * borderProgress}
          strokeDasharray={perimeter}
          strokeDashoffset={dashOffset}
        />
      </svg>

      {/* Card content */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: size[0],
          height: size[1],
          padding: '20px 24px',
          boxSizing: 'border-box',
          display: 'flex',
          flexDirection: 'column',
          gap: 6,
        }}
      >
        {/* Header */}
        <div
          style={{
            fontFamily: FONTS.family,
            fontSize: 10,
            fontWeight: 600,
            color: COLORS.label,
            opacity: headerOpacity * 0.5,
            letterSpacing: 2,
          }}
        >
          {header}
        </div>

        {/* Main stat */}
        <div
          style={{
            fontFamily: FONTS.family,
            fontSize: 28,
            fontWeight: 700,
            color: mainStatColor,
            opacity: statOpacity,
            transform: `scale(${statScale})`,
            transformOrigin: 'left center',
            marginTop: 4,
            marginBottom: 4,
          }}
        >
          {mainStat}
        </div>

        {/* Sub-stats, staggered */}
        {subStats.map((sub, i) => {
          const subDelay = 40 + i * 15;
          const subOpacity = interpolate(localFrame, [subDelay, subDelay + 12], [0, 0.7], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });
          const subTranslate = interpolate(localFrame, [subDelay, subDelay + 12], [8, 0], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          });

          return (
            <div
              key={i}
              style={{
                fontFamily: FONTS.family,
                fontSize: 14,
                fontWeight: 400,
                color: sub.color,
                opacity: subOpacity,
                transform: `translateY(${subTranslate}px)`,
              }}
            >
              {sub.text}
            </div>
          );
        })}

        {/* Source */}
        <div
          style={{
            fontFamily: FONTS.family,
            fontSize: 11,
            fontWeight: 400,
            color: COLORS.label,
            opacity: sourceOpacity,
            marginTop: 'auto',
          }}
        >
          {source}
        </div>
      </div>
    </div>
  );
};
