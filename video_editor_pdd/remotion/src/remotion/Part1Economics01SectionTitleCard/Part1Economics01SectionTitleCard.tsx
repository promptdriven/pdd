import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { COLORS, TIMING, LAYOUT, CANVAS } from './constants';
import { HorizontalRule } from './HorizontalRule';

export const defaultPart1Economics01SectionTitleCardProps = {};

const PartLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, TIMING.PART_LABEL_DURATION],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [0, TIMING.PART_LABEL_DURATION],
    [6, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.partLabelY,
        left: 0,
        width: CANVAS.WIDTH,
        textAlign: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: 'Inter, sans-serif',
        fontSize: 14,
        fontWeight: 600,
        color: COLORS.slate,
        letterSpacing: 4,
        textTransform: 'uppercase' as const,
      }}
    >
      PART 1
    </div>
  );
};

const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, TIMING.TITLE_DURATION],
    [0, 0.92],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [0, TIMING.TITLE_DURATION],
    [10, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.titleY,
        left: 0,
        width: CANVAS.WIDTH,
        textAlign: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: 'Inter, sans-serif',
        fontSize: 52,
        fontWeight: 700,
        color: COLORS.amber,
      }}
    >
      The Economics of Darning
    </div>
  );
};

const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, TIMING.SUBTITLE_DURATION],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.subtitleY,
        left: 0,
        width: CANVAS.WIDTH,
        textAlign: 'center',
        opacity,
        fontFamily: 'Inter, sans-serif',
        fontSize: 16,
        fontWeight: 300,
        fontStyle: 'italic',
        color: COLORS.slate,
      }}
    >
      Why patching was rational — and when it stopped.
    </div>
  );
};

export const Part1Economics01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade-in from black over first 15 frames
  const bgOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: '#000000',
      }}
    >
      <AbsoluteFill
        style={{
          backgroundColor: COLORS.background,
          opacity: bgOpacity,
        }}
      >
        {/* Part label — starts at frame 15 */}
        <Sequence from={TIMING.PART_LABEL_START}>
          <PartLabel />
        </Sequence>

        {/* Title — starts at frame 35 */}
        <Sequence from={TIMING.TITLE_START}>
          <TitleText />
        </Sequence>

        {/* Horizontal rule — starts at frame 60 */}
        <Sequence from={TIMING.RULE_START}>
          <HorizontalRule />
        </Sequence>

        {/* Subtitle — starts at frame 70 */}
        <Sequence from={TIMING.SUBTITLE_START}>
          <SubtitleText />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics01SectionTitleCard;
