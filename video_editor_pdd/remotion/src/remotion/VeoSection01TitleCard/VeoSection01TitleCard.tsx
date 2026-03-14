import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { COLORS } from './constants';
import { TitleText } from './TitleText';
import { HorizontalRule } from './HorizontalRule';
import { SubtitleText } from './SubtitleText';

export const VeoSection01TitleCard: React.FC = () => {
  const { width, height } = useVideoConfig();

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background, width, height }}>
      {/* Title text: "Veo Section" — fades in frame 0–10 */}
      <TitleText />

      {/* Horizontal rule — expands frame 10–18 */}
      <HorizontalRule />

      {/* Subtitle: "AI-Generated Cinematic Footage" — fades in frame 18–26 */}
      <SubtitleText />
    </AbsoluteFill>
  );
};

export const defaultVeoSection01TitleCardProps = {};

export default VeoSection01TitleCard;
