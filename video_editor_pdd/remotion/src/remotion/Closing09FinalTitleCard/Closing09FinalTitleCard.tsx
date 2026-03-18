import React from 'react';
import { AbsoluteFill } from 'remotion';
import { BG_COLOR } from './constants';
import { GhostTriangle } from './GhostTriangle';
import { TitleText } from './TitleText';
import { CommandBlock } from './CommandBlock';
import { UrlText } from './UrlText';

export const defaultClosing09FinalTitleCardProps = {};

export const Closing09FinalTitleCard: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
      }}
    >
      {/* Ghost triangle watermark — behind everything */}
      <GhostTriangle />

      {/* Title: "Prompt-Driven Development" */}
      <TitleText />

      {/* Terminal command block with typing animation */}
      <CommandBlock />

      {/* URL: pdd.dev */}
      <UrlText />
    </AbsoluteFill>
  );
};

export default Closing09FinalTitleCard;
