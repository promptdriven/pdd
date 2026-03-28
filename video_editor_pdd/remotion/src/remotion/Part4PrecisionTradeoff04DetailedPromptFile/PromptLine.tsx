import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  GUTTER_WIDTH,
  GUTTER_INDICATOR_WIDTH,
  LINE_HEIGHT,
  TEXT_COLOR,
  LINE_NUMBER_COLOR,
  ACCENT_AMBER,
  CONTENT_REVEAL_START,
  LINES_PER_FRAME,
} from './constants';

interface PromptLineProps {
  lineNumber: number;
  text: string;
  index: number;
  isHighlight: boolean;
  section: string;
}

export const PromptLine: React.FC<PromptLineProps> = ({
  lineNumber,
  text,
  index,
  isHighlight,
  section,
}) => {
  const frame = useCurrentFrame();

  // Each line reveals based on scroll progress
  const revealFrame = CONTENT_REVEAL_START + index / LINES_PER_FRAME;
  const lineOpacity = interpolate(frame, [revealFrame, revealFrame + 4], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Gutter indicator fades in slightly after the line
  const gutterDelay = revealFrame + 2;
  const gutterOpacity = interpolate(frame, [gutterDelay, gutterDelay + 4], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Section-specific colors for keywords
  const isHeader = section === 'header';
  const isSectionHeading = text.startsWith('##');
  const isComment = text.startsWith('#') && !isSectionHeading;

  let lineColor = TEXT_COLOR;
  if (isHeader || isComment) lineColor = '#8B9CB8';
  if (isSectionHeading) lineColor = '#E2E8F0';
  if (isHighlight && !isSectionHeading && !isComment && text.trim() !== '') {
    lineColor = '#E8C88A';
  }

  return (
    <div
      style={{
        display: 'flex',
        alignItems: 'center',
        height: LINE_HEIGHT,
        opacity: lineOpacity,
        position: 'relative',
      }}
    >
      {/* Gutter indicator bar */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 2,
          width: GUTTER_INDICATOR_WIDTH,
          height: LINE_HEIGHT - 4,
          backgroundColor: ACCENT_AMBER,
          opacity: text.trim() !== '' ? gutterOpacity : 0,
          borderRadius: 1,
        }}
      />

      {/* Line number */}
      <div
        style={{
          width: GUTTER_WIDTH,
          textAlign: 'right',
          paddingRight: 12,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 12,
          color: LINE_NUMBER_COLOR,
          opacity: 0.4,
          userSelect: 'none',
          flexShrink: 0,
        }}
      >
        {lineNumber}
      </div>

      {/* Text content */}
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 13,
          color: lineColor,
          opacity: 0.9,
          whiteSpace: 'pre',
          overflow: 'hidden',
          textOverflow: 'ellipsis',
        }}
      >
        {text}
      </div>
    </div>
  );
};

export default PromptLine;
