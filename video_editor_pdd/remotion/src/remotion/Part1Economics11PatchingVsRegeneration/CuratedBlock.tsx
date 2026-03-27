import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PANEL_PADDING,
  PANEL_WIDTH,
  FONT_FAMILY,
  BLOCK_LABEL_FONT_SIZE,
} from './constants';

interface CuratedBlockProps {
  panelX: number;
  panelY: number;
  /** Vertical offset from the top of the panel interior */
  topOffset: number;
  blockHeight: number;
  color: string;
  label: string;
  /** Frame at which the slide-in animation begins */
  slideInStart: number;
  /** Duration of the slide-in animation in frames */
  slideInDuration?: number;
}

const CuratedBlock: React.FC<CuratedBlockProps> = ({
  panelX,
  panelY,
  topOffset,
  blockHeight,
  color,
  label,
  slideInStart,
  slideInDuration = 30,
}) => {
  const frame = useCurrentFrame();

  const innerWidth = PANEL_WIDTH - PANEL_PADDING * 2;

  const slideProgress = interpolate(
    frame,
    [slideInStart, slideInStart + slideInDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const translateX = interpolate(slideProgress, [0, 1], [-innerWidth, 0]);
  const blockOpacity = interpolate(slideProgress, [0, 1], [0, 0.2]);
  const labelOpacity = interpolate(slideProgress, [0, 1], [0, 0.78]);

  const x = panelX + PANEL_PADDING;
  const y = panelY + PANEL_PADDING + topOffset;

  return (
    <>
      {/* Translucent colored block */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: innerWidth,
          height: blockHeight,
          backgroundColor: color,
          opacity: blockOpacity,
          borderRadius: 4,
          transform: `translateX(${translateX}px)`,
        }}
      />
      {/* Label rendered separately so it's not affected by block opacity */}
      <div
        style={{
          position: 'absolute',
          left: x + 12,
          top: y,
          height: blockHeight,
          display: 'flex',
          alignItems: 'center',
          fontFamily: FONT_FAMILY,
          fontSize: BLOCK_LABEL_FONT_SIZE,
          color,
          opacity: labelOpacity,
          fontWeight: 400,
          transform: `translateX(${translateX}px)`,
          filter: 'brightness(1.8)',
          pointerEvents: 'none',
        }}
      >
        {label}
      </div>
    </>
  );
};

export default CuratedBlock;
