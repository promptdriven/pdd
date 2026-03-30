import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface CuratedBlockDef {
  label: string;
  color: string;
  height: number;
  startFrame: number;
}

interface CuratedBlocksProps {
  blocks: CuratedBlockDef[];
  panelInnerWidth: number;
  padding: number;
  gap: number;
  roomToThinkStartFrame: number;
  roomToThinkColor: string;
  emptySpaceColor: string;
  panelHeight: number;
  fontFamily: string;
  labelFontSize: number;
}

const CuratedBlocks: React.FC<CuratedBlocksProps> = ({
  blocks,
  panelInnerWidth,
  padding,
  gap,
  roomToThinkStartFrame,
  roomToThinkColor,
  emptySpaceColor,
  panelHeight,
  fontFamily,
  labelFontSize,
}) => {
  const frame = useCurrentFrame();
  const slideDuration = 30;

  // Calculate total blocks height to determine empty space
  const totalBlocksHeight = blocks.reduce(
    (sum, b) => sum + b.height + gap,
    -gap
  );
  const emptySpaceTop = padding + totalBlocksHeight + gap * 2;
  const emptySpaceHeight = panelHeight - emptySpaceTop - padding;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
      }}
    >
      {/* Curated content blocks */}
      {blocks.map((block, i) => {
        const yPos =
          padding +
          blocks.slice(0, i).reduce((sum, b) => sum + b.height + gap, 0);

        const clampedEnd = Math.max(
          block.startFrame + 0.001,
          block.startFrame + slideDuration
        );

        const slideX = interpolate(
          frame,
          [block.startFrame, clampedEnd],
          [-panelInnerWidth, 0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        const blockOpacity = interpolate(
          frame,
          [block.startFrame, clampedEnd],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        return (
          <div
            key={block.label}
            style={{
              position: 'absolute',
              top: yPos,
              left: padding,
              width: panelInnerWidth - padding * 2,
              height: block.height,
              backgroundColor: block.color,
              opacity: blockOpacity * 0.2,
              borderRadius: 6,
              transform: `translateX(${slideX}px)`,
              display: 'flex',
              alignItems: 'center',
              paddingLeft: 16,
              overflow: 'hidden',
            }}
          >
            {/* Inner label rendered at higher opacity for readability */}
            <span
              style={{
                fontFamily,
                fontSize: labelFontSize,
                color: block.color,
                opacity: Math.min(1, blockOpacity * 3.5),
                fontWeight: 500,
                letterSpacing: '0.02em',
                whiteSpace: 'nowrap',
              }}
            >
              {block.label}
            </span>
          </div>
        );
      })}

      {/* Empty space indicator */}
      {emptySpaceHeight > 20 && (
        <div
          style={{
            position: 'absolute',
            top: emptySpaceTop,
            left: padding,
            width: panelInnerWidth - padding * 2,
            height: Math.max(0, emptySpaceHeight),
            backgroundColor: emptySpaceColor,
            borderRadius: 6,
            opacity: interpolate(
              frame,
              [
                roomToThinkStartFrame,
                Math.max(
                  roomToThinkStartFrame + 0.001,
                  roomToThinkStartFrame + 20
                ),
              ],
              [0, 0.3],
              {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
                easing: Easing.out(Easing.quad),
              }
            ),
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
          }}
        >
          <span
            style={{
              fontFamily,
              fontSize: 14,
              fontStyle: 'italic',
              color: roomToThinkColor,
              opacity: interpolate(
                frame,
                [
                  roomToThinkStartFrame,
                  Math.max(
                    roomToThinkStartFrame + 0.001,
                    roomToThinkStartFrame + 20
                  ),
                ],
                [0, 0.78],
                {
                  extrapolateLeft: 'clamp',
                  extrapolateRight: 'clamp',
                  easing: Easing.out(Easing.quad),
                }
              ),
              letterSpacing: '0.05em',
            }}
          >
            Room to think
          </span>
        </div>
      )}
    </div>
  );
};

export default CuratedBlocks;
