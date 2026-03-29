import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  PROMPT_BLUE,
  TEST_AMBER,
  GROUNDING_GREEN,
  PANEL_BG,
  ROOM_TO_THINK_COLOR,
  PROMPT_HEIGHT,
  TEST_HEIGHT,
  GROUNDING_HEIGHT,
  BLOCK_PADDING,
  RIGHT_PROMPT_START,
  RIGHT_TEST_START,
  RIGHT_GROUNDING_START,
  ROOM_LABEL_START,
} from './constants';

interface BlockItemProps {
  label: string;
  color: string;
  height: number;
  startFrame: number;
  topOffset: number;
  panelWidth: number;
}

const BlockItem: React.FC<BlockItemProps> = ({
  label,
  color,
  height,
  startFrame,
  topOffset,
  panelWidth,
}) => {
  const frame = useCurrentFrame();

  const slideProgress = interpolate(
    frame,
    [startFrame, startFrame + 30],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const translateX = interpolate(slideProgress, [0, 1], [-panelWidth, 0]);

  return (
    <div
      style={{
        position: 'absolute',
        top: topOffset,
        left: BLOCK_PADDING,
        right: BLOCK_PADDING,
        height,
        transform: `translateX(${translateX}px)`,
        opacity: slideProgress,
      }}
    >
      {/* Background fill at low opacity */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          backgroundColor: color,
          opacity: 0.2,
          borderRadius: 6,
        }}
      />
      {/* Text label at full readability */}
      <div
        style={{
          position: 'relative',
          display: 'flex',
          alignItems: 'center',
          height: '100%',
          paddingLeft: 16,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 12,
            fontWeight: 400,
            color,
            opacity: 0.78,
          }}
        >
          {label}
        </span>
      </div>
    </div>
  );
};

interface RightPanelBlocksProps {
  panelWidth: number;
  panelHeight: number;
}

const RightPanelBlocks: React.FC<RightPanelBlocksProps> = ({
  panelWidth,
  panelHeight,
}) => {
  const frame = useCurrentFrame();

  const blockStartY = BLOCK_PADDING;
  const promptTop = blockStartY;
  const testTop = promptTop + PROMPT_HEIGHT + BLOCK_PADDING;
  const groundingTop = testTop + TEST_HEIGHT + BLOCK_PADDING;
  const emptySpaceTop = groundingTop + GROUNDING_HEIGHT + BLOCK_PADDING;
  const emptySpaceHeight = panelHeight - emptySpaceTop - BLOCK_PADDING;

  // "Room to think" label fade
  const roomLabelOpacity = interpolate(
    frame,
    [ROOM_LABEL_START, ROOM_LABEL_START + 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Empty space background appears after grounding block finishes sliding in
  const emptyBgOpacity =
    frame >= RIGHT_GROUNDING_START + 30
      ? interpolate(
          frame,
          [RIGHT_GROUNDING_START + 30, RIGHT_GROUNDING_START + 50],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        )
      : 0;

  return (
    <>
      <BlockItem
        label="Prompt (300 tokens)"
        color={PROMPT_BLUE}
        height={PROMPT_HEIGHT}
        startFrame={RIGHT_PROMPT_START}
        topOffset={promptTop}
        panelWidth={panelWidth}
      />
      <BlockItem
        label="Tests (2,000 tokens)"
        color={TEST_AMBER}
        height={TEST_HEIGHT}
        startFrame={RIGHT_TEST_START}
        topOffset={testTop}
        panelWidth={panelWidth}
      />
      <BlockItem
        label="Grounding example"
        color={GROUNDING_GREEN}
        height={GROUNDING_HEIGHT}
        startFrame={RIGHT_GROUNDING_START}
        topOffset={groundingTop}
        panelWidth={panelWidth}
      />

      {/* Empty space with "Room to think" */}
      <div
        style={{
          position: 'absolute',
          top: emptySpaceTop,
          left: BLOCK_PADDING,
          right: BLOCK_PADDING,
          height: emptySpaceHeight,
          borderRadius: 6,
          opacity: emptyBgOpacity,
        }}
      >
        {/* Background */}
        <div
          style={{
            position: 'absolute',
            inset: 0,
            backgroundColor: PANEL_BG,
            opacity: 0.3,
            borderRadius: 6,
          }}
        />
        {/* Label */}
        <div
          style={{
            position: 'relative',
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            height: '100%',
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 14,
              fontStyle: 'italic',
              color: ROOM_TO_THINK_COLOR,
              opacity: roomLabelOpacity * 0.62,
            }}
          >
            Room to think
          </span>
        </div>
      </div>
    </>
  );
};

export default RightPanelBlocks;
