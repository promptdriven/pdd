import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  FLOATING_COMMENTS,
  COMMENT_COLOR,
  COMMENT_OPACITY,
  COMMENT_FONT_SIZE,
  COMMENTS_START,
  seededRandom,
} from './constants';

interface CommentPosition {
  text: string;
  x: number;
  y: number;
  delay: number;
  fromEdge: 'left' | 'right' | 'top' | 'bottom';
}

function generateCommentPositions(): CommentPosition[] {
  const positions: CommentPosition[] = [];
  const edges: Array<'left' | 'right' | 'top' | 'bottom'> = [
    'left',
    'right',
    'top',
    'bottom',
  ];

  FLOATING_COMMENTS.forEach((text, i) => {
    const rand1 = seededRandom(i + 800);
    const rand2 = seededRandom(i + 900);
    const edge = edges[Math.floor(seededRandom(i + 1000) * 4)];

    let x: number;
    let y: number;

    switch (edge) {
      case 'left':
        x = 20 + rand1 * 100;
        y = 80 + rand2 * 340;
        break;
      case 'right':
        x = 320 + rand1 * 100;
        y = 80 + rand2 * 340;
        break;
      case 'top':
        x = 60 + rand1 * 320;
        y = 40 + rand2 * 80;
        break;
      case 'bottom':
        x = 60 + rand1 * 320;
        y = 380 + rand2 * 80;
        break;
    }

    positions.push({
      text,
      x,
      y,
      delay: i * 1.5, // ~50ms apart at 30fps = 1.5 frames
      fromEdge: edge,
    });
  });

  return positions;
}

const commentPositions = generateCommentPositions();

export const FloatingComments: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {commentPositions.map((comment, i) => {
        const startFrame = COMMENTS_START + comment.delay;

        const opacity = interpolate(
          frame,
          [startFrame, startFrame + 20],
          [0, COMMENT_OPACITY],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        // Drift in from edge
        let translateX = 0;
        let translateY = 0;
        const drift = interpolate(
          frame,
          [startFrame, startFrame + 25],
          [30, 0],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        switch (comment.fromEdge) {
          case 'left':
            translateX = -drift;
            break;
          case 'right':
            translateX = drift;
            break;
          case 'top':
            translateY = -drift;
            break;
          case 'bottom':
            translateY = drift;
            break;
        }

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: comment.x,
              top: comment.y,
              fontFamily: 'Inter, monospace, sans-serif',
              fontSize: COMMENT_FONT_SIZE,
              color: COMMENT_COLOR,
              opacity,
              transform: `translate(${translateX}px, ${translateY}px)`,
              whiteSpace: 'nowrap',
              pointerEvents: 'none',
            }}
          >
            {comment.text}
          </div>
        );
      })}
    </>
  );
};

export default FloatingComments;
