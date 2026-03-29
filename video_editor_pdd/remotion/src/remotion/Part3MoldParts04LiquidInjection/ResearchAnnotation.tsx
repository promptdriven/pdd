import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  ANNOTATION_SOURCE_COLOR,
  FONT_MAIN,
  FOCUS_WALL,
} from './constants';

interface ResearchAnnotationProps {
  text: string;
  source: string;
  textColor: string;
  posX: number;
  posY: number;
  frameIn: number;
}

export const ResearchAnnotation: React.FC<ResearchAnnotationProps> = ({
  text,
  source,
  textColor,
  posX,
  posY,
  frameIn,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [frameIn, frameIn + 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const translateX = interpolate(frame, [frameIn, frameIn + 30], [20, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  if (frame < frameIn) return null;

  // Connector line from annotation to the focus wall area
  const connectorEndX = FOCUS_WALL.x + FOCUS_WALL.width + 40;
  const connectorEndY = FOCUS_WALL.y;

  return (
    <>
      {/* Connector line (SVG overlay) */}
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
      >
        <line
          x1={posX - 20}
          y1={posY + 12}
          x2={connectorEndX}
          y2={connectorEndY}
          stroke={textColor}
          strokeWidth={1.5}
          opacity={opacity * 0.4}
          strokeDasharray="6 3"
        />
        {/* Dot at annotation end */}
        <circle
          cx={posX - 20}
          cy={posY + 12}
          r={3}
          fill={textColor}
          opacity={opacity * 0.6}
        />
      </svg>

      {/* Annotation text */}
      <div
        style={{
          position: 'absolute',
          left: posX,
          top: posY,
          opacity,
          transform: `translateX(${translateX}px)`,
          maxWidth: 500,
        }}
      >
        {/* Accent bar */}
        <div
          style={{
            width: 3,
            height: 40,
            backgroundColor: textColor,
            opacity: 0.8,
            position: 'absolute',
            left: -14,
            top: 0,
            borderRadius: 2,
          }}
        />
        <div
          style={{
            fontFamily: FONT_MAIN,
            fontSize: 18,
            fontWeight: 600,
            color: textColor,
            lineHeight: 1.3,
            marginBottom: 4,
          }}
        >
          {text}
        </div>
        <div
          style={{
            fontFamily: FONT_MAIN,
            fontSize: 13,
            fontWeight: 400,
            color: ANNOTATION_SOURCE_COLOR,
            lineHeight: 1.3,
          }}
        >
          {source}
        </div>
      </div>
    </>
  );
};
