import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  ANNOTATION_SOURCE_COLOR,
  ANNOTATION_FONT_SIZE,
  ANNOTATION_SOURCE_SIZE,
} from './constants';

interface AnnotationProps {
  text: string;
  source: string;
  textColor: string;
  position: { x: number; y: number };
  fadeInFrame: number;
  fadeInDuration?: number;
  /** Optional: draw a connector line from annotation to a target point */
  connectorTarget?: { x: number; y: number };
}

export const Annotation: React.FC<AnnotationProps> = ({
  text,
  source,
  textColor,
  position,
  fadeInFrame,
  fadeInDuration = 30,
  connectorTarget,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeInFrame, fadeInFrame + fadeInDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const slideX = interpolate(
    frame,
    [fadeInFrame, fadeInFrame + fadeInDuration],
    [20, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  if (opacity <= 0) return null;

  return (
    <>
      {/* Connector line */}
      {connectorTarget && (
        <svg
          width={1920}
          height={1080}
          style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
          viewBox="0 0 1920 1080"
        >
          <line
            x1={connectorTarget.x}
            y1={connectorTarget.y}
            x2={position.x - 10}
            y2={position.y + 10}
            stroke={textColor}
            strokeWidth={2}
            opacity={opacity * 0.4}
            strokeDasharray="6 4"
          />
          <circle
            cx={connectorTarget.x}
            cy={connectorTarget.y}
            r={4}
            fill={textColor}
            opacity={opacity * 0.6}
          />
        </svg>
      )}

      {/* Annotation text block */}
      <div
        style={{
          position: 'absolute',
          left: position.x + slideX,
          top: position.y,
          opacity,
          display: 'flex',
          flexDirection: 'column',
          gap: 4,
          maxWidth: 380,
        }}
      >
        {/* Left accent bar */}
        <div
          style={{
            display: 'flex',
            flexDirection: 'row',
            alignItems: 'flex-start',
            gap: 12,
          }}
        >
          <div
            style={{
              width: 3,
              height: 44,
              backgroundColor: textColor,
              borderRadius: 2,
              opacity: 0.8,
              flexShrink: 0,
              marginTop: 2,
            }}
          />
          <div style={{ display: 'flex', flexDirection: 'column', gap: 4 }}>
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: ANNOTATION_FONT_SIZE,
                fontWeight: 600,
                color: textColor,
                lineHeight: 1.3,
                opacity: 0.9,
              }}
            >
              {text}
            </span>
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: ANNOTATION_SOURCE_SIZE,
                fontWeight: 400,
                color: ANNOTATION_SOURCE_COLOR,
                lineHeight: 1.3,
                opacity: 0.78,
              }}
            >
              {source}
            </span>
          </div>
        </div>
      </div>
    </>
  );
};
