import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import {
  BACKGROUND_COLOR,
  VERTICES,
  VERTEX_TOP_START,
  VERTEX_TOP_END,
  VERTEX_LEFT_START,
  VERTEX_LEFT_END,
  VERTEX_RIGHT_START,
  VERTEX_RIGHT_END,
  PULSE_START,
  PULSE_CYCLE_FRAMES,
} from './constants';
import BackgroundGrid from './BackgroundGrid';
import TriangleVertex from './TriangleVertex';
import TriangleEdges from './TriangleEdges';
import GeneratedCodeBlock from './GeneratedCodeBlock';

export const defaultClosing03PddTriangleProps = {};

export const Closing03PddTriangle: React.FC = () => {
  const frame = useCurrentFrame();
  const pulseActive = frame >= PULSE_START;

  const vertexConfigs = [
    {
      ...VERTICES[0],
      fadeStart: VERTEX_TOP_START,
      fadeDuration: VERTEX_TOP_END - VERTEX_TOP_START,
    },
    {
      ...VERTICES[1],
      fadeStart: VERTEX_LEFT_START,
      fadeDuration: VERTEX_LEFT_END - VERTEX_LEFT_START,
    },
    {
      ...VERTICES[2],
      fadeStart: VERTEX_RIGHT_START,
      fadeDuration: VERTEX_RIGHT_END - VERTEX_RIGHT_START,
    },
  ];

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Subtle background grid */}
      <BackgroundGrid />

      {/* Triangle edge connections (drawn starting frame 50) */}
      <TriangleEdges />

      {/* Vertex dots, glows, and labels */}
      {vertexConfigs.map((v) => (
        <TriangleVertex
          key={v.label}
          x={v.x}
          y={v.y}
          label={v.label}
          color={v.color}
          fadeStart={v.fadeStart}
          fadeDuration={v.fadeDuration}
          pulseActive={pulseActive}
          pulseCycleFrames={PULSE_CYCLE_FRAMES}
        />
      ))}

      {/* Center code block (types in from frame 80) */}
      <GeneratedCodeBlock />
    </AbsoluteFill>
  );
};

export default Closing03PddTriangle;
