import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  BG_COLOR,
  FILE_BLOCKS,
  DEPENDENCY_EDGES,
  ANNOTATIONS,
} from './constants';
import { PulseGlow } from './PulseGlow';
import { CodeBlock } from './CodeBlock';
import { DependencyLines } from './DependencyLines';
import { CodeComment } from './CodeComment';

export const defaultWhereToStart02LegacyCodebaseRevealProps = {};

export const WhereToStart02LegacyCodebaseReveal: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Ambient debt pulse — red radial glow */}
      <PulseGlow />

      {/* Dependency lines (rendered below blocks for layering) */}
      <DependencyLines blocks={FILE_BLOCKS} edges={DEPENDENCY_EDGES} />

      {/* File blocks — staggered appearance from center outward */}
      {FILE_BLOCKS.map((block) => {
        // Stagger: 2 frames per block, ordered by cluster then index
        const staggerDelay = block.cluster * 3 + (block.id % 7) * 2;
        return (
          <CodeBlock
            key={block.id}
            block={block}
            staggerDelay={staggerDelay}
          />
        );
      })}

      {/* Code annotations — red italic comments */}
      {ANNOTATIONS.map((ann, i) => (
        <CodeComment
          key={i}
          text={ann.text}
          x={ann.x}
          y={ann.y}
          opacity={ann.opacity}
          startFrame={ann.startFrame}
          jitter={2}
        />
      ))}
    </AbsoluteFill>
  );
};

export default WhereToStart02LegacyCodebaseReveal;
