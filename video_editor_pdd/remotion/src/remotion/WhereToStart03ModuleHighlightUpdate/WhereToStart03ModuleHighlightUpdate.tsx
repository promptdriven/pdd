import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import { BG_COLOR } from './constants';
import CodebaseBackground from './CodebaseBackground';
import ParticleStream from './ParticleStream';
import PromptDocument from './PromptDocument';
import TerminalPanel from './TerminalPanel';

export const defaultWhereToStart03ModuleHighlightUpdateProps = {};

/**
 * Section 6.3: Module Highlight & Update — Extracting a Prompt from Existing Code
 *
 * From a dense brownfield codebase, a single module (auth_handler.py) highlights
 * with a blue selection glow. A terminal command `pdd update auth_handler.py`
 * triggers a particle stream that flows from the code block into a materializing
 * .prompt document, demonstrating PDD's ability to create prompts FROM existing code.
 *
 * Duration: 240 frames (8s @ 30fps)
 *
 * Animation timeline:
 * - Frame 0-20:   Codebase dims, selected module pulses with blue glow
 * - Frame 20-40:  Label "auth_handler.py" appears, terminal fades in
 * - Frame 40-70:  Terminal command types out
 * - Frame 70-80:  Terminal shows "Analyzing module..."
 * - Frame 80-160: Particle stream flows, prompt document materializes with lines
 * - Frame 160-180: Terminal shows success, prompt fully visible
 * - Frame 180-240: Hold — code block and prompt document side by side
 */
export const WhereToStart03ModuleHighlightUpdate: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Dimmed codebase background with selected module and label */}
      <CodebaseBackground />

      {/* Particle stream: flows from code block to prompt document area */}
      {/* Starts at frame 80 */}
      <ParticleStream startFrame={80} />

      {/* Prompt document materializes starting at frame 100 */}
      <PromptDocument startFrame={100} />

      {/* Terminal panel in bottom-right, appears at frame 20 */}
      <TerminalPanel startFrame={20} />
    </AbsoluteFill>
  );
};

export default WhereToStart03ModuleHighlightUpdate;
