import React from 'react';
import { AbsoluteFill, useCurrentFrame } from 'remotion';
import {
  COLORS,
  EDITOR,
  NATURAL_LINES_1,
  CODE_LINES,
  NATURAL_LINES_2,
} from './constants';
import { EditorWindow } from './EditorWindow';
import { TypedLines } from './TypedLines';
import { CodeBlockBg } from './CodeBlockBg';
import { BracketLabel } from './BracketLabel';
import { FloatingAnnotation } from './FloatingAnnotation';

export const defaultPart4PrecisionTradeoff07EmbeddedCodeDocumentProps = {};

/**
 * 07_embedded_code_document — "The Fluid Boundary Between Prompt and Code"
 *
 * A .prompt file shown at large scale with natural language sections and an
 * embedded code block. The visual contrast between the two "materials" is
 * the central motif.
 *
 * 480 frames @ 30fps = 16 seconds
 */
export const Part4PrecisionTradeoff07EmbeddedCodeDocument: React.FC = () => {
  const frame = useCurrentFrame();

  // Y positions within the editor body for code block background
  // Lines 1-8 are natural language (lineHeight=22, starting at y=12)
  // Lines 9-18 are code block
  const codeBlockYStart = 12 + 8 * 22; // after 8 natural language lines
  const codeBlockHeight = 10 * 22; // 10 code lines

  // Y positions for bracket labels (relative to the absolute canvas)
  // Editor body starts at EDITOR.y + titleBarHeight (80 + 30 = 110)
  const editorBodyTop = EDITOR.y + 30;
  const naturalSection1Top = editorBodyTop + 12;
  const naturalSection1Bottom = naturalSection1Top + 8 * 22;
  const codeTop = naturalSection1Bottom;
  const codeBottom = codeTop + 10 * 22;
  const naturalSection2Top = codeBottom;
  const naturalSection2Bottom = naturalSection2Top + 6 * 22;

  // Label X position (right side of the editor window)
  const labelX = EDITOR.x + EDITOR.width + 20;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        overflow: 'hidden',
      }}
    >
      {/* Editor Window — visible from frame 0 */}
      <EditorWindow>
        {/* Natural language section 1 (lines 1-8): frames 30-120 */}
        <TypedLines
          lines={NATURAL_LINES_1}
          startFrame={30}
          startLineNumber={1}
          isCode={false}
        />

        {/* Code block background: frames 120+ */}
        {frame >= 120 && (
          <CodeBlockBg
            startFrame={120}
            yOffset={codeBlockYStart}
            height={codeBlockHeight}
          />
        )}

        {/* Code lines (lines 9-18): frames 140-240 */}
        {frame >= 140 && (
          <TypedLines
            lines={CODE_LINES}
            startFrame={140}
            startLineNumber={9}
            isCode={true}
          />
        )}

        {/* Natural language section 2 (lines 19-24): frames 260-340 */}
        {frame >= 260 && (
          <TypedLines
            lines={NATURAL_LINES_2}
            startFrame={260}
            startLineNumber={19}
            isCode={false}
          />
        )}
      </EditorWindow>

      {/* Section labels with brackets */}
      {/* "Intent (natural language)" — appears at frame 120 */}
      {frame >= 120 && (
        <BracketLabel
          text="Intent (natural language)"
          color={COLORS.intentLabel}
          startFrame={120}
          yTop={naturalSection1Top}
          yBottom={naturalSection1Bottom}
          x={labelX}
          pulseStart={340}
          pulseEnd={420}
        />
      )}

      {/* "Critical algorithm (code)" — appears at frame 240 */}
      {frame >= 240 && (
        <BracketLabel
          text="Critical algorithm (code)"
          color={COLORS.codeLabel}
          startFrame={240}
          yTop={codeTop}
          yBottom={codeBottom}
          x={labelX}
          pulseStart={340}
          pulseEnd={420}
        />
      )}

      {/* "Constraints (natural language)" — appears at frame 340 */}
      {frame >= 340 && (
        <BracketLabel
          text="Constraints (natural language)"
          color={COLORS.intentLabel}
          startFrame={340}
          yTop={naturalSection2Top}
          yBottom={naturalSection2Bottom}
          x={labelX}
          pulseStart={370}
          pulseEnd={420}
        />
      )}

      {/* Floating annotation — appears at frame 420 */}
      {frame >= 420 && (
        <FloatingAnnotation startFrame={420} y={920} />
      )}
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff07EmbeddedCodeDocument;
