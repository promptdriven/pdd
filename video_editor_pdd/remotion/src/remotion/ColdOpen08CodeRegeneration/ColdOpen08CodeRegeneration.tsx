import React from 'react';
import { AbsoluteFill } from 'remotion';
import {
  BG_COLOR,
  EDITOR_GUTTER_BG,
  GUTTER_WIDTH,
  CODE_PADDING_TOP,
  CANVAS_HEIGHT,
  LINE_NUMBER_COLOR,
} from './constants';
import { SelectionHighlight } from './SelectionHighlight';
import { CodeLines } from './CodeLines';
import { TerminalOverlay } from './TerminalOverlay';

export const defaultColdOpen08CodeRegenerationProps = {};

/**
 * Section 0.8 — Code Regeneration: Delete and Rebuild
 *
 * The patched function selects, deletes, and is regenerated clean —
 * line by line — with a terminal confirmation overlay.
 *
 * Duration: 60 frames @ 30fps (2s)
 */
export const ColdOpen08CodeRegeneration: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: '"JetBrains Mono", "Fira Code", "Cascadia Code", monospace',
        overflow: 'hidden',
      }}
    >
      {/* Editor gutter background */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: GUTTER_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: EDITOR_GUTTER_BG,
          borderRight: `1px solid ${LINE_NUMBER_COLOR}33`,
        }}
      />

      {/* Editor top bar (VS Code style) */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: CODE_PADDING_TOP - 4,
          backgroundColor: EDITOR_GUTTER_BG,
          borderBottom: `1px solid ${LINE_NUMBER_COLOR}33`,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 16,
        }}
      >
        {/* Window controls */}
        <div style={{ display: 'flex', gap: 8 }}>
          <div
            style={{
              width: 12,
              height: 12,
              borderRadius: '50%',
              backgroundColor: '#F38BA8',
              opacity: 0.8,
            }}
          />
          <div
            style={{
              width: 12,
              height: 12,
              borderRadius: '50%',
              backgroundColor: '#F9E2AF',
              opacity: 0.8,
            }}
          />
          <div
            style={{
              width: 12,
              height: 12,
              borderRadius: '50%',
              backgroundColor: '#A6E3A1',
              opacity: 0.8,
            }}
          />
        </div>
        {/* File tab */}
        <div
          style={{
            marginLeft: 24,
            color: LINE_NUMBER_COLOR,
            fontSize: 13,
            opacity: 0.85,
          }}
        >
          order_service.py
        </div>
      </div>

      {/* Selection highlight overlay */}
      <SelectionHighlight />

      {/* Code lines (patched → delete → void → regenerated) */}
      <CodeLines />

      {/* Terminal overlay (bottom-right) */}
      <TerminalOverlay />
    </AbsoluteFill>
  );
};

export default ColdOpen08CodeRegeneration;
