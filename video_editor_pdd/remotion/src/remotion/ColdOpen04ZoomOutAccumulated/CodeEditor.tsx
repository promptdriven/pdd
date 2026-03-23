import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CodeLine,
  EDITOR_BG,
  TAB_BAR_BG,
  TAB_ACTIVE_BG,
  TAB_BORDER,
  HIGHLIGHT_GREEN,
  HIGHLIGHT_GREEN_BG,
  TEXT_PRIMARY,
  TEXT_DIM,
  LINE_HEIGHT,
  CODE_FONT_SIZE,
  CODE_LEFT_PADDING,
  LINE_NUMBER_WIDTH,
  TAB_HEIGHT,
  TabData,
} from "./constants";

// ── Tab Bar ─────────────────────────────────────────────────────────
interface TabBarProps {
  tabs: TabData[];
}

export const TabBar: React.FC<TabBarProps> = ({ tabs }) => {
  return (
    <div
      style={{
        display: "flex",
        height: TAB_HEIGHT,
        backgroundColor: TAB_BAR_BG,
        borderBottom: `1px solid ${TAB_BORDER}`,
        overflow: "hidden",
      }}
    >
      {tabs.map((tab, i) => (
        <div
          key={i}
          style={{
            display: "flex",
            alignItems: "center",
            padding: "0 14px",
            height: "100%",
            backgroundColor: tab.isActive ? TAB_ACTIVE_BG : TAB_BAR_BG,
            borderRight: `1px solid ${TAB_BORDER}`,
            gap: 6,
            minWidth: 0,
          }}
        >
          {tab.isModified && (
            <div
              style={{
                width: 7,
                height: 7,
                borderRadius: "50%",
                backgroundColor: HIGHLIGHT_GREEN,
                flexShrink: 0,
              }}
            />
          )}
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 11,
              color: tab.isActive ? TEXT_PRIMARY : TEXT_DIM,
              opacity: tab.isActive ? 0.9 : 0.7,
              whiteSpace: "nowrap",
            }}
          >
            {tab.name}
          </span>
        </div>
      ))}
    </div>
  );
};

// ── Code Block ──────────────────────────────────────────────────────
interface CodeBlockProps {
  lines: CodeLine[];
  showCursor?: boolean;
  cursorLine?: number;
}

export const CodeBlock: React.FC<CodeBlockProps> = ({
  lines,
  showCursor = false,
  cursorLine = 14,
}) => {
  const frame = useCurrentFrame();
  const cursorVisible = showCursor && Math.floor(frame / 15) % 2 === 0;

  return (
    <div
      style={{
        backgroundColor: EDITOR_BG,
        flex: 1,
        padding: "8px 0",
        overflow: "hidden",
      }}
    >
      {lines.map((line) => {
        const isTarget = line.lineNum === cursorLine;
        return (
          <div
            key={line.lineNum}
            style={{
              display: "flex",
              height: LINE_HEIGHT,
              alignItems: "center",
              backgroundColor: line.isHighlighted
                ? HIGHLIGHT_GREEN_BG
                : "transparent",
              borderLeft: line.isHighlighted
                ? `3px solid ${HIGHLIGHT_GREEN}`
                : "3px solid transparent",
            }}
          >
            {/* Line number */}
            <span
              style={{
                width: LINE_NUMBER_WIDTH,
                textAlign: "right",
                paddingRight: 12,
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: CODE_FONT_SIZE - 2,
                color: TEXT_DIM,
                opacity: 0.5,
                userSelect: "none",
                flexShrink: 0,
              }}
            >
              {line.lineNum}
            </span>

            {/* Code tokens */}
            <span
              style={{
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: CODE_FONT_SIZE,
                whiteSpace: "pre",
              }}
            >
              {line.tokens.map((token, j) => (
                <span key={j} style={{ color: token.color }}>
                  {token.text}
                </span>
              ))}
              {/* Cursor */}
              {isTarget && cursorVisible && (
                <span
                  style={{
                    display: "inline-block",
                    width: 2,
                    height: CODE_FONT_SIZE + 2,
                    backgroundColor: TEXT_PRIMARY,
                    verticalAlign: "middle",
                    marginLeft: 1,
                  }}
                />
              )}
            </span>
          </div>
        );
      })}
    </div>
  );
};

// ── Mini Code Pane (for zoomed-out multi-pane view) ─────────────────
interface MiniCodePaneProps {
  lines: CodeLine[];
  title: string;
  width: number;
  height: number;
}

export const MiniCodePane: React.FC<MiniCodePaneProps> = ({
  lines,
  title,
  width,
  height,
}) => {
  return (
    <div
      style={{
        width,
        height,
        backgroundColor: EDITOR_BG,
        border: `1px solid ${TAB_BORDER}`,
        borderRadius: 4,
        overflow: "hidden",
        display: "flex",
        flexDirection: "column",
      }}
    >
      {/* Mini tab */}
      <div
        style={{
          height: 22,
          backgroundColor: TAB_BAR_BG,
          borderBottom: `1px solid ${TAB_BORDER}`,
          display: "flex",
          alignItems: "center",
          padding: "0 8px",
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 8,
            color: TEXT_DIM,
            opacity: 0.7,
          }}
        >
          {title}
        </span>
      </div>

      {/* Mini code lines */}
      <div style={{ padding: "4px 8px", flex: 1, overflow: "hidden" }}>
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              height: 12,
              display: "flex",
              alignItems: "center",
            }}
          >
            <span
              style={{
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 7,
                whiteSpace: "pre",
              }}
            >
              {line.tokens.map((token, j) => (
                <span key={j} style={{ color: token.color }}>
                  {token.text}
                </span>
              ))}
            </span>
          </div>
        ))}
      </div>
    </div>
  );
};

export default CodeBlock;
