import React from "react";
import { interpolate, Easing, useCurrentFrame } from "remotion";
import {
  GRID_ROWS,
  GRID_COLS,
  TILE_WIDTH,
  TILE_HEIGHT,
  TILE_GAP,
  TILE_PADDING,
  CODE_TILE_BG,
  DIFF_GREEN,
  DIFF_RED,
  TODO_RED,
  COMMENT_GRAY,
  CODE_TEXT_SLATE,
  CODE_KEYWORD_PURPLE,
  CODE_STRING_GREEN,
  INLINE_COMMENTS,
} from "./constants";

// Deterministic pseudo-random from seed
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 49297) * 49297;
  return x - Math.floor(x);
}

// Small code snippets to fill tiles
const CODE_SNIPPETS = [
  ["fn check(x) {", "  if x == nil {", "    return err", "  }", "}"],
  ["let val = db", "  .query(id)", "  .await?;", "ok(val)"],
  ["match res {", "  Ok(v) => v,", "  Err(_) => {", "    log(e);", "  }", "}"],
  ["for item in", "  items.iter()", "{", "  process(item)", "}"],
  ["pub fn new()", "  -> Self {", "  Self {", "    count: 0,", "  }", "}"],
  ["use std::io;", "use crate::", "  config;", "use super::", "  util;"],
  ["impl Display", "  for Node {", '  fn fmt(&self', '    f: &mut', '  ) {}', '}'],
  ["#[derive(", "  Debug,", "  Clone,", "  Serialize", ")]"],
];

interface CodeTileProps {
  row: number;
  col: number;
  tileIndex: number;
  revealFrame: number;
}

const CodeTile: React.FC<CodeTileProps> = ({
  row,
  col,
  tileIndex,
  revealFrame,
}) => {
  const frame = useCurrentFrame();
  const seed = tileIndex * 37 + 7;
  const rand = seededRandom(seed);

  // Tile reveal animation
  const opacity = interpolate(frame, [revealFrame, revealFrame + 12], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const scale = interpolate(
    frame,
    [revealFrame, revealFrame + 12],
    [0.7, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const hasDiff = rand < 0.6;
  const diffIsGreen = seededRandom(seed + 1) > 0.4;
  const hasTodo = seededRandom(seed + 2) < 0.15;
  const hasComment =
    seededRandom(seed + 3) < 0.3 && !hasTodo;
  const snippetIdx = Math.floor(seededRandom(seed + 4) * CODE_SNIPPETS.length);
  const commentIdx = Math.floor(
    seededRandom(seed + 5) * INLINE_COMMENTS.length
  );

  const snippet = CODE_SNIPPETS[snippetIdx];

  const x = col * (TILE_WIDTH + TILE_GAP);
  const y = row * (TILE_HEIGHT + TILE_GAP);

  // TODO badge pop-in
  const todoBadgeScale = hasTodo
    ? interpolate(frame, [revealFrame + 8, revealFrame + 18], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.back(1.3)),
      })
    : 0;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: TILE_WIDTH,
        height: TILE_HEIGHT,
        backgroundColor: CODE_TILE_BG,
        borderRadius: 4,
        opacity,
        transform: `scale(${scale})`,
        overflow: "hidden",
        padding: TILE_PADDING,
        boxSizing: "border-box",
      }}
    >
      {/* Diff marker bar */}
      {hasDiff && (
        <div
          style={{
            position: "absolute",
            left: 0,
            top: 4,
            bottom: 4,
            width: 3,
            backgroundColor: diffIsGreen ? DIFF_GREEN : DIFF_RED,
            borderRadius: 1,
            opacity: 0.7,
          }}
        />
      )}

      {/* Code lines */}
      {snippet.map((line, i) => (
        <div
          key={i}
          style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 7,
            lineHeight: "11px",
            color: CODE_TEXT_SLATE,
            whiteSpace: "nowrap",
            overflow: "hidden",
          }}
        >
          {line.startsWith("fn ") || line.startsWith("pub ") || line.startsWith("use ") ? (
            <span style={{ color: CODE_KEYWORD_PURPLE }}>{line}</span>
          ) : line.includes('"') || line.includes("'") ? (
            <span style={{ color: CODE_STRING_GREEN }}>{line}</span>
          ) : (
            line
          )}
        </div>
      ))}

      {/* Inline comment */}
      {hasComment && (
        <div
          style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 7,
            lineHeight: "10px",
            color: COMMENT_GRAY,
            opacity: 0.3,
            whiteSpace: "nowrap",
            marginTop: 2,
          }}
        >
          {INLINE_COMMENTS[commentIdx]}
        </div>
      )}

      {/* TODO badge */}
      {hasTodo && (
        <div
          style={{
            position: "absolute",
            top: 4,
            right: 4,
            backgroundColor: TODO_RED,
            color: "#FFFFFF",
            fontFamily: "Inter, sans-serif",
            fontSize: 6,
            fontWeight: 600,
            padding: "1px 4px",
            borderRadius: 2,
            opacity: 0.5,
            transform: `scale(${todoBadgeScale})`,
          }}
        >
          TODO
        </div>
      )}
    </div>
  );
};

interface CodeTileGridProps {
  /** Frame at which the grid starts revealing (stagger offset is added per row) */
  revealStartFrame: number;
}

export const CodeTileGrid: React.FC<CodeTileGridProps> = ({
  revealStartFrame,
}) => {
  const tiles: React.ReactNode[] = [];

  for (let row = 0; row < GRID_ROWS; row++) {
    for (let col = 0; col < GRID_COLS; col++) {
      const tileIndex = row * GRID_COLS + col;
      // 3-frame stagger per row
      const revealFrame = revealStartFrame + row * 3;
      tiles.push(
        <CodeTile
          key={tileIndex}
          row={row}
          col={col}
          tileIndex={tileIndex}
          revealFrame={revealFrame}
        />
      );
    }
  }

  const gridWidth = GRID_COLS * (TILE_WIDTH + TILE_GAP) - TILE_GAP;
  const gridHeight = GRID_ROWS * (TILE_HEIGHT + TILE_GAP) - TILE_GAP;

  return (
    <div
      style={{
        position: "absolute",
        width: gridWidth,
        height: gridHeight,
        left: "50%",
        top: "50%",
        transform: "translate(-50%, -50%)",
      }}
    >
      {tiles}
    </div>
  );
};
