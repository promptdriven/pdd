import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  WIDTH,
  HEIGHT,
  EDITOR_TOP_PADDING,
  LINE_HEIGHT,
  FADE_IN_DURATION,
  CURSOR_LINE,
  CURSOR_COLUMN,
} from "./constants";
import { CodeLine, kw, fn, str, typ, op, num, cmt, todo, hotfix, v, plain } from "./CodeLine";
import type { PatchAge } from "./CodeLine";
import { BlinkingCursor } from "./BlinkingCursor";

// ─── Patch metadata ───
// Maps 1-indexed line numbers to their patch age for left-border colouring.
const PATCH_AGE_MAP: Record<number, PatchAge> = {
  5: "old",
  12: "old",
  18: "medium",
  23: "recent",
  31: "medium",
  37: "recent",
};

// ─── 40-line Python function with patch comments ───
// Each entry is an array of tokens for one line of code.
type Token = { text: string; type: string };
const CODE_LINES: Token[][] = [
  /* 1  */ [kw("def "), fn("process_order"), op("("), v("order"), op(": "), typ("Dict"), op(", "), v("ctx"), op(": "), typ("Context"), op(") -> "), typ("Result"), op(":")],
  /* 2  */ [plain("    "), str('"""Process an incoming order through validation pipeline."""')],
  /* 3  */ [plain("    "), v("logger"), op(" = "), v("ctx"), op("."), fn("get_logger"), op("("), str('"order_processor"'), op(")")],
  /* 4  */ [plain("    "), v("logger"), op("."), fn("info"), op("("), str('"Processing order %s"'), op(", "), v("order"), op("["), str('"id"'), op("])")],
  /* 5  */ [plain("    "), cmt("# PATCH: fixed null check")],
  /* 6  */ [plain("    "), kw("if"), v(" order"), op(" is "), kw("None"), kw(" or "), kw("not"), v(" order"), op("."), fn("get"), op("("), str('"items"'), op("):")],
  /* 7  */ [plain("        "), kw("return"), v(" Result"), op("("), v("success"), op("="), kw("False"), op(", "), v("error"), op("="), str('"empty_order"'), op(")")],
  /* 8  */ [plain("")],
  /* 9  */ [plain("    "), v("items"), op(" = "), v("order"), op("["), str('"items"'), op("]")],
  /* 10 */ [plain("    "), v("total"), op(" = "), num("0.0")],
  /* 11 */ [plain("    "), v("validated"), op(" = "), op("[]")],
  /* 12 */ [plain("    "), todo("# TODO: refactor this block")],
  /* 13 */ [plain("    "), kw("for"), v(" item"), kw(" in"), v(" items"), op(":")],
  /* 14 */ [plain("        "), kw("if"), v(" item"), op("."), fn("get"), op("("), str('"price"'), op(")"), op(" is "), kw("None"), op(":")],
  /* 15 */ [plain("            "), kw("continue")],
  /* 16 */ [plain("        "), v("price"), op(" = "), fn("float"), op("("), v("item"), op("["), str('"price"'), op("])")],
  /* 17 */ [plain("        "), v("qty"), op(" = "), v("item"), op("."), fn("get"), op("("), str('"quantity"'), op(", "), num("1"), op(")")],
  /* 18 */ [plain("        "), hotfix("# HOTFIX: edge case #1247")],
  /* 19 */ [plain("        "), kw("if"), v(" qty"), op(" <= "), num("0"), kw(" or"), v(" qty"), op(" > "), num("9999"), op(":")],
  /* 20 */ [plain("            "), v("qty"), op(" = "), fn("max"), op("("), num("1"), op(", "), fn("min"), op("("), v("qty"), op(", "), num("9999"), op("))")],
  /* 21 */ [plain("        "), v("subtotal"), op(" = "), v("price"), op(" * "), v("qty")],
  /* 22 */ [plain("        "), v("total"), op(" += "), v("subtotal")],
  /* 23 */ [plain("        "), cmt("# PATCH: handle empty list")],
  /* 24 */ [plain("        "), kw("if"), v(" subtotal"), op(" > "), num("0"), op(":")],
  /* 25 */ [plain("            "), v("validated"), op("."), fn("append"), op("({")],
  /* 26 */ [plain("                "), str('"sku"'), op(": "), v("item"), op("["), str('"sku"'), op("],")],
  /* 27 */ [plain("                "), str('"amount"'), op(": "), v("subtotal"), op(",")],
  /* 28 */ [plain("                "), str('"ts"'), op(": "), v("ctx"), op("."), fn("now"), op("(),")],
  /* 29 */ [plain("            "), op("})")],
  /* 30 */ [plain("")],
  /* 31 */ [plain("    "), cmt("# PATCH: timezone fix")],
  /* 32 */ [plain("    "), v("created_at"), op(" = "), v("ctx"), op("."), fn("now_utc"), op("()")],
  /* 33 */ [plain("    "), kw("if "), kw("not"), v(" validated"), op(":")],
  /* 34 */ [plain("        "), v("logger"), op("."), fn("warn"), op("("), str('"No valid items in order %s"'), op(", "), v("order"), op("["), str('"id"'), op("])")],
  /* 35 */ [plain("        "), kw("return"), v(" Result"), op("("), v("success"), op("="), kw("False"), op(", "), v("error"), op("="), str('"no_valid_items"'), op(")")],
  /* 36 */ [plain("")],
  /* 37 */ [plain("    "), hotfix("# HOTFIX: race condition")],
  /* 38 */ [plain("    "), kw("with"), v(" ctx"), op("."), fn("db_lock"), op("("), v("order"), op("["), str('"id"'), op("]):")],
  /* 39 */ [plain("        "), v("receipt"), op(" = "), v("ctx"), op("."), fn("store"), op("."), fn("save_order"), op("("), v("validated"), op(", "), v("total"), op(", "), v("created_at"), op(")")],
  /* 40 */ [plain("    "), kw("return"), v(" Result"), op("("), v("success"), op("="), kw("True"), op(", "), v("data"), op("="), v("receipt"), op(")")],
];

export const defaultColdOpen07CodeCursorBlinkProps = {};

export const ColdOpen07CodeCursorBlink: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Fade in over first 10 frames ───
  const opacity = interpolate(frame, [0, FADE_IN_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Determine visible line range — show lines that fit within the viewport,
  // centered roughly around the cursor line (line 23).
  const maxVisibleLines = Math.floor((HEIGHT - EDITOR_TOP_PADDING * 2) / LINE_HEIGHT);
  const totalLines = CODE_LINES.length;
  // Aim to have cursor line near the vertical centre
  const idealStart = CURSOR_LINE - Math.floor(maxVisibleLines / 2);
  const startLine = Math.max(0, Math.min(idealStart, totalLines - maxVisibleLines));
  const endLine = Math.min(totalLines, startLine + maxVisibleLines);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: "hidden",
      }}
    >
      <div style={{ opacity, width: "100%", height: "100%" }}>
        {/* Code lines */}
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            right: 0,
            bottom: 0,
          }}
        >
          {CODE_LINES.slice(startLine, endLine).map((tokens, idx) => {
            const lineNum = startLine + idx + 1; // 1-indexed
            const yOffset = EDITOR_TOP_PADDING + idx * LINE_HEIGHT;
            return (
              <CodeLine
                key={lineNum}
                lineNumber={lineNum}
                tokens={tokens as any}
                patchAge={PATCH_AGE_MAP[lineNum] ?? null}
                yOffset={yOffset}
              />
            );
          })}
        </div>

        {/* Blinking cursor */}
        <BlinkingCursor
          line={CURSOR_LINE - startLine}
          column={CURSOR_COLUMN}
        />
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen07CodeCursorBlink;
