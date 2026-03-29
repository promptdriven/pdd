import React from 'react';

// ============================================================
// CodeLines — renders 40 lines of a heavily-patched Python function
// with syntax highlighting, line numbers, and patch-age borders
// ============================================================

// --- constants inlined to avoid cross-file imports ---
const GUTTER_WIDTH = 60;
const LINE_HEIGHT = 22;
const CODE_PADDING_TOP = 40;
const CODE_PADDING_LEFT = 16;
const CODE_FONT_SIZE = 14;
const LINE_NUMBER_FONT_SIZE = 12;
const FONT_FAMILY = '"JetBrains Mono", "Fira Code", "Cascadia Code", monospace';

const COLOR_LINE_NUMBER = '#6C7086';
const COLOR_TEXT = '#CDD6F4';
const COLOR_KEYWORD = '#CBA6F7';
const COLOR_FUNCTION = '#89B4FA';
const COLOR_STRING = '#A6E3A1';
const COLOR_TYPE = '#F9E2AF';
const COLOR_PARAM = '#FAB387';
const COLOR_OPERATOR = '#89DCEB';
const COLOR_NUMBER = '#FAB387';
const COLOR_COMMENT = '#6C7086';
const COLOR_TODO_COMMENT = '#F9E2AF';
const COLOR_HOTFIX_COMMENT = '#F38BA8';

const PATCH_RECENT_COLOR = '#A6E3A1';
const PATCH_RECENT_OPACITY = 0.15;
const PATCH_MEDIUM_COLOR = '#F9E2AF';
const PATCH_MEDIUM_OPACITY = 0.05;
const PATCH_OLD_COLOR = '#A6E3A1';
const PATCH_OLD_OPACITY = 0.05;

// --- types ---
interface CodeToken {
  text: string;
  color: string;
  italic?: boolean;
}

interface PatchBorder {
  color: string;
  opacity: number;
}

// Map from 1-indexed line number → patch border style
const PATCH_BORDERS: Record<number, PatchBorder> = {
  5: { color: PATCH_OLD_COLOR, opacity: PATCH_OLD_OPACITY },
  6: { color: PATCH_OLD_COLOR, opacity: PATCH_OLD_OPACITY },
  12: { color: PATCH_OLD_COLOR, opacity: PATCH_OLD_OPACITY },
  13: { color: PATCH_OLD_COLOR, opacity: PATCH_OLD_OPACITY },
  18: { color: PATCH_MEDIUM_COLOR, opacity: PATCH_MEDIUM_OPACITY },
  19: { color: PATCH_MEDIUM_COLOR, opacity: PATCH_MEDIUM_OPACITY },
  20: { color: PATCH_MEDIUM_COLOR, opacity: PATCH_MEDIUM_OPACITY },
  23: { color: PATCH_RECENT_COLOR, opacity: PATCH_RECENT_OPACITY },
  24: { color: PATCH_RECENT_COLOR, opacity: PATCH_RECENT_OPACITY },
  25: { color: PATCH_RECENT_COLOR, opacity: PATCH_RECENT_OPACITY },
  31: { color: PATCH_MEDIUM_COLOR, opacity: PATCH_MEDIUM_OPACITY },
  32: { color: PATCH_MEDIUM_COLOR, opacity: PATCH_MEDIUM_OPACITY },
  37: { color: PATCH_RECENT_COLOR, opacity: PATCH_RECENT_OPACITY },
  38: { color: PATCH_RECENT_COLOR, opacity: PATCH_RECENT_OPACITY },
};

// Helper to build a token
const t = (text: string, color: string, italic?: boolean): CodeToken => ({
  text,
  color,
  italic,
});

// --- 40 lines of heavily-patched Python ---
const CODE_LINES: CodeToken[][] = [
  // Line 1
  [t('def ', COLOR_KEYWORD), t('process_order', COLOR_FUNCTION), t('(', COLOR_TEXT), t('order', COLOR_PARAM), t(': ', COLOR_OPERATOR), t('Dict', COLOR_TYPE), t(', ', COLOR_TEXT), t('ctx', COLOR_PARAM), t(': ', COLOR_OPERATOR), t('Context', COLOR_TYPE), t(') -> ', COLOR_OPERATOR), t('Result', COLOR_TYPE), t(':', COLOR_TEXT)],
  // Line 2
  [t('    ', COLOR_TEXT), t('"""Process an incoming order through validation pipeline."""', COLOR_STRING)],
  // Line 3
  [t('    ', COLOR_TEXT), t('logger', COLOR_TEXT), t('.', COLOR_TEXT), t('info', COLOR_FUNCTION), t('(', COLOR_TEXT), t('f"Processing order {order.id}"', COLOR_STRING), t(')', COLOR_TEXT)],
  // Line 4
  [],
  // Line 5 — PATCH comment (old)
  [t('    # PATCH: fixed null check', COLOR_COMMENT, true)],
  // Line 6
  [t('    ', COLOR_TEXT), t('if', COLOR_KEYWORD), t(' order ', COLOR_TEXT), t('is', COLOR_KEYWORD), t(' ', COLOR_TEXT), t('None', COLOR_KEYWORD), t(' ', COLOR_TEXT), t('or', COLOR_KEYWORD), t(' ', COLOR_TEXT), t('not', COLOR_KEYWORD), t(' order.items:', COLOR_TEXT)],
  // Line 7
  [t('        ', COLOR_TEXT), t('return', COLOR_KEYWORD), t(' Result(', COLOR_TEXT), t('status', COLOR_PARAM), t('=', COLOR_OPERATOR), t('"failed"', COLOR_STRING), t(', ', COLOR_TEXT), t('error', COLOR_PARAM), t('=', COLOR_OPERATOR), t('"Invalid order"', COLOR_STRING), t(')', COLOR_TEXT)],
  // Line 8
  [],
  // Line 9
  [t('    ', COLOR_TEXT), t('validated', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('validate_schema', COLOR_FUNCTION), t('(order.', COLOR_TEXT), t('payload', COLOR_TEXT), t(')', COLOR_TEXT)],
  // Line 10
  [t('    ', COLOR_TEXT), t('if', COLOR_KEYWORD), t(' ', COLOR_TEXT), t('not', COLOR_KEYWORD), t(' validated.ok:', COLOR_TEXT)],
  // Line 11
  [t('        ', COLOR_TEXT), t('return', COLOR_KEYWORD), t(' Result(', COLOR_TEXT), t('status', COLOR_PARAM), t('=', COLOR_OPERATOR), t('"invalid"', COLOR_STRING), t(')', COLOR_TEXT)],
  // Line 12 — TODO comment (old)
  [t('    # TODO: refactor this block', COLOR_TODO_COMMENT, true)],
  // Line 13
  [t('    ', COLOR_TEXT), t('price', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('Decimal', COLOR_TYPE), t('(', COLOR_TEXT), t('"0"', COLOR_STRING), t(')', COLOR_TEXT)],
  // Line 14
  [t('    ', COLOR_TEXT), t('for', COLOR_KEYWORD), t(' item ', COLOR_TEXT), t('in', COLOR_KEYWORD), t(' order.items:', COLOR_TEXT)],
  // Line 15
  [t('        ', COLOR_TEXT), t('unit_price', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('get_price', COLOR_FUNCTION), t('(item.sku, ctx.region)', COLOR_TEXT)],
  // Line 16
  [t('        ', COLOR_TEXT), t('discount', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('apply_discount', COLOR_FUNCTION), t('(item, ctx.promo_code)', COLOR_TEXT)],
  // Line 17
  [t('        ', COLOR_TEXT), t('price', COLOR_TEXT), t(' += unit_price * item.qty - discount', COLOR_TEXT)],
  // Line 18 — HOTFIX comment (medium)
  [t('    # HOTFIX: edge case #1247', COLOR_HOTFIX_COMMENT, true)],
  // Line 19
  [t('    ', COLOR_TEXT), t('if', COLOR_KEYWORD), t(' price < ', COLOR_TEXT), t('Decimal', COLOR_TYPE), t('(', COLOR_TEXT), t('"0.01"', COLOR_STRING), t('):', COLOR_TEXT)],
  // Line 20
  [t('        ', COLOR_TEXT), t('price', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('Decimal', COLOR_TYPE), t('(', COLOR_TEXT), t('"0.01"', COLOR_STRING), t(')', COLOR_TEXT)],
  // Line 21
  [],
  // Line 22
  [t('    ', COLOR_TEXT), t('tax', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('compute_tax', COLOR_FUNCTION), t('(price, ctx.region)', COLOR_TEXT)],
  // Line 23 — PATCH comment (recent) — cursor line
  [t('    # PATCH: handle empty list', COLOR_COMMENT, true)],
  // Line 24
  [t('    ', COLOR_TEXT), t('shipping_opts', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('get_shipping', COLOR_FUNCTION), t('(order) ', COLOR_TEXT), t('or', COLOR_KEYWORD), t(' []', COLOR_TEXT)],
  // Line 25
  [t('    ', COLOR_TEXT), t('if', COLOR_KEYWORD), t(' ', COLOR_TEXT), t('len', COLOR_FUNCTION), t('(shipping_opts) == ', COLOR_TEXT), t('0', COLOR_NUMBER), t(':', COLOR_TEXT)],
  // Line 26
  [t('        ', COLOR_TEXT), t('shipping_opts', COLOR_TEXT), t(' = [', COLOR_TEXT), t('default_shipping', COLOR_FUNCTION), t('(ctx)]', COLOR_TEXT)],
  // Line 27
  [],
  // Line 28
  [t('    ', COLOR_TEXT), t('shipping', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('shipping_opts[', COLOR_TEXT), t('0', COLOR_NUMBER), t(']', COLOR_TEXT)],
  // Line 29
  [t('    ', COLOR_TEXT), t('total', COLOR_TEXT), t(' = price + tax + shipping.cost', COLOR_TEXT)],
  // Line 30
  [],
  // Line 31 — PATCH comment (medium)
  [t('    # PATCH: timezone fix', COLOR_COMMENT, true)],
  // Line 32
  [t('    ', COLOR_TEXT), t('ts', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('datetime', COLOR_TYPE), t('.', COLOR_TEXT), t('now', COLOR_FUNCTION), t('(', COLOR_TEXT), t('tz', COLOR_PARAM), t('=', COLOR_OPERATOR), t('timezone.utc', COLOR_TEXT), t(')', COLOR_TEXT)],
  // Line 33
  [t('    ', COLOR_TEXT), t('record', COLOR_TEXT), t(' = ', COLOR_OPERATOR), t('OrderRecord', COLOR_TYPE), t('(', COLOR_TEXT)],
  // Line 34
  [t('        ', COLOR_TEXT), t('order_id', COLOR_PARAM), t('=order.id, ', COLOR_TEXT), t('total', COLOR_PARAM), t('=total,', COLOR_TEXT)],
  // Line 35
  [t('        ', COLOR_TEXT), t('tax', COLOR_PARAM), t('=tax, ', COLOR_TEXT), t('shipping', COLOR_PARAM), t('=shipping.cost,', COLOR_TEXT)],
  // Line 36
  [t('        ', COLOR_TEXT), t('created_at', COLOR_PARAM), t('=ts', COLOR_TEXT)],
  // Line 37 — HOTFIX comment (recent)
  [t('    # HOTFIX: race condition', COLOR_HOTFIX_COMMENT, true)],
  // Line 38
  [t('    ', COLOR_TEXT), t('with', COLOR_KEYWORD), t(' ctx.', COLOR_TEXT), t('lock', COLOR_FUNCTION), t('(', COLOR_TEXT), t('"order_write"', COLOR_STRING), t('):', COLOR_TEXT)],
  // Line 39
  [t('        ', COLOR_TEXT), t('db', COLOR_TEXT), t('.', COLOR_TEXT), t('save', COLOR_FUNCTION), t('(record)', COLOR_TEXT)],
  // Line 40
  [t('    ', COLOR_TEXT), t('return', COLOR_KEYWORD), t(' Result(', COLOR_TEXT), t('status', COLOR_PARAM), t('=', COLOR_OPERATOR), t('"ok"', COLOR_STRING), t(', ', COLOR_TEXT), t('total', COLOR_PARAM), t('=total)', COLOR_TEXT)],
];

export const CodeLines: React.FC = () => {
  return (
    <div
      style={{
        position: 'absolute',
        top: CODE_PADDING_TOP,
        left: 0,
        right: 0,
        bottom: 0,
      }}
    >
      {CODE_LINES.map((tokens, idx) => {
        const lineNum = idx + 1;
        const border = PATCH_BORDERS[lineNum];

        return (
          <div
            key={lineNum}
            style={{
              display: 'flex',
              alignItems: 'center',
              height: LINE_HEIGHT,
              position: 'relative',
            }}
          >
            {/* Patch age left border */}
            {border && (
              <div
                style={{
                  position: 'absolute',
                  left: GUTTER_WIDTH - 4,
                  top: 0,
                  width: 3,
                  height: LINE_HEIGHT,
                  backgroundColor: border.color,
                  opacity: border.opacity,
                  borderRadius: 1,
                }}
              />
            )}

            {/* Line number */}
            <div
              style={{
                width: GUTTER_WIDTH,
                textAlign: 'right',
                paddingRight: 12,
                fontFamily: FONT_FAMILY,
                fontSize: LINE_NUMBER_FONT_SIZE,
                color: COLOR_LINE_NUMBER,
                opacity: 0.5,
                userSelect: 'none',
                flexShrink: 0,
              }}
            >
              {lineNum}
            </div>

            {/* Code tokens */}
            <div
              style={{
                paddingLeft: CODE_PADDING_LEFT,
                fontFamily: FONT_FAMILY,
                fontSize: CODE_FONT_SIZE,
                whiteSpace: 'pre',
                lineHeight: `${LINE_HEIGHT}px`,
              }}
            >
              {tokens.map((token, tIdx) => (
                <span
                  key={tIdx}
                  style={{
                    color: token.color,
                    fontStyle: token.italic ? 'italic' : 'normal',
                  }}
                >
                  {token.text}
                </span>
              ))}
            </div>
          </div>
        );
      })}
    </div>
  );
};

export default CodeLines;
