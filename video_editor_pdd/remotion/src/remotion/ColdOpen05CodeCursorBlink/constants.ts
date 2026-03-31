// constants.ts — Colors, dimensions, and code data for ColdOpen05CodeCursorBlink

// === Duration ===
export const DURATION_FRAMES = 210;
export const FPS = 30;

// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// === Editor Theme (Catppuccin Mocha) ===
export const BG_COLOR = "#1E1E2E";
export const GUTTER_BG = "#2D2D3D";
export const GUTTER_WIDTH = 60;
export const LINE_HIGHLIGHT_BG = "#2A2A3A";
export const TITLE_BAR_BG = "#181825";
export const TITLE_BAR_HEIGHT = 36;
export const TAB_BAR_HEIGHT = 36;

// === Syntax Colors ===
export const COLOR_TEXT = "#CDD6F4";
export const COLOR_KEYWORD = "#CBA6F7";
export const COLOR_FUNCTION = "#89B4FA";
export const COLOR_STRING = "#A6E3A1";
export const COLOR_COMMENT = "#6C7086";
export const COLOR_COMMENT_KEYWORD = "#F38BA8";
export const COLOR_LINE_NUMBER = "#6C7086";
export const COLOR_GUTTER_MODIFIED = "#FAB387";
export const COLOR_GUTTER_ADDED = "#A6E3A1";

// === Cursor ===
export const CURSOR_COLOR = "#CDD6F4";
export const CURSOR_WIDTH = 2;
export const CURSOR_HEIGHT = 20;
export const CURSOR_BLINK_MS = 530;

// === Typography ===
export const CODE_FONT = "monospace";
export const CODE_FONT_SIZE = 14;
export const CODE_LINE_HEIGHT = 22;
export const TITLE_FONT_SIZE = 13;

// === Animation Timing ===
export const FADE_IN_END = 15;
export const SCROLL_START = 15;
export const SCROLL_END = 90;
export const PULSE_START = 90;
export const PULSE_END = 210;
export const PULSE_CYCLE = 60;
export const PRE_FADE_START = 150;
export const PRE_FADE_END = 210;
export const SCROLL_PIXELS = 400;

// === Token Types ===
export type TokenType =
  | "keyword"
  | "function"
  | "string"
  | "comment"
  | "commentKeyword"
  | "text"
  | "operator"
  | "number"
  | "decorator";

export interface CodeToken {
  text: string;
  type: TokenType;
}

export interface CodeLineData {
  tokens: CodeToken[];
  gutterMark?: "modified" | "added" | "none";
  isPatchComment?: boolean;
}

// Helper to create tokens quickly
const t = (text: string, type: TokenType = "text"): CodeToken => ({
  text,
  type,
});

// === The Code: process_order.py ===
export const CODE_LINES: CodeLineData[] = [
  {
    tokens: [t("def ", "keyword"), t("process_order", "function"), t("(order, user, config):")],
    gutterMark: "none",
  },
  {
    tokens: [t('    """Process an incoming order through the fulfillment pipeline."""', "string")],
    gutterMark: "none",
  },
  {
    tokens: [t("    # HACK: workaround for #2847 — duplicate order IDs in staging", "comment")],
    gutterMark: "modified",
    isPatchComment: true,
  },
  {
    tokens: [
      t("    "),
      t("if", "keyword"),
      t(" order.id "),
      t("in", "keyword"),
      t(" _seen_orders:"),
    ],
    gutterMark: "modified",
  },
  {
    tokens: [
      t("        "),
      t("return", "keyword"),
      t(" "),
      t('{"status": "duplicate", "skipped": True}', "text"),
    ],
    gutterMark: "modified",
  },
  {
    tokens: [t("    _seen_orders.add(order.id)")],
    gutterMark: "modified",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [
      t("    validated "),
      t("=", "operator"),
      t(" validate_order_schema(order)"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("    "),
      t("if", "keyword"),
      t(" "),
      t("not", "keyword"),
      t(" validated:"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("        "),
      t("raise", "keyword"),
      t(" ValidationError("),
      t('"Invalid order schema"', "string"),
      t(")"),
    ],
    gutterMark: "none",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [t("    # TODO: refactor this — pricing logic shouldn't live here", "comment")],
    gutterMark: "none",
    isPatchComment: true,
  },
  {
    tokens: [
      t("    subtotal "),
      t("=", "operator"),
      t(" sum(item.price "),
      t("*", "operator"),
      t(" item.qty "),
      t("for", "keyword"),
      t(" item "),
      t("in", "keyword"),
      t(" order.items)"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("    "),
      t("if", "keyword"),
      t(" config.get("),
      t('"apply_discount"', "string"),
      t("):"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [t("        # PATCH: edge case from v2.3 — negative discounts", "comment")],
    gutterMark: "added",
    isPatchComment: true,
  },
  {
    tokens: [
      t("        discount "),
      t("=", "operator"),
      t(" max("),
      t("0", "number"),
      t(", calculate_discount(user, subtotal))"),
    ],
    gutterMark: "added",
  },
  {
    tokens: [
      t("        subtotal "),
      t("-=", "operator"),
      t(" discount"),
    ],
    gutterMark: "added",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [t("    # HACK: tax service returns null for non-US addresses", "comment")],
    gutterMark: "modified",
    isPatchComment: true,
  },
  {
    tokens: [
      t("    "),
      t("try", "keyword"),
      t(":"),
    ],
    gutterMark: "modified",
  },
  {
    tokens: [
      t("        tax "),
      t("=", "operator"),
      t(" tax_service.calculate(order.address, subtotal)"),
    ],
    gutterMark: "modified",
  },
  {
    tokens: [
      t("    "),
      t("except", "keyword"),
      t(" (TaxServiceError, TypeError):"),
    ],
    gutterMark: "modified",
  },
  {
    tokens: [
      t("        tax "),
      t("=", "operator"),
      t(" subtotal "),
      t("*", "operator"),
      t(" Decimal("),
      t('"0.08"', "string"),
      t(")  "),
      t("# fallback rate", "comment"),
    ],
    gutterMark: "modified",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [
      t("    total "),
      t("=", "operator"),
      t(" subtotal "),
      t("+", "operator"),
      t(" tax"),
    ],
    gutterMark: "none",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [t("    # TODO: extract shipping to its own module eventually", "comment")],
    gutterMark: "none",
    isPatchComment: true,
  },
  {
    tokens: [
      t("    shipping "),
      t("=", "operator"),
      t(" get_shipping_rate(order.address, order.items)"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("    "),
      t("if", "keyword"),
      t(" shipping "),
      t("is", "keyword"),
      t(" "),
      t("None", "keyword"),
      t(":"),
    ],
    gutterMark: "added",
  },
  {
    tokens: [
      t("        shipping "),
      t("=", "operator"),
      t(" Decimal("),
      t('"9.99"', "string"),
      t(")  "),
      t("# PATCH: default for unknown regions", "comment"),
    ],
    gutterMark: "added",
    isPatchComment: true,
  },
  {
    tokens: [
      t("    total "),
      t("+=", "operator"),
      t(" shipping"),
    ],
    gutterMark: "none",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [
      t("    charge "),
      t("=", "operator"),
      t(" payment_gateway.charge("),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("        user_id"),
      t("=", "operator"),
      t("user.id, amount"),
      t("=", "operator"),
      t("total, currency"),
      t("=", "operator"),
      t("order.currency"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [t("    )")],
    gutterMark: "none",
  },
  {
    tokens: [
      t("    "),
      t("if", "keyword"),
      t(" "),
      t("not", "keyword"),
      t(" charge.success:"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("        "),
      t("return", "keyword"),
      t(" "),
      t('{"status": "payment_failed", "error": charge.error}', "text"),
    ],
    gutterMark: "none",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [
      t("    record "),
      t("=", "operator"),
      t(" OrderRecord("),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("        order_id"),
      t("=", "operator"),
      t("order.id, user_id"),
      t("=", "operator"),
      t("user.id,"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("        total"),
      t("=", "operator"),
      t("total, tax"),
      t("=", "operator"),
      t("tax, shipping"),
      t("=", "operator"),
      t("shipping,"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [
      t("        status"),
      t("=", "operator"),
      t('"confirmed"', "string"),
      t(", charge_id"),
      t("=", "operator"),
      t("charge.id"),
    ],
    gutterMark: "none",
  },
  {
    tokens: [t("    )")],
    gutterMark: "none",
  },
  {
    tokens: [t("    db.session.add(record)")],
    gutterMark: "none",
  },
  {
    tokens: [t("    db.session.commit()")],
    gutterMark: "none",
  },
  { tokens: [t("")], gutterMark: "none" },
  {
    tokens: [
      t("    "),
      t("return", "keyword"),
      t(" "),
      t('{"status": "confirmed", "order_id": order.id, "total": str(total)}', "text"),
    ],
    gutterMark: "none",
  },
];
