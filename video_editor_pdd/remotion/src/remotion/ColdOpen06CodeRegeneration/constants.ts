// ── Colors ──────────────────────────────────────────────────────
export const BG_COLOR = "#1E1E2E";
export const GUTTER_BG = "#2D2D3D";
export const GUTTER_WIDTH = 60;

export const SELECTION_COLOR = "#89B4FA";
export const SELECTION_OPACITY = 0.2;

export const TERMINAL_BG = "#11111B";
export const TERMINAL_OPACITY = 0.9;
export const TERMINAL_GREEN = "#A6E3A1";

export const LINE_NUMBER_COLOR = "#6C7086";
export const CURSOR_COLOR = "#CDD6F4";

// Syntax highlight palette (Catppuccin Mocha)
export const SYN_KEYWORD = "#CBA6F7"; // purple — def, return, if, else, for, in, not, None, True, False, raise, with
export const SYN_FUNCTION = "#89B4FA"; // blue  — function names
export const SYN_STRING = "#A6E3A1"; // green — strings
export const SYN_COMMENT = "#6C7086"; // gray  — comments
export const SYN_OPERATOR = "#89DCEB"; // teal  — operators, parens
export const SYN_NUMBER = "#FAB387"; // peach — numbers
export const SYN_PARAM = "#F5E0DC"; // rosewater — parameters
export const SYN_DEFAULT = "#CDD6F4"; // text  — default text
export const SYN_DECORATOR = "#F9E2AF"; // yellow — decorators
export const SYN_CLASS = "#F9E2AF"; // yellow — class names / types
export const SYN_BUILTIN = "#F38BA8"; // red — built-in functions like len, ValueError

// ── Dimensions ──────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const CODE_FONT_SIZE = 14;
export const CODE_LINE_HEIGHT = 22;
export const CODE_LEFT_PADDING = 16;
export const CODE_TOP_PADDING = 48;
export const TERMINAL_WIDTH = 420;
export const TERMINAL_HEIGHT = 80;
export const TERMINAL_BORDER_RADIUS = 8;
export const TERMINAL_FONT_SIZE = 12;

// ── Timing (frames @ 30fps) ────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 150;

export const PHASE_SHOW_OLD_END = 5;
export const PHASE_SELECT_START = 5;
export const PHASE_SELECT_END = 25;
export const PHASE_DELETE_START = 25;
export const PHASE_DELETE_END = 35;
export const PHASE_EMPTY_START = 35;
export const PHASE_EMPTY_END = 45;
export const PHASE_REGEN_START = 45;
export const PHASE_REGEN_END = 120;
export const PHASE_TERMINAL_START = 120;
export const PHASE_TERMINAL_END = 150;

export const OLD_LINE_COUNT = 40;
export const NEW_LINE_COUNT = 25;

// ── Code Strings ────────────────────────────────────────────────

/**
 * The old patched function — messy, 40 lines, full of HACK/TODO comments.
 */
export const PATCHED_CODE_LINES: string[] = [
  "def process_order(order_id: str, ctx: Context) -> Result:",
  '    """Process an incoming order through the pipeline."""',
  "    order = db.fetch_order(order_id)",
  "    if order is None:",
  '        raise ValueError(f"Order {order_id} not found")',
  "",
  "    # HACK: Force reload to avoid stale cache (see #4521)",
  "    order = db.fetch_order(order_id, force=True)",
  "",
  "    # TODO: Remove this after migration completes",
  "    if order.schema_version < 3:",
  "        order = migrate_legacy_schema(order)",
  "",
  "    customer = get_customer(order.customer_id)",
  "    if customer is None:",
  '        log.warning("Customer missing, using fallback")',
  "        customer = Customer.default()",
  "",
  "    # HACK: Temporary fix for negative quantity bug (#4892)",
  "    for item in order.items:",
  "        if item.quantity < 0:",
  "            item.quantity = abs(item.quantity)",
  "            log.error(f\"Negative qty patched: {item.sku}\")",
  "",
  "    # TODO: This should use the new pricing engine",
  "    subtotal = 0",
  "    for item in order.items:",
  "        price = get_legacy_price(item.sku)",
  "        subtotal += price * item.quantity",
  "",
  "    tax = calculate_tax_legacy(subtotal, customer.region)",
  "    # FIXME: Tax rounding issue — off by 1 cent sometimes",
  "    tax = round(tax, 2)",
  "",
  "    total = subtotal + tax",
  "    order.total = total",
  "    order.status = 'processed'",
  "",
  "    # HACK: Duplicate save to work around race condition",
  "    db.save(order)",
  "    db.save(order)  # Yes, twice. Don't remove.",
];

/**
 * The clean regenerated function — ~25 lines, no hacks.
 */
export const CLEAN_CODE_LINES: string[] = [
  "def process_order(order_id: str, ctx: Context) -> Result:",
  '    """Process an incoming order through the pipeline."""',
  "    order = ctx.orders.get(order_id)",
  "    if not order:",
  '        raise OrderNotFoundError(order_id)',
  "",
  "    customer = ctx.customers.get(order.customer_id)",
  "    if not customer:",
  "        raise CustomerNotFoundError(order.customer_id)",
  "",
  "    validated_items = [",
  "        validate_line_item(item)",
  "        for item in order.items",
  "    ]",
  "",
  "    pricing = ctx.pricing_engine.calculate(",
  "        items=validated_items,",
  "        region=customer.region,",
  "    )",
  "",
  "    return ctx.orders.finalize(",
  "        order_id=order.id,",
  "        items=validated_items,",
  "        subtotal=pricing.subtotal,",
  "        tax=pricing.tax,",
  "        total=pricing.total,",
  "    )",
];
