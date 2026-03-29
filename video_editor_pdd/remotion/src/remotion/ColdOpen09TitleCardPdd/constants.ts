// === Colors ===
export const BG_COLOR = "#1E1E2E";
export const TITLE_COLOR = "#CDD6F4";
export const RULE_COLOR = "#6C7086";
export const ACCENT_COLOR = "#89B4FA";

// === Layout (1920x1080) ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Title positions
export const TITLE_Y_TOP = 470;
export const TITLE_Y_BOTTOM = 545;
export const TITLE_BOTTOM_OFFSET_X = 10; // offset-right for "DEVELOPMENT"
export const TITLE_FONT_SIZE = 64;
export const TITLE_FONT_WEIGHT = 700;
export const TITLE_FONT_FAMILY = "Inter, sans-serif";

// Horizontal rule
export const RULE_Y = 510;
export const RULE_WIDTH = 300;
export const RULE_HEIGHT = 2;
export const RULE_OPACITY = 0.7;

// Accent glow line
export const ACCENT_GLOW_WIDTH = 200;
export const ACCENT_GLOW_HEIGHT = 1;
export const ACCENT_GLOW_Y = 512;
export const ACCENT_GLOW_OPACITY = 0.2;

// Overlay
export const OVERLAY_OPACITY = 0.7;
export const CODE_BG_OPACITY = 0.15;

// === Animation Frames ===
export const OVERLAY_FADE_START = 0;
export const OVERLAY_FADE_END = 10;

export const TITLE_TOP_START = 10;
export const TITLE_TOP_END = 25;

export const RULE_DRAW_START = 25;
export const RULE_DRAW_END = 30;

export const TITLE_BOTTOM_START = 30;
export const TITLE_BOTTOM_END = 45;

export const ACCENT_PULSE_START = 45;
export const ACCENT_PULSE_END = 48;

export const TOTAL_FRAMES = 60;

// Slide distance in px
export const SLIDE_DISTANCE = 5;

// === Background code snippet (regenerated clean function from prior shot) ===
export const CLEAN_FUNCTION_CODE = `def calculate_shipping_cost(order: Order) -> Decimal:
    """Calculate shipping cost based on order weight and destination."""
    base_rate = get_base_rate(order.destination.zone)
    weight_charge = order.total_weight * RATE_PER_KG

    if order.is_expedited:
        surcharge = base_rate * Decimal("0.35")
    else:
        surcharge = Decimal("0")

    subtotal = base_rate + weight_charge + surcharge

    if order.total_weight > FREE_SHIPPING_THRESHOLD:
        discount = subtotal * Decimal("0.10")
    else:
        discount = Decimal("0")

    return max(subtotal - discount, MIN_SHIPPING_COST)`;

// Code display styling
export const CODE_FONT_SIZE = 14;
export const CODE_LINE_HEIGHT = 1.6;
export const CODE_FONT_FAMILY = "'Fira Code', 'Cascadia Code', 'JetBrains Mono', monospace";
export const CODE_PADDING_TOP = 200;
export const CODE_PADDING_LEFT = 520;

// Syntax highlight colors (Catppuccin Mocha-inspired)
export const SYN_KEYWORD = "#CBA6F7";  // purple - def, if, else, return
export const SYN_STRING = "#A6E3A1";   // green - strings
export const SYN_FUNCTION = "#89B4FA"; // blue - function names
export const SYN_TYPE = "#F9E2AF";     // yellow - type hints
export const SYN_COMMENT = "#6C7086";  // gray - comments
export const SYN_NUMBER = "#FAB387";   // peach - numbers
export const SYN_OPERATOR = "#89DCEB"; // teal - operators
export const SYN_DEFAULT = "#CDD6F4";  // text - default
