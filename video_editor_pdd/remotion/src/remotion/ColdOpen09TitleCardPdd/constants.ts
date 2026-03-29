// ColdOpen09TitleCardPdd — constants

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Duration
export const TOTAL_FRAMES = 60;

// Colors
export const BG_COLOR = "#1E1E2E";
export const TITLE_COLOR = "#CDD6F4";
export const RULE_COLOR = "#6C7086";
export const ACCENT_COLOR = "#89B4FA";

// Opacities
export const CODE_BG_OPACITY = 0.15;
export const OVERLAY_OPACITY = 0.7;
export const RULE_OPACITY = 0.5;
export const ACCENT_GLOW_OPACITY = 0.2;

// Typography
export const TITLE_FONT_SIZE = 64;
export const TITLE_FONT_WEIGHT = 700;
export const TITLE_FONT_FAMILY = "Inter, sans-serif";

// Title positions (centered at x: 960)
export const TITLE_LINE1_Y = 470;
export const TITLE_LINE2_Y = 545;
export const TITLE_LINE2_OFFSET_X = 10; // offset-right 10px

// Horizontal rule
export const RULE_Y = 510;
export const RULE_WIDTH = 300;
export const RULE_HEIGHT = 2;
export const RULE_CENTER_X = 960;

// Accent glow
export const GLOW_WIDTH = 200;
export const GLOW_HEIGHT = 1;
export const GLOW_Y = 512;

// Animation keyframes
export const OVERLAY_FADE_START = 0;
export const OVERLAY_FADE_END = 10;

export const LINE1_FADE_START = 10;
export const LINE1_FADE_END = 25;

export const RULE_DRAW_START = 25;
export const RULE_DRAW_END = 30;

export const LINE2_FADE_START = 30;
export const LINE2_FADE_END = 45;

export const GLOW_PULSE_START = 45;
export const GLOW_PULSE_END = 48;

// Slide distance in px
export const SLIDE_DISTANCE = 5;

// Background code snippet (regenerated clean function from previous shot)
export const CLEAN_FUNCTION_CODE = `def process_user_input(raw_input: str) -> ProcessedData:
    """Validate, sanitize, and transform user input."""
    sanitized = sanitize_html(raw_input.strip())
    tokens = tokenize(sanitized)

    if not tokens:
        return ProcessedData.empty()

    validated = [
        token for token in tokens
        if validate_token(token)
    ]

    return ProcessedData(
        tokens=validated,
        metadata=extract_metadata(validated),
        timestamp=utc_now(),
    )


def sanitize_html(text: str) -> str:
    """Remove dangerous HTML tags, keep safe formatting."""
    return bleach.clean(
        text,
        tags=ALLOWED_TAGS,
        attributes=ALLOWED_ATTRS,
        strip=True,
    )


def validate_token(token: Token) -> bool:
    """Check token against schema and length limits."""
    if len(token.value) > MAX_TOKEN_LENGTH:
        return False
    return token.matches_schema(SCHEMA)`;
