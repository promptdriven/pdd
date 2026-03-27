// ColdOpen09TitleCardPdd – constants

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 60;

// Colors
export const BG_COLOR = "#1E1E2E";
export const TITLE_COLOR = "#CDD6F4";
export const RULE_COLOR = "#6C7086";
export const ACCENT_COLOR = "#89B4FA";

// Opacities
export const CODE_BG_OPACITY = 0.15;
export const OVERLAY_TARGET_OPACITY = 0.7;
export const RULE_OPACITY = 0.5;
export const ACCENT_GLOW_OPACITY = 0.2;

// Title positioning
export const TITLE_FONT_SIZE = 64;
export const TITLE_FONT_WEIGHT = 700;
export const TITLE_FONT_FAMILY = "Inter, sans-serif";
export const TITLE_LINE1_Y = 470;
export const TITLE_LINE2_Y = 545;
export const TITLE_LINE2_OFFSET_X = 10;

// Rule dimensions
export const RULE_Y = 510;
export const RULE_WIDTH = 300;
export const RULE_HEIGHT = 2;

// Accent glow
export const ACCENT_GLOW_WIDTH = 200;
export const ACCENT_GLOW_Y = 512;

// Animation frame markers
export const OVERLAY_START = 0;
export const OVERLAY_END = 10;
export const LINE1_START = 10;
export const LINE1_END = 25;
export const RULE_DRAW_START = 25;
export const RULE_DRAW_END = 30;
export const LINE2_START = 30;
export const LINE2_END = 45;
export const ACCENT_PULSE_START = 45;
export const ACCENT_PULSE_END = 48;

// Slide distance for title text animation
export const SLIDE_DISTANCE = 5;

// Background code sample (representative regenerated code)
export const CLEAN_FUNCTION_CODE = `def process_data(records: list[dict]) -> dict:
    """Process and aggregate records."""
    totals: dict[str, float] = {}
    for record in records:
        key = record["category"]
        value = record["amount"]
        totals[key] = totals.get(key, 0.0) + value
    return {
        "categories": len(totals),
        "totals": totals,
        "grand_total": sum(totals.values()),
    }

def validate_input(data: dict) -> bool:
    """Validate incoming data structure."""
    required = {"category", "amount"}
    return all(
        required.issubset(r.keys())
        for r in data.get("records", [])
    )

def format_report(results: dict) -> str:
    """Format aggregated results as report."""
    lines = [f"Categories: {results['categories']}"]
    for cat, total in results["totals"].items():
        lines.append(f"  {cat}: \${total:,.2f}")
    lines.append(f"Grand Total: \${results['grand_total']:,.2f}")
    return "\\n".join(lines)`;
