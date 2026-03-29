// constants.ts — Part3MoldParts15GroundingStyles

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 780;

// Background
export const BG_COLOR = "#0A0F1A";

// Phase colors
export const TEAL = "#4AD9A0";
export const OOP_BLUE = "#4A90D9";
export const FUNC_AMBER = "#D9944A";
export const SLATE = "#94A3B8";
export const CODE_BG = "#1E1E2E";
export const MINT_GREEN = "#A6E3A1";

// Material streams data
export const MATERIAL_STREAMS = [
  { label: "OOP", color: OOP_BLUE, style: "angular" as const },
  { label: "Functional", color: FUNC_AMBER, style: "smooth" as const },
  { label: "Your Team's Style", color: TEAL, style: "organic" as const },
];

// Stream layout
export const STREAM_Y_START = 300;
export const STREAM_Y_SPACING = 80;
export const STREAM_WIDTH = 600;
export const STREAM_HEIGHT = 40;

// Code panel layout
export const PANEL_WIDTH = 580;
export const PANEL_HEIGHT = 350;
export const PANEL_LEFT_X = 170;
export const PANEL_RIGHT_X = 810;
export const PANEL_Y = 260;
export const PANEL_GAP = 40;

// OOP code snippet
export const OOP_CODE = `class UserParser:
    def __init__(self, config: Config):
        self.config = config
        self._cache = {}

    def parse(self, raw: str) -> User:
        validated = self._validate(raw)
        normalized = self._normalize(validated)
        return User.from_dict(normalized)

    def _validate(self, raw: str) -> dict:
        if not raw.strip():
            raise ValueError("Empty input")
        return json.loads(raw)

    def _normalize(self, data: dict) -> dict:
        data["id"] = data["id"].lower()
        return data`;

// Functional code snippet
export const FUNCTIONAL_CODE = `def parse_user_id(raw: str) -> Optional[str]:
    return pipe(
        raw,
        validate_input,
        normalize_id,
        extract_user_id,
    )

def validate_input(raw: str) -> Result[dict]:
    if not raw.strip():
        return Err("Empty input")
    return Ok(json.loads(raw))

def normalize_id(data: dict) -> dict:
    return {**data, "id": data["id"].lower()}

def extract_user_id(data: dict) -> str:
    return data.get("id")`;

// Syntax highlighting color map
export const SYNTAX_KEYWORD = "#C678DD";
export const SYNTAX_STRING = "#98C379";
export const SYNTAX_FUNCTION = "#61AFEF";
export const SYNTAX_TYPE = "#E5C07B";
export const SYNTAX_COMMENT = "#5C6370";
export const SYNTAX_PLAIN = "#ABB2BF";
export const SYNTAX_DECORATOR = "#E06C75";
export const SYNTAX_NUMBER = "#D19A66";

// Database icon dimensions
export const DB_ICON_WIDTH = 80;
export const DB_ICON_HEIGHT = 60;
export const DB_ICON_X = 960;
export const DB_ICON_Y = 800;

// Animation frame markers
export const PHASE1_START = 0;
export const PHASE1_END = 180;
export const HEADER_FADE_END = 30;
export const STREAM_ANIM_START = 30;

export const PHASE2_START = 120;
export const CROSSFADE_END = 150;
export const OOP_TYPE_START = 180;
export const OOP_TYPE_END = 270;
export const FUNC_TYPE_START = 270;
export const FUNC_TYPE_END = 360;
export const BOTH_GLOW_START = 360;
export const BOTH_GLOW_END = 420;
export const SELECT_GLOW_START = 420;
export const SELECT_GLOW_END = 480;

export const PHASE3_START = 480;
export const ARROW_ANIM_END = 520;
export const DB_APPEAR = 520;
export const DB_APPEAR_END = 535;
export const DASHED_ARROW_START = 600;
export const DASHED_ARROW_END = 640;

export const HOLD_START = 720;
