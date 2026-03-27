// ─── Canvas ───
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";

// ─── Duration ───
export const TOTAL_FRAMES = 780;
export const FPS = 30;

// ─── Phase Timing ───
export const PHASE1_START = 0;
export const PHASE1_END = 180;
export const HEADER_FADE_END = 30;
export const STREAM_START = 30;

export const PHASE2_START = 120;
export const CROSSFADE_DURATION = 30;
export const OOP_TYPE_START = 180; // relative to PHASE2_START => frame 180 absolute, but we use relative inside Sequence
export const FUNC_TYPE_START = 270;
export const GLOW_START = 360;
export const GLOW_BRIGHT_START = 420;

export const PHASE3_START = 480;
export const PHASE3_ARROW_DURATION = 40;
export const DASHED_ARROW_START = 600;
export const HOLD_START = 720;

// ─── Colors ───
export const OOP_COLOR = "#4A90D9";
export const FUNC_COLOR = "#D9944A";
export const TEAM_COLOR = "#4AD9A0";
export const PANEL_BG = "#1E1E2E";
export const SUBTITLE_COLOR = "#94A3B8";
export const SUCCESS_GREEN = "#A6E3A1";
export const DB_FILL_OPACITY = 0.2;

// ─── Material Stream Data ───
export interface MaterialStreamData {
  label: string;
  color: string;
  style: "angular" | "smooth" | "organic";
}

export const MATERIAL_STREAMS: MaterialStreamData[] = [
  { label: "OOP", color: OOP_COLOR, style: "angular" },
  { label: "Functional", color: FUNC_COLOR, style: "smooth" },
  { label: "Your Team's Style", color: TEAM_COLOR, style: "organic" },
];

// ─── Code Samples ───
export const OOP_CODE = `class UserParser:
    def __init__(self, config: Config):
        self.config = config
        self._cache: Dict[str, User] = {}

    def parse(self, raw: str) -> User:
        if raw in self._cache:
            return self._cache[raw]
        user = self._validate(raw)
        self._cache[raw] = user
        return user

    def _validate(self, raw: str) -> User:
        parts = raw.strip().split(":")
        return User(
            id=parts[0],
            name=parts[1],
            role=self.config.default_role
        )`;

export const FUNCTIONAL_CODE = `def parse_user_id(
    raw: str
) -> Optional[str]:
    return (
        pipe(raw,
            strip,
            split_on(":"),
            head,
            validate_id)
    )

def parse_user(
    raw: str, config: Config
) -> Optional[User]:
    return (
        parse_user_id(raw)
        .map(lambda uid: User(
            id=uid,
            name=extract_name(raw),
            role=config.default_role
        ))
    )`;

// ─── Syntax Highlighting Colors ───
export const SYN_KEYWORD = "#C678DD";
export const SYN_STRING = "#98C379";
export const SYN_TYPE = "#E5C07B";
export const SYN_FUNCTION = "#61AFEF";
export const SYN_COMMENT = "#5C6370";
export const SYN_DEFAULT = "#ABB2BF";
export const SYN_SELF = "#E06C75";
export const SYN_PAREN = "#D19A66";

// ─── Layout ───
export const STREAM_Y_CENTER = 400;
export const STREAM_SPACING = 80;
export const STREAM_WIDTH = 600;
export const STREAM_HEIGHT = 40;

export const PANEL_WIDTH = 580;
export const PANEL_HEIGHT = 350;
export const PANEL_LEFT_X = 170;
export const PANEL_RIGHT_X = 810;
export const PANEL_Y = 280;
export const PANEL_GAP = 40;

export const DB_ICON_X = 960;
export const DB_ICON_Y = 820;
export const DB_ICON_WIDTH = 80;
export const DB_ICON_HEIGHT = 60;
