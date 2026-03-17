// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 240;
export const FPS = 30;

// IDE Layout
export const IDE_BG = "#0D1117";
export const LINE_NUMBER_LEFT = 180;
export const CODE_LEFT = 210;
export const CODE_TOP = 80;
export const CODE_RIGHT_MARGIN = 100;
export const TAB_BAR_HEIGHT = 80;
export const STATUS_BAR_HEIGHT = 60;
export const LINE_HEIGHT = 22;
export const CODE_FONT_SIZE = 14;
export const LINE_NUMBER_FONT_SIZE = 12;
export const TAB_FONT_SIZE = 12;
export const STATUS_FONT_SIZE = 10;
export const TERMINAL_FONT_SIZE = 11;

// Colors
export const LINE_NUMBER_COLOR = "#484F58";
export const TAB_TEXT_COLOR = "#C9D1D9";
export const TAB_BG_COLOR = "#161B22";
export const TAB_ACTIVE_BG = "#0D1117";
export const TAB_BORDER_COLOR = "#30363D";
export const STATUS_BAR_BG = "#161B22";
export const STATUS_TEXT_COLOR = "#484F58";
export const SELECTION_COLOR = "#1F6FEB";
export const TERMINAL_COLOR = "#5AAA6E";

// Syntax Colors
export const SYN_KEYWORD = "#FF7B72";
export const SYN_STRING = "#A5D6FF";
export const SYN_FUNCTION = "#D2A8FF";
export const SYN_COMMENT = "#8B949E";
export const SYN_VARIABLE = "#FFA657";
export const SYN_OPERATOR = "#C9D1D9";
export const SYN_PUNCTUATION = "#C9D1D9";
export const SYN_NUMBER = "#79C0FF";
export const SYN_TODO_COMMENT = "#EF4444";

// Animation Timing (frames)
export const OLD_CODE_VISIBLE_END = 90;
export const CURSOR_BLINK_RATE = 15; // frames per blink half-cycle
export const SELECTION_START = 30;
export const SELECTION_END = 45;
export const DELETE_START = 60;
export const PARTICLE_DURATION = 45;
export const EMPTY_HOLD_END = 105;
export const NEW_BLOCK1_START = 105;
export const NEW_BLOCK2_START = 120;
export const NEW_BLOCK3_START = 135;
export const BLOCK_REVEAL_DURATION = 12;
export const TERMINAL_FADE_START = 150;
export const TERMINAL_FADE_DURATION = 20;

// Particle Config
export const PARTICLE_COUNT = 200;
export const PARTICLE_MIN_SIZE = 2;
export const PARTICLE_MAX_SIZE = 4;
export const PARTICLE_GRAVITY = 0.3;
export const PARTICLE_DRIFT_X = 1.5;

// Terminal Position
export const TERMINAL_X = 1600;
export const TERMINAL_Y = 1000;

// Font Families
export const CODE_FONT = "'JetBrains Mono', 'Fira Code', 'Consolas', monospace";
export const UI_FONT = "'Inter', 'Helvetica Neue', sans-serif";

// Code Content - Old code (18 lines of messy, patched function)
export interface CodeToken {
	text: string;
	color: string;
}

export type CodeLine = CodeToken[];

export const OLD_CODE: CodeLine[] = [
	// Line 1: def parse_user(raw_data, source=None):
	[
		{ text: "def ", color: SYN_KEYWORD },
		{ text: "parse_user", color: SYN_FUNCTION },
		{ text: "(", color: SYN_PUNCTUATION },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ", ", color: SYN_PUNCTUATION },
		{ text: "source", color: SYN_VARIABLE },
		{ text: "=", color: SYN_OPERATOR },
		{ text: "None", color: SYN_KEYWORD },
		{ text: "):", color: SYN_PUNCTUATION },
	],
	// Line 2:     if raw_data is None:
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "if ", color: SYN_KEYWORD },
		{ text: "raw_data ", color: SYN_VARIABLE },
		{ text: "is ", color: SYN_KEYWORD },
		{ text: "None", color: SYN_KEYWORD },
		{ text: ":", color: SYN_PUNCTUATION },
	],
	// Line 3:         return {}  # fixed null case
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "return ", color: SYN_KEYWORD },
		{ text: "{}", color: SYN_PUNCTUATION },
		{ text: "  # fixed null case", color: SYN_COMMENT },
	],
	// Line 4:     name = raw_data.get("name", "")
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "name", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ".get(", color: SYN_PUNCTUATION },
		{ text: '"name"', color: SYN_STRING },
		{ text: ", ", color: SYN_PUNCTUATION },
		{ text: '""', color: SYN_STRING },
		{ text: ")", color: SYN_PUNCTUATION },
	],
	// Line 5:     email = raw_data.get("email")
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "email", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ".get(", color: SYN_PUNCTUATION },
		{ text: '"email"', color: SYN_STRING },
		{ text: ")", color: SYN_PUNCTUATION },
	],
	// Line 6:     if email and "@" not in email:
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "if ", color: SYN_KEYWORD },
		{ text: "email ", color: SYN_VARIABLE },
		{ text: "and ", color: SYN_KEYWORD },
		{ text: '"@" ', color: SYN_STRING },
		{ text: "not ", color: SYN_KEYWORD },
		{ text: "in ", color: SYN_KEYWORD },
		{ text: "email", color: SYN_VARIABLE },
		{ text: ":", color: SYN_PUNCTUATION },
	],
	// Line 7:         email = None  # workaround for #412
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "email", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "None", color: SYN_KEYWORD },
		{ text: "  # workaround for #412", color: SYN_COMMENT },
	],
	// Line 8:     role = raw_data.get("role", "user")
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "role", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ".get(", color: SYN_PUNCTUATION },
		{ text: '"role"', color: SYN_STRING },
		{ text: ", ", color: SYN_PUNCTUATION },
		{ text: '"user"', color: SYN_STRING },
		{ text: ")", color: SYN_PUNCTUATION },
	],
	// Line 9:     if role not in VALID_ROLES:
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "if ", color: SYN_KEYWORD },
		{ text: "role ", color: SYN_VARIABLE },
		{ text: "not ", color: SYN_KEYWORD },
		{ text: "in ", color: SYN_KEYWORD },
		{ text: "VALID_ROLES", color: SYN_VARIABLE },
		{ text: ":", color: SYN_PUNCTUATION },
	],
	// Line 10:         role = "user"  # TODO: refactor this
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "role", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: '"user"', color: SYN_STRING },
		{ text: "  # TODO: refactor this", color: SYN_TODO_COMMENT },
	],
	// Line 11:     created = raw_data.get("created_at")
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "created", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ".get(", color: SYN_PUNCTUATION },
		{ text: '"created_at"', color: SYN_STRING },
		{ text: ")", color: SYN_PUNCTUATION },
	],
	// Line 12:     if created:
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "if ", color: SYN_KEYWORD },
		{ text: "created", color: SYN_VARIABLE },
		{ text: ":", color: SYN_PUNCTUATION },
	],
	// Line 13:         created = _parse_date(created)  # temporary fix (2019)
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "created", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "_parse_date", color: SYN_FUNCTION },
		{ text: "(", color: SYN_PUNCTUATION },
		{ text: "created", color: SYN_VARIABLE },
		{ text: ")", color: SYN_PUNCTUATION },
		{ text: "  # temporary fix (2019)", color: SYN_COMMENT },
	],
	// Line 14:     org = raw_data.get("org_id")
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "org", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ".get(", color: SYN_PUNCTUATION },
		{ text: '"org_id"', color: SYN_STRING },
		{ text: ")", color: SYN_PUNCTUATION },
	],
	// Line 15:     if org and not validate_org(org):
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "if ", color: SYN_KEYWORD },
		{ text: "org ", color: SYN_VARIABLE },
		{ text: "and ", color: SYN_KEYWORD },
		{ text: "not ", color: SYN_KEYWORD },
		{ text: "validate_org", color: SYN_FUNCTION },
		{ text: "(", color: SYN_PUNCTUATION },
		{ text: "org", color: SYN_VARIABLE },
		{ text: "):", color: SYN_PUNCTUATION },
	],
	// Line 16:         org = None  # don't remove — breaks prod
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "org", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "None", color: SYN_KEYWORD },
		{ text: "  # don't remove \u2014 breaks prod", color: SYN_TODO_COMMENT },
	],
	// Line 17:     return {"name": name, "email": email,
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "return ", color: SYN_KEYWORD },
		{ text: "{", color: SYN_PUNCTUATION },
		{ text: '"name"', color: SYN_STRING },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "name", color: SYN_VARIABLE },
		{ text: ", ", color: SYN_PUNCTUATION },
		{ text: '"email"', color: SYN_STRING },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "email", color: SYN_VARIABLE },
		{ text: ",", color: SYN_PUNCTUATION },
	],
	// Line 18:             "role": role, "created": created, "org": org}
	[
		{ text: "            ", color: SYN_OPERATOR },
		{ text: '"role"', color: SYN_STRING },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "role", color: SYN_VARIABLE },
		{ text: ", ", color: SYN_PUNCTUATION },
		{ text: '"created"', color: SYN_STRING },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "created", color: SYN_VARIABLE },
		{ text: ", ", color: SYN_PUNCTUATION },
		{ text: '"org"', color: SYN_STRING },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "org", color: SYN_VARIABLE },
		{ text: "}", color: SYN_PUNCTUATION },
	],
];

// New Code (14 lines — clean, no comments)
export const NEW_CODE: CodeLine[] = [
	// Line 1: def parse_user(raw_data: dict) -> User:
	[
		{ text: "def ", color: SYN_KEYWORD },
		{ text: "parse_user", color: SYN_FUNCTION },
		{ text: "(", color: SYN_PUNCTUATION },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "dict", color: SYN_KEYWORD },
		{ text: ") -> ", color: SYN_PUNCTUATION },
		{ text: "User", color: SYN_FUNCTION },
		{ text: ":", color: SYN_PUNCTUATION },
	],
	// Line 2:     validated = UserSchema.parse(raw_data)
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "validated", color: SYN_VARIABLE },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "UserSchema", color: SYN_FUNCTION },
		{ text: ".parse(", color: SYN_PUNCTUATION },
		{ text: "raw_data", color: SYN_VARIABLE },
		{ text: ")", color: SYN_PUNCTUATION },
	],
	// Line 3: (empty line)
	[],
	// Line 4:     return User(
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "return ", color: SYN_KEYWORD },
		{ text: "User", color: SYN_FUNCTION },
		{ text: "(", color: SYN_PUNCTUATION },
	],
	// Line 5:         name=validated.name,
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "name", color: SYN_VARIABLE },
		{ text: "=", color: SYN_OPERATOR },
		{ text: "validated", color: SYN_VARIABLE },
		{ text: ".name,", color: SYN_PUNCTUATION },
	],
	// Line 6:         email=validated.email,
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "email", color: SYN_VARIABLE },
		{ text: "=", color: SYN_OPERATOR },
		{ text: "validated", color: SYN_VARIABLE },
		{ text: ".email,", color: SYN_PUNCTUATION },
	],
	// Line 7:         role=validated.role,
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "role", color: SYN_VARIABLE },
		{ text: "=", color: SYN_OPERATOR },
		{ text: "validated", color: SYN_VARIABLE },
		{ text: ".role,", color: SYN_PUNCTUATION },
	],
	// Line 8:         created_at=validated.created_at,
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "created_at", color: SYN_VARIABLE },
		{ text: "=", color: SYN_OPERATOR },
		{ text: "validated", color: SYN_VARIABLE },
		{ text: ".created_at,", color: SYN_PUNCTUATION },
	],
	// Line 9:         org=validated.org,
	[
		{ text: "        ", color: SYN_OPERATOR },
		{ text: "org", color: SYN_VARIABLE },
		{ text: "=", color: SYN_OPERATOR },
		{ text: "validated", color: SYN_VARIABLE },
		{ text: ".org,", color: SYN_PUNCTUATION },
	],
	// Line 10:     )
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: ")", color: SYN_PUNCTUATION },
	],
	// Line 11: (empty)
	[],
	// Line 12: class UserSchema(BaseModel):
	[
		{ text: "class ", color: SYN_KEYWORD },
		{ text: "UserSchema", color: SYN_FUNCTION },
		{ text: "(", color: SYN_PUNCTUATION },
		{ text: "BaseModel", color: SYN_FUNCTION },
		{ text: "):", color: SYN_PUNCTUATION },
	],
	// Line 13:     name: str
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "name", color: SYN_VARIABLE },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "str", color: SYN_KEYWORD },
	],
	// Line 14:     email: EmailStr | None = None
	[
		{ text: "    ", color: SYN_OPERATOR },
		{ text: "email", color: SYN_VARIABLE },
		{ text: ": ", color: SYN_PUNCTUATION },
		{ text: "EmailStr", color: SYN_FUNCTION },
		{ text: " | ", color: SYN_OPERATOR },
		{ text: "None", color: SYN_KEYWORD },
		{ text: " = ", color: SYN_OPERATOR },
		{ text: "None", color: SYN_KEYWORD },
	],
];
