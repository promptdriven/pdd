// Part3Mold06SplitPromptVsCode constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 360;

// Panel layout
export const LEFT_PANEL = { x: 40, y: 80, w: 890, h: 920 };
export const RIGHT_PANEL = { x: 990, y: 80, w: 890, h: 920 };
export const DIVIDER_X = 960;
export const PANEL_RADIUS = 12;

// Colors
export const GOLD = "#F59E0B";
export const GOLD_LIGHT = "#FDE68A";
export const GOLD_BG = "rgba(245, 158, 11, 0.06)";
export const GOLD_PILL_BG = "rgba(245, 158, 11, 0.15)";

export const BLUE = "#3B82F6";
export const BLUE_LIGHT = "#93C5FD";
export const BLUE_BG = "rgba(59, 130, 246, 0.06)";
export const BLUE_PILL_BG = "rgba(59, 130, 246, 0.15)";

export const PANEL_BG = "rgba(15, 23, 42, 0.88)";
export const GUTTER_BG = "rgba(15, 23, 42, 0.5)";
export const LINE_NUM_COLOR = "rgba(148, 163, 184, 0.4)";

// Animation timing (frames at 30fps)
export const LEFT_SLIDE_IN_START = 0;
export const LEFT_SLIDE_IN_END = 25;
export const RIGHT_SLIDE_IN_START = 5;
export const RIGHT_SLIDE_IN_END = 30;
export const DIVIDER_FADE_START = 20;
export const DIVIDER_FADE_END = 35;
export const PROMPT_TYPE_START = 25;
export const PROMPT_CHARS_PER_FRAME = 2;
export const CODE_APPEAR_START = 30;
export const CODE_APPEAR_END = 60;
export const CODE_SCROLL_START = 60;
export const RATIO_FADE_START = 80;
export const RATIO_FADE_END = 100;
export const LINE_COUNTER_PULSE_START = 90;
export const LINE_COUNTER_PULSE_END = 100;
export const FADEOUT_START = 310;
export const FADEOUT_END = 360;

// Prompt lines (8 lines of PDD-style specification)
export const PROMPT_LINES = [
  '# UserAuth module',
  'purpose: "Handle login, signup, password reset"',
  'validate: email format, password strength',
  'on_login: issue JWT, set refresh cookie',
  'on_failure: rate-limit after 5 attempts',
  'store: users collection, bcrypt hashes',
  'expose: POST /auth/login, /auth/signup',
  'test: invalid creds → 401, valid → token',
];

// Generated code lines (47 lines of implementation)
export const GENERATED_LINES = [
  'import express from "express";',
  'import bcrypt from "bcryptjs";',
  'import jwt from "jsonwebtoken";',
  'import { RateLimiter } from "./rate-limiter";',
  'import { db } from "./database";',
  '',
  'const router = express.Router();',
  'const limiter = new RateLimiter({ max: 5, window: 900 });',
  '',
  'interface AuthRequest {',
  '  email: string;',
  '  password: string;',
  '}',
  '',
  'function validateEmail(email: string): boolean {',
  '  const re = /^[^\\s@]+@[^\\s@]+\\.[^\\s@]+$/;',
  '  return re.test(email);',
  '}',
  '',
  'function validatePassword(pw: string): boolean {',
  '  return pw.length >= 8 && /[A-Z]/.test(pw)',
  '    && /[0-9]/.test(pw) && /[!@#$%]/.test(pw);',
  '}',
  '',
  'router.post("/auth/login", async (req, res) => {',
  '  const { email, password }: AuthRequest = req.body;',
  '  if (!validateEmail(email)) return res.status(400).json({',
  '    error: "Invalid email format"',
  '  });',
  '  if (limiter.isLimited(email)) return res.status(429).json({',
  '    error: "Too many attempts"',
  '  });',
  '  const user = await db.collection("users").findOne({ email });',
  '  if (!user) { limiter.record(email); return res.status(401).json({',
  '    error: "Invalid credentials" });',
  '  }',
  '  const valid = await bcrypt.compare(password, user.hash);',
  '  if (!valid) { limiter.record(email); return res.status(401).json({',
  '    error: "Invalid credentials" });',
  '  }',
  '  limiter.reset(email);',
  '  const token = jwt.sign({ uid: user._id }, process.env.SECRET!, {',
  '    expiresIn: "1h"',
  '  });',
  '  res.cookie("refresh", token, { httpOnly: true });',
  '  return res.json({ token });',
  '});',
  '',
];

// Spring config
export const PANEL_SPRING = { damping: 16, stiffness: 160 };

// Code panel dimensions
export const GUTTER_WIDTH = 44;
export const LINE_HEIGHT = 22;
export const CODE_FONT_SIZE = 14;
