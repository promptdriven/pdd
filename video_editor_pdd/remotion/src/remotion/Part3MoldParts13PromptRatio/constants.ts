// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 540;
export const FPS = 30;

// ── Background ──
export const BG_COLOR = '#0A0F1A';

// ── Colors ──
export const PROMPT_COLOR = '#D9944A';
export const CODE_BORDER_COLOR = '#334155';
export const CODE_LABEL_COLOR = '#64748B';
export const RATIO_TEXT_COLOR = '#E2E8F0';
export const BLOCK_BG_COLOR = '#1E1E2E';
export const RED_TINT = '#EF4444';
export const RED_LABEL_COLOR = '#F87171';
export const GREEN_TINT = '#4ADE80';
export const SUBLABEL_COLOR = '#94A3B8';

// ── Phase 1: Prompt Block ──
export const PROMPT_X = 200;
export const PROMPT_Y = 300;
export const PROMPT_WIDTH = 300;
export const PROMPT_HEIGHT = 200;

// ── Phase 1: Code Block ──
export const CODE_X = 600;
export const CODE_Y = 180;
export const CODE_WIDTH = 1150;
export const CODE_HEIGHT = 600;

// ── Phase 2: Context Windows ──
export const WINDOW_WIDTH = 400;
export const WINDOW_HEIGHT = 500;
export const LEFT_WINDOW_X = 310;
export const RIGHT_WINDOW_X = 1210;
export const WINDOW_Y = 200;

// ── Animation Frames ──
export const PHASE1_START = 0;
export const CODE_BLOCK_START = 30;
export const RATIO_START = 90;
export const PHASE1_HOLD_END = 210;
export const CROSSFADE_START = 210;
export const CROSSFADE_DURATION = 30;
export const LEFT_FILL_START = 270;
export const RIGHT_FILL_START = 330;
export const EMPHASIS_START = 390;
export const HOLD_START = 450;

// ── Fade/Animation Durations ──
export const BLOCK_FADE_DURATION = 20;
export const RATIO_ANIM_DURATION = 20;
export const WINDOW_FILL_DURATION = 30;
export const EMPHASIS_PULSE_DURATION = 15;

// ── Sample Prompt Text ──
export const PROMPT_LINES: string[] = [
  'Create a UserAuth module that:',
  '- Accepts JWT tokens via Bearer header',
  '- Validates against RS256 public key',
  '- Extracts user_id and role claims',
  '- Returns typed AuthContext object',
  '- Rejects expired tokens with 401',
  '- Caches validation for 5 minutes',
  '- Logs auth failures to audit trail',
  '- Supports refresh token rotation',
  '- Exposes /auth/me endpoint',
  '- Rate limits to 100 req/min',
  '- Integrates with session store',
  '- Provides middleware wrapper',
  '- Emits auth.success events',
  '- Handles CORS preflight',
];

// ── Sample Code Lines (representing ~200 lines, showing ~40 visible) ──
export const CODE_LINES: string[] = [
  'import { verify, decode } from "jsonwebtoken";',
  'import { Request, Response, NextFunction } from "express";',
  'import { RedisClient } from "./cache";',
  'import { AuditLogger } from "./audit";',
  '',
  'interface AuthContext {',
  '  userId: string;',
  '  role: "admin" | "user" | "viewer";',
  '  sessionId: string;',
  '  expiresAt: number;',
  '}',
  '',
  'interface TokenPayload {',
  '  sub: string;',
  '  role: string;',
  '  iat: number;',
  '  exp: number;',
  '  jti: string;',
  '}',
  '',
  'const CACHE_TTL = 300; // 5 minutes',
  'const RATE_LIMIT = 100;',
  'const RATE_WINDOW = 60000; // 1 min',
  '',
  'export class UserAuthModule {',
  '  private cache: RedisClient;',
  '  private logger: AuditLogger;',
  '  private publicKey: string;',
  '',
  '  constructor(config: AuthConfig) {',
  '    this.cache = new RedisClient(config);',
  '    this.logger = new AuditLogger();',
  '    this.publicKey = config.rsaPublicKey;',
  '  }',
  '',
  '  async validate(token: string) {',
  '    const cached = await this.cache.get(token);',
  '    if (cached) return JSON.parse(cached);',
  '    const payload = verify(token, this.publicKey,',
  '      { algorithms: ["RS256"] });',
  '    await this.cache.set(token, payload, CACHE_TTL);',
  '    return payload as AuthContext;',
  '  }',
];

// ── Context Window: Dense Code Lines ──
export const DENSE_CODE_LINES: string[] = [
  'fn validate_token(&self, t: &str) -> Result<Claims>',
  '  let decoded = decode(t, &self.key, RS256)?;',
  '  if decoded.exp < now() { return Err(Expired) }',
  '  let claims = decoded.claims.as_ref();',
  '  self.cache.insert(t.to_owned(), claims.clone());',
  '  Ok(claims) } fn refresh(&mut self, r: &str) ->',
  '  Result<TokenPair> { let old = self.validate(r)?;',
  '  let new_access = sign(&old.sub, &self.priv_key)?;',
  '  let new_refresh = generate_refresh()?; self.store',
  '  .rotate(old.jti, &new_refresh)?; Ok(TokenPair {',
  '  access: new_access, refresh: new_refresh }) }',
  '  fn middleware(&self) -> impl Fn(Req, Res, Next)',
  '  { let auth = self.clone(); move |req, res, next|',
  '  { match req.header("Authorization") { Some(h) =>',
  '  { let t = h.strip_prefix("Bearer ")?; match auth',
];

// ── Context Window: Clean Prompt Lines ──
export const CLEAN_PROMPT_LINES: string[] = [
  'Module 1: UserAuth — JWT validation, RS256',
  'Module 2: SessionStore — Redis-backed sessions',
  'Module 3: RateLimiter — sliding window, 100/min',
  'Module 4: AuditLog — structured auth event logging',
  'Module 5: CORS — preflight + origin allowlist',
  'Module 6: TokenRotation — refresh token cycling',
  'Module 7: Middleware — Express auth wrapper',
  'Module 8: EventBus — auth.success / auth.fail',
  'Module 9: HealthCheck — /auth/status endpoint',
  'Module 10: Config — env-based key management',
];
