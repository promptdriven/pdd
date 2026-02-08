import { z } from "zod";

// Video specs
export const CONTEXT_COMPARISON_FPS = 30;
export const CONTEXT_COMPARISON_DURATION_SECONDS = 15;
export const CONTEXT_COMPARISON_DURATION_FRAMES =
  CONTEXT_COMPARISON_FPS * CONTEXT_COMPARISON_DURATION_SECONDS;
export const CONTEXT_COMPARISON_WIDTH = 1920;
export const CONTEXT_COMPARISON_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-30: Scene establishes (divider, labels)
// Frame 30-60: Context window frames appear
// Frame 60-150: LEFT window fills with code
// Frame 90-180: RIGHT window fills with clean blocks
// Frame 180-270: Token counters animate
// Frame 270-330: Knowledge indicator
// Frame 330-450: Hold and breathe
export const BEATS = {
  ESTABLISH_START: 0,
  ESTABLISH_END: 30,               // 0-1s: Divider + labels
  FRAMES_START: 30,
  FRAMES_END: 60,                  // 1-2s: Window frames appear
  LEFT_FILL_START: 60,
  LEFT_FILL_END: 150,              // 2-5s: Left fills with code
  RIGHT_FILL_START: 90,
  RIGHT_FILL_END: 180,             // 3-6s: Right fills with blocks
  COUNTER_START: 180,
  COUNTER_END: 270,                // 6-9s: Token counters
  BADGE_APPEAR: 250,               // Badge pops in
  KNOWLEDGE_START: 270,
  KNOWLEDGE_END: 330,              // 9-11s: Knowledge indicator
  HOLD_START: 330,
  HOLD_END: 450,                   // 11-15s: Hold
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WINDOW_BG: "#1E1E2E",
  WINDOW_BORDER: "#333333",
  CHROME_BG: "#2a2a3a",
  CHROME_DOT_RED: "#ff5f56",
  CHROME_DOT_YELLOW: "#ffbd2e",
  CHROME_DOT_GREEN: "#27c93f",
  DIVIDER: "rgba(255, 255, 255, 0.5)",
  LABEL_WHITE: "#ffffff",
  // Left panel (agentic patching)
  IRRELEVANT_RED: "rgba(217, 74, 74, 0.25)",
  IRRELEVANT_LABEL: "rgba(217, 74, 74, 0.4)",
  RELEVANT_GREEN: "rgba(90, 170, 110, 0.25)",
  CODE_TEXT: "#888888",
  LEFT_GLOW: "rgba(217, 74, 74, 0.3)",
  LEFT_COUNTER: "#D94A4A",
  // Right panel (PDD regeneration)
  PROMPT_BLUE: "#4A90D9",
  TESTS_AMBER: "#D9944A",
  GROUNDING_GREEN: "#5AAA6E",
  ROOM_TO_THINK: "#666666",
  RIGHT_COUNTER: "#4A90D9",
  // Badge & knowledge
  BADGE_WHITE: "#ffffff",
  KNOWLEDGE_GREEN: "#5AAA6E",
};

// Window dimensions
export const WINDOW = {
  width: 760,
  height: 480,
  borderRadius: 8,
  chromeHeight: 24,
  // Left panel center
  leftCenterX: 480,
  centerY: 440,
  // Right panel center
  rightCenterX: 1440,
  // Gap between panels
  dividerX: 960,
};

// Right panel block proportions (of window content height)
export const RIGHT_BLOCKS = {
  promptHeight: 0.15,    // 15% of content area
  testsHeight: 0.25,     // 25%
  groundingHeight: 0.10, // 10%
  emptyHeight: 0.50,     // 50% empty "room to think"
};

// Code line generation seed data (abstract code-like patterns)
export const CODE_PATTERNS = [
  "  def authenticate(self, token):",
  "    if not token or len(token) < 32:",
  "      raise AuthError('Invalid token')",
  "    user = self.db.find_user(token)",
  "    if user.is_expired():",
  "      self.refresh_session(user)",
  "    return user.validate()",
  "",
  "  def process_request(self, req):",
  "    data = req.get_json()",
  "    if 'action' in data:",
  "      handler = self.routes[data['action']]",
  "      return handler(data['payload'])",
  "    return {'error': 'unknown action'}",
  "",
  "class DatabaseManager:",
  "  def __init__(self, config):",
  "    self.pool = ConnectionPool(config)",
  "    self._cache = LRUCache(maxsize=1000)",
  "",
  "  def query(self, sql, params=None):",
  "    cached = self._cache.get(sql)",
  "    if cached and not params:",
  "      return cached",
  "    conn = self.pool.acquire()",
  "    try:",
  "      result = conn.execute(sql, params)",
  "      self._cache.set(sql, result)",
  "      return result",
  "    finally:",
  "      self.pool.release(conn)",
  "",
  "  @retry(max_attempts=3)",
  "  def batch_insert(self, table, rows):",
  "    chunks = [rows[i:i+100]",
  "              for i in range(0, len(rows), 100)]",
  "    for chunk in chunks:",
  "      self._insert_chunk(table, chunk)",
  "",
  "def validate_config(cfg):",
  "  required = ['db_host', 'db_port',",
  "              'api_key', 'secret']",
  "  missing = [k for k in required",
  "             if k not in cfg]",
  "  if missing:",
  "    raise ConfigError(missing)",
  "  return True",
  "",
  "class EventBus:",
  "  def __init__(self):",
  "    self._handlers = defaultdict(list)",
  "    self._queue = asyncio.Queue()",
  "",
  "  async def emit(self, event, data):",
  "    for handler in self._handlers[event]:",
  "      await self._queue.put(",
  "        (handler, data))",
  "",
  "  def subscribe(self, event, handler):",
  "    self._handlers[event].append(handler)",
  "",
  "# Legacy migration utilities",
  "def migrate_v1_to_v2(records):",
  "  for record in records:",
  "    record['schema_version'] = 2",
  "    if 'old_field' in record:",
  "      record['new_field'] = record.pop(",
  "        'old_field')",
  "  return records",
  "",
  "class RateLimiter:",
  "  def __init__(self, max_rps=100):",
  "    self._window = deque()",
  "    self._max = max_rps",
  "",
  "  def allow(self):",
  "    now = time.monotonic()",
  "    while self._window and",
  "          self._window[0] < now - 1:",
  "      self._window.popleft()",
  "    if len(self._window) < self._max:",
  "      self._window.append(now)",
  "      return True",
  "    return False",
];

// Token counter targets
export const TOKEN_COUNTS = {
  left: 15000,
  right: 2300,
};

// Props schema
export const ContextWindowComparisonProps = z.object({
  showKnowledgeIndicator: z.boolean().default(true),
});

export const defaultContextWindowComparisonProps: z.infer<
  typeof ContextWindowComparisonProps
> = {
  showKnowledgeIndicator: true,
};

export type ContextWindowComparisonPropsType = z.infer<
  typeof ContextWindowComparisonProps
>;
