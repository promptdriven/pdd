// Colors
export const BG_COLOR = '#000000';
export const SPLIT_LINE_COLOR = '#334155';
export const SPLIT_LINE_OPACITY = 0.12;

export const LEFT_COLOR = '#D9944A';
export const RIGHT_COLOR = '#4A90D9';

export const CODE_COLOR = '#94A3B8';
export const RED_HIGHLIGHT = '#E74C3C';
export const GREEN_HIGHLIGHT = '#5AAA6E';
export const PROMPT_TEXT_COLOR = '#E2E8F0';

// Layout
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const SPLIT_X = 960;
export const PANEL_PADDING = 80;

// Context window positioning (within each half-panel)
export const CW_TOP = 90;
export const CW_BOTTOM = 1020;
export const CW_LEFT = 40;
export const CW_RIGHT = 918; // 958 - 40

// Animation frames
export const SPLIT_LINE_IN = 0;
export const HEADERS_IN = 30;
export const LEFT_CODE_IN = 60;
export const LEFT_CODE_DURATION = 90; // 60-150
export const RIGHT_CONTENT_IN = 150;
export const RIGHT_CONTENT_DURATION = 90; // 150-240
export const TOKEN_COUNTS_IN = 240;
export const FILL_BARS_IN = 300;
export const HOLD_START = 360;
export const TOTAL_FRAMES = 600;

// Pulse cycle
export const PULSE_CYCLE = 50;

// Code lines to simulate dense code
export const FAKE_CODE_LINES: string[] = [
  'function processChunk(data: Buffer, offset: number) {',
  '  const header = data.readUInt32BE(offset);',
  '  if (header === 0x89504E47) return ParseResult.PNG;',
  '  const len = data.readUInt16BE(offset + 4);',
  '  for (let i = 0; i < len; i++) {',
  '    buffer[pos++] = data[offset + 6 + i];',
  '  }',
  '  return { consumed: len + 6, type: "raw" };',
  '}',
  '',
  'class StreamProcessor implements IProcessor {',
  '  private cache = new Map<string, Entry>();',
  '  private readonly maxRetries = 3;',
  '  private backoff = 100;',
  '',
  '  async process(stream: ReadableStream) {',
  '    const reader = stream.getReader();',
  '    let done = false;',
  '    while (!done) {',
  '      const { value, done: d } = await reader.read();',
  '      done = d;',
  '      if (value) this.handleChunk(value);',
  '    }',
  '  }',
  '',
  '  private handleChunk(chunk: Uint8Array) {',
  '    const key = this.computeHash(chunk);',
  '    if (this.cache.has(key)) return;',
  '    this.cache.set(key, { ts: Date.now() });',
  '    this.emit("data", chunk);',
  '  }',
  '',
  '  private computeHash(data: Uint8Array): string {',
  '    let h = 0x811c9dc5;',
  '    for (let i = 0; i < data.length; i++) {',
  '      h ^= data[i]; h = (h * 0x01000193) >>> 0;',
  '    }',
  '    return h.toString(16).padStart(8, "0");',
  '  }',
  '}',
  '',
  'export function initPipeline(config: Config) {',
  '  const stages = config.stages.map(s => {',
  '    return new Stage(s.name, s.transform);',
  '  });',
  '  const pipeline = new Pipeline(stages);',
  '  pipeline.on("error", (e) => log.error(e));',
  '  return pipeline;',
  '}',
  '',
  'interface Config {',
  '  stages: StageConfig[];',
  '  maxConcurrency: number;',
  '  timeout: number;',
  '  retryPolicy: RetryPolicy;',
  '}',
  '',
  'type RetryPolicy = {',
  '  maxRetries: number;',
  '  backoff: "linear" | "exponential";',
  '  baseDelay: number;',
  '};',
  '',
  'const DEFAULT_CONFIG: Config = {',
  '  stages: [],',
  '  maxConcurrency: 4,',
  '  timeout: 30000,',
  '  retryPolicy: {',
  '    maxRetries: 3,',
  '    backoff: "exponential",',
  '    baseDelay: 100,',
  '  },',
  '};',
];

// Prompt text for right panel
export const PROMPT_LINES: string[] = [
  'Generate a StreamProcessor class that reads',
  'from a ReadableStream, computes FNV-1a hashes',
  'for deduplication, and emits unique chunks.',
  '',
  'The processor should:',
  '- Accept a ReadableStream in process()',
  '- Cache chunks by hash to skip duplicates',
  '- Emit "data" events for new chunks',
  '- Support configurable retry with backoff',
  '',
  'Use TypeScript. The class implements IProcessor.',
  'See grounding example for hash function style.',
  'All methods should be fully typed.',
];

export const TEST_LINES: string[] = [
  'test("deduplicates identical chunks")',
  'test("emits data for unique chunks")',
  'test("respects maxRetries on failure")',
  'test("exponential backoff doubles delay")',
  'test("process reads until stream ends")',
  'test("hash is deterministic for same input")',
  'test("cache eviction after TTL expires")',
  'test("handles empty stream gracefully")',
  'test("concurrent streams are isolated")',
  'test("error event fires on unrecoverable")',
];

export const GROUNDING_LINES: string[] = [
  'private computeHash(d: Uint8Array): string {',
  '  let h = 0x811c9dc5;',
  '  for (let i = 0; i < d.length; i++) {',
  '    h ^= d[i];',
  '    h = (h * 0x01000193) >>> 0;',
  '  }',
  '  return h.toString(16);',
  '}',
];

// Red highlight positions (yStart as fraction of window height, height fraction)
export const RED_HIGHLIGHTS = [
  { yFrac: 0.02, hFrac: 0.12 },
  { yFrac: 0.18, hFrac: 0.15 },
  { yFrac: 0.42, hFrac: 0.10 },
  { yFrac: 0.60, hFrac: 0.14 },
  { yFrac: 0.82, hFrac: 0.11 },
];

// Green highlight position
export const GREEN_HIGHLIGHT_REGION = { yFrac: 0.35, hFrac: 0.06 };
