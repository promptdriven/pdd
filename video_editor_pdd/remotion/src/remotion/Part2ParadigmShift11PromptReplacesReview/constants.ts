// Colors
export const COLORS = {
  background: '#000000',
  leftPanelBg: '#0F172A',
  rightPanelBg: '#0A0F1A',
  splitLine: '#334155',
  red: '#EF4444',
  green: '#5AAA6E',
  amber: '#D9944A',
  textLight: '#E2E8F0',
  codeMuted: '#94A3B8',
  panelBg: '#1E293B',
} as const;

// Layout
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const SPLIT_X = 960;
export const LEFT_PANEL_WIDTH = 958;
export const RIGHT_PANEL_WIDTH = 958;
export const TOTAL_FRAMES = 360;

// Fake code diff lines for the left panel
export const DIFF_LINES: Array<{ text: string; type: 'add' | 'remove' | 'context' }> = [
  { text: '  const handleAuth = async (user: User) => {', type: 'context' },
  { text: '-   if (user.token && validateToken(user.token)) {', type: 'remove' },
  { text: '-     return await refreshSession(user);', type: 'remove' },
  { text: '+   const validated = await validateAndRefresh(user);', type: 'add' },
  { text: '+   if (!validated.success) {', type: 'add' },
  { text: '+     throw new AuthError(validated.reason);', type: 'add' },
  { text: '    }', type: 'context' },
  { text: '-   const perms = getPermissions(user.role);', type: 'remove' },
  { text: '+   const perms = await resolvePermissions({', type: 'add' },
  { text: '+     role: user.role,', type: 'add' },
  { text: '+     scope: validated.scope,', type: 'add' },
  { text: '+     orgPolicy: user.org.policy,', type: 'add' },
  { text: '+   });', type: 'add' },
  { text: '    return { session, perms };', type: 'context' },
  { text: '  };', type: 'context' },
  { text: '', type: 'context' },
  { text: '-  export function processQueue(items: Item[]) {', type: 'remove' },
  { text: '-    return items.filter(i => i.valid).map(transform);', type: 'remove' },
  { text: '+  export async function processQueue(', type: 'add' },
  { text: '+    items: Item[],', type: 'add' },
  { text: '+    opts: ProcessOpts = {}', type: 'add' },
  { text: '+  ): Promise<Result[]> {', type: 'add' },
  { text: '+    const validated = items.filter(i => {', type: 'add' },
  { text: '+      return i.valid && checkPolicy(i, opts);', type: 'add' },
  { text: '+    });', type: 'add' },
  { text: '+    return Promise.all(validated.map(async i => {', type: 'add' },
  { text: '+      const result = await transform(i, opts);', type: 'add' },
  { text: '+      await audit.log(i.id, result.hash);', type: 'add' },
  { text: '+      return result;', type: 'add' },
  { text: '+    }));', type: 'add' },
  { text: '  }', type: 'context' },
  { text: '', type: 'context' },
  { text: '-  function validateInput(data: unknown): data is Valid {', type: 'remove' },
  { text: '-    return typeof data === "object" && data !== null;', type: 'remove' },
  { text: '+  function validateInput(data: unknown): Result<Valid> {', type: 'add' },
  { text: '+    if (data === null || data === undefined) {', type: 'add' },
  { text: '+      return { ok: false, error: "null_input" };', type: 'add' },
  { text: '+    }', type: 'add' },
  { text: '+    if (typeof data !== "object") {', type: 'add' },
  { text: '+      return { ok: false, error: "not_object" };', type: 'add' },
  { text: '+    }', type: 'add' },
  { text: '+    const schema = getSchema(data);', type: 'add' },
  { text: '+    return schema.validate(data);', type: 'add' },
  { text: '  }', type: 'context' },
  { text: '', type: 'context' },
  { text: '  class EventBus {', type: 'context' },
  { text: '-    emit(event: string, payload: any) {', type: 'remove' },
  { text: '-      this.handlers[event]?.forEach(h => h(payload));', type: 'remove' },
  { text: '+    async emit<T extends EventType>(', type: 'add' },
  { text: '+      event: T,', type: 'add' },
  { text: '+      payload: EventPayload<T>', type: 'add' },
  { text: '+    ): Promise<void> {', type: 'add' },
  { text: '+      const handlers = this.handlers.get(event) ?? [];', type: 'add' },
  { text: '+      await Promise.allSettled(', type: 'add' },
  { text: '+        handlers.map(h => h(payload))', type: 'add' },
  { text: '+      );', type: 'add' },
  { text: '    }', type: 'context' },
  { text: '  }', type: 'context' },
];

// Prompt document text for the right panel
export const PROMPT_LINES: Array<{ text: string; highlight?: boolean }> = [
  { text: '# Auth Refactor Spec' },
  { text: '' },
  { text: 'Refactor the auth module to:', highlight: true },
  { text: '- Async token validation' },
  { text: '- Scoped permission resolution', highlight: true },
  { text: '- Org-level policy checks' },
  { text: '' },
  { text: 'Process queue must:', highlight: true },
  { text: '- Accept ProcessOpts config' },
  { text: '- Filter by policy' },
  { text: '- Audit each transform result' },
  { text: '' },
  { text: 'Input validation returns Result<T>', highlight: true },
  { text: 'EventBus uses typed payloads' },
];

// Test suite items
export const TEST_ITEMS = [
  'test_handles_null_input',
  'test_returns_correct_format',
  'test_unicode_support',
  'test_edge_case_empty',
  'test_performance_under_100ms',
  'test_idempotent_behavior',
] as const;
