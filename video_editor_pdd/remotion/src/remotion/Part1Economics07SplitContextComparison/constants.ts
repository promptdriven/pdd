// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#000000";
export const TOTAL_FRAMES = 600;

// Split
export const SPLIT_X = 960;
export const SPLIT_LINE_COLOR = "#334155";
export const SPLIT_LINE_OPACITY = 0.12;
export const SPLIT_LINE_WIDTH = 2;

// Panel dimensions
export const PANEL_WIDTH = 958;
export const PANEL_PADDING = 80;
export const WINDOW_TOP = 90;
export const WINDOW_BOTTOM = 1020;
export const WINDOW_HEIGHT = WINDOW_BOTTOM - WINDOW_TOP;

// Colors
export const AMBER = "#D9944A";
export const BLUE = "#4A90D9";
export const RED = "#E74C3C";
export const GREEN = "#5AAA6E";
export const CODE_MUTED = "#94A3B8";
export const TEXT_LIGHT = "#E2E8F0";

// Typography
export const FONT_CODE = "JetBrains Mono, monospace";
export const FONT_UI = "Inter, sans-serif";

// Timing — frame ranges
export const SPLIT_LINE_START = 0;
export const SPLIT_LINE_END = 20;

export const HEADER_START = 30;
export const HEADER_END = 45;

export const LEFT_CODE_START = 60;
export const LEFT_CODE_END = 120;
export const LEFT_HIGHLIGHT_START = 100;
export const LEFT_HIGHLIGHT_STAGGER = 10;

export const RIGHT_PROMPT_START = 150;
export const RIGHT_PROMPT_END = 170;
export const RIGHT_TESTS_START = 180;
export const RIGHT_TESTS_END = 200;
export const RIGHT_GROUNDING_START = 210;
export const RIGHT_GROUNDING_END = 230;

export const TOKEN_COUNT_START = 240;
export const TOKEN_COUNT_END = 255;

export const FILL_BAR_START = 300;
export const FILL_BAR_END = 320;

export const PULSE_CYCLE = 50;
export const PULSE_MIN = 0.08;
export const PULSE_MAX = 0.12;

// Left panel code lines — fake dense code
export const CODE_LINES: string[] = [
  "import { useEffect, useState, useCallback, useMemo } from 'react';",
  "import { fetchUserData, updateProfile } from '../api/users';",
  "import { validateEmail, sanitizeInput } from '../utils/validation';",
  "import { Logger } from '../services/logger';",
  "",
  "interface UserProfile {",
  "  id: string;",
  "  email: string;",
  "  displayName: string;",
  "  preferences: Record<string, unknown>;",
  "  lastLogin: Date;",
  "  createdAt: Date;",
  "}",
  "",
  "const DEFAULT_TIMEOUT = 5000;",
  "const MAX_RETRIES = 3;",
  "const CACHE_TTL = 60 * 1000;",
  "",
  "export function useUserProfile(userId: string) {",
  "  const [profile, setProfile] = useState<UserProfile | null>(null);",
  "  const [loading, setLoading] = useState(true);",
  "  const [error, setError] = useState<Error | null>(null);",
  "  const [retryCount, setRetryCount] = useState(0);",
  "",
  "  const fetchProfile = useCallback(async () => {",
  "    try {",
  "      setLoading(true);",
  "      const data = await fetchUserData(userId, {",
  "        timeout: DEFAULT_TIMEOUT,",
  "        includePreferences: true,",
  "        expandRelations: ['team', 'org'],",
  "      });",
  "      setProfile(data);",
  "      setError(null);",
  "    } catch (err) {",
  "      if (retryCount < MAX_RETRIES) {",
  "        setRetryCount(prev => prev + 1);",
  "        return;",
  "      }",
  "      setError(err as Error);",
  "      Logger.error('Failed to fetch profile', { userId, err });",
  "    } finally {",
  "      setLoading(false);",
  "    }",
  "  }, [userId, retryCount]);",
  "",
  "  useEffect(() => { fetchProfile(); }, [fetchProfile]);",
  "",
  "  const updateField = useCallback(",
  "    async (field: keyof UserProfile, value: unknown) => {",
  "      if (!profile) return;",
  "      const sanitized = sanitizeInput(String(value));",
  "      if (field === 'email' && !validateEmail(sanitized)) {",
  "        throw new Error('Invalid email');",
  "      }",
  "      const updated = await updateProfile(userId, {",
  "        [field]: sanitized,",
  "      });",
  "      setProfile(updated);",
  "    },",
  "    [profile, userId]",
  "  );",
  "",
  "  return { profile, loading, error, updateField, retry: fetchProfile };",
  "}",
  "",
  "export function ProfileCard({ userId }: { userId: string }) {",
  "  const { profile, loading, error, updateField } = useUserProfile(userId);",
  "  const [editing, setEditing] = useState(false);",
  "  const [draft, setDraft] = useState('');",
  "",
  "  const handleSave = async () => {",
  "    await updateField('displayName', draft);",
  "    setEditing(false);",
  "  };",
  "",
  "  if (loading) return <Spinner />;",
  "  if (error) return <ErrorBanner message={error.message} />;",
  "  if (!profile) return null;",
  "",
  "  return (",
  "    <div className={styles.card}>",
  "      <Avatar src={profile.avatar} size='lg' />",
  "      <div className={styles.info}>",
  "        {editing ? (",
  "          <input value={draft} onChange={e => setDraft(e.target.value)} />",
  "        ) : (",
  "          <h2 onClick={() => { setEditing(true); setDraft(profile.name); }}>",
  "            {profile.displayName}",
  "          </h2>",
  "        )}",
  "        <span className={styles.email}>{profile.email}</span>",
  "        <span className={styles.meta}>",
  "          Last login: {formatDate(profile.lastLogin)}",
  "        </span>",
  "      </div>",
  "      {editing && <Button onClick={handleSave}>Save</Button>}",
  "    </div>",
  "  );",
  "}",
];

// Which line ranges are "irrelevant" (red highlight)
export const IRRELEVANT_RANGES: { start: number; end: number }[] = [
  { start: 0, end: 4 },    // imports
  { start: 14, end: 17 },  // constants
  { start: 46, end: 60 },  // updateField
  { start: 64, end: 77 },  // ProfileCard render
  { start: 82, end: 92 },  // JSX
];

// Which line range is "relevant" (green highlight)
export const RELEVANT_RANGE = { start: 24, end: 43 }; // fetchProfile function

// Right panel — prompt text
export const PROMPT_LINES: string[] = [
  "Generate a React hook that fetches a user",
  "profile by ID with retry logic and caching.",
  "",
  "The hook should:",
  "- Accept a userId string parameter",
  "- Return { profile, loading, error }",
  "- Retry up to 3 times on failure",
  "- Cache results for 60 seconds",
  "- Use the existing fetchUserData API",
  "",
  "The profile type has: id, email,",
  "displayName, preferences, lastLogin.",
  "",
  "Handle loading and error states cleanly.",
  "Log errors via the Logger service.",
];

// Right panel — test names
export const TEST_LINES: string[] = [
  'it("returns profile on success")',
  'it("shows loading state initially")',
  'it("retries on network failure")',
  'it("stops after 3 retries")',
  'it("caches for 60 seconds")',
  'it("clears cache on userId change")',
  'it("handles concurrent requests")',
  'it("validates email on update")',
  'it("sanitizes input values")',
  'it("logs errors with context")',
  'it("returns null for missing user")',
  'it("preserves state across re-renders")',
];

// Right panel — grounding example
export const GROUNDING_LINES: string[] = [
  "// Example: existing useTeamData hook pattern",
  "export function useTeamData(teamId: string) {",
  "  const [data, setData] = useState(null);",
  "  // ... same fetch + retry pattern",
  "  return { data, loading, error };",
  "}",
];
