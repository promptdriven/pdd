// ── Colors ──
export const BG_COLOR = '#0A0F1A';

export const UNCONVERTED = {
  fill: '#1E293B',
  border: '#334155',
  borderOpacity: 0.2,
  borderWidth: 1,
};

export const CONVERTING = {
  border: '#4A90D9',
  borderOpacity: 0.6,
  borderWidth: 2,
  glowColor: '#4A90D9',
  glowOpacity: 0.2,
  glowBlur: 20,
  holdFrames: 8,
};

export const CONVERTED = {
  fill: '#0F172A',
  border: '#4A90D9',
  borderOpacity: 0.3,
  borderWidth: 1.5,
  glowColor: '#4A90D9',
  glowOpacity: 0.08,
  glowBlur: 12,
};

export const EDGE_UNCONVERTED = {
  color: '#334155',
  opacity: 0.1,
  width: 1,
};

export const EDGE_CONVERTED = {
  color: '#4A90D9',
  opacity: 0.2,
  width: 1.5,
};

// ── Dimensions ──
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;
export const MODULE_W = 70;
export const MODULE_H = 28;

// ── Layout — 40 modules in 6 cluster groups ──
// Clusters are loosely arranged to look like a realistic dependency graph.
// The "auth" cluster is roughly center-left so the glow spreads outward.

interface ModuleDef {
  id: number;
  name: string;
  x: number;
  y: number;
  cluster: number;
}

// Generate module positions in 6 clusters
const clusterCenters: [number, number][] = [
  [480, 300],   // cluster 0: auth area (center-left)
  [780, 250],   // cluster 1: user/role area
  [380, 550],   // cluster 2: session/token area
  [700, 520],   // cluster 3: api/middleware area
  [1050, 320],  // cluster 4: data services
  [1100, 560],  // cluster 5: external integrations
];

function spreadModules(
  clusterId: number,
  cx: number,
  cy: number,
  count: number,
  startId: number,
  names: string[],
): ModuleDef[] {
  const results: ModuleDef[] = [];
  const cols = Math.ceil(Math.sqrt(count));
  const spacingX = MODULE_W + 22;
  const spacingY = MODULE_H + 18;
  for (let i = 0; i < count; i++) {
    const col = i % cols;
    const row = Math.floor(i / cols);
    const totalCols = Math.min(count - row * cols, cols);
    const offsetX = (col - (totalCols - 1) / 2) * spacingX;
    const offsetY = (row - (Math.ceil(count / cols) - 1) / 2) * spacingY;
    results.push({
      id: startId + i,
      name: names[i] || `module_${startId + i}`,
      x: cx + offsetX,
      y: cy + offsetY,
      cluster: clusterId,
    });
  }
  return results;
}

export const MODULES: ModuleDef[] = [
  // Cluster 0: auth (7 modules, ids 0-6)
  ...spreadModules(0, 480, 300, 7, 0, [
    'auth_handler',     // 0  — pre-converted
    'session_manager',  // 1  — wave 2
    'token_validator',  // 2  — wave 2
    'auth_cache',       // 3
    'login_flow',       // 4
    'oauth_bridge',     // 5
    'api_router',       // 6  — wave 4
  ]),
  // Cluster 1: user/role (7 modules, ids 7-13)
  ...spreadModules(1, 800, 250, 7, 7, [
    'user_parser',      // 7  — wave 3
    'role_checker',     // 8  — wave 3
    'permission_gate',  // 9
    'user_profile',     // 10
    'group_resolver',   // 11
    'access_log',       // 12
    'audit_trail',      // 13
  ]),
  // Cluster 2: session (6 modules, ids 14-19)
  ...spreadModules(2, 380, 540, 6, 14, [
    'middleware_chain',  // 14 — wave 4
    'rate_limiter',      // 15 — wave 4
    'session_store',     // 16
    'cookie_parser',     // 17
    'csrf_guard',        // 18
    'throttle_mgr',      // 19
  ]),
  // Cluster 3: api (7 modules, ids 20-26)
  ...spreadModules(3, 720, 520, 7, 20, [
    'route_handler',    // 20
    'request_parser',   // 21
    'response_builder', // 22
    'error_handler',    // 23
    'validator_core',   // 24
    'schema_loader',    // 25
    'endpoint_map',     // 26
  ]),
  // Cluster 4: data (7 modules, ids 27-33)
  ...spreadModules(4, 1080, 320, 7, 27, [
    'db_connector',     // 27
    'query_builder',    // 28
    'model_factory',    // 29
    'migration_mgr',    // 30
    'cache_layer',      // 31
    'index_manager',    // 32
    'data_validator',   // 33
  ]),
  // Cluster 5: integrations (6 modules, ids 34-39)
  ...spreadModules(5, 1120, 560, 6, 34, [
    'webhook_sender',   // 34
    'email_service',    // 35
    'notification_hub', // 36
    'event_bus',        // 37
    'log_aggregator',   // 38
    'metrics_sink',     // 39
  ]),
];

// ── Edges — dependency connections between modules ──
// Each edge is [fromId, toId]
export const EDGES: [number, number][] = [
  // Auth cluster internal
  [0, 1], [0, 2], [1, 3], [0, 4], [4, 5], [0, 6],
  // Auth → User/Role
  [0, 7], [0, 8], [2, 8], [1, 7],
  // Auth → Session
  [1, 14], [0, 15], [1, 16], [0, 17],
  // User cluster internal
  [7, 9], [8, 9], [7, 10], [9, 11], [8, 12], [12, 13],
  // Session cluster internal
  [14, 15], [14, 16], [16, 17], [17, 18], [15, 19],
  // Auth → API
  [6, 20], [6, 21],
  // API cluster internal
  [20, 21], [21, 22], [20, 23], [21, 24], [24, 25], [20, 26],
  // API → Data
  [20, 27], [24, 28], [22, 29],
  // Data cluster internal
  [27, 28], [28, 29], [27, 30], [29, 31], [28, 32], [27, 33],
  // API → Integrations
  [23, 34], [22, 35],
  // Data → Integrations
  [27, 37], [31, 38],
  // Integration cluster internal
  [34, 36], [35, 36], [36, 37], [37, 38], [38, 39],
  // Cross-cluster
  [14, 20], [9, 20], [5, 34], [3, 31], [19, 23],
  // Additional edges for density
  [10, 29], [11, 12], [13, 38], [4, 1], [16, 19],
  [25, 33], [26, 20], [30, 32], [18, 15],
];

// ── Conversion waves ──
export interface ConversionWave {
  startFrame: number;
  moduleIds: number[];
  cumulative: number;
}

export const CONVERSION_WAVES: ConversionWave[] = [
  { startFrame: 0, moduleIds: [0], cumulative: 1 },          // auth_handler
  { startFrame: 20, moduleIds: [1, 2], cumulative: 3 },      // session_manager, token_validator
  { startFrame: 60, moduleIds: [7, 8], cumulative: 5 },      // user_parser, role_checker
  { startFrame: 110, moduleIds: [6, 14, 15], cumulative: 8 }, // api_router, middleware_chain, rate_limiter
];

// Flash timing
export const FLASH_IN_FRAMES = 6;
export const FLASH_HOLD_FRAMES = 8;
export const FLASH_SETTLE_FRAMES = 10;
export const STAGGER_FRAMES = 12;

// Pulse
export const PULSE_START_FRAME = 170;
export const PULSE_PERIOD = 50;
export const PULSE_AMPLITUDE = 0.02;

// Counter
export const COUNTER_POSITION: [number, number] = [1680, 80];
export const TOTAL_MODULES = 40;
