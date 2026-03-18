// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const BLUE_ACCENT = '#4A90D9';
export const LABEL_COLOR = '#E2E8F0';

export const UNCONVERTED = {
  fill: '#1E293B',
  border: '#334155',
  borderOpacity: 0.2,
  borderWidth: 1,
} as const;

export const CONVERTING = {
  border: BLUE_ACCENT,
  borderOpacity: 0.6,
  borderWidth: 2,
  glowColor: BLUE_ACCENT,
  glowOpacity: 0.2,
  glowBlur: 20,
} as const;

export const CONVERTED = {
  fill: '#0F172A',
  border: BLUE_ACCENT,
  borderOpacity: 0.3,
  borderWidth: 1.5,
  glowColor: BLUE_ACCENT,
  glowOpacity: 0.08,
  glowBlur: 12,
} as const;

// ── Edges ───────────────────────────────────────────────────────────
export const EDGE_UNCONVERTED = {
  color: '#334155',
  opacity: 0.1,
  width: 1,
} as const;

export const EDGE_CONVERTED = {
  color: BLUE_ACCENT,
  opacity: 0.2,
  width: 1.5,
} as const;

// ── Dimensions ──────────────────────────────────────────────────────
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;
export const TOPOLOGY_W = 1600;
export const TOPOLOGY_H = 800;
export const TOPOLOGY_X = (CANVAS_W - TOPOLOGY_W) / 2;
export const TOPOLOGY_Y = (CANVAS_H - TOPOLOGY_H) / 2;
export const BLOCK_W = 90;
export const BLOCK_H = 32;

// ── Module Layout ───────────────────────────────────────────────────
// 40 modules arranged in ~6 cluster groups across the topology.
// Positions are { x, y } relative to the topology origin.

export interface ModuleNode {
  id: number;
  name: string;
  x: number;
  y: number;
}

export interface Edge {
  from: number;
  to: number;
}

// Seeded pseudo-random helper for deterministic layouts
function seededPositions(): ModuleNode[] {
  const names = [
    'auth_handler',      // 0  — pre-converted
    'session_manager',   // 1  — wave 2
    'token_validator',   // 2  — wave 2
    'user_parser',       // 3  — wave 3
    'role_checker',      // 4  — wave 3
    'api_router',        // 5  — wave 4
    'middleware_chain',  // 6  — wave 4
    'rate_limiter',      // 7  — wave 4
    'db_connector',      // 8
    'query_builder',     // 9
    'cache_layer',       // 10
    'log_formatter',     // 11
    'error_handler',     // 12
    'event_emitter',     // 13
    'config_loader',     // 14
    'env_resolver',      // 15
    'schema_validator',  // 16
    'json_parser',       // 17
    'xml_adapter',       // 18
    'csv_importer',      // 19
    'file_watcher',      // 20
    'cron_scheduler',    // 21
    'job_runner',        // 22
    'queue_manager',     // 23
    'notification_svc',  // 24
    'email_sender',      // 25
    'sms_gateway',       // 26
    'push_handler',      // 27
    'metrics_collector', // 28
    'health_checker',    // 29
    'audit_logger',      // 30
    'encryption_util',   // 31
    'hash_provider',     // 32
    'cert_manager',      // 33
    'dns_resolver',      // 34
    'proxy_handler',     // 35
    'load_balancer',     // 36
    'circuit_breaker',   // 37
    'retry_policy',      // 38
    'timeout_guard',     // 39
  ];

  // Cluster-based layout — 6 clusters
  const clusters: { cx: number; cy: number; ids: number[] }[] = [
    // Auth cluster (top-center-left) — contains the conversion origin
    { cx: 480, cy: 160, ids: [0, 1, 2, 3, 4] },
    // API cluster (center-left)
    { cx: 320, cy: 400, ids: [5, 6, 7, 12, 13] },
    // Data cluster (center-right)
    { cx: 800, cy: 300, ids: [8, 9, 10, 16, 17] },
    // IO cluster (right)
    { cx: 1150, cy: 200, ids: [18, 19, 20, 14, 15] },
    // Services cluster (bottom-left)
    { cx: 400, cy: 620, ids: [21, 22, 23, 24, 25, 26, 27] },
    // Infra cluster (bottom-right)
    { cx: 1050, cy: 560, ids: [28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 11] },
  ];

  const nodes: ModuleNode[] = new Array(40);

  for (const cluster of clusters) {
    const count = cluster.ids.length;
    const cols = Math.ceil(Math.sqrt(count));
    cluster.ids.forEach((id, i) => {
      const col = i % cols;
      const row = Math.floor(i / cols);
      const spacing = 120;
      const ox = (col - (cols - 1) / 2) * spacing;
      const oy = (row - (Math.ceil(count / cols) - 1) / 2) * (BLOCK_H + 28);
      nodes[id] = {
        id,
        name: names[id],
        x: cluster.cx + ox,
        y: cluster.cy + oy,
      };
    });
  }

  return nodes;
}

export const MODULES: ModuleNode[] = seededPositions();

// ── Edges (dependency graph) ────────────────────────────────────────
// ~60 edges linking modules, weighted toward intra-cluster connections
export const EDGES: Edge[] = (() => {
  const e: Edge[] = [];

  // Auth cluster internal
  e.push({ from: 0, to: 1 }, { from: 0, to: 2 }, { from: 1, to: 3 }, { from: 2, to: 4 });
  e.push({ from: 3, to: 4 }, { from: 1, to: 2 });

  // Auth → API
  e.push({ from: 0, to: 5 }, { from: 0, to: 6 }, { from: 2, to: 7 });

  // API cluster internal
  e.push({ from: 5, to: 6 }, { from: 6, to: 7 }, { from: 5, to: 12 }, { from: 5, to: 13 });
  e.push({ from: 12, to: 13 });

  // Data cluster internal
  e.push({ from: 8, to: 9 }, { from: 9, to: 10 }, { from: 8, to: 16 }, { from: 16, to: 17 });
  e.push({ from: 10, to: 17 });

  // API → Data
  e.push({ from: 5, to: 8 }, { from: 6, to: 9 }, { from: 13, to: 16 });

  // IO cluster internal
  e.push({ from: 18, to: 19 }, { from: 19, to: 20 }, { from: 14, to: 15 }, { from: 14, to: 18 });
  e.push({ from: 15, to: 20 });

  // Data → IO
  e.push({ from: 17, to: 18 }, { from: 9, to: 14 }, { from: 10, to: 15 });

  // Services cluster internal
  e.push({ from: 21, to: 22 }, { from: 22, to: 23 }, { from: 23, to: 24 });
  e.push({ from: 24, to: 25 }, { from: 24, to: 26 }, { from: 24, to: 27 });
  e.push({ from: 21, to: 23 });

  // API → Services
  e.push({ from: 5, to: 21 }, { from: 12, to: 24 }, { from: 7, to: 23 });

  // Infra cluster internal
  e.push({ from: 28, to: 29 }, { from: 29, to: 30 }, { from: 30, to: 11 });
  e.push({ from: 31, to: 32 }, { from: 32, to: 33 }, { from: 33, to: 34 });
  e.push({ from: 35, to: 36 }, { from: 36, to: 37 }, { from: 37, to: 38 }, { from: 38, to: 39 });
  e.push({ from: 28, to: 31 }, { from: 29, to: 35 }, { from: 30, to: 38 });
  e.push({ from: 11, to: 39 });

  // Cross-cluster infra links
  e.push({ from: 8, to: 28 }, { from: 10, to: 29 }, { from: 31, to: 2 });
  e.push({ from: 25, to: 34 }, { from: 23, to: 36 }, { from: 22, to: 37 });

  return e;
})();

// ── Conversion waves ────────────────────────────────────────────────
export interface ConversionWave {
  startFrame: number;
  moduleIds: number[];
  cumulative: number;
  staggerFrames: number;
}

export const WAVES: ConversionWave[] = [
  { startFrame: 0, moduleIds: [0], cumulative: 1, staggerFrames: 0 },        // auth_handler pre-converted
  { startFrame: 20, moduleIds: [1, 2], cumulative: 3, staggerFrames: 12 },    // wave 2
  { startFrame: 60, moduleIds: [3, 4], cumulative: 5, staggerFrames: 15 },    // wave 3
  { startFrame: 110, moduleIds: [5, 6, 7], cumulative: 8, staggerFrames: 12 }, // wave 4
];

// Flash / settle timing
export const FLASH_IN_FRAMES = 6;
export const FLASH_HOLD_FRAMES = 8;
export const FLASH_SETTLE_FRAMES = 10;
export const EDGE_TRANSITION_FRAMES = 15;

// Pulse
export const PULSE_START_FRAME = 170;
export const PULSE_PERIOD = 50;
export const PULSE_AMPLITUDE = 0.02;

// Counter
export const COUNTER_POS = { x: 1680, y: 80 } as const;
export const TOTAL_MODULES = 40;
