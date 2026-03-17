// constants.ts — Colors, dimensions, block/edge data for Legacy Codebase Reveal

export const DURATION_FRAMES = 150;
export const FPS = 30;

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = '#0A0F1A';

// Colors
export const BLOCK_FILL_CLEAN = '#1E293B';
export const BLOCK_FILL_DEBT = '#2A1F1F';
export const BLOCK_BORDER = '#334155';
export const BLOCK_BORDER_OPACITY = 0.3;
export const DEBT_GLOW_COLOR = '#D9944A';
export const DEBT_GLOW_OPACITY = 0.06;
export const EDGE_COLOR = '#334155';
export const EDGE_OPACITY = 0.15;
export const ANNOTATION_COLOR = '#EF4444';
export const PULSE_COLOR = '#EF4444';
export const PULSE_OPACITY = 0.02;
export const PULSE_PERIOD = 60;

// Layout area for blocks
export const AREA = { x: 160, y: 140, width: 1600, height: 800 };

// Annotation definitions
export const ANNOTATIONS = [
  { text: '// don\'t touch', x: 380, y: 320, opacity: 0.5, startFrame: 60 },
  { text: '// here be dragons', x: 1100, y: 250, opacity: 0.5, startFrame: 80 },
  { text: '// legacy', x: 720, y: 580, opacity: 0.4, startFrame: 95 },
  { text: '// temporary fix (2019)', x: 1350, y: 650, opacity: 0.4, startFrame: 95 },
] as const;

// Seeded pseudo-random number generator for deterministic layout
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

// Block definition
export interface BlockDef {
  id: number;
  x: number;
  y: number;
  w: number;
  h: number;
  cluster: number;
  hasDebt: boolean;
}

// Edge definition
export interface EdgeDef {
  from: number;
  to: number;
}

// Generate 40 blocks in 6 clusters
function generateBlocks(): BlockDef[] {
  const rng = seededRandom(42);
  const blocks: BlockDef[] = [];

  // Cluster centers (6 clusters spread across the area)
  const clusterCenters = [
    { cx: 320, cy: 280 },
    { cx: 700, cy: 220 },
    { cx: 1100, cy: 300 },
    { cx: 400, cy: 600 },
    { cx: 800, cy: 650 },
    { cx: 1250, cy: 580 },
  ];

  const blocksPerCluster = [7, 7, 7, 6, 7, 6];
  let id = 0;

  for (let c = 0; c < clusterCenters.length; c++) {
    const { cx, cy } = clusterCenters[c];
    for (let i = 0; i < blocksPerCluster[c]; i++) {
      const w = 60 + rng() * 60;
      const h = 40 + rng() * 20;
      const offsetX = (rng() - 0.5) * 260;
      const offsetY = (rng() - 0.5) * 180;
      blocks.push({
        id,
        x: AREA.x + cx + offsetX - w / 2,
        y: AREA.y + cy + offsetY - h / 2,
        w,
        h,
        cluster: c,
        hasDebt: rng() < 0.3,
      });
      id++;
    }
  }

  return blocks;
}

// Generate ~60 edges connecting blocks
function generateEdges(blocks: BlockDef[]): EdgeDef[] {
  const rng = seededRandom(123);
  const edges: EdgeDef[] = [];
  const edgeSet = new Set<string>();

  const addEdge = (from: number, to: number) => {
    if (from === to) return;
    const key = `${Math.min(from, to)}-${Math.max(from, to)}`;
    if (edgeSet.has(key)) return;
    edgeSet.add(key);
    edges.push({ from, to });
  };

  // Intra-cluster connections (dense)
  for (let c = 0; c < 6; c++) {
    const clusterBlocks = blocks.filter((b) => b.cluster === c);
    for (let i = 0; i < clusterBlocks.length - 1; i++) {
      addEdge(clusterBlocks[i].id, clusterBlocks[i + 1].id);
      // Add some extra intra-cluster edges
      if (rng() < 0.4 && i + 2 < clusterBlocks.length) {
        addEdge(clusterBlocks[i].id, clusterBlocks[i + 2].id);
      }
    }
  }

  // Inter-cluster connections (sparser, creating the tangled web)
  for (let i = 0; i < blocks.length; i++) {
    for (let j = i + 1; j < blocks.length; j++) {
      if (blocks[i].cluster !== blocks[j].cluster && rng() < 0.04) {
        addEdge(blocks[i].id, blocks[j].id);
      }
    }
  }

  // Ensure we have roughly 60 edges
  while (edges.length < 58) {
    const a = Math.floor(rng() * blocks.length);
    const b = Math.floor(rng() * blocks.length);
    addEdge(a, b);
  }

  return edges;
}

export const FILE_BLOCKS = generateBlocks();
export const DEPENDENCY_EDGES = generateEdges(FILE_BLOCKS);
