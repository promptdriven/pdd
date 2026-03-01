/**
 * Batch Utilities for PDD Connect
 *
 * Computes connected components (batches) from the architecture dependency graph.
 * Each batch contains modules that depend on each other - modules within a batch
 * must sync sequentially (by priority), while different batches are independent.
 */

import type { ArchitectureModule } from '../api';

export interface Batch {
  id: number;
  name: string;
  modules: ArchitectureModule[];
  moduleFilenames: Set<string>;
  color: string;
}

/**
 * Union-Find (Disjoint Set Union) data structure for efficient connected component detection.
 * Uses path compression and union by rank for near-linear time complexity O(n * α(n)).
 */
class UnionFind {
  private parent: Map<string, string>;
  private rank: Map<string, number>;

  constructor(elements: string[]) {
    this.parent = new Map();
    this.rank = new Map();
    for (const el of elements) {
      this.parent.set(el, el);
      this.rank.set(el, 0);
    }
  }

  find(x: string): string {
    if (this.parent.get(x) !== x) {
      // Path compression
      this.parent.set(x, this.find(this.parent.get(x)!));
    }
    return this.parent.get(x)!;
  }

  union(x: string, y: string): void {
    const rootX = this.find(x);
    const rootY = this.find(y);
    if (rootX === rootY) return;

    // Union by rank
    const rankX = this.rank.get(rootX)!;
    const rankY = this.rank.get(rootY)!;
    if (rankX < rankY) {
      this.parent.set(rootX, rootY);
    } else if (rankX > rankY) {
      this.parent.set(rootY, rootX);
    } else {
      this.parent.set(rootY, rootX);
      this.rank.set(rootX, rankX + 1);
    }
  }

  getComponents(): Map<string, string[]> {
    const components = new Map<string, string[]>();
    for (const el of this.parent.keys()) {
      const root = this.find(el);
      if (!components.has(root)) {
        components.set(root, []);
      }
      components.get(root)!.push(el);
    }
    return components;
  }
}

// Predefined colors for batch visual distinction
const BATCH_COLORS = [
  '#8B5CF6', // Purple
  '#06B6D4', // Cyan
  '#F59E0B', // Amber
  '#10B981', // Emerald
  '#EC4899', // Pink
  '#6366F1', // Indigo
  '#EF4444', // Red
  '#14B8A6', // Teal
];

/**
 * Compute batches (connected components) from architecture modules.
 * A batch is a group of modules where all modules are reachable from each other
 * through dependency relationships.
 *
 * @param modules - Array of architecture modules with dependencies
 * @returns Array of batches, sorted by minimum priority (most important first)
 */
export function computeBatches(modules: ArchitectureModule[]): Batch[] {
  if (modules.length === 0) return [];

  const filenames = modules.map(m => m.filename);
  const filenameSet = new Set(filenames);
  const uf = new UnionFind(filenames);

  // Build adjacency by unioning modules with their dependencies
  for (const module of modules) {
    for (const dep of module.dependencies) {
      // Only union if dependency exists in architecture
      if (filenameSet.has(dep)) {
        uf.union(module.filename, dep);
      }
    }
  }

  // Get connected components
  const components = uf.getComponents();

  // Build lookup map for modules
  const moduleMap = new Map<string, ArchitectureModule>();
  for (const m of modules) {
    moduleMap.set(m.filename, m);
  }

  // Convert to Batch objects
  const batches: Batch[] = [];
  let batchIndex = 0;

  for (const [_root, memberFilenames] of components) {
    const batchModules = memberFilenames
      .map(fn => moduleMap.get(fn)!)
      .sort((a, b) => a.priority - b.priority);  // Sort by priority within batch

    batches.push({
      id: batchIndex,
      name: `Batch ${batchIndex + 1}`,
      modules: batchModules,
      moduleFilenames: new Set(memberFilenames),
      color: BATCH_COLORS[batchIndex % BATCH_COLORS.length],
    });
    batchIndex++;
  }

  // Sort batches by minimum priority (most important batches first)
  batches.sort((a, b) => {
    const minPriorityA = Math.min(...a.modules.map(m => m.priority));
    const minPriorityB = Math.min(...b.modules.map(m => m.priority));
    return minPriorityA - minPriorityB;
  });

  // Re-assign IDs and colors after sorting
  batches.forEach((batch, idx) => {
    batch.id = idx;
    batch.name = `Batch ${idx + 1}`;
    batch.color = BATCH_COLORS[idx % BATCH_COLORS.length];
  });

  return batches;
}

/**
 * Get the batch that contains a specific module.
 *
 * @param moduleFilename - The filename of the module to find
 * @param batches - Array of computed batches
 * @returns The batch containing the module, or undefined if not found
 */
export function getBatchForModule(
  moduleFilename: string,
  batches: Batch[]
): Batch | undefined {
  return batches.find(b => b.moduleFilenames.has(moduleFilename));
}

/**
 * Filter modules to only include those in the specified batch.
 *
 * @param modules - Array of all architecture modules
 * @param batch - The batch to filter by (null = no filtering)
 * @returns Filtered array of modules
 */
export function filterModulesByBatch(
  modules: ArchitectureModule[],
  batch: Batch | null
): ArchitectureModule[] {
  if (!batch) return modules;
  return modules.filter(m => batch.moduleFilenames.has(m.filename));
}
