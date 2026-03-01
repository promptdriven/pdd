import { useState, useCallback, useMemo } from 'react';
import { ArchitectureModule } from '../api';

const MAX_HISTORY = 50;

interface HistoryState {
  past: ArchitectureModule[][];
  present: ArchitectureModule[];
  future: ArchitectureModule[][];
}

interface UseArchitectureHistoryReturn {
  // Current state
  architecture: ArchitectureModule[];
  hasUnsavedChanges: boolean;

  // Module operations
  addModule: (module: ArchitectureModule) => void;
  updateModule: (originalFilename: string, updatedModule: ArchitectureModule) => void;
  batchUpdateModules: (updates: ArchitectureModule[]) => void;
  deleteModule: (filename: string) => void;

  // Dependency operations
  addDependency: (targetFilename: string, sourceFilename: string) => void;
  removeDependency: (targetFilename: string, sourceFilename: string) => void;

  // Position operations
  updatePositions: (positions: Map<string, { x: number; y: number }>) => void;

  // History operations
  undo: () => void;
  redo: () => void;
  canUndo: boolean;
  canRedo: boolean;

  // Persistence
  setOriginal: (modules: ArchitectureModule[]) => void;
  reset: () => void;
  discardChanges: () => void;
}

export function useArchitectureHistory(
  initialModules: ArchitectureModule[] = []
): UseArchitectureHistoryReturn {
  const [state, setState] = useState<HistoryState>({
    past: [],
    present: initialModules,
    future: [],
  });

  const [originalModules, setOriginalModules] = useState<ArchitectureModule[]>(initialModules);

  // Check if there are unsaved changes
  const hasUnsavedChanges = useMemo(() => {
    return JSON.stringify(state.present) !== JSON.stringify(originalModules);
  }, [state.present, originalModules]);

  // Push a new state (clears future, limits past)
  const pushState = useCallback((newPresent: ArchitectureModule[]) => {
    setState((prev) => ({
      past: [...prev.past.slice(-MAX_HISTORY + 1), prev.present],
      present: newPresent,
      future: [],
    }));
  }, []);

  // Module operations
  const addModule = useCallback(
    (module: ArchitectureModule) => {
      pushState([...state.present, module]);
    },
    [state.present, pushState]
  );

  const updateModule = useCallback(
    (originalFilename: string, updatedModule: ArchitectureModule) => {
      const newModules = state.present.map((m) => {
        if (m.filename === originalFilename) {
          return updatedModule;
        }
        // If filename changed, update dependencies in other modules
        if (originalFilename !== updatedModule.filename) {
          return {
            ...m,
            dependencies: m.dependencies.map((dep) =>
              dep === originalFilename ? updatedModule.filename : dep
            ),
          };
        }
        return m;
      });
      pushState(newModules);
    },
    [state.present, pushState]
  );

  // Batch update multiple modules in a single history entry (e.g., for group assignment)
  const batchUpdateModules = useCallback(
    (updates: ArchitectureModule[]) => {
      const updateMap = new Map(updates.map(m => [m.filename, m]));
      const newModules = state.present.map(m => updateMap.get(m.filename) || m);
      pushState(newModules);
    },
    [state.present, pushState]
  );

  const deleteModule = useCallback(
    (filename: string) => {
      const newModules = state.present
        .filter((m) => m.filename !== filename)
        .map((m) => ({
          ...m,
          // Remove deleted module from dependencies
          dependencies: m.dependencies.filter((dep) => dep !== filename),
        }));
      pushState(newModules);
    },
    [state.present, pushState]
  );

  // Dependency operations
  const addDependency = useCallback(
    (targetFilename: string, sourceFilename: string) => {
      const newModules = state.present.map((m) => {
        if (m.filename === targetFilename) {
          // Avoid duplicates
          if (m.dependencies.includes(sourceFilename)) {
            return m;
          }
          return {
            ...m,
            dependencies: [...m.dependencies, sourceFilename],
          };
        }
        return m;
      });
      pushState(newModules);
    },
    [state.present, pushState]
  );

  const removeDependency = useCallback(
    (targetFilename: string, sourceFilename: string) => {
      const newModules = state.present.map((m) => {
        if (m.filename === targetFilename) {
          return {
            ...m,
            dependencies: m.dependencies.filter((dep) => dep !== sourceFilename),
          };
        }
        return m;
      });
      pushState(newModules);
    },
    [state.present, pushState]
  );

  // Position operations - update all positions at once without creating undo history
  const updatePositions = useCallback(
    (positions: Map<string, { x: number; y: number }>) => {
      // Update all positions directly without pushing to history (too many small changes)
      setState((prev) => ({
        ...prev,
        present: prev.present.map((m) => {
          const pos = positions.get(m.filename);
          return pos ? { ...m, position: pos } : m;
        }),
      }));
    },
    []
  );

  // History operations
  const undo = useCallback(() => {
    setState((prev) => {
      if (prev.past.length === 0) return prev;
      const previous = prev.past[prev.past.length - 1];
      return {
        past: prev.past.slice(0, -1),
        present: previous,
        future: [prev.present, ...prev.future],
      };
    });
  }, []);

  const redo = useCallback(() => {
    setState((prev) => {
      if (prev.future.length === 0) return prev;
      const next = prev.future[0];
      return {
        past: [...prev.past, prev.present],
        present: next,
        future: prev.future.slice(1),
      };
    });
  }, []);

  // Set original state (e.g., after loading from server)
  const setOriginal = useCallback((modules: ArchitectureModule[]) => {
    setOriginalModules(modules);
    setState({
      past: [],
      present: modules,
      future: [],
    });
  }, []);

  // Reset to original state
  const reset = useCallback(() => {
    setState({
      past: [],
      present: originalModules,
      future: [],
    });
  }, [originalModules]);

  // Discard changes (reset to original)
  const discardChanges = useCallback(() => {
    reset();
  }, [reset]);

  return {
    architecture: state.present,
    hasUnsavedChanges,
    addModule,
    updateModule,
    batchUpdateModules,
    deleteModule,
    addDependency,
    removeDependency,
    updatePositions,
    undo,
    redo,
    canUndo: state.past.length > 0,
    canRedo: state.future.length > 0,
    setOriginal,
    reset,
    discardChanges,
  };
}

export default useArchitectureHistory;
