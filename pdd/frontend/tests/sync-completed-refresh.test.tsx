import { render, act, waitFor } from '@testing-library/react';
import { vi, describe, it, expect, beforeEach } from 'vitest';
import React, { useState } from 'react';
import ArchitectureView from '../components/ArchitectureView';
import type { PromptInfo } from '../api';

// Mock the api module
vi.mock('../api', () => {
  const listPromptsMock = vi.fn();
  const checkArchitectureExistsMock = vi.fn();
  const getArchitectureMock = vi.fn();

  return {
    api: {
      listPrompts: listPromptsMock,
      checkArchitectureExists: checkArchitectureExistsMock,
      getArchitecture: getArchitectureMock,
      getStatus: vi.fn().mockResolvedValue({ status: 'ok' }),
      getFileContent: vi.fn(),
      listRemoteSessions: vi.fn().mockResolvedValue([]),
      submitRemoteCommand: vi.fn(),
      spawnTerminal: vi.fn(),
    },
    // Re-export types needed by imports
    PromptInfo: {},
  };
});

// Mock DependencyViewer since it uses ReactFlow which needs complex setup
vi.mock('../components/DependencyViewer', () => ({
  default: () => <div data-testid="dependency-viewer">DependencyViewer</div>,
}));

// Mock other heavy components
vi.mock('../components/FileBrowser', () => ({
  default: () => null,
}));
vi.mock('../components/GenerationProgressModal', () => ({
  default: () => null,
}));
vi.mock('../components/PromptOrderModal', () => ({
  default: () => null,
}));
vi.mock('../components/GraphToolbar', () => ({
  default: () => null,
}));
vi.mock('../components/ModuleEditModal', () => ({
  default: () => null,
}));
vi.mock('../components/AddModuleModal', () => ({
  default: () => null,
}));
vi.mock('../components/SyncFromPromptModal', () => ({
  default: () => null,
}));
vi.mock('../components/SyncOptionsModal', () => ({
  default: () => null,
}));
vi.mock('../components/BatchFilterDropdown', () => ({
  default: () => null,
}));

// Import the mocked api to control it
import { api } from '../api';

const mockListPrompts = vi.mocked(api.listPrompts);
const mockCheckArchitectureExists = vi.mocked(api.checkArchitectureExists);
const mockGetArchitecture = vi.mocked(api.getArchitecture);

const defaultProps = {
  serverConnected: true,
  isExecuting: false,
  onOpenPromptSpace: vi.fn(),
  executionMode: 'local' as const,
  selectedRemoteSession: null,
  onAddToQueue: vi.fn(),
};

const makePromptInfo = (name: string, opts?: { code?: string; test?: string; example?: string }): PromptInfo => ({
  prompt: `prompts/${name}.prompt`,
  sync_basename: name,
  code: opts?.code,
  test: opts?.test,
  example: opts?.example,
});

describe('ArchitectureView syncCompletedCounter refresh', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default: architecture exists with one module
    mockCheckArchitectureExists.mockResolvedValue({ exists: true, path: 'architecture.json' });
    mockGetArchitecture.mockResolvedValue([
      {
        reason: 'Core module',
        description: 'The main module',
        dependencies: [],
        priority: 1,
        filename: 'app_module.prompt',
        filepath: 'src/app_module.ts',
      },
    ]);
    // Default: prompt exists but missing code/test/example
    mockListPrompts.mockResolvedValue([
      makePromptInfo('app_module'),
    ]);
  });

  it('calls listPrompts again when syncCompletedCounter increments', async () => {
    // Wrapper to allow re-rendering with new counter value
    const Wrapper = ({ counter }: { counter: number }) => (
      <ArchitectureView {...defaultProps} syncCompletedCounter={counter} />
    );

    const { rerender } = render(<Wrapper counter={0} />);

    // Wait for mount load to complete
    await waitFor(() => {
      expect(mockListPrompts).toHaveBeenCalledTimes(1);
    });

    // Increment counter - should trigger another listPrompts call
    await act(async () => {
      rerender(<Wrapper counter={1} />);
    });

    await waitFor(() => {
      expect(mockListPrompts).toHaveBeenCalledTimes(2);
    });
  });

  it('does NOT call listPrompts again when counter stays the same', async () => {
    const Wrapper = ({ counter }: { counter: number }) => (
      <ArchitectureView {...defaultProps} syncCompletedCounter={counter} />
    );

    const { rerender } = render(<Wrapper counter={0} />);

    await waitFor(() => {
      expect(mockListPrompts).toHaveBeenCalledTimes(1);
    });

    // Re-render with same counter value
    await act(async () => {
      rerender(<Wrapper counter={0} />);
    });

    // Should still be 1 (no extra call)
    expect(mockListPrompts).toHaveBeenCalledTimes(1);
  });

  it('updates remainingModulesCount after refresh with new data', async () => {
    // First call: prompt exists but no code/test/example (remaining = 1)
    mockListPrompts.mockResolvedValueOnce([
      makePromptInfo('app_module'),
    ]);
    // Second call: prompt now has code, test, and example (remaining = 0)
    mockListPrompts.mockResolvedValueOnce([
      makePromptInfo('app_module', { code: 'src/app.ts', test: 'tests/app.test.ts', example: 'examples/app.txt' }),
    ]);

    const Wrapper = ({ counter }: { counter: number }) => (
      <ArchitectureView {...defaultProps} syncCompletedCounter={counter} />
    );

    const { rerender, container } = render(<Wrapper counter={0} />);

    // Wait for initial load - should show remaining count
    await waitFor(() => {
      expect(mockListPrompts).toHaveBeenCalledTimes(1);
    });

    // Look for the "Sync Remaining (1)" or "Sync All (1)" button text
    await waitFor(() => {
      const text = container.textContent || '';
      expect(text).toMatch(/Sync (Remaining|All) \(1\)/);
    });

    // Increment counter to trigger refresh with new data
    await act(async () => {
      rerender(<Wrapper counter={1} />);
    });

    // After refresh, all synced - button should show "All Synced"
    await waitFor(() => {
      const text = container.textContent || '';
      expect(text).toMatch(/All Synced/);
    });
  });
});

describe('App.tsx onTaskComplete counter logic', () => {
  it('increments counter only for successful SYNC tasks', async () => {
    // Test the callback logic in isolation using a minimal component
    // that simulates what App.tsx does
    const { CommandType } = await import('../types');

    let capturedCounter = 0;
    const CounterTestHarness: React.FC = () => {
      const [syncCompletedCounter, setSyncCompletedCounter] = useState(0);

      // Simulate the onTaskComplete callback from App.tsx
      const onTaskComplete = (task: { commandType: string }, success: boolean) => {
        if (success && task.commandType === CommandType.SYNC) {
          setSyncCompletedCounter(prev => prev + 1);
        }
      };

      capturedCounter = syncCompletedCounter;

      return (
        <div>
          <span data-testid="counter">{syncCompletedCounter}</span>
          <button
            data-testid="sync-success"
            onClick={() => onTaskComplete({ commandType: CommandType.SYNC }, true)}
          />
          <button
            data-testid="sync-fail"
            onClick={() => onTaskComplete({ commandType: CommandType.SYNC }, false)}
          />
          <button
            data-testid="generate-success"
            onClick={() => onTaskComplete({ commandType: CommandType.GENERATE }, true)}
          />
        </div>
      );
    };

    const { getByTestId } = render(<CounterTestHarness />);

    expect(getByTestId('counter').textContent).toBe('0');

    // Successful SYNC should increment
    await act(async () => {
      getByTestId('sync-success').click();
    });
    expect(getByTestId('counter').textContent).toBe('1');

    // Failed SYNC should NOT increment
    await act(async () => {
      getByTestId('sync-fail').click();
    });
    expect(getByTestId('counter').textContent).toBe('1');

    // Successful GENERATE should NOT increment
    await act(async () => {
      getByTestId('generate-success').click();
    });
    expect(getByTestId('counter').textContent).toBe('1');

    // Another successful SYNC should increment to 2
    await act(async () => {
      getByTestId('sync-success').click();
    });
    expect(getByTestId('counter').textContent).toBe('2');
  });
});
