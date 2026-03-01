import { render, act, waitFor } from '@testing-library/react';
import { vi, describe, it, expect, beforeEach } from 'vitest';
import React from 'react';
import ArchitectureView from '../components/ArchitectureView';

// Track the rearrangeVersion prop that DependencyViewer receives each render
let capturedRearrangeVersion: number | undefined;

vi.mock('../components/DependencyViewer', () => ({
  default: (props: any) => {
    capturedRearrangeVersion = props.rearrangeVersion;
    return <div data-testid="dependency-viewer" />;
  },
}));

vi.mock('../components/GraphToolbar', () => ({
  default: ({ onRearrange }: any) => (
    <button data-testid="rearrange-btn" onClick={onRearrange}>
      Re-arrange
    </button>
  ),
}));

vi.mock('../components/FileBrowser', () => ({ default: () => null }));
vi.mock('../components/GenerationProgressModal', () => ({ default: () => null }));
vi.mock('../components/PromptOrderModal', () => ({ default: () => null }));
vi.mock('../components/ModuleEditModal', () => ({ default: () => null }));
vi.mock('../components/AddModuleModal', () => ({ default: () => null }));
vi.mock('../components/SyncFromPromptModal', () => ({ default: () => null }));
vi.mock('../components/SyncOptionsModal', () => ({ default: () => null }));
vi.mock('../components/BatchFilterDropdown', () => ({ default: () => null }));

vi.mock('../api', () => ({
  api: {
    listPrompts: vi.fn(),
    checkArchitectureExists: vi.fn(),
    getArchitecture: vi.fn(),
    rearrangeGraphLayout: vi.fn(),
    getStatus: vi.fn(),
    getFileContent: vi.fn(),
    listRemoteSessions: vi.fn(),
    submitRemoteCommand: vi.fn(),
    spawnTerminal: vi.fn(),
  },
  PromptInfo: {},
}));

import { api } from '../api';

const defaultModule = {
  filename: 'foo_Python.prompt',
  reason: 'Core module',
  description: 'The main module',
  dependencies: [] as string[],
  priority: 1,
  filepath: 'src/foo.py',
  tags: [] as string[],
};

const defaultProps = {
  serverConnected: true,
  isExecuting: false,
  onOpenPromptSpace: vi.fn(),
  executionMode: 'local' as const,
  selectedRemoteSession: null,
};

describe('Re-arrange positions', () => {
  beforeEach(() => {
    capturedRearrangeVersion = undefined;
    vi.clearAllMocks();

    // Set window width to desktop to avoid mobile fallback (which hides DependencyViewer)
    Object.defineProperty(window, 'innerWidth', {
      value: 1200,
      configurable: true,
      writable: true,
    });

    vi.mocked(api.listPrompts).mockResolvedValue([]);
    vi.mocked(api.checkArchitectureExists).mockResolvedValue({ exists: true, path: 'architecture.json' });
    vi.mocked(api.getArchitecture).mockResolvedValue([defaultModule]);
    vi.mocked(api.rearrangeGraphLayout).mockResolvedValue({
      success: true,
      modules: [{ ...defaultModule, position: { x: 700, y: 500 } }],
    });
    vi.mocked(api.listRemoteSessions).mockResolvedValue([]);
  });

  it('increments rearrangeVersion on DependencyViewer after successful rearrange', async () => {
    const { getByTestId } = render(<ArchitectureView {...defaultProps} />);

    // Wait for architecture to load — DependencyViewer renders and receives rearrangeVersion
    await waitFor(() => {
      expect(capturedRearrangeVersion).toBeDefined();
    });
    const versionBefore = capturedRearrangeVersion!;

    // Trigger rearrange
    await act(async () => {
      getByTestId('rearrange-btn').click();
    });

    // rearrangeVersion should have incremented
    await waitFor(() => {
      expect(capturedRearrangeVersion).toBeGreaterThan(versionBefore);
    });
  });
});
