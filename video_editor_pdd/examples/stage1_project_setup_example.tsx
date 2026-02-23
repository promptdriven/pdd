'use client';

import React, { useState } from 'react';
import Stage1ProjectSetup from '../components/stages/Stage1ProjectSetup';
import type { ProjectConfig } from '../lib/types';

// =============================================================================
// Example 1: Minimal integration in a Next.js page
// =============================================================================

/**
 * A sample project configuration that mirrors the on-disk project.json structure.
 * This is the initial state passed to the Stage1ProjectSetup component.
 */
const INITIAL_CONFIG: ProjectConfig = {
  name: 'Product Launch Video',
  outputResolution: '1920x1080',
  tts: {
    voice: 'en-US-Neural2-F',
    rate: 1.0,
    model: 'google-tts-v2',
  },
  sections: [
    {
      id: 'intro',
      label: 'Introduction',
      videoFile: 'output/sections/intro.mp4',
      specDir: 'specs/intro',
      remotionDir: 'remotion/intro',
      compositionId: 'IntroComposition',
      durationSeconds: 12.5,
      offsetSeconds: 0,
    },
    {
      id: 'main',
      label: 'Main Content',
      videoFile: 'output/sections/main.mp4',
      specDir: 'specs/main',
      remotionDir: 'remotion/main',
      compositionId: 'MainComposition',
      durationSeconds: 45.0,
      offsetSeconds: 12.5,
    },
    {
      id: 'outro',
      label: 'Outro',
      videoFile: 'output/sections/outro.mp4',
      specDir: 'specs/outro',
      remotionDir: 'remotion/outro',
      compositionId: 'OutroComposition',
      durationSeconds: 8.0,
      offsetSeconds: 57.5,
    },
  ],
  audioSync: {
    sectionGroups: {
      narration: ['intro', 'main', 'outro'],
      music: ['intro', 'outro'],
    },
  },
  veo: {
    model: 'veo-2.0-generate-001',
    aspectRatio: '16:9',
    referenceImages: {
      logo: 'assets/logo.png',
    },
  },
  render: {
    maxParallelRenders: 3,
    outputDir: 'output/final',
    fps: 30,
    width: 1920,
    height: 1080,
  },
};

/**
 * ProjectSetupPage demonstrates the standard usage pattern:
 *
 * 1. Hold the "source of truth" config in parent state.
 * 2. Pass it to Stage1ProjectSetup as `config`.
 * 3. Provide an `onSave` callback that updates the parent state
 *    with the server-confirmed config after a successful save.
 *
 * The component internally:
 *   - Clones `config` into local state for editing.
 *   - Detects unsaved changes via JSON comparison.
 *   - PUTs to /api/project on save and calls onSave with the response.
 */
export default function ProjectSetupPage() {
  const [projectConfig, setProjectConfig] =
    useState<ProjectConfig>(INITIAL_CONFIG);

  /**
   * onSave callback — receives the updated ProjectConfig from the server
   * after a successful PUT /api/project.
   *
   * @param savedConfig - The ProjectConfig returned by the API (may include
   *   server-side modifications such as computed offsets or normalized fields).
   */
  const handleSave = (savedConfig: ProjectConfig) => {
    setProjectConfig(savedConfig);
    console.log('Project saved successfully:', savedConfig.name);
    console.log(`  Sections: ${savedConfig.sections.length}`);
    console.log(`  Resolution: ${savedConfig.outputResolution}`);
    console.log(`  TTS voice: ${savedConfig.tts.voice}, rate: ${savedConfig.tts.rate}`);
    console.log(`  Veo model: ${savedConfig.veo.model}, aspect: ${savedConfig.veo.aspectRatio}`);
    console.log(`  Max parallel renders: ${savedConfig.render.maxParallelRenders}`);
  };

  return (
    <div className="min-h-screen bg-gray-50">
      <Stage1ProjectSetup config={projectConfig} onSave={handleSave} />
    </div>
  );
}

// =============================================================================
// Example 2: Empty project (no sections) — shows the "No sections yet" state
// =============================================================================

const EMPTY_CONFIG: ProjectConfig = {
  name: '',
  outputResolution: '1280x720',
  tts: {
    voice: '',
    rate: 1.0,
    model: '',
  },
  sections: [],
  audioSync: {
    sectionGroups: {},
  },
  veo: {
    model: 'veo-2.0-generate-001',
    aspectRatio: '16:9',
    referenceImages: {},
  },
  render: {
    maxParallelRenders: 1,
    outputDir: 'output',
    fps: 30,
    width: 1280,
    height: 720,
  },
};

/**
 * NewProjectPage shows Stage1ProjectSetup initialized with an empty config.
 * The Section Registry table will display "No sections yet" until the user
 * clicks "+ Add Section".
 */
export function NewProjectPage() {
  const [config, setConfig] = useState<ProjectConfig>(EMPTY_CONFIG);

  return (
    <div className="min-h-screen bg-white">
      <Stage1ProjectSetup
        config={config}
        onSave={(saved) => {
          setConfig(saved);
          // Navigate to next stage, update global state, etc.
        }}
      />
    </div>
  );
}

// =============================================================================
// Example 3: Using within a multi-stage pipeline stepper
// =============================================================================

/**
 * Demonstrates embedding Stage1ProjectSetup inside a larger pipeline UI
 * where the active stage is controlled by a parent component.
 *
 * The parent conditionally renders Stage1ProjectSetup only when
 * the current pipeline stage is 'setup'.
 */
export function PipelineEditor() {
  const [activeStage, setActiveStage] = useState<string>('setup');
  const [projectConfig, setProjectConfig] =
    useState<ProjectConfig>(INITIAL_CONFIG);

  const handleProjectSave = (saved: ProjectConfig) => {
    setProjectConfig(saved);
    // Optionally auto-advance to the next stage after saving:
    // setActiveStage('script');
  };

  return (
    <div>
      {/* Stage navigation tabs */}
      <nav className="flex gap-2 p-4 border-b">
        {['setup', 'script', 'tts-render', 'render', 'audit'].map((stage) => (
          <button
            key={stage}
            onClick={() => setActiveStage(stage)}
            className={`px-3 py-1 rounded ${
              activeStage === stage
                ? 'bg-blue-600 text-white'
                : 'bg-gray-200 text-gray-700'
            }`}
          >
            {stage}
          </button>
        ))}
      </nav>

      {/* Conditionally render Stage1ProjectSetup */}
      {activeStage === 'setup' && (
        <Stage1ProjectSetup
          config={projectConfig}
          onSave={handleProjectSave}
        />
      )}

      {activeStage !== 'setup' && (
        <div className="p-6 text-gray-500">
          Stage "{activeStage}" panel would render here.
        </div>
      )}
    </div>
  );
}