'use client';

import React, { useEffect, useState } from 'react';
import type { ProjectConfig, Section } from '../../lib/types';

interface Stage1ProjectSetupProps {
  config?: ProjectConfig;
  onSave?: (config: ProjectConfig) => void;
  projectConfig?: ProjectConfig | null;
  onAdvance?: () => void;
}

const DEFAULT_CONFIG: ProjectConfig = {
  name: '',
  outputResolution: { width: 1920, height: 1080 },
  tts: { engine: 'qwen3-tts', modelPath: '', tokenizerPath: '', speaker: 'Aiden', speakingRate: 0.95, sampleRate: 24000 },
  sections: [],
  audioSync: { sectionGroups: {}, silenceGapDefault: 0.3 },
  veo: { model: 'veo-3.1-generate-preview', defaultAspectRatio: '16:9', maxConcurrentGenerations: 4, references: [], frameChains: [] },
  render: { maxParallelRenders: 3, useLambda: false, lambdaRegion: 'us-east-1' },
};

const OUTPUT_RESOLUTIONS = [
  { label: '1920×1080', value: '1920x1080' },
  { label: '1280×720', value: '1280x720' },
];

const VEO_ASPECT_RATIOS = [
  { label: '16:9', value: '16:9' },
  { label: '9:16', value: '9:16' },
];

export default function Stage1ProjectSetup({
  config,
  onSave,
  projectConfig,
  onAdvance,
}: Stage1ProjectSetupProps) {
  const resolvedConfig = projectConfig ?? config ?? null;
  const [localConfig, setLocalConfig] = useState<ProjectConfig>(resolvedConfig ?? DEFAULT_CONFIG);
  const [hasChanges, setHasChanges] = useState(false);
  const [toast, setToast] = useState<string | null>(null);
  const [editingSectionId, setEditingSectionId] = useState<string | null>(null);
  const [draftSection, setDraftSection] = useState<Section | null>(null);
  const [dragIndex, setDragIndex] = useState<number | null>(null);

  useEffect(() => {
    if (resolvedConfig) setLocalConfig(resolvedConfig);
  }, [resolvedConfig]);

  useEffect(() => {
    const changed = JSON.stringify(localConfig) !== JSON.stringify(resolvedConfig ?? DEFAULT_CONFIG);
    setHasChanges(changed);
  }, [localConfig, resolvedConfig]);

  useEffect(() => {
    if (!hasChanges) return;
    const handler = (e: BeforeUnloadEvent) => {
      e.preventDefault();
      e.returnValue = '';
    };
    window.addEventListener('beforeunload', handler);
    return () => window.removeEventListener('beforeunload', handler);
  }, [hasChanges]);

  useEffect(() => {
    if (!toast) return;
    const timer = setTimeout(() => setToast(null), 3000);
    return () => clearTimeout(timer);
  }, [toast]);

  const updateConfig = <K extends keyof ProjectConfig>(
    key: K,
    value: ProjectConfig[K]
  ) => {
    setLocalConfig((prev) => ({ ...prev, [key]: value }));
  };

  const updateNested = <
    K extends keyof ProjectConfig,
    NK extends keyof ProjectConfig[K]
  >(
    key: K,
    nestedKey: NK,
    value: ProjectConfig[K][NK]
  ) => {
    setLocalConfig((prev) => ({
      ...prev,
      [key]: {
        ...(prev[key] as object),
        [nestedKey]: value,
      },
    }));
  };

  const handleAddSection = () => {
    const newSection: Section = {
      id: crypto.randomUUID().slice(0, 8),
      label: 'New Section',
      videoFile: '',
      specDir: '',
      remotionDir: '',
      compositionId: '',
      durationSeconds: 0,
      offsetSeconds: 0,
    };
    setLocalConfig((prev) => ({
      ...prev,
      sections: [...prev.sections, newSection],
    }));
  };

  const handleEditSection = (section: Section) => {
    setEditingSectionId(section.id);
    setDraftSection({ ...section });
  };

  const handleCancelEdit = () => {
    setEditingSectionId(null);
    setDraftSection(null);
  };

  const handleConfirmEdit = () => {
    if (!draftSection) return;
    setLocalConfig((prev) => ({
      ...prev,
      sections: prev.sections.map((s) =>
        s.id === draftSection.id ? draftSection : s
      ),
    }));
    setEditingSectionId(null);
    setDraftSection(null);
  };

  const handleDeleteSection = (id: string) => {
    setLocalConfig((prev) => ({
      ...prev,
      sections: prev.sections.filter((s) => s.id !== id),
    }));
  };

  const handleDragStart = (index: number) => {
    setDragIndex(index);
  };

  const handleDrop = (index: number) => {
    if (dragIndex === null || dragIndex === index) return;
    setLocalConfig((prev) => {
      const next = [...prev.sections];
      const [moved] = next.splice(dragIndex, 1);
      next.splice(index, 0, moved);
      return { ...prev, sections: next };
    });
    setDragIndex(null);
  };

  const handleSave = async () => {
    try {
      const res = await fetch('/api/project', {
        method: 'PUT',
        body: JSON.stringify(localConfig),
        headers: { 'Content-Type': 'application/json' },
      });

      if (!res.ok) throw new Error('Failed to save');
      const data = await res.json();
      setLocalConfig(data);
      onSave?.(data);
      setToast('Saved successfully ✓');
    } catch (err) {
      setToast('Error saving project');
    }
  };

  return (
    <div className="w-full p-6 space-y-6">
      {/* Header */}
      <div className="flex items-center justify-between">
        <div className="flex items-center gap-2">
          <h2 className="text-xl font-semibold">Stage 1: Project Setup</h2>
          {hasChanges && (
            <span className="w-2.5 h-2.5 rounded-full bg-yellow-400" />
          )}
        </div>
        <button
          onClick={handleSave}
          className="px-4 py-2 bg-green-600 text-white rounded hover:bg-green-700"
        >
          Save ✓
        </button>
      </div>

      {toast && (
        <div className="bg-slate-800 text-white px-4 py-2 rounded shadow">
          {toast}
        </div>
      )}

      <div className="grid grid-cols-1 lg:grid-cols-2 gap-8">
        {/* Left Column - Form */}
        <div className="space-y-4">
          <div>
            <label className="block text-sm font-medium mb-1">Project Name</label>
            <input
              value={localConfig.name}
              onChange={(e) => updateConfig('name', e.target.value)}
              className="w-full border rounded px-3 py-2"
            />
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">
              Output Resolution
            </label>
            <select
              value={`${localConfig.outputResolution.width}x${localConfig.outputResolution.height}`}
              onChange={(e) => {
                const [w, h] = e.target.value.split('x').map(Number);
                updateConfig('outputResolution', { width: w, height: h });
              }}
              className="w-full border rounded px-3 py-2"
            >
              {OUTPUT_RESOLUTIONS.map((opt) => (
                <option key={opt.value} value={opt.value}>
                  {opt.label}
                </option>
              ))}
            </select>
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">TTS Speaker</label>
            <input
              value={localConfig.tts.speaker}
              onChange={(e) => updateNested('tts', 'speaker', e.target.value)}
              className="w-full border rounded px-3 py-2"
            />
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">TTS Speaking Rate</label>
            <input
              type="number"
              min={0.5}
              max={2}
              step={0.05}
              value={localConfig.tts.speakingRate}
              onChange={(e) =>
                updateNested('tts', 'speakingRate', Number(e.target.value))
              }
              className="w-full border rounded px-3 py-2"
            />
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">TTS Sample Rate</label>
            <input
              type="number"
              min={8000}
              max={48000}
              step={1000}
              value={localConfig.tts.sampleRate}
              onChange={(e) =>
                updateNested('tts', 'sampleRate', Number(e.target.value))
              }
              className="w-full border rounded px-3 py-2"
            />
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">Veo Model</label>
            <input
              value={localConfig.veo.model}
              onChange={(e) => updateNested('veo', 'model', e.target.value)}
              className="w-full border rounded px-3 py-2"
            />
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">
              Veo Aspect Ratio
            </label>
            <select
              value={localConfig.veo.defaultAspectRatio}
              onChange={(e) =>
                updateNested('veo', 'defaultAspectRatio', e.target.value as '16:9' | '9:16')
              }
              className="w-full border rounded px-3 py-2"
            >
              {VEO_ASPECT_RATIOS.map((opt) => (
                <option key={opt.value} value={opt.value}>
                  {opt.label}
                </option>
              ))}
            </select>
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">
              Max Parallel Renders
            </label>
            <input
              type="number"
              min={1}
              max={4}
              value={localConfig.render.maxParallelRenders}
              onChange={(e) =>
                updateNested('render', 'maxParallelRenders', Number(e.target.value))
              }
              className="w-full border rounded px-3 py-2"
            />
          </div>
        </div>

        {/* Right Column - Section Registry */}
        <div className="space-y-3">
          <div className="flex items-center justify-between">
            <h3 className="text-lg font-semibold">Section Registry</h3>
            <button
              onClick={handleAddSection}
              className="text-sm px-3 py-1 bg-blue-600 text-white rounded hover:bg-blue-700"
            >
              + Add Section
            </button>
          </div>

          <div className="overflow-x-auto border rounded">
            <table className="min-w-full text-sm">
              <thead className="bg-slate-800 text-slate-200">
                <tr>
                  <th className="px-2 py-2 text-left">#</th>
                  <th className="px-2 py-2 text-left">Section ID</th>
                  <th className="px-2 py-2 text-left">Label</th>
                  <th className="px-2 py-2 text-left">Composition ID</th>
                  <th className="px-2 py-2 text-center">✎</th>
                  <th className="px-2 py-2 text-center">✕</th>
                </tr>
              </thead>
              <tbody>
                {localConfig.sections.map((section, index) => {
                  const isEditing = editingSectionId === section.id;
                  return (
                    <tr
                      key={section.id}
                      draggable
                      onDragStart={() => handleDragStart(index)}
                      onDragOver={(e) => e.preventDefault()}
                      onDrop={() => handleDrop(index)}
                      className="border-t border-slate-700 hover:bg-slate-700/50"
                    >
                      <td className="px-2 py-2">{index + 1}</td>
                      <td className="px-2 py-2">
                        {isEditing ? (
                          <input
                            value={draftSection?.id ?? ''}
                            onChange={(e) =>
                              setDraftSection((prev) =>
                                prev ? { ...prev, id: e.target.value } : prev
                              )
                            }
                            className="border rounded px-2 py-1 w-full"
                          />
                        ) : (
                          section.id
                        )}
                      </td>
                      <td className="px-2 py-2">
                        {isEditing ? (
                          <input
                            value={draftSection?.label ?? ''}
                            onChange={(e) =>
                              setDraftSection((prev) =>
                                prev ? { ...prev, label: e.target.value } : prev
                              )
                            }
                            className="border rounded px-2 py-1 w-full"
                          />
                        ) : (
                          section.label
                        )}
                      </td>
                      <td className="px-2 py-2">
                        {isEditing ? (
                          <input
                            value={draftSection?.compositionId ?? ''}
                            onChange={(e) =>
                              setDraftSection((prev) =>
                                prev
                                  ? { ...prev, compositionId: e.target.value }
                                  : prev
                              )
                            }
                            className="border rounded px-2 py-1 w-full"
                          />
                        ) : (
                          section.compositionId
                        )}
                      </td>
                      <td className="px-2 py-2 text-center">
                        {isEditing ? (
                          <button
                            onClick={handleConfirmEdit}
                            className="text-green-600"
                          >
                            ✓
                          </button>
                        ) : (
                          <button
                            onClick={() => handleEditSection(section)}
                            className="text-blue-600"
                          >
                            ✎
                          </button>
                        )}
                      </td>
                      <td className="px-2 py-2 text-center">
                        {isEditing ? (
                          <button
                            onClick={handleCancelEdit}
                            className="text-gray-600"
                          >
                            ✕
                          </button>
                        ) : (
                          <button
                            onClick={() => handleDeleteSection(section.id)}
                            className="text-red-600"
                          >
                            ✕
                          </button>
                        )}
                      </td>
                    </tr>
                  );
                })}
                {localConfig.sections.length === 0 && (
                  <tr>
                    <td colSpan={6} className="px-4 py-6 text-center text-gray-400">
                      No sections yet
                    </td>
                  </tr>
                )}
              </tbody>
            </table>
          </div>
          <p className="text-xs text-gray-500">
            Drag rows to reorder sections.
          </p>
        </div>
      </div>
    </div>
  );
}