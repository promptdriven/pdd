'use client';

import React, { useEffect, useState } from 'react';
import type { PipelineStage, StageStatus } from '../lib/types';

type StageStatusEntry = {
  status: StageStatus;
  error?: string | null;
};

const STAGE_CONFIG: Array<{
  stage: PipelineStage;
  label: string;
  number: number;
}> = [
  { stage: 'setup', label: 'Setup', number: 1 },
  { stage: 'script', label: 'Script', number: 2 },
  { stage: 'tts-script', label: 'TTS Script', number: 3 },
  { stage: 'tts-render', label: 'TTS Render', number: 4 },
  { stage: 'audio-sync', label: 'Audio Sync', number: 5 },
  { stage: 'specs', label: 'Spec Gen', number: 6 },
  { stage: 'veo', label: 'Veo Gen', number: 7 },
  { stage: 'compositions', label: 'Compositions', number: 8 },
  { stage: 'render', label: 'Render', number: 9 },
  { stage: 'audit', label: 'Audit', number: 10 },
];

const initStatuses = (): Record<PipelineStage, StageStatusEntry> => {
  const initial = {} as Record<PipelineStage, StageStatusEntry>;
  for (const { stage } of STAGE_CONFIG) {
    initial[stage] = { status: 'not_started', error: null };
  }
  return initial;
};

interface StageSidebarProps {
  activeStage: PipelineStage;
  onStageSelect: (stage: PipelineStage) => void;
}

export default function StageSidebar({
  activeStage,
  onStageSelect,
}: StageSidebarProps) {
  const [stageStatuses, setStageStatuses] = useState<Record<
    PipelineStage,
    StageStatusEntry
  >>(initStatuses);

  useEffect(() => {
    let mounted = true;

    const fetchStatus = async () => {
      try {
        const res = await fetch('/api/pipeline/status');
        if (!res.ok) return;
        const data: Record<PipelineStage, StageStatusEntry> = await res.json();
        if (!mounted) return;
        // Update in place without flicker
        setStageStatuses((prev) => ({
          ...prev,
          ...data,
        }));
      } catch {
        // Swallow errors; retain last known state
      }
    };

    fetchStatus();
    const interval = setInterval(() => fetchStatus(), 5000);
    return () => {
      mounted = false;
      clearInterval(interval);
    };
  }, []);

  const renderBadge = (entry: StageStatusEntry) => {
    const status = entry.status;
    const icon =
      status === 'done'
        ? '●'
        : status === 'running'
        ? '◌'
        : status === 'error'
        ? '✕'
        : '○';

    const className =
      status === 'done'
        ? 'text-stage-done'
        : status === 'running'
        ? 'text-stage-running animate-stage-running'
        : status === 'error'
        ? 'text-stage-error'
        : 'text-stage-not-started';

    return (
      <span
        className={className}
        title={status === 'error' ? entry.error || 'Error' : undefined}
      >
        {icon}
      </span>
    );
  };

  return (
    <aside className="flex flex-col w-48 bg-sidebar border-r border-border h-screen">
      {STAGE_CONFIG.map(({ stage, label, number }) => {
        const isActive = stage === activeStage;
        const entry = stageStatuses[stage];
        return (
          <div
            key={stage}
            onClick={() => onStageSelect(stage)}
            className={`cursor-pointer px-3 py-2 flex items-center gap-2 hover:bg-white/5 transition-colors ${
              isActive ? 'border-l-2 border-blue-400 bg-white/5' : ''
            }`}
            title={entry?.status === 'error' ? entry.error || 'Error' : undefined}
          >
            <span className="text-xs text-muted-foreground w-6">{number}</span>
            <span className="flex-1 text-sm">{label}</span>
            {entry && renderBadge(entry)}
          </div>
        );
      })}
    </aside>
  );
}