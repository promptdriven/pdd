import React, { useCallback, useEffect, useMemo, useState } from 'react';
import { api, ObservabilityModule, ObservabilityRunDetail, ObservabilityRunSummary } from '../api';

const formatCost = (cost: number) => `$${cost.toFixed(4)}`;

const ObservabilityDashboard: React.FC = () => {
  const [runs, setRuns] = useState<ObservabilityRunSummary[]>([]);
  const [modules, setModules] = useState<ObservabilityModule[]>([]);
  const [detail, setDetail] = useState<ObservabilityRunDetail | null>(null);
  const [selectedRun, setSelectedRun] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const refresh = useCallback(async () => {
    setLoading(true);
    setError(null);
    try {
      const [nextRuns, nextModules] = await Promise.all([
        api.getObservabilityRuns(),
        api.getObservabilityModules(),
      ]);
      setRuns(nextRuns);
      setModules(nextModules);
    } catch (requestError) {
      setError(requestError instanceof Error ? requestError.message : 'Could not load local observability data.');
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    void refresh();
  }, [refresh]);

  const stats = useMemo(() => {
    const successfulRuns = runs.filter((run) => run.status === 'success').length;
    const modelCounts = new Map<string, number>();
    for (const run of runs) {
      if (run.model !== 'unknown') modelCounts.set(run.model, (modelCounts.get(run.model) || 0) + 1);
    }
    const topModel = [...modelCounts.entries()].sort((left, right) => right[1] - left[1])[0]?.[0] || '—';
    return {
      successRate: runs.length ? `${Math.round((successfulRuns / runs.length) * 100)}%` : '—',
      totalCost: formatCost(runs.reduce((total, run) => total + run.total_cost, 0)),
      topModel,
    };
  }, [runs]);

  const selectRun = async (filename: string) => {
    setSelectedRun(filename);
    setDetail(null);
    try {
      setDetail(await api.getObservabilityRun(filename));
    } catch (requestError) {
      setError(requestError instanceof Error ? requestError.message : 'Could not load this run report.');
    }
  };

  return (
    <div className="max-w-7xl mx-auto animate-fade-in space-y-4">
      <div className="flex items-center justify-between gap-4">
        <p className="text-sm text-surface-400">Read-only local execution history and Dev Unit health.</p>
        <button
          onClick={() => void refresh()}
          className="px-3 py-2 rounded-lg bg-surface-800 border border-surface-600 text-xs font-medium text-surface-200 hover:bg-surface-700 transition-colors"
          disabled={loading}
        >
          {loading ? 'Refreshing…' : 'Refresh'}
        </button>
      </div>

      {error && <div className="rounded-xl border border-red-500/30 bg-red-500/10 px-4 py-3 text-sm text-red-300">{error}</div>}

      <div className="grid grid-cols-2 lg:grid-cols-4 gap-3">
        {[
          ['Success rate', stats.successRate],
          ['Total spend', stats.totalCost],
          ['Recorded runs', String(runs.length)],
          ['Most used model', stats.topModel],
        ].map(([label, value]) => (
          <div key={label} className="glass rounded-xl border border-surface-700/50 p-4 min-w-0">
            <p className="text-xs text-surface-500">{label}</p>
            <p className="mt-1 text-lg font-semibold text-white truncate" title={value}>{value}</p>
          </div>
        ))}
      </div>

      <div className="grid gap-4 lg:grid-cols-2">
        <section className="glass rounded-2xl border border-surface-700/50 overflow-hidden">
          <div className="px-4 py-3 border-b border-surface-700/50 flex justify-between"><h3 className="text-sm font-semibold text-white">Execution runs</h3><span className="text-xs text-surface-500">{runs.length} recorded</span></div>
          <div className="max-h-[28rem] overflow-auto">
            {!loading && runs.length === 0 && <p className="p-5 text-sm text-surface-500">No `.pdd/core_dumps` reports have been recorded for this project.</p>}
            {runs.map((run) => (
              <button
                key={run.filename}
                onClick={() => void selectRun(run.filename)}
                className={`w-full p-4 text-left border-b border-surface-800 hover:bg-surface-800/50 transition-colors ${selectedRun === run.filename ? 'bg-surface-800/70' : ''}`}
              >
                <span className="flex justify-between gap-3"><span className="text-sm text-white truncate">pdd {run.argv.join(' ') || 'run'}</span><span className={`text-[11px] font-medium px-2 py-0.5 rounded-full ${run.status === 'success' ? 'bg-green-500/15 text-green-300' : 'bg-red-500/15 text-red-300'}`}>{run.status}</span></span>
                <span className="block mt-1 text-xs text-surface-500 truncate">{run.timestamp} · {formatCost(run.total_cost)} · {run.model}</span>
              </button>
            ))}
          </div>
        </section>

        <section className="glass rounded-2xl border border-surface-700/50 overflow-hidden">
          <div className="px-4 py-3 border-b border-surface-700/50"><h3 className="text-sm font-semibold text-white">Run detail</h3></div>
          <pre className="m-0 p-4 max-h-[28rem] overflow-auto text-xs leading-5 text-surface-300 whitespace-pre-wrap">{detail ? JSON.stringify(detail, null, 2) : 'Select a run to inspect its safe local report.'}</pre>
        </section>
      </div>

      <section className="glass rounded-2xl border border-surface-700/50 overflow-hidden">
        <div className="px-4 py-3 border-b border-surface-700/50 flex justify-between"><h3 className="text-sm font-semibold text-white">Dev Units</h3><span className="text-xs text-surface-500">{modules.length} discovered</span></div>
        <div className="grid gap-3 p-4 sm:grid-cols-2 xl:grid-cols-3">
          {!loading && modules.length === 0 && <p className="text-sm text-surface-500">No `.pdd/meta` module reports found.</p>}
          {modules.map((module) => (
            <article key={`${module.module_name}-${module.language}`} className="rounded-xl border border-surface-700/50 bg-surface-900/30 p-3">
              <h4 className="text-sm font-medium text-white truncate">{module.module_name}</h4>
              <p className="mt-1 text-xs text-surface-500">{module.language} · {module.run_report?.tests_passed ?? 0} passed / {module.run_report?.tests_failed ?? 0} failed</p>
            </article>
          ))}
        </div>
      </section>
    </div>
  );
};

export default ObservabilityDashboard;
