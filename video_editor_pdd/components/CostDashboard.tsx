'use client';

import React, { useCallback, useEffect, useState } from 'react';

interface StageCost {
  stage: string;
  totalCost: number;
  totalInputTokens: number;
  totalOutputTokens: number;
  callCount: number;
}

interface CostData {
  totalCost: number;
  byStage: StageCost[];
}

interface CostDashboardProps {
  className?: string;
}

const formatCost = (cost: number): string => {
  return `$${cost.toFixed(4)}`;
};

const formatTokens = (tokens: number): string => {
  if (tokens >= 1_000_000) return `${(tokens / 1_000_000).toFixed(1)}M`;
  if (tokens >= 1_000) return `${(tokens / 1_000).toFixed(1)}K`;
  return String(tokens);
};

export default function CostDashboard({ className = '' }: CostDashboardProps) {
  const [data, setData] = useState<CostData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const fetchCosts = useCallback(async () => {
    setLoading(true);
    setError(null);
    try {
      const res = await fetch('/api/costs');
      if (!res.ok) throw new Error(`Failed to fetch costs (${res.status})`);
      const json = (await res.json()) as CostData;
      setData(json);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to load cost data');
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    fetchCosts();
  }, [fetchCosts]);

  return (
    <div className={`rounded-lg border border-slate-200 bg-white p-4 shadow-sm ${className}`}>
      <div className="mb-4 flex items-center justify-between">
        <h3 className="text-sm font-semibold text-slate-700">Cost Dashboard</h3>
        <button
          onClick={fetchCosts}
          className="rounded border border-slate-200 px-2 py-1 text-xs text-slate-600 hover:bg-slate-50"
          disabled={loading}
        >
          {loading ? 'Loading...' : 'Refresh'}
        </button>
      </div>

      {error && (
        <p className="rounded bg-red-50 px-3 py-2 text-sm text-red-600">{error}</p>
      )}

      {data && (
        <>
          <div className="mb-4 rounded bg-slate-50 px-4 py-3">
            <div className="text-xs font-medium uppercase tracking-wide text-slate-500">
              Total Cost
            </div>
            <div className="mt-1 text-2xl font-bold text-slate-900">
              {formatCost(data.totalCost)}
            </div>
          </div>

          <div className="overflow-x-auto">
            <table className="min-w-full text-sm">
              <thead className="border-b border-slate-200 text-left text-xs uppercase tracking-wide text-slate-500">
                <tr>
                  <th className="py-2 pr-3">Stage</th>
                  <th className="py-2 pr-3">Cost</th>
                  <th className="py-2 pr-3">Input Tokens</th>
                  <th className="py-2 pr-3">Output Tokens</th>
                  <th className="py-2">Calls</th>
                </tr>
              </thead>
              <tbody className="divide-y divide-slate-100">
                {data.byStage.length === 0 ? (
                  <tr>
                    <td colSpan={5} className="py-4 text-center text-xs text-slate-500">
                      No cost data recorded yet.
                    </td>
                  </tr>
                ) : (
                  data.byStage.map((row) => (
                    <tr key={row.stage}>
                      <td className="py-2 pr-3 font-medium text-slate-700">{row.stage}</td>
                      <td className="py-2 pr-3 text-slate-600">{formatCost(row.totalCost)}</td>
                      <td className="py-2 pr-3 text-slate-600">{formatTokens(row.totalInputTokens)}</td>
                      <td className="py-2 pr-3 text-slate-600">{formatTokens(row.totalOutputTokens)}</td>
                      <td className="py-2 text-slate-600">{row.callCount}</td>
                    </tr>
                  ))
                )}
              </tbody>
            </table>
          </div>
        </>
      )}

      {!data && !error && !loading && (
        <p className="text-sm text-slate-500">No data available.</p>
      )}
    </div>
  );
}
