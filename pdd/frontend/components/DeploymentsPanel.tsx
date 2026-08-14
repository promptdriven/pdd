import React, { useCallback, useEffect, useRef, useState } from 'react';
import { api, DeploymentOperation, DeploymentService, DeploymentStatus } from '../api';

/**
 * Local Services panel.
 *
 * Renders nothing unless the optional pdd-k8s plugin is installed, so projects
 * that are plain scripts, CLIs or libraries never see Kubernetes concepts.
 */

const STATE_STYLES: Record<string, string> = {
  running: 'bg-green-500/15 text-green-300',
  failed: 'bg-red-500/15 text-red-300',
  pending: 'bg-amber-500/15 text-amber-300',
  'not deployed': 'bg-surface-700/50 text-surface-400',
};

const OPERATION_STYLES: Record<string, string> = {
  running: 'text-cyan-300',
  succeeded: 'text-green-300',
  failed: 'text-red-300',
};

const stateStyle = (state: string) => STATE_STYLES[state] || 'bg-surface-700/50 text-surface-400';

const ServiceCard: React.FC<{
  service: DeploymentService;
  busy: boolean;
  onDeploy: () => void;
  onStop: () => void;
  onLogs: () => void;
}> = ({ service, busy, onDeploy, onStop, onLogs }) => (
  <article className="rounded-xl border border-surface-700/50 bg-surface-900/30 p-4">
    <div className="flex items-center justify-between gap-2">
      <h4 className="text-sm font-semibold text-white truncate">{service.name}</h4>
      <span className={`text-[11px] font-medium px-2 py-0.5 rounded-full ${stateStyle(service.state)}`}>
        {service.state}
      </span>
    </div>

    <p className="mt-2 text-xs text-surface-500">
      Dev Units:{' '}
      {service.dev_units.map((unit) => (
        <span key={unit} className="inline-block mr-1 mb-1 px-1.5 py-0.5 rounded bg-surface-800 text-surface-300">
          {unit}
        </span>
      ))}
    </p>

    <p className="mt-1 text-xs text-surface-500">
      {service.ready_replicas}/{service.desired_replicas} ready · {service.restarts} restarts · port {service.port}
    </p>

    {service.pods.map((pod) => (
      <p key={pod.name} className="mt-1 text-[11px] text-surface-500 truncate" title={pod.name}>
        · {pod.name} — health {pod.health || 'unknown'} on {pod.node}
      </p>
    ))}

    {service.events.length > 0 && (
      <ul className="mt-2 space-y-1">
        {service.events.map((event, index) => (
          <li key={index} className="text-[11px] text-amber-300/90">! {event}</li>
        ))}
      </ul>
    )}

    <div className="mt-3 flex gap-2">
      <button
        onClick={onDeploy}
        disabled={busy}
        className="px-2.5 py-1.5 rounded-lg bg-surface-800 border border-surface-600 text-[11px] font-medium text-surface-200 hover:bg-surface-700 disabled:opacity-50 transition-colors"
      >
        {service.state === 'not deployed' ? 'Deploy' : 'Redeploy'}
      </button>
      <button
        onClick={onStop}
        disabled={busy || service.state === 'not deployed'}
        className="px-2.5 py-1.5 rounded-lg bg-surface-800 border border-surface-600 text-[11px] font-medium text-surface-200 hover:bg-surface-700 disabled:opacity-50 transition-colors"
      >
        Stop
      </button>
      <button
        onClick={onLogs}
        disabled={busy}
        className="px-2.5 py-1.5 rounded-lg bg-surface-800 border border-surface-600 text-[11px] font-medium text-surface-200 hover:bg-surface-700 disabled:opacity-50 transition-colors"
      >
        Logs
      </button>
    </div>
  </article>
);

const DeploymentsPanel: React.FC = () => {
  const [status, setStatus] = useState<DeploymentStatus | null>(null);
  const [operations, setOperations] = useState<DeploymentOperation[]>([]);
  const [logs, setLogs] = useState<{ service: string; text: string } | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const pollTimer = useRef<number | null>(null);

  const refresh = useCallback(async () => {
    try {
      const next = await api.getDeployments();
      setStatus(next);
      setError(null);
      if (next.plugin_installed) {
        setOperations((await api.getDeploymentOperations()).operations);
      }
    } catch (requestError) {
      setError(requestError instanceof Error ? requestError.message : 'Could not load local deployments.');
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    void refresh();
  }, [refresh]);

  // While an action is in flight, poll so pods and operations settle on their own.
  const busy = operations.some((operation) => operation.state === 'running');
  useEffect(() => {
    if (!busy) return undefined;
    pollTimer.current = window.setInterval(() => void refresh(), 3000);
    return () => {
      if (pollTimer.current !== null) window.clearInterval(pollTimer.current);
    };
  }, [busy, refresh]);

  const act = async (action: () => Promise<DeploymentOperation>) => {
    try {
      const operation = await action();
      setOperations((current) => [operation, ...current]);
    } catch (requestError) {
      setError(requestError instanceof Error ? requestError.message : 'The action could not be started.');
    }
  };

  const showLogs = async (service: string) => {
    try {
      const result = await api.getDeploymentLogs(service);
      setLogs({ service, text: result.message || result.logs || `No logs yet for '${service}'.` });
    } catch (requestError) {
      setError(requestError instanceof Error ? requestError.message : 'Could not read logs.');
    }
  };

  // The panel is opt-in: stay entirely out of the way when unavailable.
  if (loading || !status?.plugin_installed || !status.configured) return null;

  return (
    <section className="glass rounded-2xl border border-surface-700/50 overflow-hidden">
      <div className="px-4 py-3 border-b border-surface-700/50 flex items-center justify-between gap-3">
        <div>
          <h3 className="text-sm font-semibold text-white">Local services</h3>
          <p className="text-[11px] text-surface-500">
            Dev Units mapped to runnable services in {status.manifest_path}
          </p>
        </div>
        <span className="text-xs text-surface-500 shrink-0">
          {status.available ? `${status.cluster} · ${status.namespace}` : 'cluster offline'}
        </span>
      </div>

      {error && <p className="px-4 pt-3 text-xs text-red-300">{error}</p>}
      {!status.available && status.message && (
        <p className="px-4 pt-3 text-sm text-amber-300/90">{status.message}</p>
      )}

      <div className="grid gap-3 p-4 sm:grid-cols-2 xl:grid-cols-3">
        {status.services.map((service) => (
          <ServiceCard
            key={service.name}
            service={service}
            busy={busy}
            onDeploy={() => void act(() => api.deployService(service.name))}
            onStop={() => void act(() => api.stopService(service.name))}
            onLogs={() => void showLogs(service.name)}
          />
        ))}
      </div>

      {operations.length > 0 && (
        <div className="px-4 pb-4">
          <h4 className="text-xs font-semibold text-surface-400 mb-2">Recent actions</h4>
          <ul className="space-y-1">
            {operations.slice(0, 5).map((operation) => (
              <li key={operation.id} className="text-[11px] text-surface-500">
                <span className={OPERATION_STYLES[operation.state] || 'text-surface-400'}>
                  {operation.action} {operation.service} — {operation.state}
                </span>
                {operation.message && <span className="text-red-300/80"> · {operation.message}</span>}
              </li>
            ))}
          </ul>
        </div>
      )}

      {logs && (
        <div className="border-t border-surface-700/50">
          <div className="px-4 py-2 flex items-center justify-between">
            <h4 className="text-xs font-semibold text-surface-300">Logs · {logs.service}</h4>
            <button onClick={() => setLogs(null)} className="text-[11px] text-surface-500 hover:text-surface-300">
              Close
            </button>
          </div>
          <pre className="m-0 px-4 pb-4 max-h-64 overflow-auto text-[11px] leading-5 text-surface-300 whitespace-pre-wrap">
            {logs.text}
          </pre>
        </div>
      )}
    </section>
  );
};

export default DeploymentsPanel;
