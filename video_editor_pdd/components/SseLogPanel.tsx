'use client';

import React, { useEffect, useRef, useState } from 'react';
import type { Job } from '../lib/types';

interface SseLogPanelProps {
  jobId: string | null;
  onDone?: () => void;
  onError?: (msg: string) => void;
  className?: string;
}

const formatTimestamp = () =>
  new Date().toLocaleTimeString('en-US', { hour12: false });

export const SseLogPanel: React.FC<SseLogPanelProps> = ({
  jobId,
  onDone,
  onError,
  className,
}) => {
  const [logs, setLogs] = useState<string[]>([]);
  const [completed, setCompleted] = useState(false);
  const [errorMsg, setErrorMsg] = useState<string | null>(null);

  const logRef = useRef<HTMLDivElement | null>(null);
  const eventSourceRef = useRef<EventSource | null>(null);
  const pollingRef = useRef<NodeJS.Timeout | null>(null);
  const doneCalledRef = useRef(false);
  const errorCalledRef = useRef(false);

  const appendLog = (message: string) => {
    const ts = formatTimestamp();
    setLogs((prev) => [...prev, `[${ts}] ${message}`]);
  };

  const handleDone = () => {
    if (!doneCalledRef.current) {
      doneCalledRef.current = true;
      setCompleted(true);
      setErrorMsg(null);
      onDone?.();
    }
  };

  const handleError = (msg: string) => {
    if (!errorCalledRef.current) {
      errorCalledRef.current = true;
      setErrorMsg(msg);
      setCompleted(false);
      onError?.(msg);
    }
  };

  const stopPolling = () => {
    if (pollingRef.current) {
      clearInterval(pollingRef.current);
      pollingRef.current = null;
    }
  };

  const startPolling = (id: string) => {
    if (pollingRef.current) return;

    pollingRef.current = setInterval(async () => {
      try {
        const res = await fetch(`/api/jobs/${id}`);
        if (!res.ok) return;

        const job: Job = await res.json();

        if (job.status === 'done') {
          appendLog('Job finished successfully.');
          handleDone();
          stopPolling();
        }

        if (job.status === 'error') {
          const msg = job.error ?? 'Unknown error';
          appendLog(`Error: ${msg}`);
          handleError(msg);
          stopPolling();
        }
      } catch (err) {
        // Polling failure should not crash UI
      }
    }, 2000);
  };

  useEffect(() => {
    if (!jobId) return;

    // reset on new job
    setLogs([]);
    setCompleted(false);
    setErrorMsg(null);
    doneCalledRef.current = false;
    errorCalledRef.current = false;

    stopPolling();
    eventSourceRef.current?.close();
    eventSourceRef.current = null;

    // EventSource not supported → fallback
    if (typeof EventSource === 'undefined') {
      startPolling(jobId);
      return;
    }

    try {
      const es = new EventSource(`/api/jobs/${jobId}/stream`);
      eventSourceRef.current = es;

      es.onmessage = (event: MessageEvent) => {
        try {
          const data = JSON.parse(event.data);
          if (data?.message) appendLog(data.message);
        } catch {
          appendLog(event.data);
        }
      };

      es.addEventListener('done', () => {
        appendLog('Job completed.');
        handleDone();
      });

      es.addEventListener('error', (evt: Event) => {
        // This can be a server-sent custom error event or a connection error
        if ((evt as MessageEvent).data) {
          try {
            const data = JSON.parse((evt as MessageEvent).data);
            const msg = data?.message ?? 'Unknown error';
            appendLog(`Error: ${msg}`);
            handleError(msg);
          } catch {
            const msg = (evt as MessageEvent).data || 'Unknown error';
            appendLog(`Error: ${msg}`);
            handleError(msg);
          }
        } else {
          // Connection error → fallback polling
          es.close();
          startPolling(jobId);
        }
      });

      es.onerror = () => {
        es.close();
        startPolling(jobId);
      };
    } catch {
      startPolling(jobId);
    }

    return () => {
      eventSourceRef.current?.close();
      eventSourceRef.current = null;
      stopPolling();
    };
  }, [jobId]);

  useEffect(() => {
    if (!logRef.current) return;
    logRef.current.scrollTo({
      top: logRef.current.scrollHeight,
      behavior: 'smooth',
    });
  }, [logs]);

  if (!jobId) return null;

  return (
    <div className={className}>
      <div
        ref={logRef}
        className="overflow-y-auto max-h-64 font-mono text-xs bg-black/20 p-2 rounded"
        style={{ contain: 'strict' }}
      >
        {logs.length === 0 ? (
          <div className="text-slate-400">Waiting for logs…</div>
        ) : (
          logs.map((line, idx) => (
            <div key={idx} className="whitespace-pre-wrap">
              {line}
            </div>
          ))
        )}
      </div>

      {completed && (
        <div className="mt-2 text-green-400 font-mono text-sm">✓ Completed</div>
      )}
      {errorMsg && (
        <div className="mt-2 text-red-400 font-mono text-sm">
          ✕ Error: {errorMsg}
        </div>
      )}
    </div>
  );
};

export default SseLogPanel;