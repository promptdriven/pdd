import React, { useEffect, useRef, useState } from 'react';
import { api, JobResult } from '../api';

interface CommandOutputProps {
  jobId: string | null;
  command: string;
  onClose: () => void;
  onComplete?: (result: JobResult) => void;
}

interface OutputLine {
  type: 'stdout' | 'stderr' | 'info' | 'error' | 'success';
  text: string;
  timestamp: Date;
}

const CommandOutput: React.FC<CommandOutputProps> = ({ jobId, command, onClose, onComplete }) => {
  const [output, setOutput] = useState<OutputLine[]>([]);
  const [status, setStatus] = useState<'running' | 'completed' | 'failed' | 'cancelled'>('running');
  const [cost, setCost] = useState<number>(0);
  const [duration, setDuration] = useState<number>(0);
  const outputRef = useRef<HTMLDivElement>(null);
  const wsRef = useRef<WebSocket | null>(null);
  const startTime = useRef<Date>(new Date());

  // Auto-scroll to bottom
  useEffect(() => {
    if (outputRef.current) {
      outputRef.current.scrollTop = outputRef.current.scrollHeight;
    }
  }, [output]);

  // Update duration timer
  useEffect(() => {
    if (status === 'running') {
      const interval = setInterval(() => {
        setDuration((new Date().getTime() - startTime.current.getTime()) / 1000);
      }, 100);
      return () => clearInterval(interval);
    }
  }, [status]);

  // Connect to WebSocket for job streaming
  useEffect(() => {
    if (!jobId) return;

    const addLine = (type: OutputLine['type'], text: string) => {
      setOutput(prev => [...prev, { type, text, timestamp: new Date() }]);
    };

    addLine('info', `Starting command: ${command}`);
    addLine('info', `Job ID: ${jobId}`);
    addLine('info', '---');

    const ws = api.connectToJobStream(jobId, {
      onStdout: (text) => addLine('stdout', text),
      onStderr: (text) => addLine('stderr', text),
      onProgress: (current, total, message) => {
        addLine('info', `Progress: ${current}/${total} - ${message}`);
      },
      onComplete: (success, result, jobCost) => {
        setStatus(success ? 'completed' : 'failed');
        setCost(jobCost);
        addLine('info', '---');
        addLine(success ? 'success' : 'error', success ? 'Command completed successfully!' : 'Command failed.');
        if (jobCost > 0) {
          addLine('info', `Cost: $${jobCost.toFixed(4)}`);
        }

        // Fetch final result
        api.getJobStatus(jobId).then(onComplete);
      },
      onError: (error) => {
        addLine('error', `WebSocket error: ${error.message}`);
      },
      onClose: () => {
        if (status === 'running') {
          // Connection closed unexpectedly, poll for status
          api.getJobStatus(jobId).then(result => {
            setStatus(result.status as any);
            if (result.error) {
              addLine('error', result.error);
            }
            onComplete?.(result);
          }).catch(e => {
            addLine('error', `Failed to get job status: ${e.message}`);
          });
        }
      },
    });

    wsRef.current = ws;

    return () => {
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, [jobId, command, onComplete]);

  const handleCancel = async () => {
    if (jobId && status === 'running') {
      try {
        if (wsRef.current) {
          api.sendCancelRequest(wsRef.current);
        }
        await api.cancelJob(jobId);
        setStatus('cancelled');
        setOutput(prev => [...prev, { type: 'info', text: 'Job cancelled.', timestamp: new Date() }]);
      } catch (e: any) {
        setOutput(prev => [...prev, { type: 'error', text: `Failed to cancel: ${e.message}`, timestamp: new Date() }]);
      }
    }
  };

  const getStatusColor = () => {
    switch (status) {
      case 'running': return 'text-blue-400';
      case 'completed': return 'text-green-400';
      case 'failed': return 'text-red-400';
      case 'cancelled': return 'text-yellow-400';
    }
  };

  const getStatusIcon = () => {
    switch (status) {
      case 'running': return (
        <svg className="animate-spin h-5 w-5" xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24">
          <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4"></circle>
          <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"></path>
        </svg>
      );
      case 'completed': return <span>&#10003;</span>;
      case 'failed': return <span>&#10007;</span>;
      case 'cancelled': return <span>&#9888;</span>;
    }
  };

  return (
    <div className="fixed inset-0 bg-black bg-opacity-75 flex items-center justify-center z-50 p-4">
      <div className="bg-slate-900 rounded-lg shadow-2xl w-full max-w-4xl max-h-[80vh] flex flex-col border border-slate-700">
        {/* Header */}
        <div className="flex items-center justify-between px-4 py-3 border-b border-slate-700">
          <div className="flex items-center space-x-3">
            <span className={`${getStatusColor()}`}>{getStatusIcon()}</span>
            <span className="text-white font-mono text-sm truncate max-w-md">{command}</span>
          </div>
          <div className="flex items-center space-x-4">
            <span className="text-slate-400 text-sm">{duration.toFixed(1)}s</span>
            {cost > 0 && <span className="text-green-400 text-sm">${cost.toFixed(4)}</span>}
            {status === 'running' && (
              <button
                onClick={handleCancel}
                className="px-3 py-1 bg-red-600 hover:bg-red-700 text-white text-sm rounded transition-colors"
              >
                Cancel
              </button>
            )}
            <button
              onClick={onClose}
              className="text-slate-400 hover:text-white transition-colors"
            >
              <svg className="w-5 h-5" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>
        </div>

        {/* Output */}
        <div
          ref={outputRef}
          className="flex-1 overflow-y-auto p-4 font-mono text-sm bg-black"
        >
          {output.map((line, i) => (
            <div
              key={i}
              className={`whitespace-pre-wrap break-all ${
                line.type === 'stderr' ? 'text-red-400' :
                line.type === 'error' ? 'text-red-500 font-bold' :
                line.type === 'success' ? 'text-green-400 font-bold' :
                line.type === 'info' ? 'text-slate-500' :
                'text-slate-200'
              }`}
            >
              {line.text}
            </div>
          ))}
          {status === 'running' && (
            <div className="text-slate-500 animate-pulse">&#9608;</div>
          )}
        </div>

        {/* Footer */}
        <div className="px-4 py-2 border-t border-slate-700 text-xs text-slate-500">
          Job: {jobId} | Status: <span className={getStatusColor()}>{status}</span>
        </div>
      </div>
    </div>
  );
};

export default CommandOutput;
