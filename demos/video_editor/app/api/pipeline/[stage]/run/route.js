import { NextResponse } from 'next/server';
const { spawn } = require('child_process');
const path = require('path');
const { createJob, emitJobUpdate, setPipelineStageStatus } = require('@/lib/jobs');

const VALID_STAGES = [
  'project-setup', 'script-editor',
  'tts-script', 'tts-render', 'audio-sync', 'specs',
  'veo', 'compositions', 'asset-staging', 'render', 'stitch', 'audit',
];

// Map pipeline stages to Python scripts
const STAGE_SCRIPTS = {
  'project-setup': 'project_setup.py',
  'script-editor': 'script_editor.py',
  'tts-script':    'generate_tts_script.py',
  'tts-render':    'render_tts.py',
  'audio-sync':    'sync_audio.py',
  'specs':         'generate_specs.py',
  'veo':           'generate_veo.py',
  'compositions':  'generate_compositions.py',
  'asset-staging': 'stage_assets.py',
  'render':        'render_sections.py',
  'stitch':        'stitch_video.py',
  'audit':         'audit.py',
};

function buildArgs(stage, body) {
  const args = [];
  if (body.section && body.section !== 'all') {
    args.push('--section', body.section);
  }
  if (stage === 'audio-sync' && body.parallel) {
    args.push('--parallel');
  }
  if (stage === 'render' && body.parallel) {
    args.push('--parallel', String(body.parallel));
  }
  if (stage === 'veo' && body.dryRun) {
    args.push('--dry-run');
  }
  return args;
}

export async function POST(request, { params }) {
  const { stage } = await params;

  if (!VALID_STAGES.includes(stage)) {
    return NextResponse.json(
      { error: `Invalid pipeline stage: ${stage}`, code: 'INVALID_SECTION' },
      { status: 400 }
    );
  }

  let body = {};
  try {
    body = await request.json();
  } catch { /* empty body is fine for some stages */ }

  const job = createJob({ stage });
  setPipelineStageStatus(stage, 'running');
  emitJobUpdate(job, { status: 'running', step: stage, progress: 0 });

  // Spawn the Python pipeline script
  const scriptName = STAGE_SCRIPTS[stage];
  const pipelineDir = path.join(process.cwd(), 'pipeline');
  const scriptPath = path.join(pipelineDir, scriptName);
  const args = buildArgs(stage, body);

  setImmediate(() => {
    const child = spawn('python3', [scriptPath, ...args], {
      cwd: pipelineDir,
      env: { ...process.env, PYTHONUNBUFFERED: '1' },
    });

    let lastProgress = 0;

    child.stdout.on('data', (data) => {
      const lines = data.toString().split('\n').filter(Boolean);
      for (const line of lines) {
        try {
          const event = JSON.parse(line);
          lastProgress = event.progress ?? lastProgress;

          if (event.status === 'error') {
            emitJobUpdate(job, {
              status: 'error',
              step: event.step || stage,
              progress: lastProgress,
              error: event.message,
              completedAt: new Date().toISOString(),
            });
          } else if (event.status === 'done') {
            emitJobUpdate(job, {
              status: 'done',
              step: event.step || stage,
              progress: 100,
              message: event.message,
              completedAt: new Date().toISOString(),
            });
          } else {
            emitJobUpdate(job, {
              step: event.step || stage,
              progress: lastProgress,
              message: event.message,
            });
          }
        } catch {
          // Non-JSON line — treat as log message
          emitJobUpdate(job, {
            step: stage,
            progress: lastProgress,
            message: line,
          });
        }
      }
    });

    child.stderr.on('data', (data) => {
      emitJobUpdate(job, {
        step: stage,
        progress: lastProgress,
        message: `[stderr] ${data.toString().trim()}`,
      });
    });

    child.on('close', (code) => {
      if (code === 0) {
        if (job.status !== 'done') {
          emitJobUpdate(job, {
            status: 'done',
            progress: 100,
            completedAt: new Date().toISOString(),
          });
        }
        setPipelineStageStatus(stage, 'done');
      } else {
        if (job.status !== 'error') {
          emitJobUpdate(job, {
            status: 'error',
            error: `Process exited with code ${code}`,
            completedAt: new Date().toISOString(),
          });
        }
        setPipelineStageStatus(stage, 'error');
      }
    });

    child.on('error', (err) => {
      emitJobUpdate(job, {
        status: 'error',
        error: err.message,
        completedAt: new Date().toISOString(),
      });
      setPipelineStageStatus(stage, 'error');
    });
  });

  return NextResponse.json({ jobId: job.id }, { status: 202 });
}
