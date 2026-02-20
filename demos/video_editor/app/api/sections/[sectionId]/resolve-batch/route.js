import { NextResponse } from 'next/server';
const { readAnnotations, safeWriteAnnotations } = require('@/lib/annotations');
const { getSection } = require('@/lib/config');
const { createJob, emitJobUpdate, closeJobSubscribers, enqueueForSection } = require('@/lib/jobs');
const { buildFixPrompt, runClaude } = require('@/lib/claude');
const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const { PROJECT_ROOT, OUTPUTS_DIR, SECTIONS_DIR } = require('@/lib/config');

async function fixWithClaude(job, annotation, section) {
  emitJobUpdate(job, { status: 'running', step: 'fixing', progress: 0 });
  const result = await runClaude(
    buildFixPrompt(annotation, section),
    { allowedTools: 'Read,Write,Edit,Glob,Grep' }
  );
  emitJobUpdate(job, { step: 'fixing', progress: 100 });
  return result;
}

function renderSection(job, section) {
  return new Promise((resolve, reject) => {
    emitJobUpdate(job, { step: 'rendering', progress: 0 });
    const remotionDir = path.join(PROJECT_ROOT, '..', 'remotion');
    const outputPath = path.join('..', 'outputs', 'sections', section.videoFile);
    const args = [
      'remotion', 'render', 'src/remotion/index.ts', section.compositionId,
      '--output', outputPath, '--overwrite',
    ];
    const child = spawn('npx', args, {
      stdio: ['pipe', 'pipe', 'pipe'],
      cwd: remotionDir,
    });

    child.stdout.on('data', chunk => {
      job.log.push(chunk.toString());
      const pctMatch = chunk.toString().match(/(\d+)%/);
      if (pctMatch) emitJobUpdate(job, { progress: parseInt(pctMatch[1], 10) });
    });
    child.stderr.on('data', chunk => {
      job.log.push(chunk.toString());
      const pctMatch = chunk.toString().match(/(\d+)%/);
      if (pctMatch) emitJobUpdate(job, { progress: parseInt(pctMatch[1], 10) });
    });
    child.on('error', reject);
    child.on('close', code => {
      if (code !== 0) return reject(new Error(`Remotion render exited with code ${code}`));
      emitJobUpdate(job, { step: 'rendering', progress: 100 });
      resolve();
    });
  });
}

function stitchFullVideo(job) {
  return new Promise((resolve, reject) => {
    emitJobUpdate(job, { step: 'stitching', progress: 0 });
    const concatListPath = path.join(SECTIONS_DIR, 'concat_list.txt');
    if (!fs.existsSync(concatListPath)) {
      return reject(new Error('concat_list.txt not found in outputs/sections/'));
    }
    const args = ['-y', '-f', 'concat', '-safe', '0', '-i', 'concat_list.txt', '-c', 'copy', path.join('..', 'full_video.mp4')];
    const child = spawn('ffmpeg', args, { stdio: ['pipe', 'pipe', 'pipe'], cwd: SECTIONS_DIR });
    child.stdout.on('data', () => {});
    child.stderr.on('data', chunk => { job.log.push(chunk.toString()); });
    child.on('error', reject);
    child.on('close', code => {
      if (code !== 0) return reject(new Error(`ffmpeg stitch exited with code ${code}`));
      emitJobUpdate(job, { step: 'stitching', progress: 100 });
      resolve();
    });
  });
}

async function runBatchResolvePipeline(job, sectionId) {
  try {
    const section = getSection(sectionId);
    if (!section) throw new Error(`Section not found: ${sectionId}`);

    const data = readAnnotations();
    const pending = data.annotations.filter(a =>
      a.video && a.video.sectionId === sectionId &&
      a.analysis && a.analysis.status === 'completed' &&
      !a.resolved
    );

    if (pending.length === 0) throw new Error('No pending analyzed annotations for this section');

    emitJobUpdate(job, { status: 'running', step: 'fixing', progress: 0 });

    // Apply fixes sequentially per annotation
    for (let i = 0; i < pending.length; i++) {
      const ann = pending[i];
      const fixType = (ann.analysis && ann.analysis.fixType) || 'remotion';

      try {
        if (fixType === 'remotion') {
          await fixWithClaude(job, ann, section);
        }
        // veo and tts fixTypes would call their respective pipelines here

        const progress = Math.round(((i + 1) / pending.length) * 50);
        emitJobUpdate(job, { progress });

        await safeWriteAnnotations((d) => {
          const idx = d.annotations.findIndex(a => a.id === ann.id);
          if (idx !== -1) {
            d.annotations[idx].resolveJob = { jobId: job.id, status: 'running', step: 'fixing' };
          }
        });
      } catch (fixErr) {
        // Per-annotation error: mark failed but continue batch
        console.error(`Fix failed for annotation ${ann.id}:`, fixErr.message);
        await safeWriteAnnotations((d) => {
          const idx = d.annotations.findIndex(a => a.id === ann.id);
          if (idx !== -1) {
            d.annotations[idx].resolveJob = { jobId: job.id, status: 'error', error: fixErr.message };
          }
        });
      }
    }

    // Render section once after all fixes
    await renderSection(job, section);

    // Stitch full video
    await stitchFullVideo(job);

    // Mark all pending annotations as resolved
    emitJobUpdate(job, { status: 'done', step: null, progress: 100, completedAt: new Date().toISOString() });

    await safeWriteAnnotations((d) => {
      for (const ann of pending) {
        const idx = d.annotations.findIndex(a => a.id === ann.id);
        if (idx !== -1 && (!d.annotations[idx].resolveJob || d.annotations[idx].resolveJob.status !== 'error')) {
          d.annotations[idx].resolved = true;
          d.annotations[idx].resolveJob = { jobId: job.id, status: 'done' };
        }
      }
    });
  } catch (err) {
    const errMsg = err.message || String(err);
    console.error(`Batch resolve error [job=${job.id}]:`, errMsg);
    emitJobUpdate(job, { status: 'error', error: errMsg, completedAt: new Date().toISOString() });
  } finally {
    closeJobSubscribers(job);
  }
}

export async function POST(request, { params }) {
  const { sectionId } = await params;
  const section = getSection(sectionId);
  if (!section) return NextResponse.json({ error: 'Section not found', code: 'INVALID_SECTION' }, { status: 404 });

  const data = readAnnotations();
  const pending = data.annotations.filter(a =>
    a.video && a.video.sectionId === sectionId &&
    a.analysis && a.analysis.status === 'completed' &&
    !a.resolved
  );

  if (pending.length === 0) {
    return NextResponse.json({ error: 'No pending analyzed annotations for this section', code: 'UPSTREAM_INCOMPLETE' }, { status: 400 });
  }

  const job = createJob({
    sectionId,
    stage: 'resolve-batch',
    annotations: pending.map(a => a.id),
  });

  // Save job reference to annotations
  await safeWriteAnnotations((d) => {
    for (const ann of pending) {
      const idx = d.annotations.findIndex(a => a.id === ann.id);
      if (idx !== -1) {
        d.annotations[idx].resolveJob = { jobId: job.id, status: 'pending' };
      }
    }
  });

  enqueueForSection(sectionId, () => runBatchResolvePipeline(job, sectionId));

  return NextResponse.json({ jobId: job.id }, { status: 202 });
}
