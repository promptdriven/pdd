import { NextResponse } from 'next/server';
const { getJob, createJob, enqueueForSection, emitJobUpdate } = require('@/lib/jobs');

export async function POST(request, { params }) {
  const { id } = await params;
  const oldJob = getJob(id);
  if (!oldJob) return NextResponse.json({ error: 'Job not found', code: 'JOB_NOT_FOUND' }, { status: 404 });

  if (oldJob.status !== 'error') {
    return NextResponse.json({ error: 'Only failed jobs can be retried', code: 'JOB_ALREADY_RUNNING' }, { status: 400 });
  }

  // Create a new job with the same parameters
  const newJob = createJob({
    annotationId: oldJob.annotationId,
    sectionId: oldJob.sectionId,
    stage: oldJob.stage,
    annotations: oldJob.annotations,
  });

  // The actual pipeline execution would be enqueued here
  // For now, mark as pending — the batch resolve endpoint handles the actual execution
  emitJobUpdate(newJob, { status: 'pending' });

  return NextResponse.json({ jobId: newJob.id }, { status: 202 });
}
