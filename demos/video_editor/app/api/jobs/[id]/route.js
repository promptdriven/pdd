import { NextResponse } from 'next/server';
const { getJob } = require('@/lib/jobs');

export async function GET(request, { params }) {
  const { id } = await params;
  const job = getJob(id);
  if (!job) return NextResponse.json({ error: 'Job not found', code: 'JOB_NOT_FOUND' }, { status: 404 });

  return NextResponse.json({
    jobId: job.id,
    status: job.status,
    stage: job.stage,
    step: job.step,
    progress: job.progress,
    error: job.error,
    createdAt: job.startedAt,
    updatedAt: job.updatedAt || job.startedAt,
    completedAt: job.completedAt,
  });
}
