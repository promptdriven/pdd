import { NextResponse } from 'next/server';
const { getPipelineStatus } = require('@/lib/jobs');

export async function GET() {
  return NextResponse.json({ stages: getPipelineStatus() });
}
