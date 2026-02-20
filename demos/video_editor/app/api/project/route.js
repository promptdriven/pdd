import { NextResponse } from 'next/server';
const { loadProjectConfig, saveProjectConfig } = require('@/lib/config');

export async function GET() {
  return NextResponse.json(loadProjectConfig());
}

export async function PUT(request) {
  const body = await request.json();
  const current = loadProjectConfig();
  const updated = { ...current, ...body };
  saveProjectConfig(updated);
  return NextResponse.json(updated);
}
