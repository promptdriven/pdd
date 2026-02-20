import { NextResponse } from 'next/server';
const { readAnnotations } = require('@/lib/annotations');

export async function GET() {
  const data = readAnnotations();
  return new NextResponse(JSON.stringify(data, null, 2), {
    headers: {
      'Content-Disposition': 'attachment; filename="annotations.json"',
      'Content-Type': 'application/json',
    },
  });
}
