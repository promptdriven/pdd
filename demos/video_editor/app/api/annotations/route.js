import { NextResponse } from 'next/server';
const { readAnnotations, createAnnotation } = require('@/lib/annotations');

export async function GET() {
  return NextResponse.json(readAnnotations());
}

export async function POST(request) {
  const body = await request.json();
  const annotation = createAnnotation(body);
  return NextResponse.json(annotation, { status: 201 });
}
