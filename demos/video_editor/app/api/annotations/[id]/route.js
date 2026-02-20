import { NextResponse } from 'next/server';
const { updateAnnotation, deleteAnnotation, getAnnotation } = require('@/lib/annotations');

export async function GET(request, { params }) {
  const { id } = await params;
  const ann = getAnnotation(id);
  if (!ann) return NextResponse.json({ error: 'Not found' }, { status: 404 });
  return NextResponse.json(ann);
}

export async function PUT(request, { params }) {
  const { id } = await params;
  const body = await request.json();
  const updated = updateAnnotation(id, body);
  if (!updated) return NextResponse.json({ error: 'Not found' }, { status: 404 });
  return NextResponse.json(updated);
}

export async function DELETE(request, { params }) {
  const { id } = await params;
  const deleted = deleteAnnotation(id);
  if (!deleted) return NextResponse.json({ error: 'Not found' }, { status: 404 });
  return new NextResponse(null, { status: 204 });
}
