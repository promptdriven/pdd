import { NextResponse } from 'next/server';
const { getAnnotation, safeWriteAnnotations } = require('@/lib/annotations');
const { buildAnalysisPrompt, runClaude } = require('@/lib/claude');
const { getSections } = require('@/lib/config');

export async function POST(request, { params }) {
  const { id } = await params;
  const ann = getAnnotation(id);
  if (!ann) return NextResponse.json({ error: 'Not found' }, { status: 404 });

  const text = ann.text && ann.text.content;
  if (!text) return NextResponse.json({ error: 'No annotation text' }, { status: 400 });

  try {
    const sections = getSections();
    const prompt = buildAnalysisPrompt(
      text,
      ann.video && ann.video.sectionId,
      ann.video && ann.video.timestampFormatted,
      { annotation: ann, sections }
    );
    const result = await runClaude(prompt);

    const freshData = await safeWriteAnnotations((d) => {
      const idx = d.annotations.findIndex(a => a.id === id);
      if (idx !== -1) d.annotations[idx].analysis = { ...result, status: 'completed' };
    });
    const updated = freshData.annotations.find(a => a.id === id);
    return NextResponse.json(updated || { error: 'Not found after write' });
  } catch (err) {
    console.error('Annotation analysis error:', err.message);
    return NextResponse.json({ error: err.message }, { status: 500 });
  }
}
