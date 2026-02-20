import { NextResponse } from 'next/server';
const { buildAnalysisPrompt, runClaude } = require('@/lib/claude');
const { getSections } = require('@/lib/config');

export async function POST(request) {
  const { text, sectionId, timestamp } = await request.json();
  if (!text) return NextResponse.json({ error: 'Annotation text is required' }, { status: 400 });

  try {
    const sections = getSections();
    const prompt = buildAnalysisPrompt(text, sectionId, timestamp, { sections });
    const result = await runClaude(prompt);
    return NextResponse.json(result);
  } catch (err) {
    console.error('Claude analysis error:', err.message);
    return NextResponse.json({ status: 'error', error: err.message });
  }
}
