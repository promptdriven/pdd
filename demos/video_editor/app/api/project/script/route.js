import { NextResponse } from 'next/server';
const fs = require('fs');
const path = require('path');
const { NARRATIVE_DIR } = require('@/lib/config');

export async function GET() {
  const scriptPath = path.join(NARRATIVE_DIR, 'main_script.md');
  if (!fs.existsSync(scriptPath)) {
    return NextResponse.json({ content: '', exists: false });
  }
  const content = fs.readFileSync(scriptPath, 'utf-8');
  return NextResponse.json({ content, exists: true });
}

export async function PUT(request) {
  const { content } = await request.json();
  if (typeof content !== 'string') {
    return NextResponse.json({ error: 'Content must be a string' }, { status: 400 });
  }
  const scriptPath = path.join(NARRATIVE_DIR, 'main_script.md');
  fs.mkdirSync(NARRATIVE_DIR, { recursive: true });
  fs.writeFileSync(scriptPath, content);
  return NextResponse.json({ saved: true });
}
