import { NextResponse } from 'next/server';
const fs = require('fs');
const path = require('path');
const { THUMBNAILS_DIR } = require('@/lib/config');

export async function POST(request) {
  const { dataUrl } = await request.json();
  if (!dataUrl || !dataUrl.startsWith('data:image/')) {
    return NextResponse.json({ error: 'Invalid data URL' }, { status: 400 });
  }
  const base64Data = dataUrl.replace(/^data:image\/\w+;base64,/, '');
  const filename = `thumb_${Date.now()}_${Math.random().toString(36).slice(2, 6)}.jpg`;
  fs.writeFileSync(path.join(THUMBNAILS_DIR, filename), Buffer.from(base64Data, 'base64'));
  return NextResponse.json({ url: `/thumbnails/${filename}` });
}
