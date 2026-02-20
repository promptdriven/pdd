import { NextResponse } from 'next/server';
const { getSections } = require('@/lib/config');

export async function GET() {
  return NextResponse.json(getSections());
}
