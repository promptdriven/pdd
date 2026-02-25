import { describe, it, expect } from '@jest/globals';
import fs from 'fs';
import path from 'path';

describe('FixPreviewPanel component source', () => {
  const componentPath = path.join(__dirname, '..', 'components', 'FixPreviewPanel.tsx');

  it('file exists', () => {
    expect(fs.existsSync(componentPath)).toBe(true);
  });

  it('exports a default component', () => {
    const source = fs.readFileSync(componentPath, 'utf-8');
    expect(source).toContain('export default function FixPreviewPanel');
  });

  it('accepts sectionId, onClose, and onApply props', () => {
    const source = fs.readFileSync(componentPath, 'utf-8');
    expect(source).toContain('sectionId');
    expect(source).toContain('onClose');
    expect(source).toContain('onApply');
  });

  it('fetches from preview-fixes endpoint', () => {
    const source = fs.readFileSync(componentPath, 'utf-8');
    expect(source).toContain('preview-fixes');
  });

  it('has accept/reject checkboxes', () => {
    const source = fs.readFileSync(componentPath, 'utf-8');
    expect(source).toContain('checkbox');
  });

  it('has diff display capability', () => {
    const source = fs.readFileSync(componentPath, 'utf-8');
    expect(source).toContain('diff');
    expect(source).toContain('<pre');
  });
});
