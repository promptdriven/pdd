import { describe, expect, it } from 'vitest';

import { buildCommandRequest, buildDisplayCommand } from '../lib/commandBuilder';
import { CommandType, PromptInfo } from '../types';

const prompt: PromptInfo = {
  prompt: 'prompts/example_python.prompt',
  basename: 'example',
};

describe('commandBuilder replay display', () => {
  it('uses run artifact as replay positional argument', () => {
    const display = buildDisplayCommand(CommandType.REPLAY, prompt, {
      'run-artifact': '.pdd/evidence/runs/run-1.json',
      json: true,
    });

    expect(display).toBe('pdd replay .pdd/evidence/runs/run-1.json --json');
  });

  it('keeps replay display aligned with built args after options are normalized', () => {
    const request = buildCommandRequest(CommandType.REPLAY, prompt, {
      'run-artifact': '.pdd/evidence/runs/run-2.json',
      'verify-only': true,
    });

    expect(request.args.run_artifact).toBe('.pdd/evidence/runs/run-2.json');
    expect(request.options).not.toHaveProperty('run-artifact');
    expect(request.displayCommand).toBe(
      'pdd replay .pdd/evidence/runs/run-2.json --verify-only'
    );
  });
});
