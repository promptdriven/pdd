// Generated from prompts/cli/product-composition.prompt.md (sha256: d496f7d7bf4a440365c3028bd21a55dfa2e360ca7dd2a4f82451f853b99a9540).
import { basename } from 'node:path';
import { selectTests } from './runtime-preflight.mjs';

const fail = (code, message) => { throw Object.assign(Error(message), { code }); };

export function selectJourneys(tests, selector) {
  const candidates = tests.filter(test => /^user_stories\/journeys\/[^/]+\.md$/.test(test.storyPath));
  if (selector === undefined) return candidates.map(test => test.testPath);
  const records = candidates.map(test => ({ ...test, path: test.testPath }));
  const exactPaths = records.filter(test => test.testPath === selector || test.storyPath === selector).map(test => test.testPath);
  const exact = exactPaths.length ? selectTests({ tests: records }, exactPaths).selected : [];
  const matches = exact.length ? exact : records.filter(test => {
    const name = basename(test.storyPath, '.md');
    return name === selector || name.startsWith(`${selector}-`) || name.startsWith(`${selector}.`);
  });
  if (new Set(matches.map(test => test.storyPath)).size !== 1) {
    fail('invalid-journey', `${matches.length ? 'Ambiguous' : 'Unknown'} journey ${selector}. Candidates: ${[...new Set(candidates.map(test => test.storyPath))].join(', ') || 'none'}.`);
  }
  return matches.map(test => test.testPath);
}
