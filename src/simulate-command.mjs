// Generated from prompts/cli/simulate-command.prompt.md (sha256: c97185c64b50b40704a394ebb0534e7c07378c2d205819935503ffad0d5d9fad).
// Workflow advice and future #2760 dispatch share this pure choice.
export function chooseSimulationCommand({story,complete,cliEntries,httpRoutes,screens,hasDoor}) {
  const unknown = {kind:'unknown',command:'',timeHint:'',reason:"PDD cannot determine this Story's runnable interface from current local evidence."};
  if (typeof story !== 'string' || !story || /[\0\r\n]/.test(story) || !complete || !hasDoor ||
      [cliEntries,httpRoutes,screens].some(value=>!Number.isSafeInteger(value) || value<0)) return unknown;
  const kind = screens>0 ? 'screen' : cliEntries===1 ? 'cli' : cliEntries>1 ? 'unknown' : httpRoutes>0 ? 'http' : 'call';
  if (kind==='unknown') return unknown;
  const word = /^[A-Za-z0-9_./:@%+=,-]+$/.test(story) ? story : `'${story.replace(/'/g, `'\\''`)}'`;
  return {kind,command:`pdd simulate ${word}${kind==='cli'?' --cli --shell':kind==='http'?' --serve':''}`,timeHint:'about 2 minutes',reason:`Story ${story} has a Simulator door.`};
}
