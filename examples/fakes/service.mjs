// Generated from examples/fakes/service.prompt.md (sha256: 95038774b2be59b8c43897434e6793bd251d88c7a45a8b1b6808c900cf6d1dbc).
export function lookup(service, id) {
  return service.lookup({ id });
}

// The bridge is activated only by direct execution. Library consumers retain
// the injected callback API and have no stdin or process lifecycle effects.
if (process.argv[1] && import.meta.url === (await import('node:url')).pathToFileURL(process.argv[1]).href) {
  try {
    const { parseScenarioJson, stringifyScenarioJson, exactValue } = await import('@promptdriven/runtime-client');
    const { isDeepStrictEqual } = await import('node:util');
    const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
    const same = (a,b) => isDeepStrictEqual(exactValue(a),exactValue(b));
    const keys = (value,expected) => object(value) && same(Object.keys(value).sort(),[...expected].sort());
    const count = value => Number.isSafeInteger(value) && value >= 0;
    const require = (condition,message) => { if (!condition) throw Error(message); };
    let raw = '';
    process.stdin.setEncoding('utf8');
    for await (const chunk of process.stdin) raw += chunk;
    const request = parseScenarioJson(raw);
    require(keys(request,['schema_version','operation','symbol','input','initial_world','simulation']) &&
      request.schema_version === 'prompt-runtime.code-call.v1' && request.operation === 'lookup' && request.symbol === 'lookup', 'Unsupported request.');
    require(keys(request.input,['id']) && typeof request.input.id === 'string' && object(request.initial_world) &&
      keys(request.simulation,['service.lookup']), 'Invalid input, world or simulation.');
    const fixture = request.simulation['service.lookup'];
    require(keys(fixture,['action','world_pointer','cases','result_template','result_value_pointer']) &&
      fixture.action === 'fixture.lookup' && fixture.result_template === null && fixture.result_value_pointer === '' &&
      typeof fixture.world_pointer === 'string' && fixture.world_pointer.startsWith('/') && !/~(?![01])/.test(fixture.world_pointer) &&
      Array.isArray(fixture.cases) && fixture.cases.length > 0, 'Unsupported saved fixture.');
    const tokens = fixture.world_pointer.slice(1).split('/').map(token => token.replace(/~1/g,'/').replace(/~0/g,'~'));
    const world = request.initial_world;
    let holder = world;
    for (const token of tokens.slice(0,-1)) {
      require((object(holder) || Array.isArray(holder)) && Object.hasOwn(holder,token) &&
        (!Array.isArray(holder) || /^(0|[1-9][0-9]*)$/.test(token)), 'Missing fixture counter path.');
      holder = holder[token];
    }
    const leaf = tokens.at(-1);
    require((object(holder) || Array.isArray(holder)) && Object.hasOwn(holder,leaf) &&
      (!Array.isArray(holder) || /^(0|[1-9][0-9]*)$/.test(leaf)) && count(holder[leaf]), 'Invalid fixture counter.');
    const indices = new Set();
    for (const item of fixture.cases) {
      require(keys(item,['args','call_index','result']) && keys(item.args,['id']) && typeof item.args.id === 'string' &&
        count(item.call_index) && item.call_index > 0 && !indices.has(item.call_index) &&
        keys(item.result,['label']) && typeof item.result.label === 'string', 'Invalid saved fixture case.');
      indices.add(item.call_index);
    }
    let calls = 0;
    const result = lookup({lookup(args) {
      require(holder[leaf] < Number.MAX_SAFE_INTEGER,'Fixture counter cannot advance safely.');
      const next = holder[leaf] + 1;
      const match = fixture.cases.find(item => item.call_index === next && same(item.args,args));
      require(match,'No exact saved fixture match.');
      holder[leaf] = next; calls++;
      return match.result;
    }},request.input.id);
    process.stdout.write(stringifyScenarioJson({schema_version:request.schema_version,result,world,
      calls:{resources:{'service-service-lookup':calls},internal:{}}}) + '\n');
  } catch (error) {
    process.stderr.write(`Native lookup adapter refused: ${error.message}\n`);
    process.exitCode = 1;
  }
}
