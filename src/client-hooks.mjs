// Contract: prompts/cli/client-hooks.prompt.md.
export function getOptionalClientHooks({clientAdapter,phoneCli,updateModule} = {}) {
  const client=clientAdapter===undefined?phoneCli:clientAdapter;
  const hooks={};
  for(const [owner,name] of [[client,'runStatusCommand'],[client,'doctorChecks'],[updateModule,'runUpdateCommand']]) {
    const method=owner?.[name];
    if(typeof method==='function')hooks[name]=method.bind(owner);
  }
  return Object.freeze(hooks);
}
