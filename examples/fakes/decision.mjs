// Generated from examples/fakes/decision.prompt.md (sha256: 5f9c5ca68168d09a07385a20b8b22ab4ccac90414c5f0858ba89e055fea4c6bd).
export function decideReply(reply) {
  return { label: reply.available ? 'Available' : 'Unavailable' };
}

export function doLookup(service, id) {
  return decideReply(service.lookup({ id }));
}
