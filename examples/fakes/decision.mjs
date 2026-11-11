// Generated from examples/fakes/decision.prompt.md (sha256: 7e59f3a5cfd824dbb80f2c0e83fb69d33e8a2a72241205a2aecea35a2892d13b).
export function decideReply(reply) {
  return { label: reply.available ? 'Available' : 'Unavailable' };
}

export function doLookup(service, id) {
  return decideReply(service.lookup({ id }));
}
