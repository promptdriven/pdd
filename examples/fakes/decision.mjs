// Prompt: examples/fakes/decision.prompt.md

export function decideReply(reply) {
  return { label: reply.available ? 'Available' : 'Unavailable' };
}

export function doLookup(service, id) {
  return decideReply(service.lookup({ id }));
}
