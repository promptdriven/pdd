// Prompt: examples/fakes/database.prompt.md

export function findBook(db, id) {
  return db.find({ id });
}
