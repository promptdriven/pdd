# database

`database.mjs` exports module function `findBook(db, id)`. It calls the injected SQL connection once via `db.find({ id })` with `SELECT title FROM books WHERE id = :id` and returns `{ rows }` (each row `{ title }`) in query order. Runtime operation `findBook({ id })` binds the connection as read-only SQL resource `db`; integer `id` is the sole SQL parameter. No host database is opened.

## Dependencies

None.
