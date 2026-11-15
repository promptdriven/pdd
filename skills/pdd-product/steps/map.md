# map

Read `pdd-prompting/story-guide.md` first. Write `product/map.md`: the sentence, size, Parts,
Stories, Journeys and Questions, using the tables in `references/files.md`.
Each Story is one real user goal (`As a <person>, I want <goal>, so that <reason>`),
marked `CORE` or `LATER`. Never make an internal part the actor (`"I want the
router/server/connector/daemon to..."`), and never split one user action into
duplicate plumbing Stories across parts (`1` user goal = `1` Story, assigned to
the part where the person acts or sees the result, or whose contract proves a
background rule). Keep edge cases (stale taps, blank input, retries), internal
safety rules and wire shapes out of Stories; put them in prompts and `## Rules to check`.
Say in `Parts` which parts face a person and which run headless (`0` UI screens).
Give each question a recommendation and concrete example. Count `CORE` Stories and
parts, propose the size path, show the map and questions, and wait for approval.
