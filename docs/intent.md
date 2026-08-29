# Natural-language intent: the human surface of PDD

PDD has many implementation artifacts and commands. A product/domain user
should not have to maintain them.

The human-facing contract is:

1. describe what should happen, stop happening, or change;
2. give corrections, examples, and `MUST` / `MUST NOT` constraints;
3. confirm or correct the agent's interpretation;
4. decide whether the reported evidence proves the product works.

The AI agent and PDD maintain the file formats, mappings, generated artifacts,
command selection, synchronization, and verification.

Human control means authority over meaning and acceptable evidence. It does not
mean the human must perform every file edit.

## The first `pdd intent` release

The first safe vertical slice is read-only:

```bash
pdd intent plan --text \
  "Highlight pressure intervals outside the permitted band. Never alter the uploaded samples."
```

It also accepts a local file or piped input:

```bash
pdd intent plan docs/request.md
printf '%s\n' "Add offline PDF export." | pdd intent plan
```

For an AI harness:

```bash
pdd intent plan --text "Add offline PDF export." --json
```

`pdd intent plan`:

- requires no GitHub issue;
- classifies the selected project scope;
- discovers candidate prompt-owned product areas conservatively;
- extracts stated examples and preservation constraints;
- recommends independent story coverage selectively;
- emits one human review card or stable JSON;
- does not call a model;
- does not change project files;
- does not yet apply the plan.

The command is primarily an agent-facing primitive. A human using an AI coding
harness should be able to speak normally while the harness selects the command
and project scope.

## The four adoption scenarios

The human interaction remains the same in every scenario. The agent changes its
internal route.

### 1. Existing standalone project without PDD

The agent scopes planning to the project root, inventories existing behavior,
and runs characterization tests before assigning PDD ownership. It then
proposes bounded prompt-owned product areas. Existing code does not become
generated output merely because `.pddrc` was added.

Planner classification:

```text
project_kind: conventional_brownfield
adoption_scenario: existing_project_adoption
workflow: characterize_then_adopt
```

### 2. Completely new standalone project

The agent consolidates the ordinary-language request into product intent,
proposes technology and architecture decisions, generates the prompt graph,
and verifies one small end-to-end slice before broad generation.

The proposed project directory may be absent during planning; `pdd intent plan`
does not create it.

Planner classification:

```text
project_kind: greenfield
adoption_scenario: new_project_design
workflow: design_greenfield
```

### 3. Existing monorepo subproject without PDD

The agent passes the subproject—not the entire repository—as the PDD project
scope. Discovery stays inside that boundary, so unrelated sibling projects are
not silently converted. The agent also identifies build and integration checks
at the containing repository boundary.

Planner classification:

```text
scope_kind: subproject
project_kind: conventional_brownfield
adoption_scenario: existing_subproject_adoption
workflow: characterize_then_adopt
```

### 4. New monorepo subproject

The agent may plan against a proposed subdirectory that does not exist yet. It
designs that subproject's product intent, technology, architecture, prompts,
and local tests while also planning integration checks with the monorepo.

Planner classification:

```text
scope_kind: subproject
project_kind: greenfield
adoption_scenario: new_subproject_design
workflow: design_greenfield
```

An already-PDD-managed standalone project or subproject is classified as an
existing PDD change instead.

## Two meanings of “prompt”

The word *prompt* is overloaded.

### Conversational prompts

These are the messages a person types or dictates:

> Add offline report export. Never send the report to a remote service.

They are sufficient input to start. They may be rough, corrected later, or
spread across several messages. Chat history is not a durable project source by
itself, so an agent must preserve accepted meaning in repository artifacts.

### PDD `.prompt` files

A PDD `.prompt` file is a versioned technical specification used to generate or
synchronize an implementation artifact. It contains durable behavior,
interfaces, dependencies, constraints, examples, and PDD metadata.

The prompt files collectively form a **prompt graph** that governs the
PDD-managed project or subproject. They are not one giant transcript and should
not be confused with every message the human has ever sent.

Normally:

- prompt files use the `.prompt` suffix;
- they live under a configured prompt root, conventionally `prompts/`;
- `architecture.json` maps them to generated outputs and dependencies;
- `.pddrc` defines relevant paths and defaults;
- the prompt files are committed and versioned in Git;
- an AI agent may draft and edit them;
- a human approves consequential behavior, while a technical owner reviews
  important interfaces, dependencies, and constraints.

The exact filename and directory matter to PDD, but should not be decisions the
product user must make.

## What “tests” means

Tests are executable programs that check observable behavior. They are not
another collection of chat prompts.

Depending on the project, they may be:

- unit tests for one component;
- integration tests between components;
- end-to-end or UI tests;
- regression tests preserving a previously broken behavior;
- negative tests proving a `MUST NOT`;
- compile, link, schema, security, performance, or hardware-in-the-loop checks.

They normally live in the repository's established test layout—such as
`tests/`, Rust test modules, JavaScript test directories, or a CMake/CTest
tree—and are committed to Git. `.pddrc` and project conventions tell PDD and
the agent where applicable tests belong.

The product/domain human supplies important examples and decides what outcomes
would be convincing. The agent or PDD writes and runs the test code. A
technical owner reviews critical coverage. The human should not have to know
pytest, Jest, Cargo, CTest, filenames, or test markers merely to describe the
product.

## What happens to user stories

User stories are selective independent acceptance checks, not mandatory input
syntax and not the primary compiler source.

The human does not have to:

- begin with `As a ... I want ... so that ...`;
- run `pdd story add`;
- choose a prompt or “dev unit”;
- invent a story slug;
- create `user_stories/`;
- write story metadata;
- edit the generated contract;
- choose a regression-test path.

When an independent story is useful, the agent drafts it from the preserved
original request and presents its meaning in the review card. The human says
whether it is right or supplies a correction. The agent performs the file edit.

The conventional implementation layout is:

```text
user_stories/story__<slug>.md
user_stories/contracts/<slug>.contract.md
tests/story_regression/test_story_<slug>.py
```

The small story is human-authoritative, which means a person approves its
meaning. It does not require the person to type the file by hand. The contract
is generated and must not be hand-edited.

Use a story when independent acceptance intent can catch prompt drift—for
example user-visible, cross-part, regression, security/privacy, data-loss, or
critical `MUST` / `MUST NOT` behavior. Do not generate one as paperwork for
every spelling correction or internal refactor.

## Where the artifacts live

A conventional standalone project looks like:

```text
project/
├── .pddrc
├── architecture.json
├── prompts/
│   └── <product-part>_<language>.prompt
├── user_stories/
│   ├── story__<slug>.md
│   └── contracts/
├── tests/
└── generated source directories
```

A scoped monorepo subproject may use:

```text
repository/
├── AGENTS.md
├── packages/
│   └── pressure-analyzer/
│       ├── .pddrc
│       ├── architecture.json
│       ├── prompts/
│       ├── user_stories/
│       ├── tests/
│       └── generated source
└── integration-tests/
```

These are conventions, not requirements the human must memorize. Established
project configuration is authoritative. Relative paths must resolve from the
applicable PDD project/subproject scope, and agents must avoid accidentally
mixing nested scopes.

The source and verification artifacts—`.pddrc`, `architecture.json`, `.prompt`
files, approved stories, generated contracts, tests, and normally generated
source—should be committed when they are part of the product. Operational
cache, temporary worktrees, resumable state, and some evidence under `.pdd/`
follow separate repository policy and are not automatically product source.

## The intended end state

After the planning-only release, the next command layer should apply an
approved plan:

```text
ordinary request
-> review card
-> human correction/approval
-> agent-managed PDD source changes
-> scoped synchronization
-> tests and evidence
```

Until that application layer exists, `pdd intent plan` must remain explicit
that it changed nothing. Existing advanced `pdd change`, `pdd generate`,
`pdd story`, and `pdd sync` commands remain available to agents and experienced
operators.
