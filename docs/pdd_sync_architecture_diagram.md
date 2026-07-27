# PDD Sync Architecture Diagram

## Command Dispatch

```mermaid
flowchart TD
    CLI["pdd sync command<br/>pdd/commands/maintenance.py"] --> Dispatch{"Input shape"}

    Dispatch -->|"no basename"| Global["Project-wide sync<br/>run_global_sync()"]
    Dispatch -->|"GitHub issue URL"| Agentic["Issue sync<br/>run_agentic_sync()"]
    Dispatch -->|"module basename"| Single["Single-module sync<br/>sync_main()"]

    Global --> ArchScan["Scan architecture.json files<br/>find modules needing sync"]
    ArchScan --> GlobalRunner["AsyncSyncRunner<br/>dependency ordered child syncs"]

    Agentic --> IssueRead["gh api: issue + comments"]
    IssueRead --> TargetDetect["Target detection<br/>branch diff first, LLM fallback"]
    TargetDetect --> ArchValidate["architecture.json validation<br/>filter hallucinated basenames<br/>apply dependency corrections"]
    ArchValidate --> DepGraph["Dependency graph<br/>architecture dependencies or prompt includes"]
    DepGraph --> DryRunCheck["Per-module dry-run validation"]
    DryRunCheck --> RunnerChoice{"--durable?"}
    RunnerChoice -->|"no"| AsyncRunner["AsyncSyncRunner<br/>parallel subprocess scheduler"]
    RunnerChoice -->|"yes"| DurableRunner["DurableSyncRunner<br/>isolated worktrees + checkpoint commits"]

    Single --> Discover["Discover prompt/context/languages<br/>construct_paths + .pddrc"]
    Discover --> ModeChoice{"--one-session?"}
    ModeChoice -->|"no"| Orchestrator["sync_orchestration()"]
    ModeChoice -->|"yes"| OneSession["generate code, then<br/>run_one_session_sync()"]

    GlobalRunner --> ChildSync["child: pdd --force sync module"]
    AsyncRunner --> ChildSync
    DurableRunner --> Worktree["module worktree"]
    Worktree --> ChildSync
    ChildSync --> Single
```

## Single-Module Sync Loop

```mermaid
flowchart TD
    Start["sync_main()"] --> Paths["Resolve files<br/>prompt, code, example, test"]
    Paths --> Dry{"--dry-run?"}
    Dry -->|"yes"| AnalyzeOnly["sync_determine_operation(log_mode=True)<br/>print next operation"]
    Dry -->|"no"| Engine["sync_orchestration()"]

    Engine --> Lock["SyncLock<br/>.pdd/locks/module_language.lock"]
    Lock --> Decide["sync_determine_operation()"]
    Decide --> Decision{"Next operation"}

    Decision -->|"auto-deps"| AutoDeps["auto_deps_main()<br/>refresh prompt dependencies"]
    Decision -->|"generate"| Generate["code_generator_main()<br/>write code<br/>architecture conformance retry"]
    Decision -->|"example"| Example["context_generator_main()<br/>write usage example"]
    Decision -->|"crash"| Crash["run example<br/>auto-fix simple import/env issues<br/>crash_main()"]
    Decision -->|"verify"| Verify["fix_verification_main()<br/>verify example behavior"]
    Decision -->|"test or test_extend"| Test["cmd_test_main()<br/>generate/extend tests<br/>run test command"]
    Decision -->|"fix"| Fix["fix_main()<br/>repair code/tests from failures"]
    Decision -->|"update"| Update["update_main()<br/>back-propagate code changes to prompt"]
    Decision -->|"nothing or all_synced"| Done["Return success"]

    AutoDeps --> Persist["Save operation log + fingerprint"]
    Generate --> Persist
    Example --> Persist
    Crash --> Reports["Save run report when runtime/test result is known"]
    Verify --> Reports
    Test --> Reports
    Fix --> Reports
    Update --> Persist
    Reports --> Persist
    Persist --> Decide
```

## Decision Inputs And State

```mermaid
flowchart LR
    Files["Working files<br/>prompt, code, example, tests"] --> Decision["sync_determine_operation()"]
    Fingerprint[".pdd/meta/module_language.json<br/>last command + hashes"] --> Decision
    RunReport[".pdd/meta/module_language_run.json<br/>exit code, tests, coverage, test hash"] --> Decision
    Includes["prompt include deps<br/>stored in fingerprint when needed"] --> Decision
    Flags["skip flags, budget,<br/>target coverage, context"] --> Decision

    Decision --> Operation["recommended operation<br/>auto-deps, generate, example,<br/>crash, verify, test, fix, update,<br/>nothing, all_synced"]
```

## Multi-Module Runner

```mermaid
flowchart TD
    Targets["Modules to sync"] --> Graph["Dependency graph"]
    Graph --> Scheduler["AsyncSyncRunner scheduler"]
    Scheduler --> Ready{"Deps satisfied?"}
    Ready -->|"yes"| Pool["ThreadPoolExecutor<br/>max workers or one worker with total budget"]
    Ready -->|"no"| Pending["Keep pending"]
    Pool --> Subprocess["subprocess: pdd --force sync module<br/>CI=1, PDD_FORCE=1, cost CSV"]
    Subprocess --> Phase["Parse PDD_PHASE lines<br/>update module state"]
    Phase --> Github["Optional GitHub progress comment"]
    Subprocess --> Result{"Exit status"}
    Result -->|"success"| SuccessState["module status: success<br/>save runner state"]
    Result -->|"architecture conformance failure"| Repair["retry with PDD_REPAIR_DIRECTIVE<br/>up to MAX_CONFORMANCE_ATTEMPTS"]
    Repair --> Subprocess
    Result -->|"other failure"| FailedState["module status: failed<br/>block dependents"]
    SuccessState --> Scheduler
    FailedState --> Scheduler
    Pending --> Scheduler
```

## Main Source Map

| Area | File |
| --- | --- |
| Click command dispatch | `pdd/commands/maintenance.py` |
| Single-module CLI wrapper | `pdd/sync_main.py` |
| State decision engine | `pdd/sync_determine_operation.py` |
| Single-module operation loop | `pdd/sync_orchestration.py` |
| Issue/global multi-module sync | `pdd/agentic_sync.py` |
| Parallel child sync runner | `pdd/agentic_sync_runner.py` |
| Durable worktree runner | `pdd/durable_sync_runner.py` |
| One-session agent path | `pdd/one_session_sync.py` |
| Sync UI and steering | `pdd/sync_tui.py` |
