# Local recipe listing

Own `src/workflow-list.mjs`; export `listLocalWorkflows({cwd,readDir,stat})` and `formatLocalWorkflows(catalog,{json})`. List sorted regular `.pdd/workflows/NAME/WORKFLOW.md` files under the current project, without following symlinked metadata/root/directories/files. Missing directory is an empty catalog; other filesystem errors propagate to the CLI's finite exit1. Preserve shape `{workflows:[{name,file}],default:null}` with project-relative paths. JSON emits that actual catalog. Human output explains these are instructions for the existing agent, not an automated runner. This command does not install recipes into another project or infer one as default.

## Dependencies

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

The CLI's executable-definition listing comes from the dedicated workflow-definition-loader, not listLocalWorkflows. Preserve legacy manual Markdown discovery export without making it executable authority. formatLocalWorkflows also displays authoritative {name,source} entries; preserve JSON object as supplied, with default:null. Human wording must explain listing is inert and workflow run executes validated definitions, rather than claim the whole product lacks a runner.
