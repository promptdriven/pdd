# Prompt Driven Development doctrine

PDD makes software intent a durable source that people can read, test and change. Prompts define the program. Stories and test cases state the behavior people need. The interpreter lets people check and try that behavior before a coding agent builds the implementation.

The aim is to make verified changes easier to repeat and less costly to maintain. Judge the method by working behavior and the total effort needed to deliver it.

## Maintain the source of intent

PDD calls this direction “The Last Programming Language”: people maintain the source of intent while implementation languages remain execution targets. The interpreter can run the prompt program. A coding agent can also build a native implementation from it.

A module's prompt owns its behavior and public contract. Change that source before changing the implementation's behavior. Keep the reasons for consequential rules close to those rules. A future maintainer must be able to understand why the module works as it does.

The [Prompting guide](prompting-guide.md) owns the authoring method. The [RUNBOOK](../RUNBOOK.md) owns executable file formats and verification procedures. This doctrine explains the principles behind them.

## Invest in prompts and tests

A useful comparison is a mold. The prompt describes the part we want. Tests constrain the results we will accept. Declared dependencies supply the context needed to produce it. The code is an implementation of that contract.

Improving a prompt or adding a regression case can help every later implementation. A stronger model may give us better code from the same source. Each new result still needs verification. Tests cover their stated cases; they cannot guarantee that a defect will never return in another form.

This investment is useful when behavior can be stated clearly and checked at reasonable cost. Count specification, generation, verification, repair and review when comparing costs.

## Check behavior before implementation

Use prompt space to resolve what the software should do. Prompt space contains the prompts, Stories, expected cases and required context. The PDD interpreter acts as that program so people can test it and try its behavior.

Code space contains the implementation built from that source. Replay the same expected cases against the code's public interface, then run the project's native checks. These checks answer different questions. A prompt pass establishes no native code result, and a native test pass does not settle a disputed requirement.

## Let people decide intended results

Expected results come from the accepted requirement. The implementation's output is evidence to compare with that expectation.

An agent can identify ambiguity and propose a correction. It must preserve the person's decision and the scope of any delegation. A failing check is a reason to investigate. It does not give the agent authority to change the expected answer.

## Preserve useful regression knowledge

Keep cases that protect accepted behavior when code changes or is regenerated. Add a case when a defect exposes a missing expectation. Change a requirement and its cases together through review.

For a bug, fix the defect and keep a check that detects it. Better diagnostics can help find the cause, but diagnostics alone do not establish a fix. Report that remaining work clearly.

## Give each rule one owner

Build the program from small modules with clear contracts. Put each rule in its owning prompt. Refer to shared policy and declare the context needed to use it. A link helps a reader navigate; the required content must also be available to the interpreter or generator.

Use examples to clarify real use. Use diagrams to explain decisions and returns when they help. Let the Prompting guide define how these views fit together, so the program has one consistent contract.

## Work with coding agents

PDD skills guide the agent through planning, authoring, implementation and review. The agent builds the code and runs its checks. PDD supplies prompt execution and workflow support.

Keep handoffs focused on the task and its required files. Use independent verification and review as the workflow requires. Keep durable decisions in the project's source, so later work can use them without the original conversation.

## Match the method to the work

Clear interfaces and reliable checks make repeated generation useful. Hidden dependencies, uncertain behavior and weak checks make broad regeneration harder to trust. First capture the behavior and boundaries that matter.

Use the small-change workflow for a contained change that is easy to undo. A typo or config edit can need much less process than a new behavior. Preserve the owning contract whenever behavior changes. Apply the project's actual requirements rather than adding a universal coverage target or extra approval step.

## Make results reviewable

Review the intended behavior, then the implementation and its evidence. Show real commands, results and unresolved failures. Keep prompt checks, native tests, independent review and formal checks distinct. State the scope of a formal result.

Workflow records help connect evidence to the source checked. A stored report does not by itself prove that the reported command ran. An open PR does not mean the work passed, merged or reached users.

Use the [workflow guide](workflows.md) for approvals, PRs and operating modes. Manual work and explicitly delegated Autopilot work have different routes. Repository review and merge rules still apply.

## Protect real systems and private data

State important external effects and forbidden behavior in the contract. The interpreter uses declared fakes for outside resources. Native checks must also establish that the actual integration meets its promised behavior.

Keep credentials out of prompts, examples, reports and source control. Review the files selected for a hosted check. Treat a Simulator link as access to that simulation and its call budget.

## Measure useful outcomes

Track verified behavioral changes against the full cost of delivering them. Include the time spent writing requirements, checking results and correcting failures. Compare similar tasks and report the method used.

Better models, accumulated cases and reusable contracts can improve that result. Measure those gains on the work at hand. Keep performance and reliability claims within the evidence.

For a first change, follow the [onboarding guide](ONBOARDING.md).
