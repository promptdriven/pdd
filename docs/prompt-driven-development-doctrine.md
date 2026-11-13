# Prompt Driven Development doctrine

Software outlives the code that first implements it. People change the code as
requirements change, but the reason for each behavior can disappear into old
conversations, scattered tests and local fixes. Prompt Driven Development (PDD)
keeps that intent in the project. A prompt states what a module must do and why.
A Story describes a user's task and the result that would satisfy it. Test cases
make selected expected behavior concrete. A coding agent uses this source to
build native code in the project's language; the code remains reviewable and
must still work.

The central idea is simple: preserve the intent and evidence that should guide
future implementations, so a change can improve the next build as well as the
current one. PDD calls this direction “The Last Programming Language.” The name
describes what people maintain as the source of intent. It does not mean that
native languages or their implementations disappear.

## Treat intent as the mold

When a wood carving needs a change, a craftsperson works on that particular
object. The history of earlier cuts remains in it. A mold takes a different
approach: the maker changes the mold, then forms a new object to the revised
shape. The valuable work moves toward describing the desired result and the
limits it must respect.

PDD applies this idea to software when its behavior can be stated and checked.
The prompt describes purpose, rules and important boundaries. Its public
contract names the inputs and results that callers can rely on. Tests give
concrete examples of behavior that must hold. Dependencies and usage examples
provide context about how the module fits with the rest of the system. Together,
these form a mold for an implementation. The mold guides the work; it does not
prove that every possible result is correct.

When an agent builds an implementation again from this source, that is
regeneration. The new code can differ from the old code. Preserve the behavior
people rely on by checking the same cases and the project's native tests, then
review the implementation. Do not use unchanged lines as a substitute for
evidence about behavior.

For example, suppose an `apply_coupon` module gives a discount when an order
subtotal is at least $50. Its prompt explains the rule and its reason. Test cases
show that $49.99 does not qualify, $50 does, and an unknown coupon leaves the
order unchanged. If an implementation rejects $50, the boundary case makes the
failure visible. Fixing the prompt or implementation and keeping that case gives
future work the same evidence. A test protects only the behavior it expresses
and that the project runs; it cannot rule out every related defect.

## Make the source useful to people and tools

Prompts carry the intent that should survive a rewrite. A public contract names
the inputs and results that callers can rely on. Examples show how the module is
used and can teach a generator a proven pattern. Dependencies identify required
context, such as a shared policy or another module's contract. Tests record
selected outcomes and edge cases. These parts have different jobs. Putting them
in one huge prompt or scattering them among unrelated documents makes it harder
to know which rule is authoritative.

Keep modules small enough to have a clear owner for each rule. Keep required
interfaces and shared policy available to the agent that implements the module.
Do not rely on a link alone when the generator also needs the linked content.
When a rule changes, update its owning source and the cases that show the
accepted behavior. Preserve the reason for a consequential rule so that a later
maintainer can tell whether a proposed change is safe.

## Check the prompt program before native code

PDD adds a way to work with the prompt before native implementation exists. The
PDD interpreter acts as the prompt program: people can check expected cases and
try its behavior against the requirements. This helps reveal ambiguity while
the discussion is still about what the software should do.

After the behavior is accepted, a coding agent builds the native implementation
from the same source. Run the expected cases against that implementation and
run the project's own checks. These results answer different questions. A
prompt check shows how the prompt program handled its cases. A native test shows
how the code handled its cases. Neither result proves the other. Review the code
and its evidence before treating the change as complete.

## Let each bug improve future work

A bug report is evidence that the current source, cases or implementation did
not capture an accepted expectation. First state the expected result and make
the failure observable. If the prompt misstates the requirement, correct it. If
the prompt already states the right behavior, fix the implementation. In either
case, retain a test that would expose the same failure. The prompt interpreter
can check and try intended behavior before native code is built or rebuilt; the
same case then checks the native result.

This is how knowledge accumulates. A local patch can correct one implementation.
A retained regression case can also guide every later implementation that runs
it. A clearer contract can help other modules that depend on it. These returns
are real only when future work uses the cases and context, and when the checks
cover the behavior that matters. PDD does not promise that a bug can never
return; it makes accepted learning easier to preserve and reuse.

## Match the method to the work

The mold approach pays when the behavior is stable enough to describe, its
public boundary is clear, and useful checks can be run at reasonable cost. It
often fits validation rules, adapters, data transforms and other work with
repeatable inputs and outcomes. The case is weaker when the requirement is still
being discovered, important behavior is hard to test, or a tiny reversible edit
would cost less than setting up the full source and checks. Hidden dependencies,
performance work and experimental algorithms may also need a different or
hybrid approach.

Choose the smallest method that preserves the behavior people care about. A
small, easy-to-undo change does not need the same process as a new feature. A
larger feature may need more explicit contracts and examples before an agent
builds it. PDD is a way to keep intent and evidence aligned; it is not a reason
to add universal coverage targets or extra approval steps.

## Judge the full cost

Prompt and test work takes time. So do generation, checking, repair and review.
Compare the total effort with the useful behavior delivered and the maintenance
that remains. Count the work required to write and keep the mold current. Count
only results that people checked at the boundary they care about.

As modules gain clear contracts, useful examples and meaningful cases, future
changes can start with better context and stronger evidence. A more capable
model may produce a better implementation from that source, but each result
still needs review and verification. Measure those gains on the work at hand.
The goal is not to maximize the amount generated. It is to deliver more verified
behavior for the full cost of changing the system.

The [Prompting guide](prompting-guide.md) explains how to author prompts and
contracts. The [RUNBOOK](../RUNBOOK.md) defines file formats and verification
procedures. The [workflow guide](workflows.md) explains how people and agents
use those practices during a change.
