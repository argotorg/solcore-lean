# ADR-0249: Exact positional insertion for checked application Core

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Preserve actual application semantics under an unused caller slot

## Evidence and decision

ADR-0248 executes an original singleton application-return function. Combining
calls with larger bodies also requires reasoning about local binding. Existing
recursive discard lowering inserts a hidden Core let and weakens the tail at
position zero. Its raw reflection and fixed-cost proofs currently require the
tail's `Core.Expr.LocalFragment` evidence. An application is outside that old
fragment, even when its two original children are pure local expressions.

The ADR-0243 exact elaboration records both original child lowerings. Their
`Resolved.Lowers.localFragment` consequences are sufficient for positional
insertion of the resulting application. Core weakening changes the caller's
callee and argument expressions; actual application then uses the closure body
and captured values returned by the callee. Those runtime values are not renamed
or rebuilt. The old local-fragment insertion laws preserve both child values,
so the actual closure invocation and its body evaluation can remain identical.

Add proof-only frontend modules on `LocalFunctionApplicationElaborates`.
Prove exact Core typing and raw evaluation insertion equivalences, paired
uniform-cost execution paths, and insertion/reflection of a supplied closed
path at its original cost. The retained prefix determines the insertion cutoff;
prefix, suffix and inserted type/value are arbitrary. The exact source
elaboration is used for the two child fragments, not to manufacture a runtime
environment or equate arbitrary caller contexts with the source context.

Typing retains the same data definitions and requested result type without
runtime inhabitants. Raw evaluation retains literal result values, actual
captures and every store. Neither runtime-world typing, a bound on the cutoff,
source-ID freshness, a pure closure body nor store independence is required.
The claim is conditional on a successful evaluation/path; it does not promise
termination or fault exclusion for arbitrary supplied values and stores.

## Exact cost and continuation boundary

Obtain one common cost for each local child from its paired insertion paths.
Choose a closed path for the actual closure body once, then pass that same path
to both applications of `CostStepComposition.apply`. Its fixed-cost continuation
lifting yields one total cost before quantifying over the outer continuation.
Identify a supplied closed path's cost with this common cost using final-state
path uniqueness. A continuation-dependent existence of some cost is insufficient.

The endpoint with a retained continuation is not necessarily final. Insertion
changes caller environments and saved frames, so do not assert equality of
intermediate states, exhaustion checkpoints, full runner results or subsequent
pending-continuation outcomes. Closed successful completion has the same cost,
value and final store; genuine checkpoints on each side retain their own paths.

Do not broaden the child boundary to arbitrary closure-producing expressions.
A lambda can capture the added caller slot and return a literally different
closure even when the result types agree. Existing application checking, old
local-fragment membership, recursive body/entry acceptance, executable Core,
parser, diagnostics and wire definitions remain unchanged. General recursive
body insertion still needs its own structural closure proof after this leaf.

## Validation and publication

Use independent original source/parsed/function consumers with sparse source
IDs and actual captured closures. Exercise retained-prefix insertion, arbitrary
inserted values and nominal inserted types, exact results with reads, writes,
allocation and delayed bodies, and both directions at a manually established
cost. Check distinct caller checkpoints and each genuine residual, not equal
states. Include a closure-construction counterexample outside the child profile
and a pending-continuation boundary example. Keep proof files below 300 lines.

No new semantic relation or executable definition is needed. Keep lower proof
imports free of return-body and whole-entry layers. Separate decision, proofs,
consumers and publication into small commits. Require focused/aggregate builds,
full tests, all public/consumer standard-axiom audits, dependency closure checks,
kernel-policy and whitespace checks and independent reviews.
