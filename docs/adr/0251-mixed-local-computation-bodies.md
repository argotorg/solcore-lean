# ADR-0251: Mixed local-computation bodies

- Status: Accepted
- Decision date: 2026-09-09
- Scope: A separate recursive body profile with pure or application children

## Evidence and decision

At the pinned Rust revision `18fd9f75d290df0070e21ee56e0a5691f232596f`,
`crates/hir-ty/src/infer/stmt.rs`, lines 19–41, 58–134 and 231–254,
checks ordered statements, checks an initializer before adding its binding,
checks discarded expressions, requires Boolean conditions and unifies branch
types. The canonical AST preserves the optional annotation and initializer,
semicolon flag, original return expression, ordered statements and lexical
block spans. The new profile is deliberately narrower than all Rust statements:
it has terminal returns and if/else trees, not general early-return control flow,
unification, source lambdas, shadowing, loops or assignment.

Introduce `LocalComputationReturnTree` independently of the old pure tree and
singleton application body. Its checker takes the existing type table, owner,
value-free local inputs and original block. Independent HasType and exact
Elaborates relations each have seven cases: bare return, expression return,
terminal block, annotated binding, inferred binding, strict discard and terminal
if/else. Every expression child uses ADR-0250's LocalComputation relation.
Retain original syntax, both spans, optional annotations, ordered tables and
children. The checker does not rebuild a body or invent a source expression.

An initializer is checked in the old scope. A named binding adds the existing
owner-relative fresh source ID and its inferred or matching declared type only
for the tail. A discard evaluates its original child and checks its tail in the
same source scope; its Core is `.letE head (tail.weakenAt 0)`, without a source
name or ID for the hidden binder. A terminal block retains its original inner
span and scope and adds no Core syntax. Both conditional arms use the same
original inputs and must return the same type. Empty bodies, missing initializers,
shadowing, nonterminal returns or blocks, missing else and trailing statements
after a terminal conditional remain outside this profile.

## Structural insertion boundary

Mixed tails no longer satisfy the old Core LocalFragment predicate. In
particular, nested discard tails contain previously weakened applications;
lifting a single leaf insertion theorem is insufficient for their induction.
Define a separate frontend-owned, syntax-only LocalComputationFragment over Core
with four constructors: an old LocalFragment; application of two old
LocalFragments; recursive let; recursive conditional. Every written child is
included, but an actual called closure's body and captures are not source syntax
and are neither inspected nor restricted by this predicate.

Prove weakening closure, literal successful-evaluation insertion/reflection and
paired exact-cost paths with one common cost chosen before any continuation.
Use existing pure-fragment kernels and composition laws. In application, retain
the same actual body evaluation and choose its closed path once for both callers.
The paired paths may have different intermediate frames and environments.
No typing, runtime world, store invariance, freshness or CellPayload assumption
is needed. General Core typing weakening already handles static discard typing;
do not add a redundant fragment typing-insertion or known-cost alias family.

## Independent dynamic contracts

Raw and cost relations have eight cases, splitting the two selected conditional
arms. They have no checker or typing premise. Initializers, discarded children
and guards thread their actual intermediate stores into the tail or chosen arm;
named bindings retain the actual returned value. Raw unselected arms are not
evaluated or checked. Bare return costs one, expression return uses its child's
cost, terminal block adds zero, and let/discard/conditional composition adds two.
An actual application retains its body cost and effects from ADR-0250.

Publish checker iff exact elaboration, whole typing iff an elaboration exists,
Core typing and structural fragment membership, raw iff some cost exists and
joint costed determinism. Exact elaboration with the original ordered runtime
IDs gives raw/Core equivalence, supplied-cost paths before every continuation,
and equivalence with closed Core paths at that exact cost. Keep decomposition
helpers private where possible. Derive known discard cost privately from paired
paths and closed-final uniqueness. Add an explicit old pure elaboration embedding
without changing old executable definitions or transferring their stronger laws.

This vertical body integration must accept `let r=f(x); return r+1;`, returned
callables bound and applied later, effectful discarded calls and call conditions.
It does not make LocalComputation recursively accept `f(g(x))`, `x+f(x)` or
a group around a whole call. Existing pure/application whole-function endpoints
and their header gates remain unchanged; a new whole-function entry is subsequent
work. No source-only fuel bound, store independence, arbitrary-store safety,
unfuelled total evaluator or general source-function resolution is implied.

## Validation and rollout

Exercise independent source certificates, parsed bodies and original function
headers with actual parameter binding. Cover every constructor and public kernel,
nominal value-free typing, returned higher-order values, nested hidden binders,
writer-before-reader store flow, guards whose effects reach the chosen arm,
selected raw success versus whole rejection, wrong/missing cells and delayed
actual closures. Fix expected Core, values, stores and costs independently;
test genuine checkpoints and pending continuations without equating the two
callers' intermediate states.

Separate decision, definitions, proofs, consumers and publication in small
commits, keeping new proof/test files below 300 lines. Require focused and
aggregate builds, full tests, all public/consumer standard-axiom audits,
dependency-closure, kernel-policy, and whitespace checks, plus independent
reviews. Parser, diagnostics, Core, old LocalFragment, old body/entry profiles
and runtime records remain unchanged.
