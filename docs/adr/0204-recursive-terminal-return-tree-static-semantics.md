# ADR-0204: Recursive terminal return-tree static semantics

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Separate body-only recursive checking and exact elaboration

## Decision

Introduce a separate `TerminalReturnTree` adapter for finite canonical blocks
whose leaves are singleton returns and whose internal nodes are singleton
explicit if/else statements with recursively accepted arms. Keep the existing
`ReturnBody`, `ConditionalReturnBody`, `TerminalReturnBody` and runtime-function
compilation/preparation/execution profiles unchanged in this unit.

The executable checker is total by structural size of the original source
block, without arbitrary fuel or a depth limit. A leaf reuses singleton-return
checking, including bare return as Unit. Every internal condition must have Bool
type, and both entire arms must have the same result type. Preserve the exact
ordered condition/then/else Core expressions in a nested `Core.Expr.ifE` tree.
No wrapper adds a Core operation or synthesizes an absent branch.

Define independent recursive source typing and exact elaboration judgments.
The leaf rules reuse the existing independent singleton judgments. Conditional
exact elaboration separately retains condition resolution, positional lowering
and resolved typing, plus the recursive elaboration of both original arms.
Prove success iff exact elaboration, source typing iff successful elaboration
exists, exact Core typing, Core/result-type uniqueness, failure iff no source
typing, and child inversion. No runtime values or inhabitation premise is needed.

Embed every old successful singleton, one-level conditional and terminal-union
elaboration with the identical Core and type. Full optional-result equality
with old checkers is limited to the old shapes: singleton returns, or one-level
conditionals with singleton-return arms. It is false on arbitrary blocks,
because a deeper accepted tree is rejected by the old nonrecursive adapters.

## Boundaries and next steps

All written branches are checked, including deeply nested unselected branches.
Empty or multiple-statement blocks, absent else branches, local declarations,
calls, loops, mutation, general early return and fallthrough gain no meaning.
Existing local-expression acceptance is reused unchanged; arbitrary and nominal
types may be returned by variables without requiring any runtime inhabitant.
No parser, Core, Resolved, type lookup, allocator or frozen interface changes.

This unit establishes the static adapter only. Recursive raw/cost semantics and
continuation correspondence follow separately, then the runner, recursive fuel
bound and checkpoint resumption. Identity/store invariance must be established
before any later runtime-function entry integration. The old nonrecursive fuel
bound must not be presented as a bound for arbitrary return trees.

## Validation

Independent consumers cover arbitrary-depth families, asymmetric trees, exact
ordered lowering, same-typed wrong-Core rejection, Unit and nominal leaves,
old-success embeddings and deep invalid-arm rejection. Parsed consumers use
actual source blocks and static parameter declarations without runtime values,
and contrast new deep success with unchanged old body/entry rejection.

Audit all public declarations and consumers with standard axioms only; run
focused/aggregate builds, full tests and kernel/metadata/whitespace checks.
Keep proof files below 300 lines and commits small, preserve paused diagnostics,
and place all scratch files inside the repository.
