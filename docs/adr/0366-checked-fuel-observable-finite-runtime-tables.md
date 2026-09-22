# ADR-0366: Checked fuel-observable finite runtime tables

## Status

Accepted as an additive runtime representation for the structural source
fragment.  A finite table names specialized global definitions, checks every
body against the complete table of signatures, and executes with an explicit
fuel-observable result.  This is the runtime-recursion foundation for roadmap
phase 6; it does not change `Core.Expr` or the established acyclic Core linker.

## Context

The existing source linker represents a call by inserting the callee's body
into a finite `Resolved.Expr`, then lowers that tree to Semantic Core.  That is
an appropriate authority for acyclic first-order programs and for the existing
evidence-aware staging profiles, but a direct or mutual runtime cycle cannot be
represented by finite repeated inlining.  Rejecting an already active
specialization was therefore necessary even after the specialization worklist
itself had closed the cycle finitely.

Semantic Core already has lexical closures, but it has no named global
definition table.  Encoding recursion by changing `Core.Expr`, its machine,
wire format, and safety development would couple this frontend milestone to a
much larger Core revision.  The frontend instead needs an additive checked
carrier whose recursive identity is explicit and whose nontermination remains
observable under the caller's existing execution limit.

## Decision

### Name definitions in one finite table

`SourceRuntime.Program` contains a finite list of definitions keyed by the
canonical `SourceSpecialization.SpecializationKey`.  A definition retains its
ordered stable-ID parameters, result type, and body.  Expressions add named
global references and application to the structural Unit/Bool/Word/product
forms used by the current source execution slice.

`Program.check` first rejects duplicate keys, then makes every definition
signature available while checking every body.  A reference around a direct
or mutual cycle is consequently an ordinary forward reference.  Unknown
globals, duplicate locals, incompatible argument bundles or types, and
definition result mismatches reject before execution.  Successful checking
produces a `CheckedProgram`; execution does not accept an unchecked table.

This table is finite even when its dynamic call graph is cyclic.  It is a
runtime representation, not an unrolling of the cycle and not a claim that the
program terminates.

### Make the execution bound observable

`CheckedProgram.run` validates the selected entry and every ordered Core input
before entering its body.  Evaluation is call by value, evaluates pair and
call arguments from left to right, threads the exact `Core.Store`, and evaluates
only the selected conditional branch.

Every recursive evaluation step receives structurally smaller fuel.  Reaching
zero returns `RunResult.outOfFuel` with the current store.  The budget is a
depth-shaped structural bound: sibling subexpressions may receive the same
remaining amount after an earlier sibling completes, so it is not a global
total-work counter.  Runtime faults similarly retain the store at the point of
failure; successful execution returns the runtime value and final store.

The runtime has its own precise `RuntimeError` carrier for missing entries or
globals, unbound locals, nonfunctions, invalid primitive operands, argument
mismatches, and faults returned by an embedded Core closure.  ADR-0368 defines
both the exact source-execution carrier and the intentionally opaque projection
used by the pre-existing Core result API.

### Keep Semantic Core unchanged

The new table, checker, values, and evaluator live under
`Solcore.Frontend.SourceRuntime`.  No recursive global constructor is added to
`Core.Expr`, and the existing Core checker, machine, wire formats, and proofs
are unchanged.  Acyclic programs that the established source-to-Core linker can
handle continue to use that path.

## Phase boundary

This ADR provides:

- a finite canonical-keyed global definition table;
- whole-table signature collection followed by executable body checking;
- finite representations of direct and mutually recursive runtime graphs;
- exact entry input validation and left-to-right store threading; and
- successful, faulted, and out-of-fuel outcomes that retain the current store.

The source linker initially admits only structural Unit, Bool, Word, product,
and function types.  Nominal data, sums, cells, mappings, proxies, indexing,
assignment, loops, broader statements, and effects are outside this lowering
profile.  Evidence-bearing runtime definitions and `comptime` contracts are
also excluded by ADR-0368, apart from the already checked builtin Word-literal
obligation.  The fuel result does not prove termination or bound total work.

The proof boundary is deliberately small: executable examples establish that
a checked mutual cycle exhausts fuel with the store intact and that malformed
entry arguments fault before body execution.  General progress, preservation,
determinism, fuel monotonicity, and source-to-runtime correspondence remain
future hardening.

## Verification target

A two-definition mutual cycle checks because both signatures are visible
before either body is inspected, then returns `outOfFuel` at a finite bound
without changing an arbitrary input store.  Separate executable checks reject
wrong entry arity and type before execution.  End-to-end terminating recursion
is covered after source linking in ADR-0368.
