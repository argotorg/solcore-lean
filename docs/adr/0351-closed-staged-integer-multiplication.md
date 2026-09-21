# ADR-0351: Closed staged integer multiplication

## Status

Implemented as an executable extension of the ADR-0349–0350 closed staged
integer evaluator for direct, unqualified `integerMul` calls.

## Context

The pinned reference compiler catalog defines

```text
integerMul : (integer, integer) -> integer
```

with arbitrary-precision signed multiplication.  Addition and subtraction were
already evaluated as Lean `Int`, but multiplication raises a sharper resource
question: repeated squaring over a shared expression DAG can produce a value
whose bit size is exponential in graph depth.

Source inference does not construct that graph.  It allocates a fresh identity
for every written expression occurrence, so a closed source multiplication is
a tree.  For such a tree, the result bit size is bounded by the sum of written
leaf-literal bit lengths plus linear additive overhead from the written
Add/Sub/tree nodes.  Resource growth therefore follows explicit source content
rather than hidden sharing.  The manually assembled typed-IR boundary can still
forge shared edges and is a separate whole-graph hardening concern.

## Decision

`integerMul` receives a collision-free compiler-function identity and the fixed
monomorphic signature `(integer, integer) -> integer`.  It is appended to the
supported builtin catalog, so exact bare-name lookup, local/source shadowing,
qualified-name exclusion, and no fallback after a failed visible source
candidate follow the same generic rules as the existing intrinsics.

Multiplication joins the private Add/Sub operation dispatcher in the closed
staged evaluator.  Both operands are recursively validated as exact staged
integers, including every call/callee contract and premise-free builtin
`Int<integer>` literal row, and are multiplied as Lean `Int`.  There is no
intermediate Word projection and no wrapping.  An outer `wordFromInteger`
remains the only path in this slice which reduces the signed result modulo
`2^256`.

The executable source profile imposes no fixed bit-size cap.  Its existing
node-derived depth fuel terminates malformed cycles, while exact-once
requirement reconciliation rejects reused literal evidence.  A future
graph-wide validator or total-work/value-size budget may harden manually forged
shared DAGs without changing the reference semantics accepted for ordinary
source-produced trees.  Reconciliation is a semantic gate after traversal, not
a pre-evaluation resource guard, so a forged shared DAG may still perform large
work before its repeated evidence is rejected.

As with Add/Sub, a surviving `integerMul` result has no runtime Core
representation and rejects unless consumed by a supported staged conversion or
comparison.  The call adds no source declaration, specialization request, or
call edge.

## Deferred boundaries

- ADR-0352 connects `wordToInteger` through a separately specified closed Word
  evaluator and retains the runtime Word purity boundary.
- Staged locals, parameters, integer-valued conditionals, ordinary calls,
  recursion, and general compile-time control flow remain unsupported.
- Indirect compiler-function invocation, output coercions, and custom execution
  of the compiler builtin `Int` trait remain outside this exact direct profile.
- Graph-wide `TypedSource` ownership, identity uniqueness, reachability,
  shared-DAG work accounting, and optional compile-time resource controls remain
  shared later work.

## Verification

Regressions cover exact multiplication at and beyond the Word modulus, negative
and zero operands, nested Add/Sub/Mul trees, direct signed evaluator results,
outer modulo erasure, typed identity/signature/catalog lookup, source shadowing
without failed-candidate fallback, and absence of specialization edges.  The
shared binary tamper matrix checks identity, spelling, callee/call/argument
types, arity, requirements, coercions, cycles, and duplicate requirement
consumption for `integerMul` as well.
