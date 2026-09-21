# ADR-0352: Closed Word-to-integer conversion

## Status

Implemented as the final primitive in the pinned compiler integer-function
catalog, for direct unqualified `wordToInteger` calls over a deliberately closed
Word fragment.

## Context

The reference compiler catalog defines

```text
wordToInteger : Word -> integer
```

as conversion of the canonical unsigned Word value to a nonnegative
arbitrary-precision integer.  It is not the inverse of signed
`wordFromInteger`: after `-1` is projected to a Word,
`wordToInteger(wordFromInteger(-1))` is `2^256 - 1`, not `-1`.

Accepting an arbitrary Word expression here would accidentally turn runtime
locals, storage-dependent operations, or ordinary source calls into compile-time
evaluation.  Rejecting nested `wordFromInteger`, on the other hand, would leave
the two compiler conversions needlessly disconnected.  The boundary therefore
needs a small closed Word evaluator with the same defensive metadata and fuel
contract as the closed integer evaluator.

## Decision

`wordToInteger` receives a collision-free builtin identity, is appended to the
supported compiler-function catalog, and has the fixed monomorphic signature
`Word -> integer`.  Exact bare lookup and local/visible-source shadowing reuse
the generic compiler-function rules; qualified names and failed visible source
candidates do not fall through.

The closed Word evaluator accepts only:

- an inferred numeric literal whose target is exactly `Word`, whose retained
  source and raw value agree, and whose sole requirement resolves to the
  premise-free builtin `Int<Word>` implementation;
- a transparent requirement-free group; or
- a direct `wordFromInteger` call whose argument belongs to the existing closed
  staged-integer fragment.

A Word-target literal is first projected with `Word.ofNatModulo` because that
is its established runtime literal meaning.  `wordFromInteger` similarly uses
`Word.ofIntModulo`.  `wordToInteger` then converts the resulting canonical
unsigned Word payload to nonnegative Lean `Int` without sign extension.

The integer and Word evaluators are mutually recursive under the same strictly
decreasing node-derived fuel.  This admits closed conversion round trips while
making forged cross-domain cycles terminate with a located depth error.  Every
builtin call/callee identity, spelling, type, arity, requirement, coercion, and
literal evidence row is revalidated.  Consumed requirements retain left-to-right
traversal order and pass through the existing declaration-wide exact-once gate.

`wordToInteger` produces no runtime Core integer representation.  Its result
must be consumed by a supported staged arithmetic, comparison, or outer
`wordFromInteger` boundary.  Compiler conversions create no source declaration,
specialization request, or call edge.

## Deferred boundaries

- Runtime Word locals and parameters, direct Word arithmetic/bitwise/comparison
  forms, ordinary or indirect source calls, storage-dependent expressions, and
  general closed Core evaluation are not admitted by the Word staging boundary.
- Staged locals, integer-valued conditionals, recursion, and general compile-time
  control flow remain unsupported in the integer evaluator as well.
- Output coercions, indirect compiler-function invocation, and custom execution
  of the compiler builtin `Int` trait remain outside this direct profile.
- Graph-wide `TypedSource` ownership, identity uniqueness, reachability,
  shared-DAG resource controls, and broad inference/lowering metatheory remain
  shared later work.

## Verification

Regressions cover Word-target literal evidence and modulo-first conversion,
canonical maximum-Word round trips from a negative integer, distinction from
signed `-1`, nested arithmetic/comparison use, typed catalog/signature lookup,
source shadowing without failed-candidate fallback, and absence of
specialization edges.  Adversarial tests mutate the outer and nested conversion
metadata, substitute `Int<integer>` for required `Int<Word>` evidence, construct
Word/group/cross-domain cycles, duplicate literal consumption, and confirm that
runtime-dependent Word expressions reject before Core.
