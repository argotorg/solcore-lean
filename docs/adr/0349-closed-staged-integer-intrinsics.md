# ADR-0349: Closed staged integer intrinsics

## Status

Implemented as an executable vertical slice for direct, unqualified
`integerSub` and `wordFromInteger` calls whose staged integer argument is a
closed tree of numeric literals, transparent groups, and nested `integerSub`
calls.

## Context

ADR-0344 through ADR-0347 introduced the staged `integer` type, arbitrary-size
literal payloads, and builtin `Int<integer>` evidence, but deliberately rejected
every `integer` value which reached Semantic Core.  The pinned reference
revision `argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4`
also provides compiler functions

```text
integerSub      : (integer, integer) -> integer
wordFromInteger : integer -> Word
```

with exact mathematical subtraction followed by a nonnegative reduction modulo
`2^256`.  The source grammar has no unary minus, so `integerSub` is the first
way for source execution to construct a negative staged value.

Treating these functions as source declarations would fabricate declaration
identities and specialization edges.  Treating their operands as runtime Core
values would instead invent a Core representation for `integer`.  The staged
tree therefore has to be identified explicitly and erased before ordinary Core
argument lowering.

## Decision

### Give compiler functions collision-free identities

`BuiltinFunctionId` contains `integerSub` and `wordFromInteger`.  Typed
references and calls retain that identity separately from source declaration
instantiations and indirect calls.  The exact bare, case-sensitive spellings
are lowest-priority fallbacks: locals and visible module/import source functions
win first.  Once a source lookup level contains the name, failure to fit its
arity or types does not fall through to the compiler function.  Qualified names
never acquire this fallback.

Inference checks the fixed source arity and unifies every operand and result
with the monomorphic compiler signature.  Integer-literal operands consequently
close at `integer` and retain their existing premise-free builtin
`Int<integer>` evidence.  Compiler calls do not create source specialization
requests or call edges.

### Evaluate only a closed staged tree

Source Core intercepts `wordFromInteger` before the ordinary call policy tries
to lower its `integer` argument.  A fuel-bounded evaluator accepts only:

- a decimal or hexadecimal typed integer literal with exact source/raw/type,
  requirement, predicate, evidence goal, builtin `intInteger` implementation,
  and empty premise list;
- a transparent group; or
- a direct `integerSub` call whose two children are recursively closed staged
  integers.

It computes a Lean `Int`, so subtraction is unbounded and does not wrap.
`Core.Word.ofIntModulo` then maps the signed result to its canonical residue in
`[0, 2^256)`.  Thus `1 - 2` maps to `Word.maximum`, `-2^256` maps to zero, and
`-(2^256 + 1)` maps to `Word.maximum`.  The complete staged tree becomes one
Word constant in both resolved and Core output.

Lowering rechecks the builtin call identity, exact spelling, callee function
type, call result type, positional argument types and arity, and the absence of
call/callee requirements and coercions.  Every literal requirement consumed by
the evaluator is still reconciled exactly once against the checked function's
canonical solved-requirement table.  Malformed cycles terminate at the staged
depth bound.

## Deferred boundaries

- ADR-0350 connects `integerAdd`, `integerEq`, and `integerLt`, and ADR-0351
  connects exact `integerMul`, to the same closed evaluation boundary.
  ADR-0352 connects `wordToInteger` through a separate closed Word evaluator
  and completes the pinned integer compiler-function catalog.
- Staged locals, parameters, conditionals, ordinary function calls, recursion,
  and general compile-time control flow remain unsupported.  A staged subtree
  depending on runtime data rejects as not closed.
- A surviving `integer` input, result, local, or direct `integerSub` result still
  has no Core projection and rejects.
- Compiler-function output coercions and indirect first-class invocation remain
  outside this exact direct-call profile.
- Custom execution of the compiler builtin `Int` trait remains unsupported.
- Graph-wide occurrence ownership, node-identity uniqueness, and unreachable
  node validation remain shared `TypedSource` hardening.  Source inference
  allocates a declaration-owned monotone tree, while this slice defensively
  revalidates only the builtin edges it traverses.
- The evaluator fuel bounds recursive depth and terminates malformed cycles;
  memoization or a separate total-work budget for synthetic shared DAGs remains
  later resource hardening.
- General inference, staging, and lowering metatheory remains deferred under the
  executable-first proof policy.

## Verification

Regressions cover exact typed identities and `Int<integer>` evidence, no
specialization edge, source-name shadowing without fallback after a failed
source candidate, direct and nested subtraction, decimal and hexadecimal
operands, positive overflow, `-1`, `-2^256`, a negative value beyond one
modulus, one-slot public preparation, constant erasure, store preservation,
wrong arity/type, runtime-dependent staged rejection, staged-value leakage, and
direct signed-evaluator results.  Adversarial tests mutate builtin identity,
spelling, callee/call/argument types, arity, requirements, coercions,
literal source/raw metadata and builtin evidence, and construct cyclic staged
edges; each must fail at a located checked boundary.
