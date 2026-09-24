# ADR-0263: Runtime-world safety for shared computation bodies and entries

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Proof-only safety over existing original-source body and entry contracts

## Context and evidence

The canonical reference remains `argotorg/solcore-rs` at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. This decision changes no syntax
acceptance, source lowering or Rust correspondence claim. ADR-0245 connects
actual local applications to the existing Core runtime-world safety theorems.
ADR-0254/0255 now provide shared mixed-body and exact original-entry contracts,
and ADR-0253 through ADR-0262 supply recursive child laws.

Core runtime value typing checks actual closures and their captured environments
against a store world; structural value typing alone does not check allocated
locations. Store typing requires the same world and actual cell payload types,
not just store length. Core's existing finite typed evaluator gives successful
evaluation with a possibly extended final world. Its checkpoint state typing
hides that world existentially. These distinctions determine the new premises.

## Decision

Add exactly three generic public proof kernels in three small proof modules.
Do not add an executable definition, a new judgment/bundle, profile-specific
wrapper families, a public argument-layout helper or a new Core safety theorem.
Keep the old fourteen recursive, twelve shared body and four shared entry
contracts and all old imports unchanged.

The body runtime execution kernel takes original body elaboration, child Core
typing, the existing seven child cost/execution/fragment laws, source-ID
alignment, and the actual environment and store typed in one world. It returns
one actual final world/store/value/cost: world extension, runtime value/store
typing, exact original-source cost, the same cost for every continuation-local
path, and both exact closed-run fuel thresholds. The cost is chosen before
all continuations. Child typing equivalence, checker correctness and cost
determinism are not extra requirements for this kernel.

The checkpoint safety kernel needs only original body elaboration, child Core
typing and the actual environment/store/pending continuation typed in one world.
It gives initial state typing, all-fuel no-fault and, for every genuine
out-of-fuel result, typing of that exact saved state and no-fault for every
resumed fuel. It does not require source-ID alignment or child execution/cost
laws. Its checkpoint world remains existential in existing StateHasType;
explicit extension is claimed for final body evaluation, not the checkpoint.

The entry runtime execution kernel takes independent preparation evidence for
the original declaration and actual arguments, the body kernel's child laws,
child checker correctness, each original argument's runtime typing in one
world and the actual store typed in that same world. A private list proof plus
the existing argument-values/types layout theorems transports the original
arguments into the exact reverse-once prepared environment. Return the body
kernel's original-source and execution evidence and preserve the exact
prepared record and full stateful result for every supplied runner fuel.

## Consumers and limits

Consume all three public kernels through independent original-source evidence.
Use parsed mixed bodies and full original entries, arbitrary well-typed actual
delay closures, and separately fixed Core/value/cost paths. Include inferred
and typed bindings, blocks, discard hidden slots and conditional returns.
Exercise actual reader/writer/allocator bodies, literal captures, same-typed
argument/capture swaps, genuine checkpoints and exact full resumption.
Allocation must extend the world rather than being treated as store invariant.

Retain explicit counterexamples for missing cells, same-length wrong payloads,
structural-only references, incompatible separate argument worlds and untyped
pending frames. Existing arbitrary-checker factorization continues to preserve
faults; it cannot replace child Core typing. No theorem supplies arbitrary-store
safety, a source-only fuel bound or completion under an untyped continuation.

Keep the existing empty nominal-definition environment and CellPayload
restrictions; do not claim termination of unrestricted Solcore or inhabitance
of nominal types. Source closures/global resolution/arrays/index/projection,
parser and diagnostic proofs remain outside this proof-only change.
Use independent reviews, small phase commits, focused and aggregate builds,
full tests, all-public/all-consumer standard-axiom audits, unchanged-contract
and dependency checks, kernel-policy and whitespace checks, and local scratch.
