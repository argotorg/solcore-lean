# solcore-lean

Implemented behavior is defined by the Lean modules and checked by the
repository tests. This README keeps only the unfinished work.

## Remaining work

## Priority implementation

- Finish integrating the generic grouped-conditional spine: add its independent
  consumer, register it in the frontend, and provide the generic-first selecting
  wrapper.
- Broaden whole-program execution to cover advanced generic/type cases,
  coherent unrestricted trait resolution, let-polymorphic runtime values,
  general evidence/coercion dispatch, members, mappings, proxies, mutation, and
  higher-order or effectful staging.
- Complete public compiler orchestration: automatic entry and ABI-root
  discovery, multi-root and mixed-backend compilation, backend override, and
  serialization of source values, closures, heaps, and results.

## Proof and specification work

- Add declarative raw-source parsing, module/import, and name-resolution
  semantics before the existing resolved-source layer.
- Prove end-to-end soundness, completeness, and correspondence from checking,
  inference, staging, and specialization through every execution backend;
  include unification, trait solving, and module resolution.
- Complete general progress and determinism results, exhaustive fault
  classification, divergence/fuel correspondence, backend-uniform deep
  preservation, plan-validator completeness, and aggregate work bounds.

## Optional scope extensions

- Extend contract execution beyond one nested-call level and, if desired,
  model richer external-call, creation, storage-layout, gas, and EVM behavior.
- Replace the static Word-only ABI with dynamic and composite ABI support.
- Extend Core generation and shrinking to functions, recursion, algebraic data,
  cells, and host effects, and add an independent cross-implementation
  differential harness.

## Paused

- Parser and diagnostic proof densification, including integration of the
  left-associative trace proof work, remains intentionally deferred.
