# ADR-0278: shared computation function owner covariance

## Status

Accepted; additive frontend-semantics proofs. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. No executable definition,
grammar, source admission or header policy changes.

## Context

ADR-0276 transports independent shared-body elaboration and checking under a
single injective owner map. ADR-0277 separately transports raw body evaluation
and exact costs. Neither provides shared function compilation, actual argument
preparation or a whole runner owner law.

The shared function interfaces retain original parameter order, interpret the
original header and require every original body branch to elaborate. Compiled
records contain type-only local inputs; prepared records contain the actual
typed arguments in their bound row order. Changing declaration owners must not
replace values, closure captures, source ranges, types or generated Core.

Existing parameter owner laws give forward transport from empty inputs.
Reflection must recover original parameter results, including failure, without
assuming an inverse owner map or covariance under every possible owner map.
Older direct-function owner proofs are not the shared-body integration.

## Decision

Add `ComputationFunctionOwnerProperties` with five public laws:

- `computationFunctionCompiles_mapOwner_iff`;
- `computationFunctionPrepares_mapOwner_iff`;
- `compileComputationFunction?_mapOwner`;
- `prepareComputationFunction?_mapOwner`;
- `runComputationFunction?_mapOwner`.

Fix one injective declaration-owner mapping and use `ownerLocalIdMap` to retain
every binder index. Keep the type-name table and original function declaration
literal. The two independent judgment iff laws assume only covariance of their
same fixed child elaboration relation under that mapping. Do not obtain these
judgments by assuming checker correctness or successful checking.

The executable laws instead assume whole optional covariance of the same fixed
child checker. Compile and prepare return the complete original optional record
with only its local-input IDs mapped. This preserves both failure and every
successful record field, not merely an erased success projection. Preparation
uses the same list of actual typed arguments. The runner returns the same full
optional typed Core result for arbitrary fuel and initial store.

Keep parameter reflection private. Induct on the existing independent
`RuntimeParametersDeclareFrom` and `RuntimeParametersBindFrom` judgments while
retaining original input preimages. Commute fresh allocation through the owner
map and recover the original final rows. Input-map injectivity then identifies
the exact original record. Derive private complete parameter Option-map laws
from the existing soundness/completeness contracts.

Reuse the shared-body owner laws and actual-input type erasure/values transport.
Do not import old direct-function owner proofs, a concrete child implementation,
or consumers into the generic module. Existing record definitions may retain
their historical dependencies; this is not a claim to remove those dependencies.

## Consumers and verification

Construct independent original compilation/preparation judgments and original
body semantics before applying the new laws. Include symbolic parameter lists
and repeated body binders where valid, arbitrary actual closures and costs, original
annotations, and a non-surjective injective owner map. Preserve actual argument
order, captures, fresh binder indices and first-match type meanings.

Use original parsed functions with typed/inferred shadows, explicit blocks,
strict calls and conditional or ordered-match bodies. For separately elaborated
and aligned examples, compare independent literal Core paths, allocation/write/
read effects, exact full-fuel results, saved caller frames and resumption.
Same source and argument types may still have different actual captured behavior.

Check duplicate parameter names, missing annotations/types, incorrect argument
arity/types and unselected invalid bodies as whole preparation/compilation
boundaries. Distinguish preparation failure from a prepared program's fault,
exhaustion or success. A covariant arbitrary checker is not necessarily sound;
a non-covariant checker does not acquire owner invariance from injectivity alone.

Require focused/aggregate builds, full tests, exact standard-only public and
consumer axiom catalogs, old contracts/imports/bytes, kernel-policy, EOF, and
whitespace checks, and independent reviews. Keep new proof/consumer files below
300 lines and decision, proof, consumers and publication in separate small commits.

## Non-goals

No general local-index renaming across fresh allocation, nominal/type-table
renaming, new header policy, new raw function evaluator or cost semantics,
runtime safety/world reconstruction, source lambdas, global resolution,
parser/diagnostic work, or changes to old definitions/contracts/consumers.
