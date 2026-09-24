# ADR-0264: Validation of actual typed runtime inputs

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Exact same-world validation for existing typed arguments and stores

## Context and evidence

The canonical reference remains `argotorg/solcore-rs` at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. No source syntax, lowering,
entry acceptance or Rust execution correspondence changes in this decision.
ADR-0263 connects original computation bodies and prepared entries to Core
safety when actual arguments and the actual store are typed in one world.
These are explicit proof premises, not currently executable validation.

Existing TypedRuntimeArgument already carries structural ValueHasType evidence.
For closures this checks the actual body and captured environment, but cell
references need not name allocated locations. Core.Value.type records tags and
component shapes; it does not check arbitrary closure bodies or captures.
StoreHasTypes additionally requires exact world/store length, allowed
CellPayload types and structural typing of every stored value.

## Decision

Add one opt-in Bool function, validateRuntimeInputs, taking a supplied world,
the unchanged list of TypedRuntimeArgument records and the actual store.
Add exactly one public iff theorem characterizing true by the conjunction of
runtime typing of every original argument in that same world and StoreHasTypes
for that world and store. Definitions and private proofs may share one small
module so implementation helpers do not become public API.

Private reference checking traverses pair components, selected sum payloads
and every actual captured value, including unused captures and nested closures.
Each cell reference must have its exact stored element type at its actual
location in the supplied world. This scan does not inspect Core source code or
re-check closure body typing; the existing structural evidence supplies that.
It cannot validate unproved raw values, forged closures, JSON or wire input.

Private store checking traverses world and store together and accepts only
simultaneous exhaustion. Each original row requires isCellPayload and exact
Value.type agreement. For CellPayload, a private structural proof turns that
agreement into ValueHasType. All cells are checked, including unreferenced ones;
a matching prefix, equal lengths alone or valid referenced cells alone do not
suffice. No allocation, mutation, inferred world or repair is performed.

Do not add well-formedness requirements beyond the existing two typing
relations. In particular, nominal/function types in a function signature or
the unselected type of a sum are not blanket rejection reasons for arguments.
The existing empty nominal-definition environment and unsupported host-value
structural typing remain unchanged. Store payload restrictions still exclude
functions, references and nominal values, including in unselected sum types.

## Integration and consumers

Use the public iff directly to supply the two runtime premises of ADR-0263's
existing entry kernel. Keep original header/parameter/body evidence, exact
prepared records, original argument order and full runner results. Add no
new runner, safety wrapper, bundle, public helper or automatic guard to an old
entry. Rejection of the validator is not rejection of source preparation and
does not redefine raw Core faults or successful values.

Symbolic consumers cover nested actual values/captures, arbitrary world/store
sizes, unused missing references, equal-length wrong payloads, extra trailing
cells/types, incompatible argument worlds, and argument-versus-cell payload
boundaries. Parsed original entries independently establish preparation and
fixed Core paths, obtain runtime premises by computation and iff, and consume
the existing generic safety kernel with exact values/stores/costs/checkpoints.
Retain counterexamples showing why structural evidence and source checking
cannot be replaced by a raw tag/reference scan.

Keep all prior semantic contracts and executable entry definitions unchanged.
Use separate small definition/proof/consumer/publication commits, independent
reviews, focused/aggregate/full tests and complete standard-axiom, dependency,
kernel-policy, whitespace, and EOF audits. Keep scratch repository-local and parser
and diagnostic work paused.
