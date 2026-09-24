# ADR-0376: Graph deep preservation and typed-heap foundations

## Status

Accepted for finite-graph whole-evaluator deep preservation and typed-runtime
dependency proofs. Backend-uniform whole-language preservation is still open.

## Context

ADR-0374 and ADR-0375 connect successful execution to backend-native and
public result signatures. Only direct Core had a recursive value relation and
final-store preservation. A graph value's tag alone cannot validate a source
closure's body or captured environment, and a typed-runtime value's tag alone
cannot validate nested data, captured locations, or the heap. A caller can also
provide a malformed initial store. These cases prevent a sound deep theorem
with only shallow input premises.

## Decision

- The finite graph runtime has a mutually inductive deep value/environment
  relation. It retains Core's closure/body/store typing for projected Core
  values and checks source closures against their captured lexical context.
  Global values require a well-typed program and a matching signature.
- The graph checker exposes a proof that successful checking types each actual
  definition body. Each linked entry retains the successful checker witness,
  selected definition identity, and input signature. Thus deeply typed Core
  arguments and an initial store in the same world imply the exact selected
  runtime-input relation. The compiler exposes this deep graph premise.
- Graph structural argument packing, unpacking and binder construction preserve
  the deep relation. Core-closure application proves deep result and final
  store preservation. Source-closure and global application prove the same
  conclusion under an explicit body-evaluation preservation contract, deriving
  the global body certificate from checked-program provenance. Checker
  inversion lemmas recover all subexpression premises. A fuel induction over
  all 13 executable expression forms discharges the callback contract for
  every well-typed graph program. The actual checked runner and linked entry
  transport this deep conclusion to their selected-result and final-store
  boundary under deep caller inputs and an initial typed store. The compiled
  graph route carries the conclusion at the public source result projection;
  its deep result refines the earlier shallow native-result certificate.
- The source-typed runtime has a step-indexed structural value/heap relation
  whose all-depth form checks products, mappings, constructors and captured
  locations, including cyclic heaps. A separate code-origin relation checks
  closure source/owner/node identity and retained globals against the
  validated plan. Allocation, binding, primitive writes, and root-place
  assignment have deep-heap and code-origin preservation lemmas under their
  stated input/update conditions. Mapping and member projected-update paths
  also have local reconstruction/frame lemmas; constructor payload replacement
  discharges the member frame condition. Empty-mapping defaults have deep
  structural typing and code-origin certificates.
- Raw-workspace compilation retains its source-check witness. Selection of the
  typed backend retains the fact that the complete executable plan passed its
  validation preflight. Neither fact is inferred for an arbitrarily
  constructed `CheckedProgram` or `CompiledEntry`.

## Proof boundary

The graph whole-evaluator theorem is for the finite checked call-graph profile,
not for every source-language feature or an arbitrary untyped program. It
states successful-result/store preservation, not termination or exclusion of
all runtime faults. The typed structural relation does not by itself prove
that a closure's body is well typed. Full typed evaluation also
needs checked IR body/occurrence typing, environment-ID-to-cell typing, and
a composed proof for projected mapping/member update recursion. An unrestricted
default-value typing theorem would be false for `.comptime` types, whose
runtime default is an inner-type value, so any such theorem must state the
applicable runtime-type restriction. No backend-uniform deep
whole-language subject reduction or general fault exclusion is claimed here.

## Verification target

The focused modules, full build and tests, kernel-policy checks,
and whitespace check must pass. No omitted proof, new axiom, unsafe
definition, or native decision shortcut is permitted.
