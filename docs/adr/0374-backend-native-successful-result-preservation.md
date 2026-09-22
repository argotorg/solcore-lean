# ADR-0374: Backend-native successful-result preservation

## Status

Accepted for the second proof tranche after roadmap phase 10.

## Context

ADR-0373 stopped at canonical-plan validation.  All three executable compiler
paths already checked result types at some boundary, but those checks were not
available as one theorem and did not have the same semantic strength:

- direct Core already has a deep logical relation over values and stores;
- the finite source call graph reconstructs and checks a runtime type tag; and
- the source-typed runtime reconstructs a source `Ty` tag and validates public
  inputs separately.

Treating these three facts as one undifferentiated deep preservation theorem
would be unsound.  In particular, the graph and source-typed tags do not inspect
closure bodies or captures, and their state carriers did not yet have a general
preservation invariant.

## Decision

### Preserve direct Core deeply

Deep `Core.RuntimeEnvironmentHasTypes` evidence now determines the same ordered
type tags used by executable entry guards.  A direct linked entry supplied with
deeply typed arguments and a `Core.StoreHasTypes` witness for the same world has
the following checked guarantees:

- every `.done` result has the elaborated return type;
- the final store has a corresponding store-typing world; and
- no finite fuel budget produces a Core machine fault.

These laws are lifted through `SourceCompiler.CompiledEntry.run`.

### Expose the finite-graph result boundary

`SourceRuntime.Value.HasType` is the public shallow tag relation used by the
finite graph.  Every successful `CheckedProgram.run` result has the result type
declared by the exact selected definition, even if a Lean client manually
constructs the otherwise forgeable `CheckedProgram` carrier.

The separate `Value.RuntimeHasType` and `ValuesRuntimeHaveTypes` relations cover
only values which project to deeply typed Core values.  They prove lossless
`ofCore`/`toCore?` transport and connect same-world deeply typed Core arguments
and an initial typed store to the graph entry boundary.  They do not yet type
source-native closures or globals, or the final graph store.

### Make the typed result authority explicit

Typed-runtime preflight now rejects a specialized function whose declared
function result differs from `inferredBodyType`.  Successful trusted, validated,
compatibility, and optional runs consequently return a value whose `Value.type?`
is exactly the unique selected specialization's `inferredBodyType`.

`Cell.HasShallowType` and `RuntimeState.HasShallowTypes` begin the state
invariant: every initialized heap cell agrees with its annotation according to
`Value.type?`, and the primitive state operations have preservation laws.  The
resolved-place writer also rejects stale root-type metadata before mutation and
preserves this shallow invariant on successful writes.  The
names deliberately record that mappings, closures, captures, constructor
authenticity, and reachable locations are not recursively validated yet.

### Join the compiler paths without erasing their domains

Successful compilation now exposes `CompiledEntry.HasCanonicalRoot`.  The
compiler defines a backend-sensitive `PreservationPrecondition` and
`SuccessfulResultHasNativeType`, then proves one result theorem for direct
Core, finite graph, and source-typed execution.  The same theorem is lifted to
the one-shot raw-workspace compiler.

The common conclusion is intentionally *backend-native*:

- direct Core carries deep result and final-store typing;
- finite graph carries its selected definition's shallow result tag; and
- source-typed execution carries the canonical root's shallow source tag.

For the source-typed backend, a separate public corollary expresses that tag
against `CompiledEntry.resultType` without exposing the sealed plan.

A shared projection lemma shows that each source type accepted by direct-Core
lowering projects to the same Core type in the finite graph.  It does not yet
certify that a particular linked entry's projected result equals the sealed
compiler artifact's public result type.

It is not named or documented as uniform deep whole-language preservation.

## Proof boundary

This tranche does not yet prove:

- deep preservation for source-native graph closures or globals;
- graph final-store typing, world extension, or general fault exclusion;
- recursive typed-value validity for mappings, nominal constructors, closures,
  captured locations, or the final heap;
- preservation of `RuntimeState.HasShallowTypes` through the complete typed
  evaluator;
- a compiler certificate relating every backend-native Core type directly to
  public `CompiledEntry.resultType`; or
- source/runtime simulation or preservation for deferred language forms.

The next priority is a declarative validity relation for checked graph programs
and source closures, followed by induction over graph evaluation.  In parallel,
the typed evaluator should preserve a recursive heap/value relation through
binding, place updates, calls, and control flow.  Once those two state theorems
exist, backend/public-signature coherence can close the fully deep
whole-language subject-reduction statement.

ADR-0375 subsequently closes the public result-signature portion and the
shallow binding-heap step; the deep graph and typed-state obligations remain.

## Verification target

The focused runtime, linker, compiler, and typed-runtime modules, their runtime
regressions, the full build and tests, semantic-kernel audit, metadata audit,
forbidden-proof scan, and whitespace check must pass.  No omitted proof, new
axiom, unsafe definition, or native decision shortcut is permitted.
