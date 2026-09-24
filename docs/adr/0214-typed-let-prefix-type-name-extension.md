# ADR-0214: Typed let-prefix type-name extension

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Annotation-meaning extension and complete checked body observations

## Decision

Use the existing semantic `TypeNameTable.Extends` relation to preserve typed
let-prefix acceptance when caller type meanings grow. Extension preserves every
old first-match meaning, not merely membership of the original rows. Fix the
source body, owner and explicit input bundle; do not redeclare types or replace
values supplied in that bundle.

Transport independent exact elaboration and whole typing to the extended table.
Only each written annotation's meaning needs extension: the initializer's old
name/type scope, unused-name evidence, resolved expression, positional Core,
declared type and freshly extended tail remain unchanged. Retain the exact
resulting Core and result type. Static inputs require no runtime inhabitants.

Preserve successful checker results under one-way extension. Under extension
in both directions, preserve the whole optional checker result, including
rejection. Do not require the tables themselves to be equal or duplicate-free.
The proof may transport successful evidence in each direction and inspect the
two optional results; no new source recursion or parser change is necessary.

Lift both laws through `LocalInputs.checkTypedLetReturnBody?` and the actual
body runner. One-way extension preserves the complete successful `(type, result)`
pair, not only completed values. Mutual extension preserves the complete Option.
Keep owner, body, ordered actual values, fuel and store fixed, including genuine
suspended states. No extra whole-typing or sufficient-fuel premise is needed
beyond the success premise for the one-way law or mutual extension for equality.

## Boundaries and validation

One-way extension does not preserve `none`: adding a previously unknown annotation
meaning can enable the same body with the same fixed inputs. Prepending a changed
meaning for an existing key is not semantic extension, even if every original
row remains present, and can turn an accepted prefix into rejection. Later hidden
duplicates may differ without changing first-match meanings. Preserve component
lists of qualified names rather than joining them into a single spelling.

Independent raw/cost judgments and the numerical source bound do not take a type
table; add no redundant transport API for them. Raw paths and positive bounds
still do not imply whole acceptance. No runtime-entry, parser, Core, Wire, call,
inference, default initialization or general binding-policy extension is made.

Use independent source and completely parsed consumers. Cover arbitrary-length
typed prefixes, arbitrary and nominal static types, actual opaque values,
noncommutative initializers, asymmetric branches and whole-source rejection.
Check same-fuel complete result/checkpoint equality and genuine resumption under
mutual extension, as well as exact Some preservation under one-way extension.
Include unknown-annotation repair, changed-head counterexamples, differing hidden
duplicates and distinct qualified component keys. Keep runtime values explicit.

Audit all public contracts and consumers, exact registration and standard axioms.
Run focused/aggregate builds, actual parsed execution, full tests, kernel
checks and acyclic dependency-direction checks. Keep proof files below 300 lines,
commits small, diagnostics paused and all scratch files inside the repository.
