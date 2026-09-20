# ADR-0342: Executable whole-program static-semantics spine

## Status

Implemented for the initial executable checking profile.  Explicit public
interfaces, type/trait/value imports and re-exports, rank-1 inference, bounded
trait evidence, minimum-cost overload selection after candidate-local literal
defaulting, source-arity-preserving per-argument coercion and bounded multi-step
shortest-path coercion are connected end to end.  A first monomorphic builtin
typed-source-to-Core bridge, rigid/generic specialization and finite direct-call
specialization worklist are also executable.  A restricted linker connects
complete acyclic direct-call plans to independently rechecked Core entries.
It statically discharges proof-only call-signature predicates after exact
requirement/evidence validation and forwards closed implementation witnesses
through nested constrained calls.  Trait and implementation method declarations
are retained in checked catalogs with exact signature conformance.  Narrow
runtime-evidence slices execute `BitNot<T>.bnot`, the strict arithmetic/bitwise
trait methods, `Eq<T>.eq` and `Ord<T>.gt` by selecting, checking and
capture-free inlining a ground implementation method specialization.  Generic
implementation bodies are checked under rigid parameters and closed from the
selected evidence goal through the existing source specializer.
Target-compatible
`!=`, `<`, `<=`, `>=`,
`&&`, `||` and `!` select ordinary `ne`, `lt`, `le`, `ge`, `and`, `or` and
`not` functions and reuse the direct-call specialization/linking path.  A
conversion slice validates each closed coercion edge by exact requirement
identity and executes the selected `Coerce<From, To>.coerce` method body for
direct-call arguments, forwarded generic evidence and call results.  A finite
detached linker now lets those selected methods call cataloged functions and
consume coherent trait-header or exact implementation-premise evidence through
the same policies.
Other runtime evidence, recursive or indirect source calls, automatic entry
discovery and a public source pipeline remain staged extensions.

## Context

The canonical syntax retains declarations, imports, generic parameters,
predicates, traits and impls, while the active frontend still consumes
caller-supplied monomorphic name tables.  Extending local expression adapters
does not establish a source-program type system.

The next milestone prioritizes one executable path across the whole static
semantics over theorem density.  Parser diagnostics and exhaustive edge-case
proofs remain useful, but they must not block an initial working checker.

## Decision

Add an independent source type-system layer instead of extending `Core.Ty`.
The layer provides:

1. deterministic whole-program declaration identities and environments;
2. source type-name resolution, including generic-parameter shadowing;
3. rigid type parameters, flexible inference variables, substitutions,
   schemes and instantiation;
4. occurs-checking first-order unification;
5. resolved trait predicates, impl rules, evidence and bounded tabled search;
6. overload selection, explicit coercion search and literal defaulting; and
7. an executable parser-to-program-checker entry point.

The implementation order is:

```text
program environment
  -> type-name resolution
  -> source types and schemes
  -> unification and impl-head matching
  -> trait evidence and tabled resolution
  -> overload/coercion/literal inference
  -> whole-program checking
```

`Core.Ty` remains the closed monomorphic runtime language.  A separate
specialization boundary projects fully solved source types and expressions to
Core.  This prevents source polymorphism from invalidating the existing Core
metatheory.

## Initial executable profile

The first profile is deliberately small but end to end:

- canonical parsed files and stable top-level declaration IDs;
- builtin and user-defined type constructors;
- rank-1 explicit polymorphism and ordinary let generalization where safe;
- functions, calls, lambdas, tuples, conditionals and the canonical operators;
- numeric literal constraints with a deterministic default;
- trait and impl predicates with finite evidence-producing search;
- direct-first, bounded shortest-path coercion over concrete intermediate
  types; and
- enough statement checking to validate ordinary function bodies.

Success, rejection and inconclusive search are distinct results.  No failed
selected overload or impl silently falls back after committing to an ambiguous
candidate.

## Deferred boundaries

The first profile may reject rather than guess for:

- cyclic aliases and polymorphic recursion;
- higher-rank or higher-kinded polymorphism;
- overlapping/default impl policy beyond explicit ambiguity;
- recursive trait cycles that need coinductive reasoning;
- generic or symbolic intermediate coercion paths and coercion cycles that need
  coinductive reasoning;
- general executable conversion terms outside the closed method-backed
  `Coerce<From, To>.coerce` profile;
- budget-exhausted specialization outcomes and every direct-call cycle;
- seed roots with unresolved assumptions, runtime evidence outside the narrow
  `BitNot<T>`, strict arithmetic/bitwise, `Eq<T>`, closed standard `Ord<T>` and
  `Coerce<From, To>` profiles, indirect calls and general impl-method execution
  at the Core-linking boundary;
- constructor/operator export selectors and the remaining module-reference
  edge cases;
- nested contract namespaces and every member-overload rule; and
- proof-level completeness for diagnostics and all negative edge cases.

These are explicit extensions of the executable profile, not permission to
return an unsound successful result.

## Verification policy

Every stage must compile and have executable positive and negative tests.
Small correspondence lemmas are added where they stabilize an API, but broad
soundness/completeness theorem families are postponed until the vertical path
is usable.  `sorry`, `admit`, authored axioms, `unsafe` and `native_decide`
remain forbidden.

ADR-0340's standalone generic grouped-conditional work remains compatible but
is not a prerequisite for this milestone.  Further grouped-depth frontend
expansion is paused while this whole-program path is built.

## Implemented boundary

The executable path now validates and parses every workspace module, assigns
stable declaration identities, constructs whole-program namespaces, resolves
source types and signatures, checks implementation heads and `where`
predicates, and infers the supported function-body fragment.  Successful
checking retains substitutions, normalized predicates and concrete trait
evidence.  Failed and depth/cycle/ambiguity-inconclusive trait searches remain
distinct results.  Resolved trait and implementation catalogs retain stable
trait, implementation and method identities.  Catalog construction rejects
duplicate, missing, extra and signature-incompatible implementation methods.

This delivery intentionally has a lower proof density than the preceding
parser and local-semantics slices.  Executable positive and negative tests fix
the vertical behavior; broad soundness/completeness theorem families and rare
negative cases are deferred.  Imports consume explicit fixed-point public
interfaces in the type, trait and value namespaces; overload sets, aliases,
hiding, local and remote re-exports, positive cycles, and public module-binding
traversal are executable.  The initial profile still retains its no-import and
explicit canonical-path compatibility fallbacks.  Source arity controls
per-argument fitting without flattening a tuple-valued argument.  Candidate-
local numeric defaulting and coercion counts select only minimum-cost overloads.
Expected-type mismatches prefer a direct coercion, then breadth-first search
ground intermediate types to the configured bound; a unique shortest path
retains ordered predicates and evidence, while equal shortest paths and depth
exhaustion are explicit errors.  Proxy values resolve their source type, and
mapping read indexes unify a key/value pair while checking the key through the
same expected-type/coercion boundary.  They remain type-checking-only forms.
Constructor/operator export selectors, the remaining advanced expressions and
statements, generic/symbolic coercion intermediates, general executable
conversion terms, unrestricted source specialization and general lowering to
`Core.Ty` are outside the completed profile; the ground specialization,
builtin tail-normal lowering and restricted acyclic linking slices below are
implemented.

The next internal boundary is an occurrence-addressed typed/resolved source IR.
As its first carrier step, every inferred trait or coercion obligation now gets
a function-local `RequirementId`.  Unsolved requirements retain that identity,
and finalization produces one ordered `SolvedRequirement` containing the same
identity, its normalized predicate and its matching evidence.  Speculative
overload candidates fork the immutable input state and only the selected state
is committed, so rejected candidates cannot consume IDs or leave gaps.  Small
preservation lemmas fix canonical allocation and ID-order preservation across
solving, while executable tests cover coercion paths, candidate rollback,
numeric finalization and repeated equal predicates.

The inference traversal now populates that additive carrier.  Declaration-
owned occurrence IDs distinguish expressions and statements; typed nodes
retain stable input, lambda and let binders, selected declaration
instantiations, requirement IDs and ordered coercion steps.  `ExpressionNode.type`
is authoritative after its output coercions: a nonempty path starts at its
first edge's source, composes exactly, and ends at the stored type.  Indirect
calls separately retain the bundled arguments' type before and after coercion
and their ordered edge path, rather than attaching that conversion to the call
result.  A final substitution closes every embedded type, scheme, predicate,
coercion endpoint and indirect bundle field without changing identities.
Generic declaration instantiation retains the exact rigid-parameter
substitution instead of only its applied body and predicates.

The inference state owns the declaration, monotone binder/occurrence
allocators and the typed-node table.  Scope exit restores only lexical
visibility, never allocation or accumulated semantic facts.  Direct and
indirect calls, operators, coercions and numeric defaulting return metadata to
the exact introducing occurrence.  Only the selected overload state is
committed, so rejected candidates cannot leak nodes, requirements or allocator
progress.  Checked functions expose the final substituted table as their typed
body.  End-to-end tests cover shadowing, generic selection, losing candidates,
ordered multi-step coercion and one-owner correspondence between attached and
solved requirements.  Broad transition-preservation and ownership-completeness
theorems remain deferred by the executable-first verification policy.

The carrier is semantic rather than a lossless parser trace.  Transparent
groups and qualified-name field chains in a selected direct callee normalize
to one declaration-reference node with the outer callee span.  Expected-type
coercions are attached at the fitting boundary: expected-driven transparent
descent may place one on the inner node, while later call-argument fitting
places it on the completed outer argument node.  Specialization and worklist
admission validate the exact endpoints and adjacency of every output path and
the separately stored indirect argument-bundle path before using the carrier.

The first Core consumer accepts a tail-normal statement profile over closed
builtin Unit/Bool/Word/product types.  Initialized lets, nested lexical blocks,
terminal conditionals with two returning branches and terminal returns compose
with local references, groups, tuples, builtin operators and expression
conditionals.  It follows typed occurrence edges into `Resolved.Expr`, lowers
stable local identities to an open positional Core context, and retains checked
equations for exact resolved lowering and the independently inferred Core
result type.  It has
explicit located failures for malformed carriers, overflow literals,
fallthrough, non-tail control statements and every staged type, coercion or
expression form.  Requirements reject unless a call-aware consumer reports an
exact discharge which is reconciled against the canonical solved-requirement
table.  Regressions run both conditional paths with
concrete inputs and stable-ID shadowing rather than stopping at structural
output.

The policy-bearing Core consumer now also owns coercion traversal.  It checks
that every path has non-identity edges, exact source/target continuity and an
endpoint equal to the node's authoritative post-coercion type.  Every step must
refer to an attached `RequirementId` exactly once; its policy must declare the
matching lowered Core endpoint types and consume exactly that ID.  Ordered
plans are then applied to the already lowered raw expression, and the function
still reconciles all consumed IDs once against its solved-requirement table.
The compatibility and standalone entries continue to reject coercions until a
whole-program consumer supplies such a policy.

The first rigid/generic specialization boundary uses the resolved signature's
complete parameter list to canonicalize exact ground call-site substitutions
into deterministic declaration/argument keys.  It closes every retained
typed-source, nested declaration-instantiation, requirement and recursive
evidence type while preserving semantic identities.  Phantom parameters remain
in the key; missing, duplicate, foreign, open or residual types and mismatched
evidence goals reject explicitly.  Call-free generic bodies specialized at
Word or Bool continue through the Core consumer and execute.  Local
let-polymorphism remains an explicit deferred boundary.

The finite specialization worklist now accepts raw seed requests and resolves
each one through exact declaration/signature/body lookup and the canonical
specialization function.  Plans preserve canonical seed roots in input order,
first-discovery FIFO specializations and every direct-call expression edge.
Discovery follows typed-node order.  Duplicate canonical keys do not consume
budget, so same-key recursion closes; type-growing polymorphic recursion exposes
a partial plan and the first unseen key at the finite bound.  Callee-reference,
instantiation, specialized type and predicate metadata are checked before an
edge is accepted.  Signature assumptions and solved evidence are retained for
the linker rather than discharged by planning, and indirect calls are an
explicit profile error.

The first specialized direct-call linker accepts only complete acyclic plans.
It reconstructs the worklist from canonical roots, checks canonical entries and
the exact per-occurrence edge list, and expands each direct call into
capture-free `Resolved.Expr` lets.  Arguments are evaluated left to right into
fresh temporaries before callee input aliases enter scope.  Every explicitly
seeded entry is then lowered and independently rechecked by `Core.infer?`, and
runtime entry checks require the exact argument-type sequence.  Seed order and
duplicates are preserved.  This is finite inlining rather than a named or
global recursive-function facility.

Call-signature predicates are proof-only in this executable fragment.  Every
call must account positionally for its exact requirement IDs; the linker
rejects duplicate IDs and validates the uniquely selected solved requirement's
predicate and evidence goal against the callee instantiation.  Closed
implementation evidence is forwarded into the callee.  A nested generic
caller's assumption marker is replaced only by a unique incoming implementation
witness for the same goal.  The validated call requirements are then consumed
statically and never become Core values or impl-method calls.

The runtime unary trait-evidence consumer is connected for `BitNot<T>.bnot`.
A required unary occurrence owns exactly one solved requirement, and any
assumption marker must resolve to a unique incoming closed implementation
witness.  The selected one-parameter trait, its sole `bnot` method and the
ground implementation specialization are signature-checked.  The operand is
recursively lowered at the declared Core type, and the checked body is
capture-free inlined.  The implementation body is
authoritative; a regression returning `91` distinguishes it from builtin Word
complement, while concrete Word `~` retains its evidence-free builtin path.

The runtime binary trait-evidence consumer is connected for strict arithmetic,
bitwise operators, equality and greater-than ordering.  A required occurrence
must carry exactly one
solved operator requirement whose closed implementation evidence agrees with
the typed occurrence.  The selected declaration must be a one-parameter trait
with exactly one non-generic method.  Its implementation may be generic only
when every declaration parameter is determined by the closed evidence goal;
the implementation has exactly one conforming predicate-free method.  The
generic checked body and all retained typed-IR/evidence positions are then
closed by `SourceSpecialization`.  Closed implementation-level
predicates must match the selected evidence premises positionally and are
retained as static method assumptions.  Closed predicates on the trait
declaration are instantiated from the evidence goal in
declaration-parameter order and become static assumptions of the synthetic
method signature.  They do not become premises of implementation search: the
standard `trait Ord<T> where T: Eq` header may therefore execute an
`Ord<Word>.gt` body which does not consume `Eq<Word>`, even when no separate Eq
implementation exists.  When the body consumes that assumption, the linker
resolves coherent closed evidence on demand; missing evidence rejects without
changing the unused-assumption case.  Its body is
checked against the instantiated two-operand signature and capture-free inlined
after the operands have been bound left to right.  `Add.add`, `Sub.sub`,
`Mul.mul`, `Div.div`, `Mod.mod`, `BitAnd.band`, `BitXor.bxor` and `BitOr.bor`
must return the operand type; `Eq.eq` and `Ord.gt` must return Bool.  The
implementation body, not a builtin operator
opcode, is authoritative; each regression returns a distinguishable non-builtin
result.

Before an implementation method is exposed, its complete closed evidence tree
is re-resolved against the current catalog at the standard finite depth and
must be structurally identical to the unique selected result.  Publicly
constructible evidence therefore cannot choose one side of an ambiguous catalog
or smuggle a different same-goal premise into execution.

The source checker follows the target's mixed operator dispatch table.  `!=`,
`<`, `<=`, `>=`, `&&`, `||` and unary `!` resolve visible ordinary functions
named `ne`, `lt`, `le`, `ge`, `and`, `or` and `not`.  The operator occurrence is recorded as an
ordinary direct call with a synthetic callee reference at the operator span,
so overload selection, signature predicates, argument and result coercions,
specialization edges and evidence forwarding use the existing call path.
Binary comparison/logical results must fit Bool before they are fitted to the
surrounding expected type; unary `not` instead receives that expected type
directly, matching the target.  A visible but inapplicable candidate is an
overload error; only complete
absence of the operator function enables the compatibility fallback to direct
Word/Bool builtins for source fixtures without a loaded standard prelude.

The first runtime coercion consumer is connected by the same rule: method
bodies, not endpoint types, define behavior.  One step must identify exactly
one solved requirement whose predicate and evidence goal are precisely
`Coerce<From, To>` for the typed edge.  An assumption is accepted only when a
unique matching closed implementation witness was forwarded into the current
generic specialization.  The selected trait has two parameters and the sole
method `coerce`; the implementation must have a ground specialization, its
predicates must be closed and backed by exact selected premises, and the method
must be predicate-free and signature-conforming.  The checked method must
lower from one `From` input to one `To` result before it is capture-free inlined.
Executable regressions cover a direct call-argument conversion, a conversion
inside a generic callee justified by forwarded evidence, and conversion of a
call result which also carries independent proof-only signature evidence.  A
Bool-to-Word fixture returns `41` or `7`, demonstrating that no hard-coded
endpoint conversion supplies the runtime result.

Budget-exhausted outcomes, direct-call cycles, seed roots with unresolved
assumptions, non-call/operator/literal requirements outside the supported
unary, binary and conversion profiles and indirect calls all reject explicitly.
Other evidence-dependent operators, underdetermined generic implementations,
multi-method traits and method-level `where`-constrained profiles are not
assigned an invented runtime meaning.
Selected implementation methods instead enter a finite detached linker.  It
reconstructs method-local direct-call metadata against the program catalog,
including callees absent from the top-level specialization plan, forwards exact
proof evidence, and recursively applies the supported unary, binary and
coercion policies.  Static trait-header assumptions are resolved only when a
body consumes them.  Cycles and expansion-fuel exhaustion reject explicitly,
as do nominal types with no `Core.Ty` projection.  The worklist can therefore close
same-key recursive graphs for finite planning without claiming they are
executable in the current Core.  Executable regressions cover proof-only
constrained and nested generic calls, both conditional paths,
method-authoritative `BitNot.bnot` and strict Word binary profiles, all three
conversion placements, an implementation-only direct-call helper, and an
`Ord.gt` → constrained Eq helper → `Eq.eq` chain.  Runtime input mismatches,
malformed plans and each principal staged boundary remain covered; small
checked laws retain the runtime input gate and budget result.

A further executable regression selects `Add<Word> where Word: Eq`, validates
its single Eq evidence premise against the implementation predicate in source
order, and makes the detached method consume that exact witness through a
generic helper.  The observed Word result is `92`, so this path also confirms
that the implementation body remains authoritative.

A generic companion selects `impl<T> Add<T> where T: Eq` at `T = Word`.  Its
canonical detached-link key retains the Word argument, the selected Eq premise
survives specialization and is consumed through the same helper, and an
identical trait-header witness is deduplicated.  Structurally different evidence
is never collapsed: a noncanonical root rejects, while a remaining conflict is
ambiguous when consumed.  A declaration parameter absent from the evidence-bearing
head remains open and is rejected explicitly rather than assigned an arbitrary
runtime type.
A separate generic `Ord<T>` fixture consumes only the trait-header `Eq<T>`
assumption, so generic body checking retains `Eq<T>` until specialization closes
it to `Eq<Word>`.

The next internal boundary is multi-method implementation shapes, method-level
predicates, generic arguments not represented by the current evidence language,
and additional runtime-evidence profiles.  Recursive calls require
a separate named or global recursive Core representation rather than cyclic
inlining.
Selection-bearing constructor,
member, match and assignment work follows the same carrier rather than
extending an information-losing result shape.  Whole-program consumers
identify an obligation by its owning declaration together with its
function-local ID.
