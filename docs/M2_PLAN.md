# Canonical syntax implementation plan

This plan covers the active source frontend. The old parser target is replaced
by the stabilized canonical syntax introduced by `solcore-rs` PR #20.

## Target and compatibility

The canonical frontend is implemented afresh under `Solcore/Syntax`. The
Surface v1 and Multi definitions are historical compatibility artifacts, not
constraints on the new AST, lexer, parser, or diagnostics.

Oracle v4 bytes remain unchanged. A future public source Oracle will use a new
additive version and will not reinterpret v4 requests or responses.

The pinned Rust implementation is migration evidence for accepted spelling,
grammar, recovery, comments, and byte spans. The accepted Lean definitions and
their declarative rules remain the formal specification authority.

## Implementation order

1. Define source identities, UTF-8 byte spans, the complete token catalog, and
   a source-preserving parsed AST.
2. Implement a total lexer with deterministic, accumulated lexical diagnostics.
3. Implement parsing for types, expressions, patterns, statements, inline Yul,
   declarations, and complete source files.
4. Port the relevant positive and negative fixture corpus from the pinned Rust
   revision and add focused span, comment, recovery, and Unicode cases.
5. Establish resource bounds, span validity, token provenance, and parser
   success soundness against a declarative grammar.
6. Expose one canonical Lean frontend umbrella after executable behavior and
   its initial provenance boundary are coherent.
7. Add name resolution, source type checking, and elaboration into checked
   Semantic Core as separate stages.

## Current executable coverage

### Active semantic priority

Further diagnostic-trace proof work is paused in favor of frontend semantics.
The first semantic slice, ADR-0154, introduces structured resolved declaration
and local identities, exact local-table lookup, and a monomorphic local
expression language. Independent typing and evaluation correspond in both
directions to a total Core elaborator and the existing Core checker/evaluator.
Closed typed expressions execute with sufficient fuel, preserve the store, and
cannot fault. Source spelling, fresh-ID allocation, name resolution, source
mutation, overloading, and staging remain outside this slice.

Type-independent scope validity is now equivalent to elaboration existence.
Injective resolved-ID renaming preserves exact Core output, checker results,
and named evaluation; a non-injective capture example fixes the limit of this
guarantee. A pure scope-relative allocator now supplies the premise for fresh
binding insertion. Lookup, typing, exact free-index weakening, and independent
evaluation are preserved, including under inner binders with the inserted ID.
For originally scoped expressions, insertion gives an exact evaluation equivalence;
the regression for a newly enabled reference protects the original-scoping premise.
These proofs do not implement a source declaration traversal or global allocator.

The explicit-ID ordered Word less-than foundation (ADR-0187) now builds two
existing resolved lets, proves exact Core expansion/Word typing and forward
evaluation, and reflects evaluation under original right scoping. The first
temporary is fresh for the outer scope and the two temporary IDs differ; the
second may reuse an outer binding and source inner shadowing is retained.
Exact continuation paths cost both children plus nine, with the weakened right
path explicitly supplied. Canonical `<` integration remains separate; the
restricted-Core insertion foundations below do not introduce hidden allocation
or change the existing resolver's identity-map contract.

The next prerequisite, exact untyped insertion for the local Core fragment
(ADR-0188), is proved independently of Resolved correspondence. A structural
predicate is closed under weakening and includes every currently
lowered resolved expression. Inserting an arbitrary runtime value behind any
retained prefix while shifting free indices preserves and reflects exact
evaluation values/stores, including under nested lets and for missing variables.
Typing, scope, freshness and runtime-world premises are unnecessary. Closure
creation/calls and cell access remain excluded even when a broader CellFree
judgment holds; returned existing values remain arbitrary. Exact-cost transport
and canonical `<` integration are still separate steps.

The static insertion counterpart (ADR-0189) now preserves and reflects exact
typing and proves equal executable inference results, including rejection.
Retained context prefixes extend with each actual let-bound type; arbitrary
data definitions and inserted/context types require no runtime inhabitants or
extra well-formedness premises. Explicit prefixes avoid the false unrestricted
reflection claim for a clamped, out-of-range `Context.insertAt`. Every written
conditional child still needs typing even if execution skips it. This is an
independent Core prerequisite, not exact-cost insertion or source `<` support.

Exact-cost insertion for the local Core fragment is now available (ADR-0190).
A common cost is selected before arbitrary continuations for the original and
shifted evaluation paths. Closed final paths transport and reflect at that
exact cost, with identical values/stores and unconsumed outer continuations.
The proof is Core-only and introduces neither a new cost relation nor extra
type, scope or runtime-world assumptions. Final-path uniqueness is used only
at empty-continuation final endpoints. Existing fuel and resumption laws can
be reused while genuine suspended states remain distinct. Canonical ordered
`<` integration remains a separate representation-and-adapter change.

Binary pairs now extend the initial eight-form local predicate to nine forms
(ADR-0228). Existing evaluation/typing insertion iff, complete inference equality
and exact path transport/reflection keep their names and premises. Left and
right children use the same original environment and ordered actual stores;
pair costs are their costs plus three. Shared child costs precede arbitrary
continuations, and each side retains its own pair frames and captured environment.
Independent proof and executable consumers cover nesting, retained prefixes,
opaque values, nominal static types without inhabitants, missing/wrong children
and real checkpoint resumption. Core semantics, projections, closure/cell
exclusions and wire policies do not change. Resolved pair representation follows
in ADR-0229, followed by canonical binary tuples in ADR-0230. Larger tuples,
tuple type syntax and projection spelling are not enabled by these steps.

Resolved binary products (ADR-0229) now lower both original children in the same
scope to ordered Core pairs, with independent product typing, whole-child scope
validity and actual-value/store evaluation. The affected modules' 54 generic
proof contracts retain their names and assumptions, including complete checker
and Core correspondence, store/determinism, structural renaming and semantic
transport, and fresh insertion/reflection. Rename identity/composition allow
arbitrary maps; lookup/lowering/evaluation transport retain existing injectivity.
Pairs introduce no binder or allocation condition, and a left-local let cannot
alter the right operand's scope. Nominal static/opaque raw and duplicate-ID
consumers retain the old raw/whole, suffix-fresh and original-scoping boundaries.
Independent ordered Core paths and checkpoints test cost and execution without
changing any runner. This prerequisite leaves source policy to the separate
adapter below and preserves frozen wire rejection.

Canonical two-element tuple expressions (ADR-0230) now resolve to ordered
binary products using the original children and spans, with both children in
the same caller scope/environment. Independent product typing, whole-name
avoidance, raw evaluation and exact costs extend the existing generic laws.
The direct evaluator returns the actual ordered pair and child costs plus three;
the source fuel bound uses the same additive composition. All 80 affected
public proof contracts keep their names/premises, including direct lookup
extensionality, store replay, safety, renaming and fresh insertion. The cost
renaming split retains the historical import path.

Independent source, fully parsed expression and complete-entry consumers cover
ordered/nested products, opaque actual values, nominal static types, exact
checkpoints/resumption and whole-versus-selected boundaries. True-and/false-or
still forward a raw pair while whole Boolean checking fails. Named product
aliases let existing recursive entries return pairs without tuple type syntax,
new argument layouts or broader header gates. Existing grouping/trailing commas
need no parser change, and the old binary-tuple negative becomes an independent
positive. Empty tuples follow separately in ADR-0231; manual-singleton/larger tuple expressions, tuple types,
projections and multiple returns remain outside the adapter; Core/resolved
semantics, diagnostics and frozen wire formats are unchanged.

Canonical empty tuple expressions (ADR-0231) now map to the existing Unit
constant through independent source resolution, typing, name avoidance and
raw/exact-cost rules. They require no name/context/environment lookup and keep
their original ranges and own store. Direct evaluation and the source bound
are exactly one, matching the existing Core transition. The expression proof
suite's 80 generic contracts retain their names and premises (56 contracts in
the 25 changed production modules).

Independent source, complete parsed expressions and function entries cover
nested Unit/products, arbitrary caller rows, same-typed wrong Core, all fuel
thresholds and genuine continuation resumption. Nullary Unit and ordered binary
pairs stay distinct; grouping adds no steps, and strict lets retain binding
costs. Selected raw short circuits need not be whole-typed. Omitted return
annotations and caller aliases admit Unit results, without reserving `Unit`
spelling or bypassing original header/unused-argument gates. The empty-expression
negative and old unsupported-arity consumer migrate explicitly; tuple types,
manual singleton/larger tuples, projections and empty/multiple return headers
remain unsupported. No Core/resolved, diagnostic or frozen wire change is made.

An opt-in structural type interpretation prerequisite (ADR-0232) now handles
named leaves and canonical zero/one/two-element tuple types. Independent meanings
give exact soundness/completeness, uniqueness and rejection; every recursive
child retains the same caller table and explicit product association. Type
singletons are interpreted from their original tuple nodes without rewriting.
The old named-only API and whole-type table membership contract stay intact.

Lookup-extensional equality, successful semantic extension and full equality
under mutual extension are proved without row uniqueness or inhabitation.
Independent source/parsed consumers cover ordering, aliases, hidden duplicates,
nominal types, invalid ranges, strict missing leaves and unsupported forms.
One-way extension may turn rejection into success, so no full-result invariant is claimed
for it. The prerequisite initially leaves parameter/header/let gates named-only;
the return/header integration follows separately in ADR-0233, parameters in
ADR-0234 and recursive lets in ADR-0235 below. Older prefix lets stay named-only.
Larger tuple types follow in ADR-0236. Other type forms, expressions, Core/resolved semantics, diagnostics and frozen
wire formats do not change.

Single structural return annotations now reach the existing compilation,
preparation and execution path (ADR-0233). The shared independent return rule
widens its annotation premise; all seven generic header/extension theorem
contracts remain unchanged. Explicit empty/multiple clause lists stay distinct
from a single Unit/product annotation. Absent returns still denote Unit, and
old named-only meanings remain usable through the compatibility proof.

Independent source/parsed entries cover exact ordered/nested Core, strict named
lets, conditional costs, nominal static types, opaque values, original parameter
records and all fuel/checkpoint boundaries. Legacy return negatives become
independent positives, with 110 affected source-test theorem headers unchanged.
Parameters are integrated separately in ADR-0234 and recursive lets in ADR-0235. Whole-body, type/arity, modifier,
unsupported-type and empty/multiple-clause gates remain. No new entry API,
runtime transition, expression, Core/resolved, diagnostic or frozen wire change
is introduced.

Structural parameter declarations and actual bindings now share the independent
annotation interpretation atomically (ADR-0234). Four constructor premises and
two position conclusions deliberately change meaning; general erase/restore,
factorization, ID/order/layout and named-specialization statements stay intact.
Original Unit/singleton/product parameters consume exactly one typed argument
each, including unused Unit and opaque products. Source and parsed consumers
retain arbitrary nominal static types, sparse mixed-owner allocation, original
positions, exact Core, costs, stores and checkpoints. Four parsed negatives migrate
to independent positives; one obsolete source rejection is explicitly renamed,
while 152 other affected source-test contracts remain unchanged. The old named-only
API, same-name rejection and other syntax/runtime boundaries are preserved.
Structural recursive let integration follows separately in ADR-0235.

Recursive typed let annotations now use the shared structural interpretation
(ADR-0235), with two independent binding premises and one decomposition conclusion
explicitly widened. Fifteen other affected generic statements remain unchanged;
old prefix successes still embed without claiming full optional equality. Mandatory
initializers stay strict in their old scope, fresh bindings extend only their tails,
and complete conditional-arm checking and owner allocation remain intact.
Independent arbitrary-depth source proofs and complete parsed entries retain
exact Core, original parameter records, nominal/opaque boundaries, strict unused
initializer costs, stores and actual resumptions. Three parsed declarations across
eight actual vectors become positives; 106 legacy source statements stay unchanged,
with one obsolete rejection explicitly moved to the old named-only/prefix boundary.
Raw evaluation, source bounds, Core transitions and all unrelated syntax, diagnostic
and wire policies do not change.

Every finite structural tuple-type list now has its original source-order,
right-associated meaning (ADR-0236). The existing four rules and 13 generic
contracts stay intact, with one new three-or-more-element rule and decreasing-size
interpretation/soundness. There is no implicit terminal Unit or flattening of
explicitly nested children. Original-span transport, caller first-match tables,
strict missing leaves, successful extension and full mutual-extension equality
retain their statements.
Independent arbitrary-length source and complete parsed consumers check exact
association, byte ranges, nominal static types, one parameter/one actual, and
existing entry Core, costs, stores and resumptions. Two parsed type rejections
and one static parameter rejection become positives, while the original Unit
actual's type mismatch remains. Two obsolete source contracts are explicitly
renamed and 26 others retained. Expression arity, projections, inference,
shadowing, old named-only membership, multiple-return clauses and all runtime,
parser, diagnostic and wire policies remain unchanged.

Canonical expression tuples now use the same right-associated convention
(ADR-0237), retaining original flat elements and both outer/delimited spans.
Five new independent rules cover three or more elements; empty Unit, binary
pairs and grouping remain unchanged, without implicit Unit tails or flattening.
All 80 affected generic contracts are preserved across static checking,
raw/Core semantics, safety, transport, exact costs, direct execution and bounds.
The typing proof split retains its original import path and theorem names.
Original-scope head/tail evaluation costs their sum plus three: three/four leaves
take nine/thirteen steps, and a strict unused four-element initializer plus return
takes sixteen. Independent arbitrary-length and parsed consumers retain exact
Core, original byte ranges, first matches, nominal/opaque boundaries, whole versus
selected checks, both stores and genuine checkpoint/residual execution.
Five old parsed rejections become positives; the obsolete generic arity boundary
is explicitly narrowed to manual singleton nodes and renamed, retaining its
named-only type conclusion and the other ten source statements. Projections,
inference, shadowing, multiple clauses, older prefix adapters, Core/Resolved,
parser, diagnostics and wire policies remain unchanged.

Initialized lets now support an absent original annotation through the existing
recursive checker and function entry (ADR-0238). The old-scope initializer fixes
its unique independent type and exact Core; the original tail receives the
existing fresh binding, without source rewriting or inferred-type table membership.
Four independent inferred rules keep every old annotated binding rule intact,
and all 53 directly affected generic statements remain unchanged. A new exact
child-decomposition theorem records the inferred type and original Core children.
Raw/direct evaluation, safety, owner/lookup/type extension, costs, stores, bounds
and genuine resumption retain their existing premises. Strict initialization
still costs initializer plus tail plus two, including when its value is unused.
Independent mixed-prefix and parsed consumers check annotation absence, original
ranges, sparse IDs, exact Core, nominal/opaque boundaries, actual parameter-only
records and checkpoints. Eleven old parsed rejection claims become independent
positives while older prefix rejection and neighboring invalid cases remain.
General inference, polymorphism, missing initialization, assignment, shadowing,
calls, Core/Resolved definitions, parser, diagnostics and wire policy are not added.

Exact frontend-to-local-fragment bridges now connect existing provenance to
Core positional insertion (ADR-0239). Four body-level results retain exact
expression lowering and all singleton, terminal-tree and recursive-let children;
four entry-level results project independent or successfully checked compilation
and preparation. No same-typed substitute or runtime inhabitant supplies the
structural proof, and body imports remain independent of entries. Independent
source and parsed consumers retain arbitrary inserted values/types, nested lets,
original parameter rows, nominal/opaque boundaries and exact path lengths.
Original and inserted suspended states are separate; each resumes with its own
captured environment. Membership alone implies neither evaluation nor valid
indices, source acceptance or provenance for arbitrary records. This proof-only
step changes no existing definition, generic statement or source policy.

Strict expression prefixes now use these insertion foundations (ADR-0240).
The existing recursive adapter accepts an original `.expression source true`
before an accepted terminal tail. Both source children use the same input scope;
exact Core uses `letE expressionCore (tailCore.weakenAt 0)` without allocating a
source LocalId or changing parameter records. Four discard rules keep all old
constructors and 58 affected generic statements intact, with one exact original
child-decomposition theorem. Typing and raw iff reuse insertion/reflection;
actual discarded values lift closed tail paths into arbitrary retained
continuations at unchanged costs. Head plus tail plus two counts strict work,
not optimized Rust transitions. Independent source/parsed consumers retain
mixed let/if scopes, nominal/opaque boundaries, exact Core and genuine residuals.
Four original parsed rejections become positives; narrower adapters and all
neighboring invalid forms remain. No unterminated prefix, missing terminal tail,
assignment, source call, general early return, parser or runtime-record policy
is added.

Terminal lexical wrappers now preserve their inner body's full semantics
(ADR-0241). An original singleton `.block statements` recurses with the inner
statement span and the same input scope. Four independent rules retain the
exact child Core, type, raw value, stores and cost; no hidden binder or extra
transition is introduced. The wrapper/child checker equality retains full
Option behavior, and all 59 directly affected generic statements remain intact.
Independent source/parsed consumers cover arbitrary finite wrapper depth,
mixed prefixes and both arms, original byte ranges and parameter records,
nominal/opaque boundaries, exact manual costs and genuine checkpoint residuals.
Six legacy parsed consumers migrate original block rejection fixtures without
changing their callers, including six buried nominal declarations. Narrower
adapters and neighboring rejections remain. Empty or
nonterminal blocks, implicit or general early returns, scope escape and
shadowing are not introduced. Core/Resolved, parser, diagnostics and runtime
records remain unchanged.

A separate static root-application prerequisite now handles exactly one original
argument to a known Function-typed callee (ADR-0243). Independent old-profile
child resolution, lowering and typing yield the exact ordered Core application;
whole-call typing and success/rejection correspondence require no runtime values.
This is the builtin Function arity-one specialization, not general Invokable
selection. Unit/products remain individual arguments without packing or implicit
Unit insertion. Old pure/body/entry adapters and every existing generic contract
remain unchanged. Nested calls, source lambdas, fields/global resolution and
entry integration are separate work. Local-fragment store/fuel guarantees do not
apply to the new Core application.

Independent actual source-call evaluation and exact costs now connect to that
static provenance (ADR-0244). Both original pure children use the caller scope;
the resulting actual closure supplies the body and captured values. The actual
argument precedes those captures, with all stores retained. Raw/cost erasure,
existence and uniqueness need no static or runtime typing; ordered ID alignment
gives exact Core evaluation and path correspondence in both directions.
Child costs plus the actual body cost plus three transitions work uniformly
under every continuation. Pending frames may still fault after the endpoint,
and actual bodies can have effects or different costs for the same source call.
Source-call evaluators and whole-entry integration remain separate work;
existing executable definitions and old generic contracts are unchanged.

Runtime-world safety now bridges the dynamic typing gap (ADR-0245). The actual
environment, including captures and referenced locations, and the actual store
are typed in one world. Whole source typing supplies a successful actual cost
and runtime-typed result/final store in an extending world. Exact elaboration
gives uniform continuation paths and closed fuel thresholds; raw evaluation and
checked completion preserve the result type under the same explicit premises.
Typed continuations additionally give all-fuel fault exclusion and preservation
through genuine checkpoints and resumption. These state-only results use
positional values; source correspondence separately retains ordered IDs.
The existing restricted Core payload/reducibility rules justify successful
execution, without a source-only bound, arbitrary-store guarantee, or any change
to executable definitions or old body/entry acceptance.

A separate checked local application runner is now implemented (ADR-0246).
The existing actual `LocalInputs` projections supply its static gate and Core
environment without new records. Only static rejection yields outer absence;
all checked machine outcomes retain their exact state and static result tag.
Independent whole typing plus raw evaluation characterizes completion at some fuel; actual
costs give exact fuel thresholds, and genuine checkpoints give residual paths
and full-result resumption, including faults. Same-world runtime typing of the
actual values and store separately establishes typed completion, a sufficient
actual cost and all-fuel fault exclusion. Missing/wrong-payload stores, delayed
closures, effects and unselected-branch rejection retain their distinct meanings.
Original parsed declarations use this local endpoint without enabling old pure
or whole-function entries. A direct source-call evaluator remains separate work;
later body/entry integration and opt-in runtime-world validation are described
below. There is no source-only bound or arbitrary-store safety claim.

An original singleton application return is now connected as a separate body
profile (ADR-0247). Independent whole typing, exact elaboration, raw evaluation
and actual costs retain the original child and both enclosing spans. Static
correspondence and raw/cost laws reuse the application proofs, including both
directions of closed Core correspondence and forward paths at one fixed cost
under every continuation. Complete child/body checker and runner equalities
preserve rejection, faults, tags and saved states at every fuel and store, with
zero extra Core transitions. Existing runtime-world and resumption guarantees
transfer through those equalities; fixed-fuel whole-body typed-cost reflection
does not assume successful evaluation from structural inputs alone. Old body and
whole-entry endpoints remain unchanged. General body integration is separate:
recursive discards also rely on local-fragment positional insertion, not just
store independence and source-only bounds. The new profile does not add bare or
pure returns, surrounding statements, nested blocks or nested calls.

The application-return profile now has separate whole-function compile,
prepare and run endpoints (ADR-0248). Independent new provenance retains the
original header, parameters and exact body at the declared return type while
reusing existing data-only records. Local success alone cannot open a whole
entry. Compilation remains value-free; actual preparation requires exactly the
supplied typed arguments. Success/rejection and record uniqueness are exact.
Preparation/compilation factorization includes failure and the ordered type/arity
guard. Full-result entry/body equality and compiled execution retain actual
values reversed once and the separately supplied store. Same-typed value swaps
can change preparation and results even with identical compiled projections.
Existing body costs, saved-state resumption and explicit runtime-world safety
transfer without new duplicate entry judgments. Old endpoint, record and lower
layer definitions remain unchanged; their stronger arbitrary-store/local-fragment
claims are not reused. General source calls, closure creation and recursive-body
integration remain separate work.

Checked application Core now has exact caller insertion laws (ADR-0249), using
the two original local child lowerings and leaving actual closure body/captures
unchanged. Arbitrary retained-prefix slots preserve and reflect raw evaluation
and typing; paired uniform paths and closed-path cost uniqueness retain the
exact successful cost, value and final store. Runtime caller contexts need not
equal source contexts, and inserted types need no inhabitants. Intermediate
frames/checkpoints are not equated, pending continuations are not executed by
the path theorem, and closure-producing children remain outside the premise.
These proof-only leaf laws support discard integration; the old pure fragment
and old executable body/entry contracts remain unchanged. The separate mixed
body below supplies its recursive closure argument and effect-aware semantics.

A common pure-or-root-application computation child is available (ADR-0250).
Its original-root dispatch, independent exact provenance and zero-overhead
raw/cost union preserve both older profiles unchanged. Eight common semantic
contracts and three insertion kernels support later mixed-body proofs without
duplicating checker/runner/safety aliases. Static typing remains separate from
actual runtime-world typing, skipped raw children remain skipped, and effects
retain both store endpoints. The union alone does not add whole-body acceptance
for call initializers, discards or guards. Nested call syntax and calls embedded
inside the pure profile are not added by the union.

A separate mixed recursive body integrates those child positions (ADR-0251).
Its seven static cases preserve original syntax and scopes; eight raw/cost cases
thread real stores and actual bound values through calls, lets, discards and
selected branches. A separate four-form caller fragment handles whole-tail
insertion under nested hidden binders without changing actual closure captures.
Checker/typing correspondence, Core typing, raw/Core equivalence, exact costs
and uniform continuation paths are proved independently. The old pure tree
embeds with unchanged Core/type, not its stronger store or source-bound laws.
This body feeds the separate original-header/actual-argument entry below;
existing pure/application entries stay unchanged. General nested call syntax,
source functions and arbitrary-store safety are outside this body profile.

Explicit mixed-computation function compilation, preparation and running are
available (ADR-0252). They preserve the original header/parameter policy and
declared-return gate, reuse data-only records and retain independent new whole
provenance. Four kernels cover exact-record Some iff and full-Option factoring
through compilation and the ordered argument-type guard. Actual running uses
the original arguments' values reversed once, not values inferred from erasure;
same-typed swaps, all faults and genuine checkpoints remain observable. Old pure
and singleton-application successes embed without changing their endpoints.
Body typing/cost and generic Core runtime-world safety/resumption are reused
directly instead of adding parallel wrapper families. Source-function resolution
remains separate; recursive expression calls are handled by the profile below.

Recursive local computation expressions are available separately (ADR-0253):
nested argument/callee calls and groups preserve the original AST and positional
scope, with independent static/raw/cost judgments. Exact execution laws retain
actual captures and ordered intermediate stores; recursive caller insertion
uses shared closed body paths without identifying intermediate checkpoints.
The fourteen-kernel interface embeds old computation successes unchanged and
does not broaden old pure, mixed-body or explicit-function endpoints.

Recursive children now integrate into a shared mixed-body engine (ADR-0254).
Separate child checker/typing/elaboration/raw/cost parameters preserve the
original syntax and concrete scope policy without copying a specialized proof
family. Twelve shared laws cover static, raw, exact Core/cost and whole-tail
insertion contracts; five operation/judgment specializations provide the concrete
recursive body, and two old-body elaboration/cost embeddings retain all indices.
The whole unit/leaf/let/if fragment handles hidden discard slots and actual
intermediate stores without runtime typing or world premises.

Shared explicit compilation/preparation/running now selects this body
(ADR-0255). Independent whole-record provenance uses child elaboration, while
operations use only the child checker. Two success-iff kernels need its checking
correspondence; preparation and actual-running factorization hold for arbitrary
checkers without semantic premises. The original header/return gates, ordered
argument count/types and actual values reversed once remain explicit, with full
fault/checkpoint outcomes and the separately supplied store. Five concrete
specializations reuse the four laws; old entry endpoints remain unchanged.

Ten direct Word binary roots now recurse through the same child (ADR-0256),
using an independent finite operator relation and one map-correspondence law.
The existing fourteen proof signatures and shared body/entry implementations
remain unchanged. Both children preserve original scope and exact Core; raw
execution retains left-to-right actual stores and child costs plus three.
Pure/binary overlap is resolved privately without global call-free premises,
and binary caller insertion retains literal observations and a shared cost.
Three old recursive addition rejection fixtures become exact independent
positive cases; older nonrecursive endpoints remain unchanged.

Conditional roots now recurse through the same child (ADR-0257). Original Bool
guard and both branch Cores/types are checked independently, while raw execution
uses only the actual guard and selected branch with their actual store flow and
costs plus two. Seven constructors extend the existing static/raw/cost and
caller-fragment relations without changing the fourteen proof signatures or
shared body/entry code. Private pure overlap, literal insertion, old rejection
boundaries and genuine saved branch-choice checkpoints remain explicit.
Static rejection of an unselected child does not rule out raw selected success.

Canonical Bool negation and Word complement now recurse through the same child
(ADR-0258). Original operands and prefix order retain fixed exact unary Core,
independent static/raw evidence, actual final stores and child cost plus two.
Nine constructors preserve the fourteen proof signatures and shared body/entry
code without adding operator-map or wrapper-law families. Old pure overlap,
caller insertion, genuine unaryApply checkpoints and faults after child effects
remain explicit. Only well-typed original rejection fixtures are promoted;
logical negation of a Word and old nonrecursive endpoint boundaries remain unchanged.

The fixed ADR-0159 conjunction/disjunction profile now supports recursive
children (ADR-0259), without claiming general Rust named-operator agreement.
Both original children require Bool statically; execution requires an actual
Bool on the left and either selects the right actual value/store at combined
child costs plus two or skips it at left cost plus three. Internal Bool literals
are not source lookups. Selected right payloads remain unrestricted, including
Word success under a declared Bool entry tag with an unchecked actual store.
Twelve constructors retain the fourteen recursive signatures and shared body/
entry code. Existing typing and continuation proofs move to smaller modules;
the caller fragment and insertion rules need no new constructors. Three original
rejections migrate with unchanged source and caller tables, while whole checking,
old endpoints, actual effects/faults and genuine ifBranches resumption stay explicit.

Fixed Word inequality and less-or-equal now recurse through the same child
(ADR-0260). Original Word children retain ordered equality/greater comparison
inside Bool negation, with actual left-to-right stores and child costs plus five.
Eight constructors preserve the fourteen signatures; private cost determinism
moves with its existing public theorem to a smaller module, retaining the old
import entry. Existing caller-fragment/insertion and shared body/entry code are
unchanged. The two original rejection fixtures retain their source and tables
as exact successes. Wrong actual left payloads do not suppress right effects
before comparison failure; comparison and negation checkpoints remain distinct.
General named ne/le resolution and Rust execution-cost agreement are not claimed.

Unsigned less and greater-or-equal now recurse through original Word children
(ADR-0261). Exact Core retains two ordered positional bindings and, for
greater-or-equal, an outer Bool negation; child costs add nine or eleven.
Generic recursive-caller letE membership and arbitrary-prefix insertion keep
actual bound values, captures, stores and one cost before every continuation.
The right child need not be call-free. Reverse execution removes its generated
insertion to recover the original source evaluation. Eight source constructors
and one fragment constructor preserve fourteen signatures. The cost judgment
is separately defined with its old import preserved; shared body/entry code
stays unchanged. Original rejection sources and caller tables migrate intact,
including generated-binding checkpoints and ordered effect/fault resumption.
This fixed Word profile does not implement general named lt/ge resolution.

Canonical tuples now use recursive children (ADR-0262). Original binary and
longer lists retain their caller scope, spans and right-associated shape, with
arbitrary component types and actual values. The unchanged synthetic-tail
decomposition adds no source rewrite or terminal Unit. Empty tuples stay pure;
canonical singleton parentheses are groups and manual singleton nodes remain
unsupported. Eight source constructors and generic caller pair membership
preserve fourteen proof contracts and unchanged shared body/entry definitions.
Actual stores flow left to right, each pair costs three transitions, and literal
insertion chooses one paired cost before all continuations. Six original
rejection fixtures migrate with identical sources and caller layouts; symbolic,
parsed and entry consumers retain exact pair frames, effects, strict child
faults and full resumption. No runtime component-typing premise is inferred.

Shared bodies and entries now connect to runtime-world safety through exactly
three generic proof kernels (ADR-0263). Same-world actual environment/store
typing plus original elaboration and existing child laws yield an extending
typed final world/value/store, original-source cost, uniform continuation-local
paths and exact closed fuel thresholds. Original runtime-typed arguments reach
the exact prepared environment through existing reverse-once layout, retaining
the full prepared record and every complete runner result. Structural argument
typing alone remains insufficient; these proof kernels add no validator or runner.
Typed pending frames separately give all-fuel no-fault and exact saved-state
typing/safe full resumption, without source-ID or child execution premises.
Checkpoint worlds remain existential; final evaluation exposes extension.
Symbolic/parsed/entry consumers retain actual effects, allocation, captures,
hidden discard slots, same-typed swaps and non-uniform actual callee costs.
All fourteen recursive, twelve shared body and four shared entry contracts,
empty nominal definitions, CellPayload limits and source acceptance are unchanged.

The explicit actual-input validator is now available separately (ADR-0264).
Its Bool result is equivalent to runtime typing of every original structurally
typed argument and full StoreHasTypes in the same supplied world. Actual
references in all captures/pairs/selected payloads are checked, while existing
structural evidence supplies closure body typing. World/store traversal requires
exact simultaneous exhaustion and checks every CellPayload/type row, including
unreferenced cells. The iff directly supplies ADR-0263's runtime premises without
changing original source preparation, actual records or any runner result.
No raw/JSON validator, inferred world, repair, extra signature well-formedness,
public helper or automatic entry guard is added.

Raw Core values now construct the existing structurally typed argument records
through one exact Option builder (ADR-0265). Its record iff preserves each
literal input and unique type, including original order under list traversal.
Actual closure bodies are checked in the actual captured-type context, and all
captures are checked even when unused. No extra signature/unselected-type
well-formedness is imposed; forged bodies, host values and constructed values
under empty definitions are rejected. Unallocated references remain structurally
accepted, with same-world/store validation still supplied separately by ADR-0264.
Original preparation, execution, actual stores, costs and checkpoints remain
unchanged; no JSON decoder, source closure profile or automatic guard is added.

Actual checkpoint worlds now extend the original supplied world (ADR-0266).
A single shared theorem uses original body typing, actual same-world inputs and
typed pending frames plus a genuine outOfFuel equation. It exposes the saved
store's extending world and a further extending world for every finite path from
that same checkpoint. Existing cell locations/types persist, while typed writes
may alter values and allocation appends types. Private world uniqueness and only
the allocation/write cases reuse existing state preservation. The old state and
no-fault kernel, all entry contracts and executable definitions remain unchanged;
equal-length separately typed stores or unrelated saved states are insufficient.

Terminal Word literal matches now use these shared contracts (ADR-0267).
One original statically Word scrutinee is evaluated once before an ordered case
selection, with a required default and all original bodies checked at a common
result type. Duplicate literals retain first-match priority, not a rejection
gate. Independent pattern/choice rules preserve source spans, order and actual
effects; no source binding or additional runner family is introduced.

One hidden Core let and ordered Word tests give actual scrutinee plus selected
body costs plus two and seven per visited test. Existing shared theorem
signatures, actual-value insertion, full fuel and genuine resumption contracts
remain intact. Empty cases deliberately perform no comparison, so raw non-Word
success there does not justify treating a non-Word comparison as a miss.
Symbolic arbitrary case counts and parsed effectful bodies protect those
boundaries. Binding/constructor patterns, source lambdas
and global function resolution remain separate work.

Original wildcard cases now share this same engine (ADR-0268). They preserve
case order and marker spans, choose the first reached body without binding or
comparison, and do not bypass the typing of any later case/default. Tagged
entries separate wildcard success from checker failure; the Core fold removes
only the already-checked unreachable tail. All shared typing, execution, cost,
insertion and runtime contracts retain their existing theorem signatures.

The scrutinee and hidden let remain unconditional. Only literal comparisons
contribute seven transitions each; wildcard contributes zero. Raw leading
wildcard success is distinct from a preceding non-Word comparison fault.
The formerly rejected parsed wildcard example is migrated with its original
header, owner, types, arguments and source location; independent source costs
and literal Core paths protect effects and genuine resumption. This initial
Word restriction is relaxed for catch-all-only matches in ADR-0271 below.

Original optional defaults now preserve this same body/entry pipeline (ADR-0269).
Static coverage requires a present original default or an original wildcard;
raw literal-hit success without either is not static acceptance. Every original
body is checked at the default's type, or at the first original case body's
type when no default exists. Arbitrary branch result types remain independent
of the scrutinee's Word type. The partial Core fold lets a wildcard recover an
unlowerable literal-only suffix without suppressing any static obligation or
inventing a fallback. One narrowly scoped checker decomposition supports the
unchanged shared 12, recursive-expression 14 and entry 4 theorem signatures.
Actual calls/captures/stores, arbitrary prefixes, nested scopes, full fuels and
genuine saved-state/world resumption are exercised independently of checking.

Grouped Word match patterns now use an independent recursive classification
(ADR-0270). Only original group nodes are transparent, including the parser's
singleton trailing-comma form; strict literal and wildcard leaves keep their
original meaning. All outer/inner spans and original cases/defaults remain
present. The total interpreter's exact iff, classification uniqueness and
unchanged Core fold preserve coverage, all-body checking and once-only effects.
Arbitrary group depth changes neither comparisons nor source/Core costs.
Parsed effectful and nested-scope consumers retain actual captures, stores and
genuine checkpoints. Binding/Boolean/constructor, tuple and comptime patterns
remain separate work; parentheses do not make an unsupported leaf acceptable.

Type-general catch-all matching now extends the same engine (ADR-0271).
Any existing child-profile type is accepted when every original case classifies
as a wildcard, including grouped cases and a default-only empty case list.
Scrutinee and common result types are independent. Compatibility and coverage
are separate: empty/no-default still fails, and an unreachable literal still
requires a Word scrutinee. All unselected bodies/defaults retain their checking
obligations. Classification uniqueness transports independent original-arm
typing to exact checked-row elaboration without assuming runtime success.

Only hidden-slot Core typing generalizes; the original fold, raw/cost rules,
captures and shared12/recursive14/entry4 contracts remain unchanged. Consumers
exercise arbitrary types/counts/actual payloads, real parsed Bool effects and
nested Bool/function hidden slots, every fuel outcome and genuine checkpoint
resumption with explicit same-world evidence. The three old Bool wildcard-only
rejections migrate with exact original source contexts. Nominal construction,
broader numeric patterns and global/constructor resolution are not implied.

Unary structural function annotations now extend the shared type interpreter
and independent meaning rules (ADR-0272). Keep exactly one original parameter;
an explicit Unit/product parameter is not zero/multiple source arguments.
Absent/empty returns mean Unit, singleton returns preserve their child, and
multiple returns use the existing right-associated tuple meaning under their
original delimiter span. Nested function types are allowed recursively without
normalizing the original AST or adding whole-function alias requirements.

All thirteen structural interpretation/extension contracts retain their
signatures. Existing parameter, recursive typed-let and single outer return gates inherit
the extension; the outer declaration's absent/single policy is unchanged.
Independent symbolic and parsed consumers retain old fixture contexts, lookup
priority, strict child failures and wrong actual argument rejection. Supplied
closure factories/writers exercise actual captures, allocation, writes, returned
closures, exact costs, all-fuel outcomes and genuine checkpoint/world extension.
No source lambda, call-arity expansion, global resolution or implicit runtime
world/inhabitant follows from function type meaning.

Scoped same-name lets now extend the shared body engine (ADR-0273), not the
older fresh-name body adapters. Typed and inferred initializers retain original
inputs, then prepend a fresh identity and their own type/actual value without
overwriting old rows. Repeated spellings, parameter shadowing and changed types
reuse the existing Core let and raw/cost rules; duplicate parameters stay invalid.

Preserve the pinned resolver boundary: bare if branches share sequential name
resolution, explicit blocks and match arms do not. Independent source occurrence
and Boolean exactness protect current input names from then-side exposed lets,
including nested unscoped else branches. Else-side shadowing is terminal-only;
then-only new names remain unavailable to Lean's else. This intentionally omits
some reference programs rather than asserting complete name-resolution agreement.

The shared12/recursive14/entry4 contracts and old one-way body embedding remain
intact. Consumers retain the exact three migrated source contexts, arbitrary
repeated-name proofs, actual captures/stores, old-name initializer lookup,
45-step effect paths, raw failures and genuine checkpoint/world resumption.
Further scope expansion must account for branch leakage and subsequent statements
explicitly; this change does not establish nonterminal block/if sequencing,
source lambdas, global resolution or automatic runtime-world validation.

Meaning-preserving type-name tables now transport shared body/function results
(ADR-0274): four body and eight entry laws retain original independent evidence,
exact Core, parameter IDs/order, complete actual preparations and all present
runner results. Every original branch is transported, including unreachable
match rows and conditional arms; scoped shadowing and nested unary-function /
ordered-tuple annotations need no new cases in executable code.

Keep the one-way/mutual distinction explicit. Append and fresh-key prepend
preserve successes; complete optional equality requires meaning preservation in
both directions, not equal row lists. Unknown-type repair can change rejection,
and a changed first-match prefix is not an extension. Fixed arbitrary child
operations need no new correctness premise for their operational equations;
independent judgments still have their own original-evidence transport proofs.
Actual capture/effect/fault and checkpoint consumers preserve the same values,
fuel and store, without an inferred world or runtime-safety claim. Old semantic
definitions, theorem signatures/bodies and consumer contexts remain unchanged.

Next extend recursive children to the remaining expression forms using these
shared contracts. Expected-type source lambdas and global function resolution
remain separate. The old stronger pure store/source-bound guarantees do not
transfer, and structural arguments alone do not validate stores.

The ordered Core comparison bridge now uses these prerequisites (ADR-0191).
Right-local membership alone supports exact typing inversion and raw ordered
evaluation equivalence for the original operands, with arbitrary left effects
and actual ordered stores. Original operand paths compose at their costs plus
nine using exact insertion internally. Both children must be local only when
establishing membership of the whole expansion. A stored-closure counterexample
retains the necessary right-side boundary. Existing Core comparison APIs remain
unchanged; dedicated resolved representation and the canonical source adapter
are the next distinct integration steps, without a hidden LocalId allocator.

The dedicated resolved representation is now implemented (ADR-0192): `wordLt`
lowers both original children in the same original scope and expands only into
positional Core lets. All existing independent typing, scope, evaluation,
lowering, checker, store, determinism, renaming and fresh-insertion/reflection
theorems include this form without stronger premises. Arbitrary structural maps
need no fresh allocation; semantic invariance still requires injectivity and
duplicate IDs retain first-match behavior. The Core expansion remains in the
local predicate. Raw skipped-child success does not excuse whole
scope/type rejection. Explicit-ID builders remain unchanged. Canonical source
`<` support and its negative-fixture migration are completed below in ADR-0193.

Canonical identifiers and grouping now have an exact explicit-table adapter
to typed resolved references and Core variables (ADR-0155). The name table does
not replace source scope construction. Execution correspondence retains exact
identity-order alignment between the type context and runtime environment.

An additive local-expression adapter now covers canonical conditional ASTs
(ADR-0156). Independent source typing requires a Boolean condition and equally
typed branches, and characterizes successful checked elaboration exactly.
Independent source evaluation selects just one branch, is deterministic and
store-preserving, and corresponds to resolved/Core evaluation under whole
resolution and runtime identity alignment. Typed aligned environments ensure
existence, type preservation, sufficient-fuel execution, and fault exclusion.
Literal interpretation, source declaration resolution, and general source
typing are not supplied by this explicit-table fragment.
Source-text regressions exercise the existing lexer/parser and execute the
returned checked Core, with exact branch selection, unchanged stores, and
fuel boundaries. The previous reference adapter embeds without changing its
checked results or value/store semantics.

The typed local-input bundle (ADR-0157) now constructs the three ordered tables
together with unique IDs and structural value typing. Its fresh insertion and
exact row lookup proofs support a checked runner without separate caller
alignment premises. The runner distinguishes failed checking from present fuel
exhaustion and has exact typed source-evaluation correspondence. This constructs
explicit inputs only, not source declarations or globally allocated identities.
Fresh insertion under a spelling unused by the entire supported expression now
preserves source type/evaluation in both directions, the exact checked type and
free-index shift (including check failures), and completed value/store results.
The premise covers both conditional branches and deliberately excludes
same-name shadowing; it does not assert equality of suspended machine states.

The canonical `!` constructor now uses the existing Boolean-negation primitive
(ADR-0158). Source typing, raw evaluation correspondence, typed execution, and
unused-name preservation include the new case. Non-Boolean operands are not
coerced. Parsed negated conditions and double negation exercise the returned
Core and exact execution bounds.

Canonical `&&` and `||` now expand to the existing short-circuit conditionals
(ADR-0159). Both operands must resolve and type-check as Boolean, but only a
selected right operand executes. Raw evaluation keeps the exact untyped
expansion meaning, including forwarding an ill-typed selected right value;
the checker rejects that case. Correspondence, safety, and unused-name laws
cover both operators. Tests protect generated constants from caller-name
capture and exercise parsed precedence and selected/skipped fuel bounds.

Frontend identity relabeling (ADR-0160) now lifts the resolved laws to unchanged
canonical source trees and typed input bundles. Resolution commutes with any
ID map; injective maps preserve exact checked Core/type and raw evaluation in
both directions. The bundled runner retains the whole result at identical
fuel, including failed checking and suspended states. This is not source-name
renaming, global allocation, or a claim about subsequent fresh-ID choices.

Canonical `~` now has fixed Word-only typing and direct Core complement
semantics (ADR-0161), reusing the existing 256-bit operation. Its source/Core
correspondence, typed execution, unused-name preservation, and ID-relabeling
laws are proved. Arbitrary Word/double-complement and exact fuel tests include
parsed source execution; Bool/reference coercion is not introduced.

Numeric spelling now has independent digit/positional natural-number semantics
and a sound/complete total decoder (ADR-0162). A separate strict Word projection
rejects values at or above `2^256` without modulo reduction. Whole ASCII spelling,
nonempty hexadecimal digits, both hex letter cases, arbitrary leading zeroes,
raw-payload validation, and span irrelevance are proved and tested, including
complete actual-source parsing. General source numeric typing and overload
policy are not inferred from this layer.

The existing monomorphic local-expression adapter now explicitly uses the
strict Word projection for literal leaves (ADR-0163). Independent resolution,
typing, evaluation, exact Core correspondence, safety, input insertion, and ID
relabeling proofs include constants. Actual parsed literal/complement/conditional
runs cover one/three/five-transition boundaries and preserve nonempty stores.
Invalid or overflowing literals still block whole checking, even when skipped;
Word operands do not satisfy Boolean requirements. The narrower reference-only
adapter and general source inference/overload policy remain unchanged.

Canonical `&`, `|`, and `^` also use fixed Word-only source semantics (ADR-0164).
Independent rules retain both operands and left-to-right evaluation through the
existing Core operations; raw value/store correspondence and all typing, safety,
input-extension, and ID-renaming guarantees are preserved. Unlike Boolean
short-circuit forms, masks never skip an invalid right operand. Parsed examples
check exact Core precedence/association, mask values, complement/conditional
composition, nonempty stores, and the four/five-transition exhaustion/completion
boundary. Arithmetic, comparison, assignment, and general overload policy remain
separate; no parser or Core-machine changes are needed.

Independent source costs now count the exact successful Core transitions for
the entire supported fragment (ADR-0165). Erasure, existence, positivity, and
joint value/store/cost uniqueness are proved without whole typing or resolution.
With whole resolution and runtime-order lowering, continuation-local Core paths
have exactly that cost; checked and bundled execution complete iff fuel is at
least that threshold and exhaust below it. Raw costs do not bypass whole
checking. Terminal detection is free; nonterminal path lengths do not supply
completion bounds. This is not a gas or frontend-time model and does not change
any executable behavior.

Cost derivations now preserve their exact index under injective ID relabeling
and unused-name fresh insertion (ADR-0166), including raw unresolved skipped
branches. A typed-cost characterization of exhaustion yields same-fuel
completion and exhaustion-presence invariance for input insertion. Old/new
suspended states are separate; fuel-zero environments can differ. Same-spelling
shadowing can retain the result but change the cost, protecting the avoidance
premise. Parsed observations exercise the stronger fuel boundary without
changing evaluation or source-name allocation.

Direct local-expression evaluation (ADR-0223) now follows original syntax and
explicit actual tables, returning the exact raw value and Core-transition cost
without checking, resolution, lowering or Core execution. Independent soundness
and completeness cover every existing raw constructor, with exact absence and
uncosted-value projection laws. General store correspondence retains the final
store equality. First-match duplicate/sparse/unaligned rows and untyped opaque
values remain legitimate raw inputs. Strict operands preserve their order and
existing overheads, including both operands for zero divisors; selected-only
conditions/short-circuit forms do not validate skipped syntax or impose extra
typing on the forwarded right value. Raw success is not whole acceptance.
Whole checking and ID alignment separately give exact checked Core paths and
fuel thresholds, while completed runs reflect the same computed cost. Typed
actual environments supply successful output; bundled runner equivalences retain
whole source typing. Retained-continuation endpoints do not guarantee completion.
Independent and complete parsed consumers retain raw/checked, literal, row-order,
opaque-value and actual-checkpoint boundaries. Existing APIs and language policies
stay fixed; direct recursive-body evaluation composes it separately in ADR-0224.

Explicit monomorphic type-name interpretation (ADR-0167) now supplies a first
bridge from canonical named/no-arguments types to caller-provided Core types.
Independent first-match rules and exact qualified component keys characterize
the executable adapter in both directions. Source ranges are irrelevant; no
normalization, implicit primitive names, type-argument interpretation, or
global type collection is added. Parsed known, unknown, and unsupported types
exercise this boundary independently of syntactic acceptance.

Runtime parameter input preparation (ADR-0168) now uses that bridge to construct
`LocalInputs` from canonical runtime parameters and explicitly typed arguments.
Independent paired binding specifies exact arity, annotation meaning, unused
spellings, and matching value/type rows; it is equivalent to executable success.
Source-order IDs, reversed table storage, per-position pairing, projections,
and unique names are proved. Actual parsed parameter lists and signatures feed
existing local-expression checking and execution without a new evaluator.
Comptime, generic/signature constraints, function calls and returns, external
argument validation, and global allocation are not inferred from this adapter.

Single-return body semantics (ADR-0169) now wrap bare or expression returns in
independent type/value/store/cost judgments. Checked bare returns produce Unit
in one Core transition; expression returns retain the exact child Core and fuel
behavior. Whole body checking, runtime correspondence, typed execution, and
fault exclusion are proved without inventing general return control. Parsed
parameters and actual declaration bodies exercise the composition; the body
endpoint deliberately does not check a declared return type or other signature
contracts.

A separate terminal-conditional body adapter (ADR-0195) accepts one explicit
`if/else` whose arms are existing singleton return bodies. The original Bool
condition and same-typed arms elaborate independently to exact Core `ifE`.
Raw selected-arm evaluation is separate from mandatory whole-arm checking.
Typing, exact simulation, store and cost determinism, safe checked execution,
all fuel thresholds, max-arm bounds and genuine-state resumption are proved.
No binding/identity allocation or extra return operation is introduced. Parsed
and independent consumers preserve actual typed arguments and test invalid
unselected arms, extra/nested statements and absent else. Existing singleton
body contracts remain unchanged; ADR-0198 below integrates the conditional
form into the separately checked whole-entry contract.

The nonrecursive `TerminalReturnBody` union (ADR-0196) provides a common body-only
interface for singleton and explicit-if/else profiles. Shape dispatch and the
independent two-case judgments add no Core nodes, values, stores or cost.
Typing/exact elaboration, raw and cost laws, exact continuation paths, all fuel
thresholds, source bounds and genuine-state resumption lift from the original
profiles. Full optional runner results are equal to the selected old runner,
including failure and suspended states. Parsed tests retain actual values and
original singleton behavior. The two conditional arms remain singleton bodies,
not recursive unions. ADR-0198 connected both shapes to whole entries; ADR-0208
extends those entries to recursive trees without changing this body-only union.

The body identity/store layer (ADR-0197) now gives injective exact-elaboration
transport and unconditional optional checker/full same-fuel runner equality for
single, conditional and terminal profiles. Raw/cost replay keeps value and cost
at arbitrary stores; completed observations and exhaustion presence retain each
store rather than equating entire results. Existing singleton map/replay laws
move unchanged out of runtime-owner/store modules into acyclic body-only modules,
with old-import availability retained. Noninjective lookup counterexamples remain
explicit. This layer itself does not change entries, input-shadowing policy or
accepted syntax; its acyclic imports allow the entry integration below.

The separate recursive `TerminalReturnTree` static adapter (ADR-0204) accepts
finite nested explicit if/else trees with singleton-return leaves. Structural
source-size recursion needs no fuel/depth limit. Independent source typing and
exact elaboration characterize all successful results, retain both whole arms
and ordered Core `ifE` nodes, and prove Core typing, exact uniqueness and failure
characterization without runtime values. Old successes embed exactly; complete
Option equality only applies to old singleton/one-level shapes. Deep positive
and negative parsed trees retain valid static parameters/header. The unchanged
old body-only checker still rejects deep trees, while ADR-0208 migrates valid
deep entry rejection to exact compilation success. The static unit itself
changed no existing acceptance or execution policy.

Recursive selected-path evaluation/cost semantics (ADR-0205) now retain each
condition and only its selected arm, exact stores and child costs plus two per
node. Raw/cost determinism, store preservation and cost erasure/existence/positivity
need no whole acceptance. Typed existence remains conditional on real aligned,
typed environments. Whole acceptance plus identity alignment alone characterizes
exact Core evaluation, even without runtime typing. Exact cost paths retain any
pending continuation unexecuted; no arbitrary-continuation inverse is asserted.
Old raw/cost profiles embed exactly without checking premises. Deep selected-path,
untyped-aligned and misaligned-ID consumers retain those distinct boundaries.
The separate tree runner, recursive bounds and genuine resumption now follow in
ADR-0206. The runner retains actual checked Core and existing ordered values;
exact result/failure and typed-cost fuel contracts preserve complete suspended
states. The recursive max-arm bound is only an upper bound: long/short paths may
cost seven/four with bound seven, while the old nonrecursive bound can be four.
Raw cost upper bounds require no whole typing; sufficient-fuel safety requires
actual runtime typing in addition to checking and ID alignment. Genuine states
retain exact residual paths and multi-chunk execution without resetting frames
or values. Old-shape full optional runtime equalities include failure and real
checkpoints. ADR-0207 adds body-level injective ID and arbitrary-store replay
invariance for recursive trees. Exact Core, type, whole optional checking and
same-store runner states survive injective relabeling without reordered values.
Raw value/cost replay needs no whole typing, while typed runner observations
retain each run's own store and relate exhaustion presence, not checkpoint
equality across stores. Deep skipped invalid subtrees still reject; noninjective
first-match collisions are outside the ID law. The body modules remain acyclic
and runtime-entry-independent. Existing function entries reuse these contracts
in ADR-0208 below; the old body-only adapters remain unchanged.

The separate typed-let-prefix static adapter (ADR-0209) adds finite outer
sequences of annotated, initialized, non-shadowing declarations before an
existing terminal tree. Initializers use the old scope and the exact annotated
type; only the tail sees the freshly prepended static binding. Independent
typing and exact provenance characterize total checking, exact nested Core
`letE`, Core typing, uniqueness and rejection without runtime inhabitants.
All written initializers and terminal branches are checked. Old tree successes
embed; whole Option equality only applies to old singleton return/if shapes.
The restrictions do not imply that omitted annotations/initializers or shadowing
are invalid source. This static unit adds no inference/default values, arm-local
prefix, execution, cost, runner or entry integration. Actual parsed static declarations
and arbitrary-length/type source proofs retain original order, binder positions,
whole failure and same-typed wrong-Core boundaries.

Independent typed-prefix evaluation/cost (ADR-0210) now complements that static
unit. Each initializer evaluates once in the old inputs, even when unused, and
the actual resulting value/fresh ID extends only the tail. Raw rules retain
stores and require neither whole acceptance nor annotation/name/type policy;
determinism, unchanged stores, cost erasure/existence/positivity/uniqueness are
independent of checking. Typed existence and preservation separately require
actual aligned, typed values. Accepted exact Core and aligned IDs alone give
evaluation iff and exact arbitrary-continuation paths using child costs plus two
per let. Names/ID projection identifies raw and static allocation without claiming
freshness in arbitrary inconsistent environments. Pending frames are retained,
not executed; bad frames can fault with zero fuel at the endpoint. Source and
parsed consumers retain strict unused initialization, old-scope positions,
opaque values, asymmetric terminal paths and raw-success/whole-rejection cases.
The checked prefix runner, bound and genuine resumption follow in ADR-0211;
ADR-0215 now integrates these contracts into the existing runtime entries.

The separate typed-prefix runner (ADR-0211) checks `toTypeInputs` with the caller's
type meanings/owner and executes the actual Core with original ordered values.
Full Option/Core-result laws distinguish check failure from fuel exhaustion.
Whole typing and independent costs characterize observations; real typed inputs
give exact thresholds and fault exclusion. A source-only additive prefix bound
delegates terminal trees to the recursive max-arm bound. It bounds raw costs
without checking, but neither positive nor zero budgets imply acceptance, and
rejected annotations or duplicate names may still have nonzero bounds. Actual
typing and whole checking remain necessary for sufficient-fuel safety.
Genuine checkpoints retain initializer frames, captured environments, actual
bound values and stores. Their exact residual costs are for closed body paths;
resumption preserves full results across multiple chunks, not restarted or
reconstructed states. Old singleton/if shapes preserve full optional results at
every fuel. Source and parsed consumers retain asymmetric path/bound differences,
unsupported zero/nonzero budgets and incorrect-checkpoint counterexamples.
This body-runner unit changes no tree/entry, parser, Core, call or broader binding policy.

Typed-prefix store replay (ADR-0212) now transports independent raw paths and
exact costs to arbitrary replacement stores, preserving each initializer's
actual value in the extended environment. The body, owner, names and original
runtime values stay fixed. No annotation meaning, checking, freshness or runtime
typing is needed for raw replay. Bidirectional laws retain final-store equality.
Typed body runners relate same-fuel done values with their own stores and
exhaustion presence, keeping whole checking. Complete results/checkpoints at
distinct stores are not equated; each genuine state is resumed separately.
This is not general Core or arbitrary-continuation store independence, and does
not extend source mutation, calls, inference, binding policy or runtime entries.

Typed-prefix owner covariance (ADR-0213) additionally relabels every input owner
and the supplied owner together under a global injective declaration map, leaving
binder indices and ordered types/values fixed. Fresh allocation commutes on any
mixed/sparse/repeated-ID scope, and value-free fresh binding needs no additional
index-equality or runtime-inhabitation premise. Exact elaboration and whole typing
transport; recursive checker equality preserves failures without surjectivity.
The checked wrapper keeps full optional results and genuine checkpoints equal
at fixed fuel/store. This does not equate the owner-bearing inputs, generalize
allocation to arbitrary index-changing/owner-collapsing maps, introduce raw/cost
owner transport or change parameter policies. ADR-0215 reuses it at runtime entries.

Typed-prefix type-name extension (ADR-0214) now transports annotation meanings
while keeping original inputs, initializer scope, fresh tails and exact Core/type
fixed. One-way semantic extension preserves successful checking and full runner
pairs, including actual checkpoints; mutual extension preserves complete Options.
Static nominal inputs require no values, and runtime values/fuel/stores are never
reconstructed or changed. Unknown annotation meanings can be added to enable a
previously rejected body, so one-way None preservation is not claimed. Keeping
old rows beneath an overriding head is not semantic extension, whereas differing
hidden duplicates can preserve all visible meanings. No redundant raw/cost/bound
transport or runtime-entry/inference/binding-policy extension is introduced.

Recursive typed-let tree static semantics (ADR-0216) now separately admits
arbitrary finite alternation of typed prefixes and terminal explicit if/else
inside either arm. Initializers use old inputs, tails use exact fresh extensions,
and both siblings restart from the same original scope, allowing independent
reuse of a fresh identity without name leakage. Whole syntax size justifies
total recursion even when a singleton conditional contains a long child body.
Independent typing/exact elaboration give success and rejection equivalences,
Core type preservation and uniqueness, without runtime inhabitants or a new
name-uniqueness premise. Old tree/prefix successes embed unchanged; singleton
return has full Option equality, but old branch-let failures may become successes.
Arbitrary-depth source proofs and complete parsed declarations exercise exact
Core, original parameter positions, same-ID siblings, ancestor visibility,
noncommutative initialization, qualified/first-match meanings and deep rejection.
Existing body adapters remain unchanged. Evaluation/cost
is supplied by ADR-0217 and separate body runner/fuel/resumption by ADR-0218.
ADR-0222 now supplies entry integration, without calls or broader policy.

Recursive typed-let evaluation/cost (ADR-0217) now evaluates strict initializers
in their old scope, extends tails with actual obtained values and follows only
the selected original-scope arm. Let and conditional costs are evaluated child
costs plus two; selected unused initialization is not erased. Independent raw
store/value/cost laws impose no annotation meaning, freshness or runtime typing.
Whole source typing with real aligned, typed environments separately proves
existence and preservation. Whole acceptance and ID alignment suffice for the
actual Core evaluation iff and exact-cost paths with arbitrary retained frames.
Those frames are neither executed nor unwound; a bad frame may fault at zero
remaining fuel. Old tree/prefix raw paths and costs embed unchanged. Source and
parsed consumers retain arbitrary depth, noncommutative/unused work, asymmetric
choices, opaque values, actual stores and raw rejection/ID/continuation contrasts.
No checker policy, entry, parser/Core/Wire change or fabricated inhabitants are
added in this evaluation unit; the separate body runner follows in ADR-0218.

Recursive body fuel/resumption (ADR-0218) now runs the exact checked Core with
actual ordered values and empty continuation. Known independent cost gives
exact Core fuel thresholds with only acceptance and aligned IDs; actual typed
inputs separately yield wrapper typing/cost thresholds and fault exclusion.
A syntax-size-recursive source bound adds initialized lets and uses maximum
recursive arms. It bounds raw costs without whole checking, but does not replace
acceptance or actual typed values for sufficient-fuel safety. New branch-local
work can exceed old tree/prefix bounds; rejected bodies can have positive bounds.
Genuine exhausted states give exact residual costs and full sum-fuel results,
retaining every captured value, environment, store and pending frame across
multiple chunks. Restarting or dropping frames is not resumption. Old runner
successes embed with complete same-fuel payloads; only singleton shapes preserve
the full Option without a success premise. Independent and parsed consumers
exercise depth, asymmetry, opaque values, rejected positive bounds and actual
initializer/conditional/tail checkpoints. No entry integration, old bound change,
owner transport or broader source policy is introduced; store replay follows
separately in ADR-0219.

Recursive body store replay (ADR-0219) preserves raw values and exact costs at
any replacement store without adding typing, checking, alignment, freshness or
store-validity premises. Strict initializers retain their obtained values and
fresh tail identities; only the selected original-scope arm replays. Bidirectional
raw/cost contracts retain the necessary original final-store equality. Checked
same-fuel done observations have the same type/value with each own store, while
out-of-fuel presence agrees without identifying complete results or checkpoints.
Each actual state resumes separately via ADR-0218. Source and parsed consumers
cover depth, asymmetric costs, opaque values, whole rejection, distinct stores
and genuine captured states. Pending loads provide an explicit boundary: retained
continuation endpoints do not imply store-independent continuation execution.
No new bound/resumption, old entry, parser/Core/Wire or policy extension;
owner covariance is treated separately in ADR-0220.

Recursive owner covariance (ADR-0220) preserves independent exact elaboration
and whole typing with unchanged source, type-name table, Core and type. A global
injective owner-only map keeps all indices, transports each fresh tail and starts
both sibling arms from the same mapped original inputs. Sparse mixed-owner
scopes and local sibling ID reuse follow the existing allocator. Full checker
Options, including rejection, are preserved without a surjective map or inverse.
For actual inputs, unchanged positional values give identical whole runner
results and genuine checkpoints at fixed fuel/store. Static nominal proofs need
no inhabitants; opaque actual values need no access or calls. Arbitrary index
changes and collapsing owners do not meet this contract. Existing raw/cost,
bound/resumption, owner helpers and outer-prefix function entries are unchanged.

Recursive type-name extension (ADR-0221) transports independent exact elaboration
and whole typing through every annotation and both original-scope arms. Fixed
source, owner, input bundles, Core/type and actual values preserve successful
complete checker/runner pairs under one-way first-match semantic extension.
Mutual extension retains full Options, including rejection and genuine suspended
states at the same fuel/store, without equal tables or unique keys. Unknown
annotations in unselected arms may instead be repaired by one-way extension.
Retained rows do not justify conflicting prepended meanings; qualified component
keys keep their existing interpretation. Independent and parsed consumers cover
depth, mixed annotations, nominal/opaque values, asymmetric unused work and real
checkpoint resumption. Old entries, body adapters, owner/allocator, raw/cost,
bound/resumption and parser/Core/Wire policies remain unchanged.

The explicit runtime entry (ADR-0170) now connects a restricted header's return
contract, typed parameter binding, and exact body elaboration. Independent
preparation characterizes success/failure and fixes the actual Core, while
whole-entry typing and source cost characterize checked execution at each fuel.
Absent returns mean Unit; one explicit named type is supported, but empty or
multiple return lists, generics, where clauses, and modifiers stay outside this
profile. Actual complete declarations exercise this boundary. Neither hand-built
prepared records nor arbitrary source functions receive unconditional safety.

Terminal entry integration (ADR-0198) initially connected the existing entry API
to the nonrecursive union. ADR-0208 extended that same compiler/preparer to the
recursive tree checker and exact provenance, typing and independent cost. Old
accepted Core/value/store/cost and complete same-fuel observations are retained.
The compiled/prepared layouts, header and complete parameter policies, actual
value order, factorization, owner/store invariance and genuine resumption remain
intact. Value-free compilation, parameter positions and type-table extension
need no runtime inhabitants. In that unit, only the three entry fuel-bound statements migrated
to `terminalReturnTreeFuelBound`; the old nonrecursive bound can be too small for
a deep selected path. Whole checking still covers unselected deep children.
Valid deep entry failures became exact successes; that profile still rejected missing else,
extra statements, nested-block wrappers, bad headers/arguments and mismatched arms.
Old body-only adapters and the absence of general source calls/early returns are
unchanged. Independent and parsed entry consumers retain exact source Core,
real arguments, asymmetric bounds and actual multi-chunk checkpoints.

Typed-prefix entry integration (ADR-0215) initially connected the same APIs to the
annotated, initialized, nonshadowing outer prefix followed by a terminal tree.
Compilation uses complete value-free inputs; preparation uses their exact actual
projection. Parameter-declaration uniqueness preserves that entire bundle across
same-typed arguments. Compiled/prepared records retain only original parameters,
not prefix locals, and direct Core execution retains the one reversed value list.
Whole provenance, declared returns, exact cost/typing/factorization, owner and
type-name transport, own-store replay and genuine resumption remain mandatory.
Only three generic theorem formulas change, to `typedLetReturnBodyFuelBound`:
the old tree bound is zero on a one-let body costing four. Body fields and the
cost constructor broaden explicitly. Independent arbitrary-length entry proofs
and parsed whole declarations cover exact positional Core, nominal types without
inhabitants, actual opaque values, strict unused work and real multi-chunk states.
Valid prefix entry failures migrate to exact success without changing old tree
rejection. Missing annotation/initializer, shadowing, self/forward references,
arm-local lets and all invalid whole contracts remained outside that adapter.
No parser/Core/Wire change, inference, defaults, general calls or binding policy.

Recursive typed-let entry integration (ADR-0222) connects the compiler,
preparer, whole typing and cost constructor to independent recursive judgments.
Both arms keep the same original scope; annotated, initialized, fresh-name lets
may alternate with terminal conditions at any finite depth. Original parameter-only
records, ordered actual-value reversal, header/argument/declared-return guards and
direct Core execution stay fixed. Erased parameter-bundle uniqueness transports
body typing across same-typed arguments without assuming nominal inhabitants.
Owner/type-name transport, exact provenance/factorization, own-store observations,
safety and real checkpoint resumption reuse the existing body contracts.
Only three generic fuel formulas change to `typedLetReturnTreeFuelBound`: a
branch-local let costs seven against the old prefix bound of four. Old body
adapters/bounds and prior accepted full results remain unchanged. Independent
arbitrary-depth proofs and parsed actual declarations cover exact positional Core,
strict noncommutative/unused work, asymmetric costs, opaque values and all-fuel
multi-chunk checkpoints. Valid arm-local rejections become exact successes;
missing annotations/initializers, shadowing, sibling leakage, mismatched returns,
bad headers/arguments and invalid unselected children rejected in that initial
profile. ADR-0238 additionally accepts initialized lets with absent annotations by
inferring their initializer type. ADR-0240 adds strict discard prefixes, and
ADR-0241 preserves the inner computation of singleton terminal block wrappers.
Other rejection boundaries remain, including nonterminal or empty blocks.
No general inference, defaults, general calls or broader binding policy is added.

Direct recursive-body evaluation (ADR-0224) now executes the existing raw typed
let/return-tree grammar on original blocks and actual explicit tables, composing
the direct expression evaluator. Strict old-scope initializers supply real values
to name-table-relative fresh tails; selected conditions retain the original scope.
Child costs add two per let/if, with bare return one and expression return unchanged.
Independent soundness/completeness, absence and uncosted projection laws retain
the necessary final-store equality. Annotation presence is a raw shape requirement,
not meaning/type/unused-name checking. Duplicate names and environment-only fresh
ID collisions preserve exact first-match behavior; omitted shapes or trailing
statements remain absent. Raw selected success can still fail whole checking.
Whole acceptance and ID alignment separately supply exact Core paths and fuel
thresholds; actual typed inputs provide existence, and completed runs reflect the
computed value/cost. Bundled laws retain whole typing and continuation endpoints
do not guarantee pending-frame completion. Independent and parsed depth, scope,
strict-unused, opaque-value and actual-checkpoint consumers preserve these boundaries.
Existing entry/checker/raw/bound/parser/Core/Wire policies are not changed.

Raw recursive-body owner covariance (ADR-0226) now preserves full optional direct
results and independent costed/uncosted raw paths under globally injective
owner-only maps, including non-surjective maps without inverses. Arbitrary
duplicate, sparse, unaligned and untyped caller rows are allowed: no static
input bundle, whole checking or runtime/store typing premise is inserted.
Original syntax, actual values, row order and binder indices are unchanged.
Syntax-size recursion composes expression-cost transport with name-table-relative
fresh allocation and actual strict initializer values; selected branches retain
their original scope. Both-store correspondence remains exact. Independent and
parsed consumers preserve raw/whole and genuine-absence distinctions, fresh-ID
environment collisions and opaque values. Owner collapse can change first-match
values, while an index-shift allocator counterexample is not mislabeled as a
raw-value counterexample. Existing evaluators, entry gates and typed owner-runner
contracts are unchanged.

Raw lookup-extensional semantics (ADR-0227) generalizes value/cost invariance to
equality of composed optional actual-value lookup for every spelling. Full
expression/body Options and costed/uncosted raw iff laws retain absence and both
stores, with independently chosen owners and no map, alignment, uniqueness or
typing premise. Each side's name-table-relative fresh ID implements the same
name update with the actual strict initializer value, despite different IDs or
environment-only collisions. Independent and parsed consumers retain missing-
versus-unbound names, untyped opaque values, genuine absence and raw/whole
distinctions. Allocation need not commute for raw results to agree. Changed
visible values can change results, and the new laws do not identify static
tables, compiled Core or store-bearing checkpoints. Existing definitions,
checked execution premises, entry gates and source-language policies are unchanged.

Direct checked entry evaluation (ADR-0225) now gates on unchanged runtime
preparation, then evaluates the original body with its actual parameter-only
names and values. The result is the declared type, value and exact transition
cost. Static preparation still lowers; the result is not obtained by running
Core, rebinding arguments or adding entry transitions. Two contracts suffice:
exact independent entry-cost correspondence with explicit final-store equality,
and absence iff preparation failure. Actual typed prepared inputs prove there
is no post-acceptance evaluation failure. Whole header/argument/return/body
checks remain mandatory even when raw selected body evaluation succeeds.
Independent and parsed consumers reuse established fuel, compiled-path,
store and checkpoint contracts through the new correspondence, preserving exact
source/Core/argument provenance and nominal/opaque boundaries. Existing entry
definitions, records and source policies are unchanged.

Arbitrary-position parameter semantics (ADR-0171) now connect source index `k`
to identity `(owner, k)`, exact Core position `n - 1 - k`, and the original
argument's type/value. Independent row layout, index bounds, and unique-name/ID
lookup proofs compose with source reference, singleton return, and a complete
matching entry contract. Exact zero/one fuel behavior is preserved. Parsed
regressions check all positions across several arities and mixed argument types;
no executable semantics or supported source form is changed by this proof layer.

Static argument invariance (ADR-0172) now proves independent parameter and entry
transport under an unchanged ordered type list. The executable preparation's
optional static projection is exactly equal, retaining failure as well as names,
context, identities, Core, and return type. Actual runtime values and costs may
differ; consumers and parsed declarations demonstrate that distinction. No
runtime argument decoder, unchecked-value shortcut, or new evaluator is added.

Owner invariance (ADR-0173) now transports independent parameter binding and
exact preparation while fixing binder indices. Swapping two declaration owners
gives optional Core/type/runtime-value equality and unconditional full same-fuel
runner equality, including suspended states. Fresh-ID correspondence is proved
along the existing allocation chain, not for arbitrary injective index changes.
The source declaration and typed argument values stay fixed; name/context/ID
tables are related by relabeling rather than directly equated.

Type-only parameter declarations (ADR-0174) now separate annotation meaning
from runtime argument supply. Static rows retain spelling, identity, and type
without value evidence; the independent declaration relation exactly matches
the executable adapter. Existing runtime binding erases to static declaration,
and an actual typed argument list reconstructs binding precisely when its
ordered types agree with the declared parameter context. No type-inhabitation
assumption, argument decoder, or new source policy is introduced.

Value-free layout and position laws (ADR-0201) now pair original parameters with
exact type-only rows and retain arbitrary initial rows under reverse-order
extension. Generated IDs start at the owner-relative fresh index, not initial
length; preservation of distinct names requires initial distinctness. Empty-start
source lookup at `k` proves its bound, identity `(owner, k)`, reversed row, name
and type lookup, and Core index `n - 1 - k`. Exact reference and singleton-return
elaboration use annotation meaning alone, including nominal types with no values.
Tests distinguish equal types from equal source positions, combine owner transport,
and retain sparse/mixed-owner, duplicate-initial-name and out-of-range boundaries.
Static parameter success is not whole-function acceptance; executable policies stay fixed.

Meaning-preserving type table extension (ADR-0203) now transports independent
annotation, return/header, general static declaration and compilation evidence.
The extension relation preserves first-match meanings, so right-appended duplicate
entries are safe while meaning-changing prefix shadowing is not. Fresh prepend
is sufficient but same-meaning duplicate prepend can also be safe. Exact successful
results and complete compiled records remain unchanged, including nominal types
without runtime inhabitants. Only mutual extension guarantees full Option equality;
one-way extension may turn unknown-type rejection into success. Qualified keys,
initial rows and generated IDs remain exact. Existing same-Core observation laws
connect already compiled entries without changing lookup or execution policy.

Actual-argument transport now completes this boundary directly (ADR-0242).
Independent binding retains arbitrary initial/final value-bearing rows and
original arguments, names, owner-relative identities and source order. Header
and recursive-body transport preserve the same complete prepared record and
whole-entry typing, not just its compiled projection. Exact successful binding,
preparation and run payloads survive one-way extension; mutual extension also
preserves all rejections. Whole outcomes include actual exhaustion states at
the same fuel/store and their genuine residual execution. Unknown meanings can
repair a one-way rejection, and changing first-match meanings or actual values
is not justified by equal row membership, types or compiled projections.
No executable definition, accepted syntax, runtime record or private binder changes.

Value-free restricted function compilation (ADR-0175) now combines these
static inputs with the existing header and exact return-body semantics. The
independent compilation relation characterizes the executable compiler and
proves typing for the actual open Core in its parameter context. Existing
runtime preparation factors into this compilation and an exact ordered type
guard, including arity and rejection; reconstruction uses only actual supplied
typed arguments. Parsed declarations and independent consumers preserve the
distinction between static success, argument availability, and runtime outcomes.
This is not closure generation, a source-call machine, or whole-program lookup.

Value-free owner invariance (ADR-0200) now transports static parameter declarations
and independent compilation directly, without runtime argument inhabitants.
Type-only rows support injective ID maps and exact projection/identity/composition
laws; relabeling commutes with erasure of actual supplied inputs. Owner transport
follows the empty-start fresh-ID chain and retains binder indices. Arbitrary owner
pairs have equal complete optional Core/return-type/context-type projections,
including failure, while their identity-bearing records may differ. Existing
owner helpers move unchanged into a shared module with old import availability.
Nominal static success, whole rejection, exact source order, allocator and forged
record counterexamples are covered without changing compilation or runtime policy.

Whole-entry positional compilation (ADR-0202) now lifts value-free reference
evidence to exact singleton parameter returns and terminal parameter selectors.
Forward proofs keep whole static declarations, annotation meanings, header and
body shape; executable corollaries retain exact records. Inverse contracts use
existing compilation provenance to recover the positional Core and return type.
Repeated arm indices and Bool guard/arm aliasing are valid, with no extra bounds
or distinctness assumptions. Nominal and repeated-type consumers reject equally
typed wrong Core trees and preserve whole-entry premises. These are proof profiles,
not new acceptance restrictions; the compiler and runtime policies are unchanged.

Exact execution factorization (ADR-0179) closes the next proof boundary without
adding another runner. The existing runtime endpoint equals value-free
compilation, the exact ordered argument-type guard, and Core execution with
the actual compiled tree and reversed supplied values. Equality includes
rejection and every full stateful result at every fuel, not just final values.
Independent entry costs produce exact paths and completion/exhaustion thresholds
for that same initial state; typed execution and no-fault require compilation
provenance and matching actual typed arguments. Cached-compilation regressions
cover different values at equal types, argument order/arity, unequal short-circuit
costs, and supplied closure/reference values without inventing inhabitants.

Compiled observation invariance (ADR-0180) compares independently compiled
declarations across source/type-table/owner differences. The same ordered type
context and exact Core imply the same return type, full runtime results for
all common actual arguments, and bidirectional independent cost evidence.
The proof preserves both-sided guard rejection and exact suspended states;
it does not infer Core equality from surface renaming or final-value agreement.
Counterexamples distinguish context/arity changes, adding zero, and substituting
different values with the same argument types. No new runner or relation is used.

Initial-store independence (ADR-0181) transports independent raw expression,
return-body, and checked entry cost evidence to arbitrary replacement stores
with the same value and exact cost. Fixed-fuel terminal/exhaustion observations
also agree for entries and proven compiled Core with matching actual arguments.
This does not equate store-carrying results or suspended states across stores,
nor apply to arbitrary Core reads/effects or execution of supplied closures.
Raw skipped-invalid-branch examples remain distinct from whole checked rejection;
parsed tests retain each empty/nonempty store and exact selected-path costs.

Source-derived fuel bounds (ADR-0182) supply computable sufficient Core budgets
for the current fragment and singleton return bodies, uniformly over actual
argument values. Independent costs are bounded by structural arithmetic and
branch maxima; complete typing/preparation then guarantees typed store-preserving
completion at every budget at least the bound, including proven compiled Core.
The bound may exceed the selected path's exact cost and does not grant acceptance
to unsupported syntax, invalid branches, or mismatched/uninhabited argument types.

Exact checkpoint resumption (ADR-0183) joins genuine Core fuel exhaustion with
source cost correspondence. Continuing the actual state agrees with one larger
run in its full result; a known terminal cost yields the exact residual path
and completion/exhaustion thresholds at `cost - spent`. Checked local/body/entry
endpoints and proven compiled paths retain their original contracts, actual
frames, values, and stores. No new runner or host-response protocol is added.
Parsed multi-chunk tests distinguish resumption from discarding a pending frame.

Binary Word addition (ADR-0176) now extends the expression fragment through
existing body, entry, and value-free compilation bridges. Its independent
rules require two Word operands, preserve strict left-to-right evaluation,
and use the existing modulo-`2^256` sum. Exact Core retains the addition node,
and cost is both child costs plus three. Literal range checking, whole-branch
checking, identity transport, and unused-input invariance remain intact.
Parsed regressions distinguish wrapping arithmetic from overflowing literal
rejection and preserve canonical grouping/precedence and exact fuel boundaries.
Word subtraction and multiplication (ADR-0177) extend the same monomorphic
rules and generic bridges with existing modular Core operations. Ordered source
trees, two strict Word operands, intermediate stores, and child costs plus three
are retained; all typing, safety, exact-fuel, renaming, and unused-input proofs
cover both forms. Independent consumers and fully parsed position-pair tests
distinguish noncommutative subtraction, grouping and multiplication precedence,
operation wrap from literal rejection, and pending frames from terminal values.
The fresh-input typing/evaluation proof split preserves existing public APIs.
Unsigned Word greater-than (ADR-0178) now connects computed Words to Boolean
conditions through the direct ordered `wordGt` node. Independent typing requires
Word operands and a Bool result; evaluation and cost retain strict store order
and both child costs plus three. Generic safety, correspondence, invariance,
value-free compilation, and runtime entry proofs include the form. Consumers
verify unsigned boundaries, equality, exact pending frames, declared Bool results,
wrong Word returns, computed-guard branch costs, and all tested parameter pairs.
Source shape laws are split without changing their public contracts/import path.
Word equality `==` (ADR-0184) extends the same strict ordered Word-to-Bool rules
using direct `wordEq`, not polymorphic equality or Word-valued flags. All generic
proofs now cover equality, including store replay, structural fuel bounds, and
genuine-checkpoint residual paths. Independent and parsed consumers retain
actual argument/operand order despite symmetric final values, exact fuel-four
frames and five-step results, declaration return contracts, and whole rejection
of non-Word operands or invalid unselected branches. Evaluation rules are split
from determinism while preserving old names and the historical import boundary.
Word inequality `!=` (ADR-0185) is ordered `boolNot(wordEq(left, right))` with
Word-only operands, a Bool result and both child costs plus five. The exact
nested Core shape, two distinct pending frames at fuels five/six, completion at
seven, and resumption from either genuine checkpoint are retained. All generic
static and dynamic proofs include this derived form; source bounds account for
the extra negation, and whole entry contracts are unchanged. Cost erasure and
cost determinism are split while keeping existing names and imports available.
Unsigned Word `<=` (ADR-0186) uses ordered `boolNot(wordGt(left, right))` with
the same child costs plus five, preserved fuel-five/six checkpoints, and seven
transitions for leaves. Equal operands return true; unsigned order and actual
argument positions remain explicit. Independent typing/evaluation reflection
peels both nodes and generic cost, store, fuel-bound, resumption and entry proofs
cover the form. Relational precedence stays above equality and non-associative;
mixed parsed forms still obey Word-only comparison/equality operand types.
Unsigned Word `<` (ADR-0193) now uses the dedicated identity-free resolved form
and the existing ordered two-let Core expansion. No temporary LocalIds are
allocated; original operand order and arbitrary structural-map laws are retained.
Independent source typing requires two Words and returns Bool; raw evaluation
returns unsigned `decide (leftWord < rightWord)`. Cost and structural bounds add
nine, with eleven-step leaves and genuine two/five/ten checkpoints retaining
nine/six/one remaining steps. All generic static, dynamic, store, extension,
resumption and compiled-entry contracts include the new form. Parsed arithmetic,
conditional and Bool-returning entry tests retain actual arguments and provenance.
Six obsolete `<` rejection fixtures were migrated without changing precedence
or parser rejection of chained comparisons.
Unsigned Word `>=` (ADR-0194) resolves to `boolNot(wordLt(left, right))` under
the original table, retaining the ordered two-let lowering and all generic
contracts. Independent source semantics returns `!(decide (leftWord < rightWord))`;
Word operands and Bool result are mandatory, with equality true. Costs/bounds
add eleven, giving thirteen-step leaves. Actual checkpoints at three/six/eleven/
twelve have ten/seven/two/one transitions left; the last retains the less-than
Boolean and pending negation. Independent and parsed consumers cover actual
arguments, exact resumption, short-circuit/arithmetic composition and own entry
provenance. Seven obsolete `>=` rejections are removed without changing
chained-comparison parser rejection.

Unsigned Word division and remainder (ADR-0199) now map canonical `/` and `%`
directly to the ordered existing `wordDiv` and `wordMod` nodes. Two Word operands
and a Word result use `Word.udiv`/`Word.umod`, including zero for both zero-divisor
cases. Evaluation always visits both operands once, left before right; exact
cost and source bound are the child costs/bounds plus three, or five for leaves.
Every existing static/dynamic and identity/input/store/fuel/resumption theorem
extends without new premises. Integrated terminal entries retain exact compiled
Core, actual ordered arguments and independent provenance. Tests distinguish
quotient/remainder and operand order, cover zero/high-bit/max values and actual
checkpoints, and migrate obsolete unsupported-operator negatives while retaining
non-Word, call and invalid-arm rejection. Structural bounds also change for some
still-ill-typed expressions. Unary signs, assignment and general overload policy
remain separate; Core/Resolved definitions, parsing and frozen interfaces do not change.

Further frontend semantics should preserve exact identity, binding, and Core
execution correspondence while extending supported expressions and declarations.
General calls and control flow remain separate. The resolved immutable expression
binder must not be treated as a decision about mutable source declarations.

### Source-to-AST coverage

The source-to-AST path is operational and public as a Lean library. It
includes:

- the total public lexer and parser result;
- source-identity and exact full-file-span provenance;
- the Rust-compatible delimiter and conditional nesting guard;
- leading-comment attachment;
- the complete declaration and type grammar;
- expressions, patterns, statements, blocks, and inline Yul;
- deterministic recovery and diagnostic filtering;
- all 23 pinned dedicated positive fixtures plus focused negative cases; and
- explicit rejection of representative spellings from the replaced grammar.

The external fixed-revision comparison audit also accepts all 490 upstream
`corpus/ok` sources without lexical or parse diagnostics and found no
source-AST gap. The four diagnostic-cardinality differences are frozen by
exact malformed-fixture regressions and preserve the same rejection/recovery
behavior.

Source and full-file-span provenance and exact lexer-carrier retention are
complete. The public lexer is proved total and always returns a `LexedFile`
whose tokens and comments are nonempty, source ordered, nonoverlapping, and
valid at UTF-8 byte boundaries; its lexical diagnostics also have valid source
spans. Exact-prefix scanner proofs and the strict decrease of the unconsumed
suffix establish this contract for every lexer branch and rule out the
exceptional fuel result.

Parser preflight accepts exactly the lexer results satisfying that contract,
and every public lexer result passes preflight. Any public parser error
therefore occurs only after successful lexing and preflight. Parser state,
primitive consumers, carrier-preservation rules, and cursor/order laws now
support compositional proofs for names, selectors, literals, delimiters,
pragmas, derive attributes, Core blocks, the complete recursive type parser,
complete function signatures, and the public Yul expression, statement, and
body parsers. The generic Core block proof now lifts any valid,
token-preserving statement parser. Complete imports, exports, type aliases,
and enums have source-validity, token-window, carrier, cursor, and
start-position contracts.
Function declarations, constructors, fallback entries, and implementations now
reach the canonical boundary through the unconditional public Core block
contract. Trait methods, bodies, and complete trait declarations have full
source and state contracts. Contract fields and optional initializers also have
complete source and state contracts.
Individual trait predicates have reached the same boundary. Named parameters
preserve provenance through recovery, and their delimited function-parameter
list has the complete compositional boundary. Public lambda parameters also
have complete source, token-window, carrier, cursor, and starting-token
contracts.

The public lexer and parser are now total. For every `SourceFile`, public
parsing returns an ordinary output; neither fuel exhaustion nor an internal
parser invariant is reachable. Ordinary malformed input stays inside the same
output type and is represented by source-located diagnostics and recovery
nodes.

This result is assembled from the production parsers rather than assumed at
the outer API. It covers recursive types, expressions, patterns, statements,
Core blocks, inline Yul, all declaration forms, contract members, derive
handling, recovery, and complete-file accumulation. The corresponding proofs
also preserve the immutable token carrier, source ownership, cursor order, and
valid UTF-8 spans.

Every successful public result has one complete provenance contract covering
the parsed file, tokens, nested comments, lexical diagnostics, and parse
diagnostics. All carriers refer to the same input file, and the parsed file
retains its exact full-file span.

The independent declarative grammar now covers pragma declarations, maximal
dotted qualified names, local and `@`-prefixed external module paths, and
identifier or parenthesized-operator selector names. Shared declarative rules
and parser-soundness theorems also cover nonempty comma-separated lists with
an optional trailing comma, selected import names and aliases, nonempty
selected-import lists, hiding clauses, optional hiding dispatch, and both
allow-empty delimiter policies. Export coverage additionally includes
nonempty lists without trailing commas, constructor selections, prioritized
export names, local export items, and remote selections. Derive targets and
normal `#[derive(...)]` attributes now have exact parser-independent grammars;
the public attribute theorem uses diagnostic freedom only to exclude recovery.

All four generic delimiter policies now lift an exact nested outcome contract:
required or allow-empty, each with or without a trailing comma. Their tails fix
written element order, closing span, and final remainder; whole lists fix the
complete `DelimitedList` value; and rejection fixes the first failing endpoint.
The constructors are public and compile-time consumed, while concrete callers
still need to establish exactness for their own nested production.

Prioritized transactional fallback now lifts exact contracts for both branches
to one exact successful value/remainder and one original-input double-rejection
endpoint. Primary success excludes fallback selection. The generic constructor
is exported and compile-time consumed; concrete uses remain conditional on
exact primary and fallback outcomes.

Shared generic parameters now have an exact nonempty `<...>` grammar with an
optional trailing comma. Required-list rejection records the exact delimiter
or nested checked-identifier failure. `requireGenericParameters` adds no
reject branch; its defensive empty-list invariant is unreachable after a
successful required-list parse. The optional judgment makes an absent `<` a
nonconsuming success, while a present guard commits from the original input
and retains positive evidence for that `<`. Required and optional success
endpoints are deterministic and each is exclusive with exact rejection. Both
parsers also retain unconditional success soundness and compose with their
established source-validity contracts.

Algebraic enum declarations now have complete ordinary success and
first-rejecting-stage coverage from the contextual `enum` marker through the
closing brace.
A leading `(` commits constructor payload parsing; payloads may be empty but
cannot have a trailing comma. The custom body loop is reflected into the exact
allow-empty, allow-trailing delimited relation while preserving constructor
order and every rejecting remainder. Full declarations distinguish marker,
name, optional-generic, and body rejection. Constructor, body, and declaration
success endpoints are deterministic and success/rejection exclusive. Stronger
exact contracts now unconditionally fix constructor and body ASTs, final
remainders, and rejection endpoints. The full declaration has the same exact
contract for each fixed supplied derive attribute. Declarative and executable
APIs expose these laws without claiming equality across different attributes.
A supplied derive attribute consumes no input, remains in the AST, and supplies
the outer span start; source validity still composes with its existing
contract.

Recursive type expressions now have exact mutual declarative judgments for
named, mapping, comptime, proxy, tuple, and function forms. The concrete
recursive delimiter rules retain empty and nonempty lists, optional trailing
commas, optional nonempty named arguments and function returns, exact token
windows, and source element order. Named-type derivations explicitly retain
the failed `comptime<` and `mapping(` pair lookaheads that select the dispatcher
branch. Both the fuel-bounded parser and the public recursive type parser have
unconditional success soundness, with source validity available by
composition. Exact recursive outcomes are now complete as well: successful
derivations fix the full `TypeExpr` AST and final remainder, while rejection
fixes its first failing endpoint at fixed fuel and at the public boundary.
Recursive list tails, complete delimited lists, optional named arguments, and
optional function returns have public exact composite theorems.

Transparent aliases now have an exact grammar for their keyword, name,
prioritized optional parameter list that may be empty and may have a trailing
comma, equals sign, recursive value type, and semicolon. Diagnostic freedom is
used only to rule out the executable alias-value recovery branch; ordinary
recursive type success is already unconditional. Recursive type, shared
generic-parameter, type-alias, and enum-declaration theorem families have
compile-time consumers and public `Solcore.Syntax` registration. The full
build and `lake test` pass with those registrations.

Type-alias exactness is now complete. Optional alias parameters fix the
complete optional identifier-list AST, final remainder, and rejection
endpoint, while malformed RHS recovery fixes its error type and nonconsuming
endpoint. The completed Core `TypeExpr` exact contract makes recovery-aware
alias values unconditional and lifts through the full declaration sequence,
so complete alias ASTs, final remainders, and all six first-failure stages are
unique. Parser reflection and both dedicated and public-boundary consumers
compile against these APIs; diagnostic and failure payload equality is not
claimed.

Backward diagnostic reflection now provides the reusable bridge needed by
strict diagnostic-free grammars: diagnostic-free successful output implies a
diagnostic-free parser input. The laws cover pure parsing, sequencing,
transactional choice, primitive token consumers, and delimiter policies, and
are instantiated through recursive types, parameters, predicates and their
sequences, optional `where`, generic parameters, modifiers, and return
clauses. Named-parameter recovery and missing-type errors separately prove
that every successful error path commits a diagnostic.

Typed named parameters now have an exact `FunctionParameterParses` grammar for
ordinary and contextual `comptime` forms. The ordinary constructor records
the absence of the composite `comptime`-identifier prefix, and
`FunctionParametersParses` lifts the element grammar to a possibly empty,
optionally trailing-comma parenthesized list. Diagnostic freedom excludes
parameter error and recovery nodes, yielding strict element and list
soundness with source-validity compositions.

The single public `namedParameter` now also has a broad ordinary-outcome
relation. A missing colon is a diagnosed `.error` Core success at the post-name
remainder, not recovery. Only a Core rejection rewinds to the original cursor:
end, comma, or right parenthesis gives exact nonconsuming rejection; otherwise
the parser emits the failure diagnostic and performs its mandatory-first-token
maximal recovery scan. A carrier hole is reflected as recovery rejection.
Success endpoints are deterministic and exclusive with rejection, while the
strict `FunctionParameterParses` relation remains diagnostic-free. Recovery
scan exactness, Core `TypeExpr` exactness, and the public recovery wrapper now
compose to a full exact named-parameter contract: the AST and final remainder
of success and the endpoint of rejection are unique.

The canonical `TypeExpr` and recovery-aware `namedParameter` outcomes now lift
to the `(` / `)` parameter list, with empty contents and a trailing comma
allowed. Delimiter and nested rejection endpoints are exact: recovery stops
leave an outer comma or right parenthesis unconsumed, a carrier hole remains a
nested rejection, and recovery to the window end may then yield exact
`delimiterMissing` rejection. Generic trailing-list exactness lifts the exact
element contract to the full parameter-list AST, final remainder, and
delimiter or nested rejection endpoint. Strict `FunctionParametersParses`
remains the diagnostic-free list relation, and declarative, executable,
dedicated-consumer, and umbrella APIs all expose the stronger broad contract.

Individual predicates, nonempty bare and grouped predicate sequences, and
prioritized optional `where` clauses now have parser-independent grammars and
unconditional success soundness. Bare tails preserve forward order and their
optional trailing comma; grouped sequences use the generic nonempty trailing
delimiter grammar. Transactional grouped-or-bare dispatch now records exact
grouped-first priority. A bare result carries
`GroupedPredicateSequenceUnavailable`, derived either from opening-parenthesis
absence or from exact grouped rejection and its `no_parse` consequence before
transactional fallback restarts at the original input. Exact rejection traces
cover the bare tail, the complete bare sequence, and grouped-first dispatch.
When both transactional alternatives reject, the grouped attempt's intermediate
remainder is retained separately while the relation returns the final bare
remainder reached from the original input. Bare and complete sequence outcomes
have deterministic success remainders and exclude simultaneous rejection. An
absent contextual `where` marker is a nonconsuming success, while a present
marker commits to the prioritized predicate sequence. Executable ordinary
rejection is reflected exactly as that committed sequence rejection; optional
`where` has a deterministic success remainder and exclusive success/rejection
outcomes. Predicate, grouped and bare sequence, grouped-first dispatch, and
optional `where` contracts now also fix their complete ASTs, final remainders,
and rejection endpoints. The bare tail theorem explicitly shares its preceding
span, which complete sequences determine from their first exact predicate.

For optional `returns`, an absent contextual marker is likewise a nonconsuming
success, while a present marker commits to the allow-empty, allow-trailing
parenthesized `TypeExpr` list. Executable ordinary rejection reflects the exact
nested type or delimiter remainder. The success endpoint is deterministic and
success/rejection outcomes are exclusive. The completed Core `TypeExpr` exact
contract lifts through the optional clause to fix its AST, remainder, and
committed rejection endpoint.

Optional function modifiers now preserve exact keyword absence or presence in
the fixed `public`-then-`payable` order. Modifier grammar soundness is
unconditional; diagnostic-free module success proves that both contract-only
markers are absent, while contract success satisfies its permissive policy.
The complete diagnostic-free `functionSignature` parser, which ends before a
function body or trait-method semicolon, now derives `FunctionSignatureParses`
for either location. Its proof reflects diagnostic freedom from `where`
through returns and modifiers to the parameter boundary, retains every
intermediate remainder and AST field, and identifies the parser and
declarative endpoint calculations exactly. Source validity composes with the
generic location-indexed theorem. These parameter, predicate/`where`,
modifier, and function-signature theorem families are exported through
`Solcore.Syntax` and checked by compile-time consumers.

A broad ordinary `functionSignature` outcome is now independent of location
and modifier policy. Success preserves the exact keyword, name, generics,
recovery-aware parameters, modifiers, returns, and `where` order, complete AST,
signature cover span, and final remainder. Rejection records the first failing
keyword, name, generics, parameter-list, returns, or `where` stage. Modifiers
always succeed; module-location markers may instead emit diagnostics without
changing the declarative remainder. Success endpoints are deterministic and
exclusive with rejection, while `FunctionSignatureParses` remains the strict
diagnostic-free, location-policy judgment. Exact child contracts for every
stage now make this broad signature contract unconditional: complete signature
ASTs and final remainders are unique, as is every rejection endpoint, with
matching executable reflection.

The broad ordinary `functionDecl` layer is now complete and location
independent. Its success judgment sequences the ordinary signature into the
isolated `.allow` Core body and preserves the exact declaration AST, outer
signature/body cover span, and final remainder. Its exact rejection judgment
has only the signature branch and the uncaptured body branch reached after
ordinary signature success. A balanced captured child's rejection is instead
an empty-body success with a retained recovery diagnostic and the exact parent
remainder. The combined declaration outcomes are deterministic and mutually
exclusive. This complements, rather than replaces, the location-policy-aware
diagnostic-free `FunctionDeclParses` boundary. Exact signatures and unconditional
isolated `.allow` body exactness now discharge complete declaration exactness.
The earlier body- and statement-parameterized APIs remain available.

The broad ordinary `constructorDecl` layer now records the exact executable
order from the required `constructor` keyword through recovery-aware
parameters, optional `public` then `payable`, and the isolated `.require` body.
An explicit `public` marker emits a diagnostic but is omitted from the AST, and
that emission does not change the declarative remainder. Successful derivations
retain the exact parameter and payable fields, final remainder, and complete
marker/body cover span. Exact rejection exposes only a missing marker, rejected
parameters, or an uncaptured body rejection after successful modifiers. A
rejection inside a balanced captured child becomes diagnosed empty-body
recovery success at the exact parent remainder. Success is deterministic and
exclusive with rejection; strict diagnostic-free `ConstructorDeclParses`
continues to coexist as the canonical acceptance judgment. Exact parameters,
modifiers, and isolated `.require` bodies now make full constructor ASTs and
outcome endpoints unconditionally unique.

The broad ordinary `fallbackDecl` layer now follows the exact `fallback`
keyword with recovery-aware parameters and a pure validation outcome. Empty
parameters pass directly, while nonempty parameters are retained in the AST
and emit their constraint diagnostic without changing the declarative
remainder. Fixed optional `public`-then-`payable` modifiers then precede the
isolated `.require` body. Success retains every AST field, the marker/body cover
span, and the exact final remainder. Exact rejection has only marker absence,
parameter rejection, or uncaptured body rejection after validation and
modifier success. A balanced captured child rejection is absorbed as diagnosed
empty-body recovery at the parent remainder. Success endpoints are deterministic
and exclusive with rejection, while strict diagnostic-free
`FallbackDeclParses` continues as the canonical acceptance judgment. Exact
parameters, validation, modifiers, and isolated `.require` bodies now give
unconditional fallback AST and rejection-endpoint exactness.

Implementation outcomes now span the complete declaration. The method wrapper
adds only empty parser-time comments to a broad module function declaration.
The optional `default` prefix is deterministic and cannot reject; required
head arguments use a nonempty, trailing-comma angle list of broad types. The
custom body loop retains right-brace priority, a positive `function` guard,
strict progress, forward method order, and exact unexpected or nested
rejection remainders. Full declarations distinguish missing contextual marker,
generic, name, head-argument, `where`, and body rejection after the default
prefix. Default, head, method, body, and declaration successful remainders are
deterministic and success/rejection exclusive, while module diagnostics and
captured-body recovery remain ordinary successes.
The default marker and head arguments now have unconditional exact contracts:
their successful values and final remainders are unique, head rejection fixes
its endpoint, and the default marker cannot reject. Unconditional exact isolated
`.allow` Core bodies now discharge method, body, and full declaration AST and
rejection-endpoint uniqueness. Existing conditional APIs remain available.

Trait methods now add an exact semicolon to the broad module-policy signature
outcome, so modifier diagnostics remain ordinary successes. Their only reject
stages are the signature and missing semicolon. Trait bodies expose the custom
right-brace-first loop directly: each method branch retains a positive
`function` guard, strict progress, forward source order, and the exact
unexpected, nested-method, or later rejection remainder. Full declarations
then distinguish contextual marker, name, required generics, optional `where`,
and body rejection. All three success endpoints are deterministic and
success/rejection exclusive. Exact signatures and child contracts now also
make method, body, and declaration ASTs, final remainders, and rejection
endpoints unconditionally unique, retaining source-order methods and exact
spans. These are declarative value/remainder laws, not diagnostic-trace,
failure-payload, or whole-parser-state equality. The earlier diagnostic-free
grammars and source-validity compositions remain registered beside these
broad outcomes.

Function declarations still compose exact location-indexed signatures with an
abstract parser-independent block relation. The strict diagnostic-free
implementation grammar, reflection, and source-validity compositions remain
registered beside the broad executable outcomes.
Contract declarations now extend these parametric boundaries through exact
member dispatch, enum-only derive attachment, brace-delimited forward member
order, strict progress, and recovery exclusion by diagnostic commitment.
Their body and declaration soundness theorems compose with source validity and
are publicly consumed. Exact plain and derive-aware top-item judgments now
compose every declaration branch in executable priority order. Their
diagnostic reflection feeds a complete-file theorem that preserves forward
item order, strict progress, end-of-window termination, exact source-order
comment attachment, and recovery exclusion. The resulting `SourceFileParses`
boundary composes with source validity and is publicly consumed. Independent
Core block, expression-layer, and ordered pattern-layer judgments are now in
place, together with Core simple, control, `for`, `match`, and assembly
statement judgments. Inline-Yul coverage now includes name sequences, the
public expression layer, exact braced blocks, `let`, assignment, expression
and source-level `return(...)` statements, `if`, `for`, `switch`, function
definitions, keyword controls, optional semicolons, and the complete ordered
dispatcher through its diagnostic-free recovery boundary. The aggregate Core
dispatcher is also complete. Concrete rejection witnesses now cover delimited
constructor/call fallbacks and public Yul assignment. The public Yul
expression, statement, and braced-body parsers have complete fuel-indexed
clean/ordinary/reject closures, including recovery, transactional rewind,
exact dispatcher priority, optional termination, and block-boundary rejection.

Inline-Yul expression, statement, and body exactness is now unconditional,
including fixed-fuel and public recursive boundaries. Name/literal values,
optional-call rewind, statement priority, optional termination, switch/default
selection, and recursive blocks determine complete ASTs and final remainders.
Diagnosed empty switches and recovery remain ordinary successes; body and arm
lists retain source order. Recovery scans explicitly share the first and last
accumulated spans. Expression and statement rejection have nonconsuming
endpoints, while body rejection fixes the first failing position. Public APIs
and dedicated consumers are included in the successful full build and tests.
Diagnostic-trace, failure-payload, and whole-state equality are not claimed.

The mutually recursive Core expression, pattern, statement, and block parsers
now likewise have fuel-indexed ordinary/reject closures, public production-fuel
specializations, deterministic outcomes, and backward diagnostic reflection.
A shared fuel induction now proves exact ASTs and endpoints for expressions,
patterns, and statements without additional premises. It preserves maximal
postfixes, precedence, lambda and tuple order, diagnosed successes, prioritized
fallback, and recovery spans. Exact statements make raw block items, public
blocks, balanced isolation/recovery, and both tail policies unconditionally
exact in their ASTs, closing spans, remainders, and rejection endpoints.
Public APIs and independent grammar-result consumers pass the full build and
tests without diagnostic-free assumptions. Diagnostic traces, failure payloads,
and whole parser states remain outside this contract.
The concrete `CoreSourceFileOrdinaryParses` grammar instantiates the completed
parametric file theorem with public Core expressions and isolated `.allow` and
`.require` bodies. `CoreSourceFileOrdinaryParsesFromStart` fixes its exact root
window and canonical terminal remainder, preserving the carrier and `endIndex`
while setting the final cursor to the token count. Diagnostic-free successful
`parseLexed` and `parse` results derive that form over their exact input or
retained-output carriers, and paired theorems add canonical parsed-file source
validity. The ordinary component relations remain reusable for recovered
parser outcomes; the diagnostic-free premise excludes such recoveries from
these public conclusions.

Import leaf and payload outcomes now cover selector names, optional aliases,
module paths, selected entries and nonempty braced lists, required and optional
hiding, the recovery-aware terminator, and all four payload helpers. Without
`(`, selectors use one checked identifier; a positive `(` commits to a
nonempty maximal operator-symbol scan and exact close. An absent `as` or
`hiding` guard returns its empty option without consumption, while a positive
guard commits to the complete selected alias or hiding clause. Module paths
split an absent `@` local name from an exact `@` external name. Selected-import
and hiding lists require at least one element and permit a trailing comma.

An exact semicolon terminates normally. A missing semicolon immediately before
an exact top-item starter is a diagnostic-bearing, nonconsuming success that
returns the last payload span; any other missing terminator rejects. Plain,
namespace, wildcard, and selective payload relations retain executable stage
order, AST and covering span, token carrier, active window, cursor, and exact
first rejection. Each endpoint is deterministic and exclusive with rejection.
Stronger unconditional exactness now fixes complete ASTs and first rejecting
endpoints throughout aliases, selected lists, hiding clauses, all four payloads,
and full imports. Shared start/preceding spans are explicit where required.
Module paths, maximal selectors, export paths, and both terminators have exact
leaf APIs; dedicated consumers compare independent grammar results.

The complete broad `importDecl` relation consumes exact `import` and retains
the dispatch lookahead without consuming it. Current `*` plus offset-one hard
`as` commits to namespace import; current `*` without that lookahead commits to
wildcard import. Otherwise current `{` commits to selective import, with plain
import as the final branch. A committed branch never falls through after
failure. The aggregate success/rejection pair is deterministic and exclusive,
including diagnostic-bearing terminator recovery.

The export vertical now has exact broad outcomes from its leaves through the
complete `exportDecl`. Export paths are maximal dotted checked names.
Constructor selection prioritizes `(*)` over a nonempty, no-trailing-comma
name list; export names prioritize `*`, a parenthesized operator selector, then
a checked identifier with optional constructor selection. Local items commit
to qualified `path.*` only under identifier-plus-offset-one-dot lookahead, and
remote selection chooses wildcard or an allow-empty, trailing-comma-permitting
braced name list.

Local payloads pair an allow-empty, trailing-comma-permitting item list with an
exact nonrecovering semicolon. Path payloads prioritize dot plus selection,
absent-dot `as` plus checked alias, then bare module, with the same exact
terminator. The aggregate consumes exact `export` and dispatches local versus
path on a nonconsuming `{` guard. It preserves exact AST, covering span,
carrier, active window, cursor, and first rejection; success endpoints are
deterministic and exclusive with rejection. Public parser and declarative APIs
are compile-time consumed at dedicated and umbrella boundaries. These
declaration-local guarantees feed the broader top-item outcome below.

Stronger unconditional export exactness now fixes the full constructor/name,
selection, payload, and declaration ASTs and all rejecting endpoints. The
constructor-name list retains its nonempty source order, maximal operator
selection fixes the closing span, and supplied outer spans remain explicit.

Pragma item scanning and complete `pragmaDecl` now likewise have exact broad
ordinary outcomes. An immediate `;` is an empty, nonconsuming scan. Otherwise
checked identifiers are retained in forward order; comma absence stops without
consumption, while comma followed by `;` consumes only the trailing comma.
Complete declarations compose exact `pragma`, a raw-identifier name, the item
scan, and an exact semicolon. The raw name deliberately omits the checked-name
hyphen diagnostic. Rejection distinguishes keyword, name, items, and semicolon
stages. Item-tail, item-list, and declaration successful remainders are
deterministic, and success is disjoint from rejection. Unconditional exactness
also fixes complete item lists, located declaration ASTs, and rejection
endpoints. Production-tail results retain the same supplied reverse prefix.
Public exactness APIs and consumers feed the broader top-item and file outcomes.

Dotted derive targets now have exact broad ordinary success and rejection at
the component, recursive dotted-tail, and complete-target layers. Component
success includes checked identifiers and diagnosed reserved hard keywords;
component rejection requires both alternatives to be unavailable. Tail
rejection retains the consumed dot and the exact first or later component
failure. Each layer has a unique successful remainder and disjoint
success/rejection. A reusable stronger outcome contract now fixes the
successful AST together with its remainder and fixes the rejection endpoint;
exact-token and checked-identifier primitives and all three derive-target
layers instantiate it. Executable reflection re-exports these laws and is
compile-time consumed at dedicated and umbrella boundaries.

Complete derive attributes now also have exact broad ordinary outcomes. The
valid path distinguishes five rejection stages: hash, opening bracket,
contextual `derive` marker, no-trailing target list, and closing bracket. The
recovery scan prioritizes and consumes a current `]`; without one it stops
nonconsumingly at the window end, a top-item start, an identifier-plus-colon
contract field, `}`, or an active-window carrier hole. Every other raw token
is consumed while updating the last retained span. Once exact `#[` has been
consumed, the tail cannot ordinarily reject. Public `orElse` retries recovery
from the original input after valid-path rejection, and public rejection
retains evidence that both attempts rejected. Exact nested outcomes now lift
through generic no-trailing lists, fixing their complete AST and every rejected
endpoint. The valid path, complete recovery, and public prioritized outcome
therefore fix the successful derive-attribute AST together with its final
remainder and fix the public rejection endpoint. Tail value uniqueness keeps
the necessary shared last-retained span explicit. Executable reflection
re-exports these laws and dedicated and umbrella consumers compile against
them; diagnostic lists, failure payloads, and whole parser-state equality are
outside this declarative exactness claim.

Attribute-free `contractMemberCore` now has complete broad ordinary coverage for
its prioritized six-way dispatcher. Identifier-plus-colon field lookahead runs
before `function`, `constructor`, `fallback`, `type`, and contextual `enum`;
once selected, a rejecting branch cannot fall through. Success retains the
wrapped member AST, declaration span, empty leading comments, carrier, window,
cursor, and final remainder. Rejection records its selected leaf or an exact
nonconsuming unrecognized-member case. Successful remainders are deterministic
and success is disjoint from rejection. The stronger exact contract is now
unconditional: public Core expressions fix field initializers, isolated bodies
fix body-bearing declarations, and type aliases and enums are independently
exact. Earlier conditional APIs and strict member soundness remain available.

Exact pure derive attachment now gives every input one unique AST result across
all seven contract-member variants. Only enums retain the supplied attribute.
The five other declaration variants preserve their payload while extending
both the member and nested declaration spans; the error variant extends only
its member span, and leading comments remain unchanged throughout. Every
executable attachment succeeds, reflects this exact transformation, and
preserves the declarative remainder. The diagnostic emitted for non-enum
attachment does not create a rejection stage.

The derive-aware public contract-member dispatcher now has complete broad
ordinary coverage. Hash absence selects the attribute-free core, while hash
presence commits to public derive parsing, core member parsing, and pure attachment in
that order. Exact rejection separates plain-core failure, derive failure, and
core failure after a successful derive. Executable success and rejection are
reflected into those relations. Successful remainders are deterministic and
success is disjoint from rejection. Exact attribute-free members and pure
attachment now give unconditional derive-aware AST and rejection-endpoint
functionality. The generic conditional lift remains available.

Standalone contract-member recovery now has exact broad success and rejection.
It consumes one mandatory token, scans without consuming the next recovery
boundary, and exactly records window-end, boundary, and missing-carrier stops;
only an unavailable first token rejects. Recovery-aware contract bodies compose
that scan with right-brace priority, strict direct-member progress,
window-preserving rejection rewind, forward member order, and exact opening or
tail rejection. Broad contract declarations add exact marker, name, optional
generic, and body stages with matching first rejection. All three outcome
families have deterministic successful remainders, disjoint success/rejection,
public executable reflection packages, and compile-time consumers. Standalone
recovery additionally fixes the complete error-member AST and final remainder,
and fixes its rejection endpoint; scan value uniqueness retains the necessary
shared first and last spans explicitly.
Unconditional exact member contracts now lift through the complete recovery-aware
body and declaration, fixing their full ASTs, final remainders, and rejection
endpoints. Core expression and statement exactness discharge the previous
shared premises. Declarative and executable consumers cover the conditional
lifts; diagnostic traces, failure payloads, and whole parser states
remain outside this stronger contract.

The attribute-free top-item dispatcher now has exact broad outcomes for its
nine declaration branches and final nonconsuming unrecognized case, including
all earlier negative guards. Pure derive attachment is total for all ten item
variants: enums retain the attribute and other variants preserve their payload
while extending the exact outer and nested spans selected by the executable.
The public derive-aware dispatcher records hash absence or the committed
derive, plain-item, and attachment sequence, with all first rejection stages.

Standalone top-item recovery, the recovery-aware file-item suffix, and the
complete `sourceFile` wrapper now have exact broad outcomes as well. Recovery
consumes its mandatory first token, updates the last span, and preserves the
next recognized top-item boundary. The file loop keeps forward item order while
hiding its executable reverse accumulator, enforces direct progress, rewinds
window-preserving rejection, makes a recognized-start rejection a
nonconsuming diagnostic success, and otherwise inserts a recovered error item.
The source-file wrapper retains exact source identity, full-file span, comment
attachment, comments, carrier, window, cursor, and first rejection. All layers
have deterministic successful remainders and disjoint success/rejection, and
their public reflection packages are compile-time consumed. Broad success does
not imply end-of-window when the recognized-start boundary-stop branch runs.

Unconditional exact import/export contracts now discharge the final shared
premises for complete syntax exactness. Plain and derive-aware top items,
recovery-aware file items, and the source-file wrapper each fix the full AST
and final remainder and every rejecting endpoint. Public parsed-file value
uniqueness includes both nesting branches over fixed file/tokens/comments;
`parseLexed` and `parse` expose that independent AST law without claiming a
public final cursor, diagnostic-trace equality, or whole-state equality.

Ordinary completeness now follows from exactness, success/rejection soundness,
and absence of invariant failures. The generic proof needs no axioms. Its
public instances cover Core types/terms/lambda parameters, both block policies,
Yul, every top-level declaration, derive paths, top-item dispatch, standalone
recovery, and file-item accumulation. They preserve complete successful ASTs
and declarative remainders or the rejected endpoint, not failure payloads.
Internal APIs require only `State.ValidFor` where totality needs it; pragma,
derive-target, recovered-derive, and top-item recovery correspondence is
unconditional. File-loop APIs retain the shared reverse-prefix contract and
have a production version without a separate fuel-adequacy premise.

Public token-to-file AST correspondence is now an iff with independent
validation acceptance and public syntax. Public source-to-file correspondence
uses an actual canonical lexical witness. Both nesting branches and recovered
ASTs are included, without diagnostic-free premises; arbitrary token payloads
are not claimed to arise from canonical lexing. All public instances have
dedicated/umbrella consumers and depend only on the allowed standard axioms.

The correspondence now also gives independent public AST existence, uniqueness,
and recursive provenance over validated carriers, with no parser-reply premise.
Contract field/member/body/recovery completeness exposes the same precise
internal boundaries without strengthening diagnostic or whole-state claims.

Bounded nesting now has a parser-independent, total, functional scan relation.
Its six token actions reproduce delimiter scopes, conditional bases, resets,
and the first overflowing token exactly, using one shared canonical limit.
Executable `checkNesting` returns `none` exactly when that relation clears and
returns `some` exactly when the relation reports the mapped overflow span,
dimension, and limit.

Already-tokenized input validation now has its own parser-independent, total,
functional outcome relation. Source mismatch has first priority, followed by
the first invalid token, comment, and lexical-diagnostic span, with exact index
and span payloads. Acceptance is equivalent to `LexedFile.ValidFor`, every
executable validation result reflects the relation, and every arbitrary
`parseLexed` error is exactly the mapped first validation rejection. The
complementary certified branch supplies an actual successful public output,
broad source-file syntax, exact retained carriers, and canonical validity.

The public token-to-file and source-to-file parser boundaries now have broad
syntax-only soundness without a diagnostic-free premise. Nesting overflow
selects the exact empty parsed file; nesting clearance selects the
recovery-aware complete-file grammar from the exact root token window, with
the unexposed final remainder existentially hidden. Both forms compose with
complete output validity and use the exact retained public carriers. For the
overflow branch, the complete `ParseOutput` is fixed, including its retained
lexical carriers and unsuppressed singleton nesting diagnostic. Extending the
normal branch to an exact full parse-diagnostic list remains a separate trace
milestone because the current broad grammar does not retain parser diagnostic
accumulation. An exact executable witness now retains the normal branch's
successful `sourceFile` reply, final state, complete output assembly, and
diagnostic-filter equation without presenting that witness as an independent
grammar trace.

The first independent normal-branch trace vertical is now closed for one
unrecognized top-item recovery to the root-window end. Recovery has an exact
singleton-span event trace, or an empty trace on mandatory-token rejection;
the raw file loop retains earlier diagnostics and does not emit its inner
unrecognized-item failure. Declarative cascade filtering fixes retained event
order and duplicates with the pinned LF-only, overlap, inclusive-boundary,
and whitespace conditions. Executable interpretation is equivalent in both
directions. Together with validation and nesting clearance, these rules fix
all fields of public `ParseOutput`, not merely its AST.

The next recognized-start slice is complete for a `pragma` keyword followed by
an unavailable raw name. Independent current-input and rejection-report rules
fix source, end-byte context, found token, expectations, and failure span.
Primitive rejection is silent; the recognized-start file boundary retains the
failed attempt's earlier diagnostics, rewinds only its cursor, and appends the
exact failure report. The missing-name prefix crosses all top-item dispatchers
and determines complete `parseLexed` and `parse` outputs, including the empty
AST item list and exact lexical-cascade filtering of the unexpected diagnostic.
Other recognized-start and nested declaration/block traces remain next work.

Raw and checked identifier success now expose exact independent AST/remainder
and event-suffix correspondence. Raw names are silent; checked names emit one
located report iff the spelling contains a hyphen. Arbitrary earlier diagnostics
are preserved. Mixed-report cascade normalization also has a total and unique
independent grammar equivalent to the executable filter. It retains complete
payloads, order, and repeated surviving occurrences; identifier, constraint,
and nesting reports cannot be removed as lexical cascades. These shared trace
components support the remaining declaration and nested-block work.
Hard-keyword, symbol, and contextual primitives now have the same exact silent
success and uncommitted-rejection correspondence, including fixed expectation
categories and EOF context. Protected identifier traces survive concatenation
with arbitrary independently normalized diagnostic prefixes. A separate
executable composition lemma carries a successful final top item through the
file loop and comment attachment without adding or discarding diagnostics; its
item-reply premise remains explicit rather than masquerading as grammar evidence.

Complete successful pragma traces now concatenate only the checked items'
events in written order, including empty and trailing-comma forms. Production
tail completeness keeps an accumulated item prefix outside the newly emitted
trace. Pragma success iff fixes the entire declaration, remainder, and added
diagnostics without validity or diagnostic-free premises. One root pragma
reaching the end determines the complete public singleton output and comment
attachment; protected spelling reports all survive lexical normalization.
Empty token input also has complete public-output equality, retaining comments
and lexical diagnostics but introducing no parse diagnostics. Canonical lexical
fixtures cover empty, whitespace-only, comment-only, and diagnosed tokenless
source. Compositional sequencing and transactional-choice laws separately fix
diagnostic retention versus rollback, including nonempty prior and discarded
traces; their executable premises remain explicit.
Ground successful-pragma outputs now cover raw-name hyphens, ordered checked
item diagnostics with a trailing comma, protected reports beside a same-line
lexical error, and exact comment attachment. Independent normalization stability
also yields executable idempotence and concatenation laws for mixed traces.

Arbitrary successful pragma-only windows now have independent sequence grammar,
ordinary file-item erasure, exact declaration/remainder/trace uniqueness, and
production execution correspondence. Declaration count bounds the required
loop steps; a pre-existing reverse item prefix contributes no fresh diagnostic.
The source-file wrapper preserves comment attachment and event order. Complete
public output laws extend from one pragma to any finite sequence, including
empty input. With root grammar and nesting clearance supplied, tokenized output
is equivalent to validation plus exact trace equality, and canonical-source
output is equivalent to exact trace equality after lexing supplies validation.

All four pragma rejection stages now have independent trace soundness and
completeness, including fixed complete failures, exact remainders, and arbitrary
prior diagnostic prefixes. Checked-item failure traces expose their successful
prefix existentially, since a rejected parser reply returns no item AST.
Full file/window frame laws preserve report context without `ValidFor`.
Recognized initial pragma rejection is connected through boundary rollback to
complete token/source output: prior protected events survive, one failure is
committed, and independent mixed filtering fixes the final diagnostic list.
Its only alternatives are the full raw prefix with or without the final report.
Ground regressions distinguish missing item after comma from missing semicolon
and verify that same-line lexical suppression removes only the final expectation.

Successful pragma prefixes followed by recognized pragma rejection now have
independent grammar, unique items/stopping remainder/report/trace, structural
execution bounds, and complete production/public output correspondence. The
stopping remainder points at the final pragma's start, not the internal failure
site; the latter is retained in the report. Prior items are returned in source
order and no item is fabricated for the rejected declaration. Ground two-pragma
examples verify both retained and lexically suppressed final reports while
keeping successful and rejecting checked-item events in their original order.

Balanced block isolation has a separate conditional trace boundary. Independent
direct/captured/recovered judgments retain explicit source/end-byte context,
exact AST/remainder, and ordered diagnostics. Fixed-context inner functionality
and disjointness lift to outer exactness; capture uniqueness resolves the child
window. Execution laws reset child diagnostics, restore the complete parent
frame, append child events, and commit only recovered rejection. Four explicit
inner soundness/completeness contracts lift to outer success/rejection iff laws.
Soundness guarantees an appended suffix for every result; fixed-trace iff alone
is not substituted for that guarantee. Concrete inner Core trace contracts
remain a subsequent obligation, distinct from this completed wrapper proof.

Core block closing has a completed trace boundary. Independent per-statement
and whole-tail judgments determine termination reports, including the final
`allow`/`require` distinction, full statement spans, order, and duplicates.
Existence, uniqueness, protection, and empty-trace/old-validity equivalence are
proved. A proof-only seam for the private validator supports exact successful
closing iff with the actual closing-token span kept existential (cover spans
need not be injective). Rejection is exactly the silent right-brace primitive
failure and does not run tail validation. Filtering any earlier mixed trace
followed by this protected suffix preserves that suffix in its final position.

Raw Core block trace composition is complete under explicit statement contracts.
Independent item/full-block success and rejection judgments fix branch priority,
AST/remainder/report/trace and erase to the established ordinary grammars.
Exact statement outcomes lift to joint raw and isolated block exactness.
Execution soundness supplies a suffix for every ordinary result; completeness
uses strict cursor progress and full-window preservation to establish sufficient
production fuel. Fixed-trace success/rejection iff and full-Failure rejection
iff retain arbitrary incoming diagnostics. Existing reverse item prefixes are
included once in final whole-body validation, while only new statements emit
fresh statement events. Rejection runs no delayed validation. Raw contracts
compose directly through isolation under the same statement assumptions.
Concrete general statement traces and whole-file traces remain later work.

Nonempty contract consumers now instantiate a test-only checked-name statement
parser on explicit token carriers. They verify name-event ordering before all
tail checks, the final-expression policy difference, rejection without tail
validation, and one-report captured recovery preserving the parent window and
following token. This adapter is not the concrete Core statement parser.

The actual `break`/`continue` leaves now discharge all five statement trace
contracts unconditionally. Silent success fixes the full AST and cursor-only
two-token state update; silent rejection fixes the first missing keyword or
semicolon and the full failure record. Independent leaf existence is separate
from joint exactness and covers missing slots in malformed carriers as well as
window exhaustion. Raw and isolated restricted-block exactness follows with
no abstract statement premise. Nonempty token-carrier consumers retain prior
events, compare both tail policies, and verify recovered parent continuation.
Two source fixtures now bridge canonical lexing to these success/rejection
consumers without deciding the execution of the complete block parser.
Return trace composition now lifts explicit expression contracts through the
semicolon-first optional value and final required semicolon. Independent
success/rejection grammars preserve exact ASTs, first reports, and ordered
expression events, with ordinary erasure and joint exactness. Conditional
expression existence separately supplies optional-value/return existence, not
block totality. Successful trace correspondence requires no expression context
frame; full-window/source preservation is explicit where final rejection reports
or successful context are claimed. Empty `return;` is unconditional and skips
expression execution. Restricted return block composition uses the resulting
five statement contracts. Concrete general expressions and remaining statement
forms are the next trace layer.

Literal/Boolean primitive traces are now unconditional: silent one-token
success preserves every payload and prior event, while silent rejection fixes
the full unchanged state and expectation-specific report. Their independent
outcomes exist and are exact on arbitrary carriers. The actual literal-expression
leaf discharges the five expression execution contracts, joint exactness, and
outcome existence. Literal-only return instances therefore need no abstract
expression premise, including their restricted raw/isolated block laws.
Canonical source consumers cover a decimal return and its missing-semicolon
failure; an explicit-token block combines literal and empty returns, retaining
both ASTs, all prior events, and the post-isolation parent continuation.

Block-statement traces now wrap the raw required-tail Core block, not balanced
isolation. Inner statement contracts lift to five outer contracts and exact
success/rejection/full-failure iff. Success maps only the AST; failure retains
the entire raw rejected state and its uncommitted report. Independent structural
and joint outcome laws compose, and successful source/full-window preservation
requires only the inner frame. Concrete recursive statement dispatch remains
separate from this conditional block-statement layer.

Boolean-first expression-name traces and actual identifier-expression contracts
are now unconditional. Checked-name events preserve full spelling/span metadata;
success fixes the entire one-token state update and ordered diagnostic suffix.
Fallback rejection fixes the unchanged input and identifier-specific report.
Independent output shape, existence, and joint exactness close the corresponding
expression assumptions, including a concrete checked-name return instance.

Protected trace composition now covers successful and rejected returns, raw
Core blocks, and block statements. Complete checked-name and delayed constraint
events survive lexical normalization while arbitrary prior candidates can still
be filtered. Uncommitted and isolated-recovery reports are not assumed protected.
Concrete nested break blocks and canonical checked-name return fixtures exercise
ordered events, exact inner failure propagation, single outer recovery, and
parent continuation without broadening to general statement traces.

Generic no-trailing delimiter traces now cover both empty policies, successful
and rejecting tails/lists, independent joint exactness, and protected suffixes.
Five arbitrary-result execution contracts separate child traces from successful
source/full-window preservation. Soundness and completeness retain arbitrary
prior events and reverse prefixes, using the real after-opening production fuel.
No token-carrier law is hidden in trace grammar; whole-list ordinary erasure
requests it explicitly. Comma priority, direct child invocation after comma,
and ordered possibly duplicate delimiter expectations are preserved. These are
conditional list laws, not concrete recursive expression or full-file traces.

Array-literal traces now wrap no-trailing lists without changing their output
states or failure reports. Five expression contracts and success/reject/full
failure iff compose explicit child laws; independent exactness and protected
events compose separately. Actual identifier/literal child consumers exercise
ordered checked-name events, empty/numeric arrays, delimiter failure, and child
rejection after comma. Canonical lexer-to-initial-state connections cover four
success/rejection fixtures. General recursive expression contracts remain open.

Concrete checked-name array returns now discharge all five statement contracts
and run through raw and isolated Core blocks under both tail policies. Canonical
fixtures retain two ordered success events or one earlier event followed by the
unchanged child failure; outer isolation alone appends that report once and
restores the parent continuation. Independent restricted exactness and raw
normalization consumers compose the same array/return/block laws.

Leading-dot constructor traces now compose the real Boolean-first checked name
with conditional no-trailing argument traces. Optional absence preserves the
whole state; absent and empty arguments bypass any child. Raw dot rejection
includes a missing-dot report and explicitly separates that case when erasing
to the old selected ordinary grammar. Name events precede argument events on
both outcomes; reports stay uncommitted, and protected suffixes survive actual
normalization. Independent joint exactness and five expression execution
contracts keep recursive child assumptions explicit.

Canonical constructor consumers now connect lexing directly to initial states,
fixing the complete three-event success or two-event rejected prefix alongside
separate dot/name/list spans, parent window, and unconsumed following tokens.

Parenthesized group/tuple traces now have conditional success/rejection
correspondence, independent exactness, and protected child-event composition.
The bespoke comma tail keeps a singleton trailing-comma form as a group and
preserves forward tuple order; immediate closes bypass any child. A missing
close after a non-comma child expects only right parenthesis. Raw missing-marker
cases stay separate from selected ordinary erasure, and production fuel is
measured after the first child. Canonical empty/group/tuple and closing-failure
consumers retain full ASTs, windows, unread tokens, arbitrary prior events, and
uncommitted reports. Recursive child contracts remain explicit.

Proxy traces now lift the actual type parser's explicit success/rejection
contracts, preserving its full AST, ordered events, and unchanged returned
failure/state. Raw marker absence is separate from selected ordinary erasure;
the final report stays uncommitted. Joint exactness and protected normalization
retain type assumptions. Canonical checked-name success and type rejection
provide concrete restricted consumers, not general type trace completeness.

Named-type finishing now unconditionally distinguishes bare `mapping` from
qualified or other spellings. Its unique protected constraint event covers any
supplied arguments; full-state execution keeps every other field and all prior
diagnostics, including duplicates. Recursive type trace contracts remain open.

Optional lambda return annotations now inherit exact type success/rejection
traces conditionally. An absent arrow is an unconditional same-state success,
not a missing-marker failure. Selected annotations preserve complete child
states, reports, and duplicate events; protected suffixes normalize unchanged
under child protection laws. Parameters and complete lambda traces remain open.

Qualified names now expose unconditional exact diagnostic success/rejection
and complete-state correspondence in every context/phase, including maximal
silent dots, ordered checked-name events, uncommitted identifier failures, and
arbitrary raw reverse prefixes. Independent exactness/protection and canonical
three-name success/two-name-prefix failure consumers are verified. Remaining
type arguments and recursive type traces still need separate composition.

Generic trailing-enabled list traces now compose explicit child contracts for
both empty policies. Comma-first priority, immediate post-comma close bypass,
arbitrary reverse prefixes/events, and actual post-opening fuel are exact;
successful source/full-window framing is separate from ordinary carrier laws.
Joint uniqueness/disjointness and protected suffixes are public. Canonical
checked-name success and two distinct rejection paths verify real execution,
but do not supply real type-argument or lambda-parameter child contracts.

Optional named-type argument traces now inherit the nonempty trailing list's
five contracts under nested type contracts. Silent absence and nonempty
conversion preserve whole states; selected rejection preserves its exact
failure and earlier events. Joint exactness and protected normalization are
public, with real-type-child canonical success/rejection examples. General
recursive type trace contracts and named-type composition remain separate.

Raw named-type traces now compose name, optional arguments, and finishing
diagnostics under nested type contracts. Every earlier event survives failure;
the mapping constraint is emitted only after arguments succeed. Componentwise
ordinary erasure and raw rejection remain distinct from prioritized dispatch.
Joint exactness, protected suffixes, full-state consumers, and canonical bare
mapping success/failed mapping arguments are verified. General recursive type
trace contracts and type-dispatch integration remain open.

Raw mapping-type traces now preserve contextual marker and exact AST spans,
key/value event order, and all six first-failure positions under nested child
contracts. Raw prefix failures remain distinct from selected ordinary rejection.
No unsupported child progress premise is added; a non-advancing-child execution
was independently checked. Joint exactness, protected suffixes, and canonical
real-type-child success/closing failure are verified. General recursive type
contracts and dispatcher composition remain separate.

Raw proxy-type traces now forward exact child success/rejection without an
extra frame premise; successful framing is a separate contract. Independent
joint uniqueness/disjointness, raw/selected rejection separation, protected
suffixes, whole-state marker bypass, and canonical real-type-child success and
failure are verified. General recursive type contracts and dispatch remain open.

Raw comptime-type traces now cover exact marker/angle/outer spans and all four
first failures. Success needs no child frame; closing-report composition uses
the successful source/window frame. Raw tuple-type traces inherit trailing-list
priority/progress and retain empty and singleton tuples. Both slices expose
conditional five contracts, independent joint uniqueness/disjointness, protected
suffixes, raw/selected rejection separation, and canonical real-type-child
full-state consumers. Recursive type and dispatcher trace composition remain open.

Optional function-return clauses now compose exact contextual markers and
empty-allowed trailing-list outcomes under child contracts. Silent absence,
empty child bypass, joint uniqueness/disjointness, protected suffixes, and
canonical real-type-child success/separator-failure consumers are verified.
Function-type and general recursive trace composition remain separate.

Raw function types now preserve exact parameter-before-return events and choose
the correct full AST end span under nested contracts. Five contracts, full-state
component correspondences, independent erasure/joint/protection, and canonical
real-type-child success/return failure are verified. Recursive type success also
has an unconditional source/full-window frame at explicit and production fuel,
with a noncanonical-carrier consumer. This frame is not recursive trace
soundness/completeness; prioritized trace dispatch and recursive composition
remain separate obligations.

The one-layer type dispatcher now has independent exact priority selection,
all six raw outcomes plus final type-only rejection, ordinary erasure, joint
uniqueness/disjointness, and protected events. Positive-fuel correspondence
retains preceding-child trace contracts while using the unconditional frame.
Keyword/contextual/window boundary consumers and complete final failures are
verified. General recursive production traces and outcome existence still need
separate proofs; the one-layer contract does not imply either.

Monotonicity is now verified for trailing lists, every raw type form, and both
dispatcher outcomes. Replacing child evidence by pointwise implication keeps
all indexed values, remainders, events, and reports unchanged. Consumers erase
auxiliary protection annotations without losing the protected exact suffix.
These laws alone do not construct the recursive trace relation.

Generic pointwise and unrestricted completeness bridges now combine both trace
soundness laws with independent exactness and explicit invariant exclusion.
Checked-name consumers preserve arbitrary prior events and complete failure
states. Countermodels verify that neither joint exactness nor vacuous complete
contracts assert ordinary outcome existence; invariant exclusion remains an
explicit additional obligation for recursive instantiation.

Recursive type success and rejection soundness now target a fuel-free least
closed relation of the selected layer. Fixed-point roll/unroll and simultaneous
induction are verified independently of execution. Successful ordinary erasure,
token carrier/window preservation, and both protected-event laws are
unconditional, as are actual explicit-bound and production soundness. Public
consumers retain arbitrary prior diagnostics. This forward result alone does
not establish reverse correspondence or ordinary outcome existence.

Three-level canonical proxy/comptime/name success and closing failure now
consume public recursive soundness. Component proofs retain full states,
precise AST/report spans, arbitrary prior events, and following tokens.

Independent recursive joint exactness is now verified by strong induction,
using heterogeneous child agreement lifted through trailing lists, raw forms,
and dispatch. It assumes no recursive uniqueness. Pointwise completeness and
exact-failure equivalences follow under explicit invariant exclusion. Joint
exactness remains distinct from trace outcome existence.

Unrestricted recursive type totality now discharges invariant exclusion for
every state. The new generic list/raw-type argument requires only child
end-index preservation, strict successful progress, and ordinary execution
below its resource bound. Actual opening/comma consumption pays for recursive
steps without global validity. All five type trace contracts and exact
success/rejection/full-Failure equivalences now quantify over arbitrary earlier
diagnostics and noncanonical windows. General expression, statement, and
whole-file diagnostic composition remain separate.

Totality plus soundness also give execution-derived trace existence for every
State and independent remainder. Noncanonical reverse consumers cover malformed
provenance/ranges, absent backing tokens, and past-window cursors with arbitrary
prior events. A synthetic child that changes every unconstrained field and
overshoots endIndex verifies the resource contract's minimal frame boundary.

Separate source-preservation laws now lift type trace equivalences to exact
whole-State success and rejection on arbitrary inputs. Reconstruction uses
every independent remainder field, with explicit counterexamples for dropping
token-carrier or end-index equality. Nested consumers recover the complete
Failure and retain untouched following tokens and arbitrary prior events.

Raw proxy expressions and optional lambda return annotations now consume the
actual unrestricted type contracts, making all five execution contracts and
trace equivalences unconditional. Independent reverse consumers also preserve
protected diagnostic suffixes. Full expression and lambda composition remain
open. Parameter finishing is a separate completed leaf: independent event
existence/uniqueness and exact full-State execution preserve earlier events,
append only an outer-comptime or specified missing-type constraint, and retain
duplicates. Name selection and recovery are not covered by this leaf.

Raw named-parameter tails now unconditionally compose real recursive types and
finishing traces. The five contracts, exact whole-State/full-Failure reverse
correspondence, independent joint exactness/protection, and ordinary execution
distinguish missing-colon error success from typed success and type rejection.
Nested reverse consumers verify type-before-finishing order, skipped finishing
on failure, duplicate preservation, and untouched following tokens. Selected
parameter-core and recovery traces are separate composition stages.

Ordinary-name finishing and checked-prefix composition now retain exact event
order through arbitrary continuations. Both parameter cores share a reflected
window-visible contextual-name pair; source preservation also covers their raw
helpers and cores. Consumers verify hidden/missing second tokens, duplicate
earlier warnings, and no ordinary-name warning after a selected comptime marker.
These prefix and selection laws are distinct from full core/recovery traces.

Raw ordinary/comptime named parameters and their selected non-recovering core
now have all five unconditional trace contracts and exact whole-State/Failure
equivalences. Independent raw first failures and pair guards preserve priority,
name/type/finishing order, and the absence of an ordinary-name warning after a
marker. Separate totality and soundness supply explicit traced outcome existence
for arbitrary States and independent remainders. Reverse consumers distinguish
raw outcomes on the same input and verify selected success over a bypassed raw
failure. Public named and lambda rewind/recovery are composed separately below.

Lambda tails now have unconditional five contracts and complete State/Failure
equivalences. Typed tails retag the exact named-tail AST and retain its events;
missing colons distinguish silent inference from a comptime missing-type error.
Consumers verify earlier duplicates, ordered type/finishing events, and complete
child-failure forwarding. These results do not yet cover the full lambda parser.

Standalone parameter recovery now has unconditional five contracts, independent
joint exactness, and full-State reverse consumers. Mandatory first consumption,
later delimiter stops, and initial versus later missing backing are distinct.
The one newly appended recovery event has conditional lexical-cascade keep/drop
laws; the already committed original report is never replayed. Public named
rewind/recovery is covered by a separate composition stage below.

Public named parameters now compose core traces, cursor-only rewind, boundary
rejection, and standalone recovery. All five contracts and whole-State/Failure
equivalences are unconditional. Separate ordinary execution and soundness supply
actual trace existence without reading existence into independent joint exactness.
Reverse consumers distinguish terminal reports from committed reports, retain
name warnings and prior duplicates, and verify conditional mixed-event filtering.
Public lambda parameters are composed below; general recursive expressions remain open.

Raw ordinary/comptime lambda parameters and their selected non-recovering core
now have unconditional five contracts, exact State/Failure equivalences, and
independent joint exactness/protection. The core additionally has separate
execution-derived trace existence for arbitrary States and remainders. Reusable
independent witnesses verify ordinary inference over a bypassed raw failure,
marked missing-type error success, all three nested events, second-name silence,
and full child rejection. Public lambda recovery is composed below; expressions
remain a separate stage.

Standalone lambda recovery now retags only the recovered error AST while keeping
the exact State, Failure, and event suffix. Its unconditional five contracts,
whole-State equivalences, joint exactness, and conditional filters reuse the
function-recovery specification. Public lambda parameters compose that recovery
with cursor-only core rewind and exact original-report commitment. Their five
contracts and State/Failure equivalences are unconditional, and separate ordinary
execution proves trace existence on every State and independent remainder.
Consumers distinguish inference and missing-type core success from recovery,
and retain ordered mixed events, prior duplicates, and separate terminal reports.
Parameter lists are composed below; complete lambda/general expression traces
remain separate.

Actual functionParameters and the inline lambda parameter list now instantiate
the trailing-enabled list contracts with public recovering parameters. All five
contracts, complete State/Failure iff laws, joint exactness, unrestricted ordinary
execution, and separate actual/independent trace existence are available without
child or validity premises. Empty lists, trailing commas, and recovery events
retain the existing runtime behavior. Signature and lambda-expression traces,
including their following returns and bodies, are separate composition stages.

Shared-carrier reverse consumers check both lists' exact empty/single/trailing
success, ordered delimiter report, first-child boundary failure, recovering
child events with duplicate prior diagnostics, and invalid-window trace existence.
They distinguish function missing-type errors from lambda inference while
retaining the complete AST, State, Failure, and unread semicolon.

Raw lambda expressions now compose the real parameter list and optional return
with explicit body trace contracts. All five contracts and full-Failure suffix
iff laws are available; complete successful/rejected States require the respective
body context law explicitly. Independent joint exactness assumes only body joint
exactness. Separate ordinary execution plus body soundness proves traced outcome
existence without deriving it from uniqueness. Marker, parameter, return, and body
failures are distinguished, and pointwise early failures bypass any supplied body.
Mixed filtering retains the protected return events between explicit parameter
and body filters. General recursive expression and atom-selection trace completion
are still open; raw body-conditional laws do not close those obligations.

Concrete raw-lambda consumers now exercise recovering parameters followed by a
hyphenated return name, arbitrary body success/failure and ordered body events,
all body-before-execution failure positions, conditional mixed filtering, and
the real empty Core block with an arbitrary bypassed statement parser. General
body results remain explicit pointwise assumptions; the empty case is concrete.

The atom dispatcher now independently selects all eight ordered branches on
arbitrary remainders, with uniqueness, separate selection existence, and exact
raw Reply reflection. Concrete consumers cover token/window distinctions and
unselected-child independence. This does not establish recursive trace existence.
Standalone atom recovery has unconditional five trace contracts and whole-State/
Failure equivalences, with a mandatory initial token, boundary scan, singleton
event, and conditional cascade filtering. Public atom rewind and report commitment
are covered below under explicit core contracts.
Standalone reverse consumers additionally distinguish mandatory-first behavior
from later boundary/missing-backing stops, active-window hiding, original report
non-replay, duplicate prior events, and concrete conditional lexical filtering.

The selected atom core now composes all raw trace branches under explicit nested
expression and body contracts. Four soundness/completeness laws need no rejection
frame, validity, progress, or ordinary execution; collection children retain an
explicit success context. Complete State equivalences add only the relevant
success context or rejected file/end-byte frame, preserving exact returned
carriers/end indices. Joint exactness depends on nested/body joint specifications;
recursive totality and non-vacuous trace existence are still separate obligations.
Separate rejection-context composition preserves a chosen window observation,
including file/end-byte-only frames that permit failed token/end-index changes.
It requires no body success, token preservation, validity, or progress contract.

Public atom rewind/recovery now has conditional independent traces, exact
State/Failure equivalences, and explicit core file/end-byte frames that preserve
changed failed carriers/end indices. Non-boundary recovery commits the core
report once; boundary and recovery terminal reports remain separate. Ordinary
execution and trace existence require an explicit core ordinary contract.
A stationary-child consumer satisfies all five child trace contracts and joint
exactness but reaches the actual parenthesized noProgress invariant; completeness
proves that neither independent atom outcome exists there. Recursive progress
and totality remain distinct obligations.

The actual selected core plus recovery now form a child-conditional public atom
layer. Separate unrestricted collection/core/public ordinary laws require only
successful child endIndex preservation, strict progress, bounded ordinary
execution, body ordinary execution, and an explicit remaining-count bound.
No validity or rejected carrier/source frame is needed for these totality laws.
Soundness plus this totality gives bounded non-vacuous core/public trace existence,
including an independent public remainder outcome. General recursive closure is
still open. A changed-carrier consumer verifies that public boundary testing uses
the failed tokens/endIndex after cursor-only rewind, not the original carrier.

Concrete reverse public consumers use a literal-only nested parser to check
checked-name-before-failure-before-recovery order, no replay on skipped names,
unread right parentheses, name-success bypass, uncommitted boundary failures,
and initial missing backing with exactly one committed original report. Lexical
filtering explicitly distinguishes protected name events from recovery/report events.

Real literal-child consumers discharge the minimal totality contract and exercise
invalid numerical carriers without assuming ValidFor. Overshot/hidden ends retain
the complete State, initial missing backing commits exactly one original report,
and independent group/tuple traces reconstruct successes with arbitrary prior
events. This keeps one-layer execution and its explicit budgets separate from
recursive expression closure.

Postfix-tail independent traces and runtime soundness now cover prioritized
index/call/field suffixes, exact ASTs, ordered events, and all seven failure
positions. Independent nested joint laws give uniqueness/disjointness only;
all-fuel soundness assumes nested success/rejection traces and success context,
without silently imposing index progress or totality. Finite derivations now
execute above derivation-specific thresholds. Separately, explicit child and loop
budgets plus the minimal child progress contract establish ordinary execution
and non-vacuous trace existence, including the production tail budget. Independent
joint exactness then gives fixed-fuel completeness. Whole-State/Failure equivalences
retain explicit invariant exclusion and, for rejection, weak child source/end-byte
frames. This is not yet recursive expression closure.

Concrete counter-consumers separate stationary index success from call noProgress.
A full-window-preserving rewinding child has five trace contracts and ordinary
execution, but its two-index independent trace needs fuel three where the initial
production budget is two. Reverse derivation checks and exact Reply checks retain
arbitrary prior events. Child framing and trace exactness therefore do not imply
the strict progress needed by production totality.

Real literal-child reverse consumers now cover mixed `.a-b[1](2)` maximal tails,
exact nested spans and States, later field failure with only earlier name events,
Boolean-keyword rejection as a field, duplicate prior events, and hidden/missing
suffix termination. These consumers instantiate production adequacy rather than
assuming it from trace correspondence.

Actual atom-plus-postfix composition now has independent ordered traces and
joint exactness, observed soundness, and pointwise complete State/Failure
correspondence under explicit invariant exclusion. Numerical totality separately
uses an ordinary atom and its successful endpoint bounds, or supplied atom/nested
progress contracts with two input bounds. Separate actual/independent existence
follows totality and soundness, not uniqueness. Atom contract construction and
recursive expression closure remain separate obligations.

The selected-core/recovery/postfix layer now specializes both soundness laws
to nested-expression/body trace contracts, with explicit full-window frames.
Bounded body contracts also replace global body ordinary execution in the raw
lambda/core/public atom totality laws; expression and body bounds stay separate.
These ordinary laws do not imply successful numeric-window preservation through
recovery or construct the atom progress contract.

Separate numeric endIndex frames now lift through both ordinary outcomes of
raw/core/public atoms. Child bounded contracts plus rejected-child endpoint
preservation construct the actual atom contract for A ≤ N+1 and A ≤ B+1, without
source/token/endByte/validity frames. An independent reverse recovery consumer
shows that child fuel contracts alone do not suffice: a rejected endpoint change
survives as public success. Recursive expression/block closure remains separate.

Actual postfix contracts now construct their atom contract internally and lift
numeric endpoint frames through the tail. Explicit child budgets/rejected endpoint
frames suffice for ordinary execution and the successor contract step. Concrete
layer soundness additionally supplies child-only actual/independent trace existence
under its source/window frames, without joint-exactness or completeness assumptions.

Unary traces now preserve maximal source-order operators, exact wrapped ASTs,
postfix events, and the terminal report. Scanner production is unconditionally
successful with complete silent-State correspondence and separate existence.
The unary layer independently lifts corresponding postfix soundness/completeness
contracts; whole-State iff adds only a matching weak file/endByte frame. No
child progress or joint law is mistaken for recursive expression totality.

The actual unary contract now inherits the postfix budget unchanged, since an
empty prefix pays nothing. Separate numeric frames, bounded ordinary execution,
and actual/independent trace existence retain their distinct assumptions.
Reverse literal-child consumers fix `!~a-b(1).c` operator order, complete postfix
operand/spans/State, one name event and prior multiplicity, later uncommitted
field reports, and minus/hidden/missing scanner boundaries.

At the complete diagnostic-free declaration level, strict soundness now covers
all four canonical import forms—plain, namespace, wildcard with or without a
hiding clause, and selective imports—transparent type aliases, and traits.
Unconditional strict soundness also covers all four canonical export forms:
local, module, module alias, and items-from-module, together with complete
algebraic enums. Parser-independent `ImportDeclParses` and `ExportDeclParses`
judgments combine their respective forms without caller-supplied AST shape
guards. `EnumDeclParses` directly characterizes complete enum success while
retaining the supplied derive attribute. Export and enum soundness need no
diagnostic-free premise. `PlainTopItemParses` records exact earlier-branch
absence, and `TopItemParses` records leading-hash priority and enum-only derive
attachment. The complete-file item loop and `SourceFileParses` theorem now
preserve forward order, strict progress, end-of-window termination, exact
comment attachment, and recovery diagnostics. Recovered malformed output
remains separate so that recovery is not confused with language acceptance.

This frontend work remains separate from the completed syntax-independent
execution semantics. Resolution, source typing, and elaboration will consume
the canonical syntax result after the grammar boundary is coherent.

## Completion conditions

The canonical syntax slice is complete when:

- every active token and parsed-node form has an executable witness;
- the selected canonical corpus parses and obsolete spellings are rejected;
- lexical and parse diagnostics are deterministic and source-located;
- all retained token, comment, and AST spans use valid UTF-8 byte boundaries;
- ordinary malformed input produces total diagnostic output;
- every diagnostic-free public `parseLexed` or `parse` result is proved
  derivable in both the parametric independent grammar and its concrete
  mutually recursive Core term, block, and inline-Yul ordinary specialization;
- the canonical frontend is the only current syntax described by public
  documentation; and
- the complete build, tests, metadata validation, and kernel audit pass.

Resolution, source typing, elaboration, and end-to-end source execution are the
next frontend stages. They consume the syntax result without changing the
meaning of checked Semantic Core or Oracle v5.
