# Current status

This page describes what works at the current revision and where its public
boundary ends. It is not an implementation-history ledger.

## At a glance

`solcore-lean` now has a public, syntax-independent path for checking Semantic
Core programs and executing checked contracts. Oracle v5 accepts an explicit
contract package, initial world, immutable execution environment, top-level
invocation, resource limits, and requested state probes. It returns a total
typed result as JSON.

The executable contract semantics and its Oracle v5 interface are implemented.
Checked-in command-line fixtures cover both Core checking and contract
execution, and the aggregate test and metadata checks protect those public
bytes.

A public Lean library can also generate reproducible, checker-sealed programs
from a pure Word/Boolean subset of Core Wire v3, package them as minimal Oracle
v5 scenarios, and enumerate type-preserving shrink candidates.

Standalone JSON Schema files have not been published for Core Wire v3 or
Oracle v5. Their closed wire catalogs and strict Lean codecs are the current
normative format definitions. Producing additional schema files is a packaging
task, not missing executable behavior.

Canonical Solcore syntax is implemented as a fresh `Solcore.Syntax` layer. Its
executable lexer and parser follow the stabilized syntax introduced by
`solcore-rs` PR #20 and do not reuse the Surface v1 or Multi AST and parser
definitions. Oracle v4 remains available only as a frozen historical
compatibility interface. Formal parser proofs continue after the executable
grammar; this does not block use of the Lean parser API.

## What works now

### Resolved local-expression semantics

Frontend semantic work now takes priority over additional diagnostic-trace
proof depth. `Solcore.Resolved` provides the first local-expression foundation
between source syntax and Semantic Core, as specified by ADR-0154.

Structured declaration/local identities retain module and library ownership.
Independent first-match lookup and positional judgments prove exact binding
selection, uniqueness, and non-dangling references. The monomorphic expression
fragment includes semantic unit/Boolean/Word values, local references, selected
Core unary/binary primitives, ordered unsigned Word less-than, immutable
expression binding, and conditionals.
Its total elaborator preserves lexical scope and rejects unresolved references.

Independent typing and named-environment evaluation are connected to Core in
both directions. Every typed expression has a type-preserving elaboration,
the checker accepts exactly independently typed expressions, and elaboration
preserves the exact evaluation result and store. Independent evaluation is
deterministic and store-preserving even when an unselected branch prevents
whole-expression elaboration. Closed typed expressions have an evaluation,
return the same result at all sufficient Core fuel, and never machine-fault.

Independent, type-free scope validity now characterizes successful elaboration
exactly, checking both conditional branches and excluding a new binder from its
own initializer. Injective identity renaming preserves the exact Core expression
(including elaboration failure), typing, and evaluation. Concrete counterexamples
show that merging two distinct IDs can instead capture an outer reference and
change its result; the injectivity premise is essential.

A local allocator now chooses an unused ID for an explicit owner and scope.
Its freshness is relative to that supplied scope, not an unexamined source
program. Fresh binding insertion preserves lookup and types, changes only the
corresponding free Core indices, and retains existing evaluation values and
stores. Inner binders may reuse the inserted ID: their own bindings remain
nearest. The evaluation-preservation law also covers a skipped ill-scoped
branch, without mistaking newly enabled elaboration for unchanged scope validity.
For originally well-scoped expressions, fresh insertion also reflects evaluation:
the exact value and both stores agree in both directions. Freshness alone does
not justify this inverse; an absent reference can become evaluable after insertion.

An explicit-ID derived Word less-than builder now composes two existing resolved
lets (ADR-0187). It evaluates left then right once and lowers exactly to the
Core `wordLt` expansion, including right-operand weakening and comparison of
the retained values at indices zero/one. The first temporary must be absent
from the original scope and the two temporaries must differ; the second may
reuse an outer ID, and inner source binders may shadow either ID. Word typing,
explicit-ID structural renaming and forward evaluation are proved. Evaluation
reflection additionally retains original right scoping. Counterexamples protect
the distinctness, non-capture and original-scoping boundaries. Continuation-aware
let/less-than path composition counts both child costs plus nine (eleven for two
leaves), with the weakened right path under the retained left value supplied
explicitly. No unrestricted Core weakening theorem is assumed. This is a resolved
foundation, not canonical `<` support or a hidden source temporary allocator;
existing resolver and arbitrary identity-map guarantees are unchanged.

An independent Core local-fragment predicate and exact environment-insertion
equivalence are now available (ADR-0188). Its structural forms include the
current resolved lowering; a separate `Lowers.localFragment` proof connects
them without Core depending on Resolved evaluation. With free indices shifted
past an arbitrary inserted value behind any retained prefix, successful
evaluation preserves and reflects the identical result and both stores. The
proof passes directly under Core lets and needs no type, scoping, freshness or
runtime-world premise; missing positional references stay missing too. Runtime
closures/cell references may be returned unchanged, but closure creation/calls
and cell operations are outside the predicate. CellFree alone would be too broad:
a created lambda captures a different environment after insertion. No equality
of suspended states, exact-cost transport or canonical `<` support is claimed.

The same independent fragment now has exact retained-prefix typing reflection
and inference-result equality (ADR-0189). Shifting free indices past an inserted
type preserves and reflects the identical result type under arbitrary data
definitions, including through nested lets. Executable inference retains both
success and rejection. Neither inserted/context types nor runtime inhabitants
need extra well-formedness assumptions. The position is fixed by the retained
prefix: unrestricted out-of-range `Context.insertAt` reflection would be false
because insertion clamps while weakening does not. All conditional children
still require typing, even when execution skips a branch. This static result
does not claim exact-cost transport or extend canonical operator support.

Exact-cost insertion is now proved for the same independent fragment (ADR-0190).
Each successful evaluation yields original and shifted paths with one common
cost, chosen before their arbitrary outer continuations. A supplied closed final
path can be transported and reflected at its exact length, retaining the literal
value, stores and outer continuation. Only empty-continuation final paths are
used for length uniqueness. Nested lets extend the retained prefix with the
actual bound value; skipped branches do not execute or add to the cost. Existing
fuel-threshold and checkpoint-resumption theorems apply to these paths, without
equating distinct suspended states or executing an outer continuation early.
This adds no typing or runtime-world premise and does not yet enable canonical
`<` or `>=`.

Binary pair construction now belongs to this independent local fragment
(ADR-0228), extending the original eight forms to nine. Both children must
belong, including syntactically present children that a conditional skips.
Existing evaluation, typing, inference and exact-cost insertion contracts keep
their original names and premises. Each pair evaluates left then right in the
original environment, retains actual component values and ordered stores, and
costs both child costs plus three. Shared-cost proofs build each side's own
pair frames and saved environment under the same unexecuted outer continuation.
Independent proof and executable consumers cover nested pairs/lets, retained
prefixes, opaque values, nominal static types, missing/wrong children and actual
pair checkpoints/resumption. Neither state equality nor typed inhabitants are
assumed. Core semantics and frozen wire rejection are unchanged; projections,
closures/calls and cell access remain excluded from this predicate. Resolved
pair representation is added in ADR-0229 below, followed by the separate
canonical two-element adapter in ADR-0230. Larger tuples and tuple type syntax
are not enabled by these changes.

Resolved immutable expressions now include ordered binary pairs (ADR-0229).
Their independent lowering, typing, whole-scope and raw evaluation constructors
retain both original child scopes/environments, arbitrary component types and
actual ordered values with left-to-right store threading. All 54 generic proof
contracts in the affected modules keep their original names and premises.
Core correspondence, complete inference, determinism/store preservation,
whole-scope closure and fresh insertion/reflection now include this case.
Rename identity/composition still allow arbitrary maps; first-match lookup,
lowering and semantic transport retain their existing injectivity condition.
Fresh insertion preserves its suffix-fresh boundary, and reflection still
requires original whole-scoping. No pair creates or allocates a binder.

Independent proof and executable consumers cover nested products/lets, exact
ordered Core and values, duplicate first matches, nominal open types without
inhabitants, opaque values, raw skipped-child success versus whole rejection,
and the existing renaming/freshness boundaries. Separate Core paths and actual
checkpoints preserve exact cost and both stores; same-typed wrong output is not
treated as correct lowering. This resolved prerequisite changes no Core
semantics, runtime entry gates or wire formats and introduces no source tuple
policy; its source adapter follows separately below.

Canonical two-element tuple expressions now use ordered binary products
(ADR-0230). The original delimited list must contain exactly two children, in
written order; both children retain the same caller tables, context and actual
environment. Independent resolution, product typing, whole-name avoidance,
raw evaluation and exact-cost constructors correspond to the existing resolved
and Core pairs. Both child costs plus three is the exact Core cost and the
source-only bound composition. The direct evaluator follows original syntax,
returning actual ordered values without consulting a checker or running Core.

All 80 affected public proof contracts retain their names and premises across
static checking, raw/Core correspondence, safety, renaming, fresh insertion,
store replay, costs, bounds and lookup-extensional direct execution. One cost
renaming module is split with the old import path retained. Explicit binary
nesting, grouping and existing trailing commas are supported without parser
changes. Empty tuples receive a separate meaning in ADR-0231 below; manually constructed singleton and larger tuple expressions,
tuple type syntax, projections and multiple return annotations remain unsupported.
The old two-element tuple negative is migrated to an independent positive.

Independent source, parsed-expression and complete-function consumers fix exact
Core, ordered values, types and costs separately from the tested evaluators.
They cover opaque raw values, nominal static types without inhabitants, actual
pair checkpoints and residual fuel, strict children and raw/whole contrasts.
True-and and false-or still forward any selected raw value, including a pair,
while whole Boolean typing rejects those ill-typed expressions. Existing
recursive function entries accept pair results through caller-provided named
product aliases, preserving original parameter-only records and all old gates.
No Core/resolved semantics, diagnostic, source type or frozen wire policy changes.

Canonical empty tuple expressions now denote the existing Unit constant
(ADR-0231). The original empty delimited list independently resolves, types,
avoids names and evaluates to Unit with the same store and exact cost one.
This leaf requires no caller lookup, actual-value typing, row alignment or
source-span validity. The direct evaluator and source fuel bound agree with
the single existing Core unit transition. All 80 existing generic proof
contracts in the expression proof suite retain their names and premises;
56 of those contracts occur in the 25 changed production modules.

Independent source, parsed-expression and complete-entry consumers distinguish
the nullary unit from binary pairs of units, preserve grouping at zero extra
cost, and retain actual continuations, stores and residual fuel. Raw short
circuits can forward Unit while whole Boolean checking still fails. Complete
Unit-return entries support omitted annotations and caller-provided named aliases;
strict Unit lets retain their two binding transitions and original parameter-only
records, and unused arguments retain every type/arity gate. The identifier and
type-name spelling `Unit` are not reserved. The former empty-expression negative
becomes an independent positive; the old arity rejection adds an explicit
nonempty premise. Wrong product-return/Unit-body entries remain rejected.
Manual singleton and larger tuples, tuple type syntax, explicit empty/multiple
return annotations and projections remain outside this change. Core/resolved
semantics, parser ranges, diagnostics and frozen wire formats are unchanged.

A separate opt-in structural type adapter now interprets original canonical
type syntax (ADR-0232). Independent named, Unit, singleton and ordered binary
product meanings correspond exactly to total interpretation. Type singletons
remain original tuple nodes, unlike expression grouping. All children use the
same caller table, exact qualified components and duplicate first matches;
arbitrary nominal types require no runtime inhabitants. Structural results need
not be table entries. The old named-only API and its whole-result membership
contract are unchanged.

Soundness/completeness, unique meaning, exact success/failure, outer-range and
lookup extensionality, successful semantic extension and full mutual-extension
equality are proved. Independent source and complete parsed-type consumers
cover explicit nesting/order, hidden duplicates, missing written leaves,
arbitrary raw ranges and unchanged unsupported forms. One-way extension may
enable a formerly missing leaf. This prerequisite initially left all
parameter/header/let annotation gates named-only; the shared single-return gate
is connected separately in ADR-0233 below, followed by parameters in ADR-0234
and recursive lets in ADR-0235. Original parsed annotations and correct-arity
actuals distinguish these integrations from the older named-only prefix adapter.
Larger tuple-type lists follow in ADR-0236. Other type constructors, expressions,
Core/resolved semantics, diagnostics and frozen wire formats are unchanged.

The existing shared return/header gate now accepts one structural annotation
(ADR-0233). `returns(())` denotes Unit, singleton parentheses preserve their
child type, and `returns((Word,Bool))` denotes an ordered product. Explicit
empty `returns()` and multiple `returns(Word,Bool)` remain rejected. No parallel
entry API is added. The independent single-return constructor intentionally
widens its premise to structural meaning; all seven general header/extension
theorem statements and 110 affected legacy source-test contracts stay unchanged.
Named-only evidence transports through the proved compatibility bridge.

Independent source and complete parsed-entry consumers retain original header
and body evidence, exact Core, original parameter-only records and reversed actual
environments. Unit/singleton, ordered and explicitly nested products, strict named
lets, conditional branches and opaque values keep their existing exact costs,
own stores and actual checkpoint/resumption paths. Static nominal results need
no inhabitants; type agreement never substitutes for exact Core provenance.
Old structural-return negatives migrate to independent positives. Parameter
integration follows in ADR-0234 and recursive lets in ADR-0235. Argument, modifier, whole-body, unknown-leaf,
empty/multiple-clause and unsupported-type gates remain in force. There is no
new runtime transition, expression, parser, Core/resolved, diagnostic or wire policy.

Structural parameter annotations now feed the existing static declaration and
actual binding adapters together (ADR-0234). Four constructor annotation premises
and two position-theorem meaning conclusions intentionally widen to structural
meaning. All other general contracts, including value erasure/restoration,
preparation factorization and named-only positional specializations, are retained.
Each original Unit, singleton or ordered/nested product parameter remains exactly
one row, generated identity and typed actual argument. Products are not flattened;
unused Unit parameters are not erased. Static nominal types need no inhabitants.

Independent source and parsed consumers check exact declaration/binding evidence,
original ranges, owner-relative sparse allocation, repeated initial names, reversed
actual environments, table extension and both source-position APIs. Whole entries
keep separately specified Core, values, costs, own stores and real resumptions;
same-typed wrong Core cannot substitute for provenance. Four old parsed rejections
become independent positives. One obsolete source rejection is explicitly renamed
and narrowed to the then-unchanged named-only/let boundary; the other 152 affected
source-test statements remain exact. Recursive lets follow in ADR-0235. Same-name rejection,
unknown leaves, count/type checks, whole-body/header gates and all
runtime, parser, diagnostic and wire policies remain unchanged.

Recursive typed let bodies now interpret structural annotations at the existing
entry boundary (ADR-0235). Two binding-rule premises and one annotation-decomposition
conclusion intentionally widen; the other 15 affected generic proof statements
stay unchanged. Old named-only prefix successes still embed, but new structural
tree successes do not imply optional equality with that older adapter. Initializers
remain mandatory, strict and checked in the old scope; only the fresh tail sees
the new binding. Whole conditional arms, unused-name checks and owner-relative
allocation retain their existing contracts.

Independent source proofs cover arbitrary type/let depth, exact Core and fresh
positions, nominal static types, opaque actual values, extension and relabeling.
An unused product initializer still costs eight transitions. Complete parsed
entries check original annotations, parameter-only records, explicitly specified
Core/value/cost, both stores and every bounded fuel/checkpoint/resumption path.
Three old parsed declarations (eight actual-argument vectors) become positives;
106 affected legacy source statements remain unchanged and one obsolete rejection
is explicitly renamed to retain the old named-only/prefix boundary. Product-on-Unit
mismatches, unknown leaves, self/forward/sibling references, shadowing and invalid
unselected arms remain rejected by the whole checker. Raw evaluation, fuel bounds,
Core transitions, parser, diagnostics and wire formats are unchanged.

Structural tuple types now support every finite element count (ADR-0236), following
the pinned reference's right-associated product convention: `(A,B,C)` denotes
`A × (B × C)`, without adding a terminal Unit. Explicit nested children remain
distinct. The original four rules and all 13 generic theorem statements are
retained; one independent `many` constructor covers three or more original
elements. Interpretation and soundness decrease the original source size;
outer-span independence recurses through the original-span tail. Every leaf
retains the same caller table and first-match meaning.

Independent arbitrary-length source proofs cover ordered child meanings, strict
missing leaves at every position, exact association, table/range transport and
nominal types without actual inhabitants. Complete parsed consumers retain flat
element counts, exact byte ranges, nested syntax and one row/actual per parameter.
Whole entries separately specify Core, values, costs, stores and genuine
resumptions: a strict unused three-element initializer costs 12 transitions.
Two parsed type negatives and one static parameter negative become independently
certified positives; the original wrongly typed Unit actual is still rejected.
Two obsolete source boundaries are explicitly renamed, while the other 26 affected
source-test statements remain unchanged. Old named-only membership, empty/multiple
return-clause rejection, expression tuple arity, projections, inference, shadowing,
Core transitions, fuel bounds, parser, diagnostics and wire formats do not change.

Canonical tuple expressions now also support every finite canonical element
count (ADR-0237). Three or more original elements form right-associated pairs,
without a terminal Unit or flattening an explicitly nested child. Empty Unit,
binary pairs and grouping keep their existing meanings. Five independent `many`
rules extend resolution, typing, name avoidance, raw evaluation and exact cost.
Head and tail retain the original caller scope, environment and both source
spans; evaluation visits them in order with actual intermediate stores.

All 80 affected generic theorem statements remain unchanged, including exact
Core correspondence, safety, renaming, fresh-input reflection, store replay,
lookup equality, direct evaluation and fuel bounds. One typing proof moves to
an import-compatible module. Each pair still adds exactly three transitions:
three/four one-step elements cost nine/thirteen, and an unused four-element
initializer in a strict let costs sixteen including its return.

Independent arbitrary-length source proofs and complete parsed expression/entry
consumers retain exact Core, association, original flat syntax and byte ranges,
first-match duplicates, nominal static types and opaque actual values. Manual
transition paths check all bounded fuel thresholds and genuine nested-pair/let
checkpoints with their saved environments, continuations and residual costs.
Selected raw success remains distinct from whole-expression checking. Five old
parsed rejection claims become independent positives; the obsolete generic arity
rejection is explicitly narrowed and renamed to manual singleton nodes, with
its old named-only type boundary and the ten other source statements preserved.
Manual singleton tuple nodes, projections/indexing/arrays/calls, inference,
shadowing, multiple return clauses and old named-only prefix adapters remain
outside this change. Core/Resolved definitions, parser, diagnostics and frozen
wire formats are unchanged.

Initialized local declarations now also accept an absent type annotation in the
existing recursive body and function-entry adapters (ADR-0238). The original
initializer independently fixes its unique type and exact Core in the old scope;
only the original tail sees the fresh binding. No annotation is synthesized into
the source AST, and an inferred product or nominal type need not occur as a whole
in the caller's type-name table. Written annotations still require their exact
structural meaning and matching initializer type.

Four new independent `inferred` rules retain the four old annotated binding
rules unchanged. All 53 directly affected generic theorem statements remain
intact; a new child-decomposition theorem exposes exact initializer/tail Core,
the inferred type and fresh scope. Whole typing, Core correspondence, raw value
and store laws, exact costs, direct execution, owner/lookup/type-table transport,
fuel bounds and checkpoint resumption include the new case. A copied leaf and
return cost four, an unused binary-product initializer and return cost eight,
and conditional selection can distinguish seven from four. Inference itself
adds no Core transition; every initialized let retains child costs plus two.

Independent mixed-prefix proofs and complete parsed consumers preserve original
annotation absence/presence, byte ranges, sparse IDs, exact Core and fresh tails,
nominal static types, typed opaque values, parameter-only records and real
continuations/residual execution. Eleven obsolete parsed rejection claims become
positives using their original source and callers; the older prefix adapter's
rejection and all neighboring invalid forms remain. Missing initializers,
self/forward/sibling references, ancestor shadowing and invalid unselected arms
still fail whole checking, independently of raw selected execution. This limited
monomorphic inference introduces no polymorphism, overload resolution, default
initialization, assignment, general calls or new shadowing policy. Core/Resolved
definitions, parameter/return annotations, parser, diagnostics and wire formats
are unchanged.

Exact frontend provenance now exposes membership in the independent local Core
fragment (ADR-0239). Four body-level bridges cover successful expression
elaboration and independent singleton-return, terminal-tree and recursive-let
elaboration. They use exact lowering and every original child, including both
conditional arms and written/inferred initializers. Four separate entry bridges
project this fact from independent compilation/preparation or their successful
executable results. No runtime values are manufactured, and body-level imports
do not depend on entries.

Independent source and parsed consumers compose these bridges with the existing
positional insertion laws for types, actual values and exact costs. Retained
prefixes, nested lets, nominal static types and existing opaque closures/cells
remain intact. Original and inserted executions resume their own genuine
checkpoints; matching final values and costs do not identify captured environments.
Membership itself guarantees neither valid indices, evaluation, source acceptance
nor whole-entry provenance for an arbitrary same-typed record. No accepted or
rejected source form, existing definition, constructor, theorem statement, parser,
diagnostic or wire policy changes in this proof-only step.

Strict semicolon-terminated expression prefixes now compose with the existing
recursive body and function-entry adapters (ADR-0240). The original expression
is resolved, lowered and typed in the existing inputs, with no Unit-type
restriction. Its original tail uses those same inputs: no source spelling,
LocalId or parameter row is introduced. Exact Core is a strict `letE` whose tail
is weakened under its hidden positional binder. Original AST spans, statement
order, first-match caller tables and owner-relative allocation remain intact.

Four independent discard constructors retain all previous constructors, and
all 58 directly affected theorem statements remain unchanged. A new exact
child-decomposition theorem retains the original expression and unweakened tail
Core. Typing and raw evaluation compose existing insertion/reflection laws;
exact paths first insert the actual discarded value into the tail's closed path
and then preserve any outer continuation. Cost and source bound add head plus
tail plus two. Discarded work remains strict, including unused products or
noncommutative arithmetic. These are the existing Lean Core transition counts,
not optimized Rust execution counts.

Independent mixed-prefix and complete parsed consumers retain original scopes,
exact Core, nominal static types, actual opaque values, complete entry contracts
and genuine saved-continuation residuals. Four previous parsed rejection claims
become independent successes using their original sources and callers. Narrower
body-only adapters and neighboring rejections remain unchanged. Missing
semicolons or terminal tails, statements after return, assignment, general calls,
unknown children and invalid whole contracts are not accepted by this extension.
Core/Resolved definitions, parameter-only records, parser, diagnostics and wire
formats do not change.

Singleton terminal lexical blocks now compose at every accepted recursive body
position (ADR-0241). The original inner statement list uses the inner braces'
span and the same caller scope. Four independent block rules preserve the
child's exact Core, type, raw value, initial/final stores and cost without a
new positional binder, source identity or transition. A full-Option checker
equality retains both success and rejection, and all 59 directly affected
generic statements remain unchanged.

Independent source and complete parsed consumers exercise finite wrapper depth
with mixed lets, strict discards and asymmetric conditional arms. Exact manual
paths, nominal static types, actual opaque values and original parameter rows
remain distinct obligations. Since wrapper and child have the same Core and
environment, their complete machine results and genuine saved states agree at
every fuel; residual execution does not restart the computation. Six legacy
parsed consumers migrate their original rejected block fixtures to whole-entry
successes, including six buried nominal declarations, with sources and callers
unchanged. Narrower body adapters, neighboring invalid cases and whole-entry
contracts remain unchanged. Empty or nonterminal blocks, local scope escape,
shadowing, implicit returns and general early returns are not added. The zero
additional cost is a Lean Core fact, not a Rust optimizer or emitted-cost claim.
No Core/Resolved, parser, diagnostic, wire or runtime-record definition changes.

An opt-in static root-application adapter now handles a known single-argument
Function type (ADR-0243). Original callee and argument expressions check in the
same caller scope using the existing pure child grammar. Independent whole
typing and exact elaboration retain the two original child lowerings and their
ordered `Core.apply`, with complete success/rejection correspondence and exact
Core/result-type uniqueness. No actual argument or closure inhabitants are
needed for static checking, including nominal context types.

This specializes the pinned builtin Function Invokable case, not general
overload or global resolution. One Unit/product argument is not a zero- or
multiple-argument list. Root grouping, nested calls, fields, source lambdas and
other invocation forms remain outside this adapter. Existing pure expressions,
return-body adapters and whole entries retain their previous boundaries. Static
acceptance alone does not supply execution, local-fragment membership, store
preservation or source-only fuel bounds. Core, Resolved, parser and wire
definitions are unchanged.

Independent successful source-call evaluation and exact costs now account for
the actual closure body, captured values and threaded stores (ADR-0244). The
original callee and argument evaluate in the caller environment; the body uses
the actual argument followed by the actual captures. Raw and cost judgments need
no checker premise. Erasure, cost existence and value/store/cost uniqueness hold
without runtime typing. Exact static provenance plus ordered runtime-ID alignment
gives both directions of Core evaluation and exact closed-path correspondence.

The cost is the original child costs plus the actual body path and three
application transitions. That same cost works under every continuation, whose
pending frames are retained rather than executed. The actual body may access or
change cells and have a different cost for identical source syntax and types.
Structural value typing does not establish allocated cells; raw selected-branch
success does not establish whole static acceptance. These raw correspondence
proofs alone provide no automatic termination/no-fault result, source-call
evaluator or whole-entry integration. Existing body/entry contracts and all
executable definitions remain unchanged.

Explicit runtime-world safety now supplies the missing dynamic premises
(ADR-0245). Actual caller and captured values must be runtime-typed in the same
world as the actual store, including allocated reference locations and valid
payload types. Independent whole-call typing then yields successful source
evaluation with an actual exact cost, a possibly extended world, a well-typed
final store and runtime-typed result. Exact elaboration retains that same cost
under every continuation and gives both closed-run fuel thresholds. Preservation
also applies to an independently supplied successful evaluation or checked run.

For machine-state safety, typed positional values, the typed store and a typed
continuation suffice; source-ID alignment is needed only for source evaluation
correspondence. All-fuel fault exclusion and preservation through actual
exhaustion checkpoints retain complete frames, captures and current stores.
Untyped pending frames may still fault. Successful execution reuses Core's
existing restricted payload/reducibility theorem with the empty data environment;
it is not a termination claim for arbitrary stateful closure languages or a
source-only bound. No checker/evaluator, body/entry, parser or Core definition
changes are introduced.

A separate checked application endpoint now runs on the existing actual
`LocalInputs` record (ADR-0246). `checkApplication?` preserves exact original-call
elaboration, and `runApplication?` uses the same ordered values and supplied
store. Outer absence is exactly static rejection, independent of fuel and store;
successful checking preserves the static type tag and every complete Core result,
including faults and genuine exhaustion states. Completion reflects independent
raw evaluation, and completion at some fuel is equivalent to whole typing plus
that evaluation.

Whole typing with an actual cost gives exact completion/exhaustion thresholds;
genuine checkpoints retain exact residual paths and full-result resumption,
including fault outcomes and the same tag. Explicit runtime-world typing of these
same values and store separately supplies typed completion, an actual sufficient
cost and all-fuel fault exclusion. Structural input typing alone does not:
a missing cell can fault, and a wrong payload can produce a Bool under a checked
Word tag. Independent original parsed calls and declarations cover these cases,
delayed closures, writes, allocation and rejected unselected branches. The old
pure and whole-entry endpoints remain unchanged. A direct source-call evaluator
remains separate work; later body/entry integration and opt-in runtime-world
validation are described below.

Original singleton application-return bodies now have a separate opt-in profile
(ADR-0247). The complete block must contain exactly one return with an original
application expression. Four independent rules preserve the block/return/child
syntax and the child's exact Core, type, value, stores and actual cost. Static
checking corresponds exactly to independent elaboration and whole typing; raw
evaluation and cost laws retain the child semantics. Ordered IDs give Core
evaluation and closed exact-cost correspondence both ways, with the same cost
under every retained continuation.

The new body checker and runner equal their child endpoints as complete Options,
at every fuel and store. No return frame, binder, source ID or transition is added.
This preserves faults, static tags and genuine checkpoints as well as successful
results, so existing cost, resumption and runtime-world guarantees transfer using
the same actual inputs. Whole-body absence and fixed-fuel typed-cost reflection
also hold. Bare or pure returns, surrounding statements, conditional statements,
nested blocks and nested calls are outside this profile. Existing pure/recursive
body and whole-entry acceptance remain unchanged; general body integration must
separately address their local-fragment insertion, store and fuel contracts.

A separate explicit whole-function entry now connects this application-return
body to the original declaration (ADR-0248). New compilation and preparation
propositions require the unchanged header policy, original parameter declaration
or actual argument binding, and the exact body Core at the declared return type.
Distinct compile/prepare/run endpoints reuse only the existing data records;
local body acceptance does not bypass a whole-header or return-type failure.
Static compilation needs no argument inhabitants, and exact success/rejection
and complete-record uniqueness hold independently for both stages.

Preparation erases to the new compilation and can be reconstructed from actual
supplied arguments with matching arity and ordered types. Complete-Option
factorization retains failures; full-result execution equals the prepared body
runner and the compiled Core on the original argument values reversed once.
Binding fixes those actual values and captures, while execution separately fixes
the store. Same-typed value swaps may change prepared inputs and results without
changing the compiled projection. Body/child cost, checkpoint, resumption and
runtime-world guarantees transfer through the complete execution equalities.
Missing cells and wrong payloads remain observable; arbitrary-store safety,
store independence and source-only bounds are not imported from the old entry.
Old endpoints and records remain unchanged. This is explicit entry execution,
not global/source-function resolution, source closure creation or recursive calls.

Exact application provenance now supports caller-slot insertion without extending
the old local fragment (ADR-0249). Both original child lowerings supply the
existing pure-child insertion laws, so the actual returned closure, captures,
argument and effectful body are retained literally. Raw evaluation and exact
typing are equivalent before and after insertion at any retained-prefix cutoff;
arbitrary caller contexts, inserted values/types and data definitions need no
source-ID agreement, runtime inhabitants or runtime-world assumptions.

Paired paths choose one common cost before the outer continuation. A supplied
closed path preserves and reflects its exact cost, result and final store.
Caller frames and exhaustion checkpoints can differ, and a retained continuation
endpoint is not necessarily final. This neither guarantees arbitrary-store
success nor permits closure-producing children: such children can capture the
added slot. This leaf changes no executable or old body/entry contract; recursive
mixed bodies use the separate structural insertion proof described below.

A shared nonrecursive computation child now combines the unchanged pure
expression and root single-argument application profiles (ADR-0250). The original
root selects its old checker; independent whole typing and exact provenance
agree with this combined checker. Raw and cost relations wrap either original
child without changing values, stores or transition counts. Whole typing still
checks children skipped by raw evaluation; actual call values and effects are
not inferred from static types.

Eight shared contracts cover checking, typing, raw/cost existence and determinism,
raw/Core correspondence, uniform continuation paths and exact closed costs.
Three insertion kernels preserve arbitrary caller/context slots for either
branch. No duplicate runner, runtime-world or source-bound family is introduced.
This is a child profile, not itself a let/discard/guard or whole-entry
implementation. Nested calls, calls inside pure operators and
grouping around an entire call remain outside this nonrecursive union.

A separate recursive mixed body now uses that child in returned expressions,
annotated/inferred initializers, strict discards and terminal if/else guards
(ADR-0251). It also retains bare returns and terminal lexical blocks. The original
AST, spans, optional annotations, first-match tables and fresh named IDs determine
exact Core and types independently of the checker. Every named initializer uses
the old scope; a discard adds only a hidden Core binder, with unchanged source
scope. Both written arms are checked, while raw evaluation selects only one.

The new raw and cost semantics pass each child's actual intermediate store to
the tail or chosen arm, including effectful calls and returned callable values.
A separate four-form caller fragment proves closure under repeated weakening
and exact raw/cost insertion without restricting actual closure bodies or
captures. Original-ID agreement gives bidirectional Core correspondence and
exact costs before any continuation. The old pure elaboration embeds with the
same Core and type, but its store/source-bound guarantees are not transferred.
Call-result lets, effectful discards and call guards are now body-level forms;
whole-function header and argument gates are handled separately below. Nested
expression calls and general early returns remain outside the profile.
Old pure/application entries and all runtime records are
unchanged. Arbitrary-store safety and a source-only cost bound are not claimed.

A separate explicit function entry now connects that mixed body to the original
header and ordered parameters (ADR-0252). Independent compilation and preparation
evidence retain the exact original Core and declared return type. Value-free
compilation needs no actual inhabitants; preparation uses the same actual bound
input record for its type-only view and runtime values.

Four shared laws characterize exact-record checking and full-Option preparation
and execution. Compilation plus the ordered argument-type guard accounts for
all rejection. Running additionally uses the original argument values, reversed
once, and the separately supplied store; declared tags, faults and genuine
checkpoints are retained. Same-typed argument swaps are accepted but may change
actual results or effects despite the same compiled projection. Old successful
pure and singleton-application cases embed one way; old endpoints are unchanged.
Runtime-world/store evidence is still needed for safety, and no new source-only
bound, unfuelled evaluator or global source-call mechanism is introduced.

A separate recursive expression profile now admits nested single-argument calls,
computed callees and arbitrary grouping (ADR-0253). Each original callee and
argument is checked recursively in the same scope; direct unary, Word binary,
ordered/negated comparison, conditional, fixed lazy and tuple roots are extended below.
Other roots retain the old pure interpretation.
Independent syntax/type/Core evidence and raw/cost rules
preserve the exact actual closure, captures and callee-to-argument-to-body store
order. Grouping adds no Core wrapper or transitions, even where pure/group
derivations overlap. Fourteen shared kernels connect checking, typing, exact
execution/cost and caller insertion, with unchanged old-success embeddings.

The recursive caller fragment permits applications, direct unary/binary combinations,
pairs, conditionals and generated lets of recursively admitted children, without source lambda construction.
Its paired insertion paths use the same actual
body path and one cost before every continuation; intermediate caller states
need not coincide. Old mixed-body/function entries remain unchanged and do not
accept these nested expressions. Calls under other unextended expression
forms, source lambdas and global function resolution remain outside this
profile; pure such subtrees remain usable as call children. No source-only fuel
bound, store-invariance or arbitrary-store safety is inferred.

A shared body engine now connects these recursive expression children to mixed
bodies (ADR-0254). Its checker, independent typing/elaboration and raw/cost
relations take separate child operations or judgments, not a bundled runtime
contract. The original seven static and eight raw cases retain source spans,
owner-filtered fresh IDs, initializer-before-binding, unchanged discard scope
and selected-branch store flow. The concrete recursive body uses the ADR-0253
child; no parallel family of specialized proof aliases is added.

Twelve shared laws cover exact checking/typing, raw cost existence and joint
determinism, Core evaluation and exact cost before every continuation, plus
whole-body membership, weakening and literal insertion. A separate unit/leaf/
let/if fragment closes the entire discarded tail, without requiring arbitrary
child predicates to contain bare return. Paired paths retain actual captures,
bound values and stores, with one cost chosen before every continuation.
Old mixed elaborations and costs embed unchanged; static checking still inspects
unselected written branches even when raw evaluation can skip them. Existing
whole-function endpoints remain unchanged; a separate shared entry connects the
new body below. No source-only bound, source closure construction,
general early return or arbitrary-store safety follows from this integration.

A shared explicit entry now compiles, prepares and runs recursive computation
bodies (ADR-0255). Its operations receive only the child checker; independent
whole compilation/preparation evidence receives only child elaboration. Original
header policy, parameter declaration or actual binding, body provenance and the
declared-return gate are retained. Five concrete specializations select the
recursive child without adding a parallel wrapper-theorem family.

Two exact-record success laws use the child's checking correspondence. Two
full-Option factorization laws hold for any child checker, independently of
semantic correctness: compilation and the original ordered argument types
account for preparation rejection. A private checker graph supports only those
operational equations, not independent source semantics. Actual running uses
the original supplied values reversed once and the separately supplied store.
Same-typed argument/capture swaps can change values and effects despite equal
compiled projections; declared tags, faults and genuine checkpoints are kept.
Existing pure/application/nonrecursive-computation endpoints remain unchanged.
Structural argument evidence alone supplies neither store validation nor safety.
Source closure construction and global source-function resolution remain separate.

The same recursive child now admits ten direct Word binary operators (ADR-0256):
arithmetic, bitwise and/or/xor, greater-than and equality. An independent finite
operator relation and one map-correspondence law select the existing Core
interpretations; this is not general overloaded-operator resolution.
Both original children retain their spans and caller scope. Static operands are
Word, with Bool results for comparisons. Raw rules instead thread actual stores
left to right and apply the operator to the actual values afterward, with exact
cost left plus right plus three. Zero divisors retain the existing Word results.

The fourteen recursive proof signatures and the shared body/entry implementation
remain unchanged. Private compatibility proofs reconcile old pure and new binary
evidence, including raw lazy branches that skip unsupported syntax. Binary caller
insertion preserves literal values, stores and one cost before every continuation.
The former recursive addition rejection fixtures now assert independent exact
success; the older nonrecursive endpoints retain their rejection. Recursive
conditional, unary, fixed lazy, ordered/negated comparison and tuple roots are
recorded below. Actual wrong
payloads can fault after a successful right child's effects; neither structural
typing nor this extension supplies store safety.

Canonical conditional roots now recurse through the same child (ADR-0257).
Independent typing and elaboration inspect the original Bool guard and both
written branches, requiring exactly the same branch type. The original question,
colon and child spans remain intact; the exact Core is the corresponding ifE.
Raw and cost rules instead evaluate the actual Bool guard and selected branch
only, threading their real intermediate store at guard plus branch plus two.
Unknown or mismatched unselected syntax can still permit raw success while
preventing whole static success. Wrong actual guard payloads fault before choice.

Seven constructors extend the existing relations and caller fragment; all
fourteen recursive proof signatures and the shared body/entry code remain
unchanged. Private pure/conditional compatibility retains old overlapping
derivations. Literal insertion uses only the actual selected path, with a shared
cost before every continuation. Original recursive ternary rejection fixtures
become exact independent successes, while old nonrecursive endpoints still
reject them. Parsed and symbolic consumers retain unequal branch costs, actual
guard/selected effects, returned callables, full faults and genuine ifBranches
checkpoints. No unselected effect, source-only bound or arbitrary-store safety
is inferred; other unextended expression roots remain separate.

The two canonical unary roots now recurse through this child (ADR-0258).
Logical negation requires Bool and complement requires Word, preserving the
original operand, prefix span/order and exact Core boolNot/wordNot. These are
the existing fixed interpretations, not general named-function/class resolution.
Raw rules use the actual child payload and preserve its final store at child
cost plus two. Child effects remain visible even if a wrong payload then faults;
a child fault prevents unary application. Pure/raw overlap can still skip
unsupported child syntax without making that whole expression statically valid.

Nine constructors extend the existing static/raw/cost and caller-fragment
relations; the fourteen proof signatures and shared body/entry code stay
unchanged, with no new operator map or wrapper laws. Literal caller insertion
retains the actual child path and one cost before every continuation. Original
Word complement and Bool negation rejection fixtures become independent exact
successes, while logical negation of a Word and old nonrecursive entry rejection
remain intact. Parsed/source/entry consumers retain exact values and captures,
operand effects, full fault tags and genuine unaryApply checkpoints. No stronger
store safety, general overload mechanism or source-only cost bound is implied.

Fixed Boolean conjunction and disjunction now recurse through this child
(ADR-0259). Both original children are statically checked as Bool, while the
exact Core expansion is `ifE left right (bool false)` or
`ifE left (bool true) right`. The internal constants do not use source lookup.
This extends the established ADR-0159 profile, not general Rust operator-function
resolution: the pinned Rust version resolves named and/or functions as ordinary
calls and explicitly leaves their short circuiting unimplemented. Only its
residual logical BinOp emission uses the corresponding conditional expansion.

Raw execution requires an actual Bool only on the left. A selected right child
returns its actual value and final store at left cost plus right cost plus two;
skipping keeps the left final store and costs left plus three, counting the
internal literal. Thus a statically Bool right call can successfully return
Word from an unchecked actual store, retaining the explicit entry's Bool tag.
A wrong left payload faults before the right child; a missing right cell faults
only when selected. Whole checking still rejects unknown unselected syntax.

Twelve constructors preserve all fourteen recursive proof signatures. Existing
typing and continuation laws move to smaller proof modules without new public
helper families; caller-fragment constructors and insertion rules are unchanged.
The shared body/entry code is reused unchanged. Three original rejection cases
retain their source and ordered caller tables as independent exact successes.
Parsed, symbolic and actual-entry consumers exercise selection-dependent costs,
effects, faults, literal caller insertion and genuine ifBranches resumption.
No source-only bound, arbitrary-store safety or general overload agreement follows.

Fixed Word inequality and unsigned less-or-equal now support recursive children
(ADR-0260). Both original children are checked as Word in the same caller scope;
the exact Core is Bool negation around ordered Word equality or greater-than.
No source rewrite, operand swap, negation folding or general ne/le resolution
is introduced. Original operator spans and non-associative precedence stay intact.

Successful raw rules retain the actual left and right Words, intermediate and
final stores, and negated comparison result at both child costs plus five.
Both strict child effects occur before primitive application: a wrong actual
left payload can fault only after the right child's effects, whereas a fault
inside the left child prevents the right child. Comparison and negation remain
distinct pending frames with exact checkpoint and resumed outcomes.

Eight constructors retain all fourteen recursive signatures. Cost determinism
and its private overlap proof move to a smaller module reexported through the
old evaluation entry point. Existing unary/binary caller-fragment and insertion
rules already cover the expansion; shared body/entry definitions stay unchanged.
Two original rejection fixtures migrate with identical source and ordered caller
tables, while older endpoints and wrong operand types remain rejected. Parsed,
symbolic and actual-entry consumers retain exact values, captures, effects,
faults, costs and fuel boundaries. Ordered less/greater-equal and tuples follow below;
general operator resolution, source-only bounds and store safety
remain separate.

Unsigned less and greater-or-equal now admit recursive children (ADR-0261).
Both original Word operands retain their caller scope. The exact less-than Core
evaluates and saves the left operand, evaluates the positionally shifted right
operand once, then compares the saved right and left values. Greater-or-equal
adds the original outer Bool negation. No source operand is swapped and no
temporary LocalId is allocated. Exact successful costs add nine or eleven to
the original child costs.

One generic letE caller-fragment constructor supports both generated bindings.
Insertion proofs retain the actual bound value ahead of an arbitrary caller
prefix and choose one paired cost before every continuation. This handles
recursive calls in the right operand without assuming the smaller call-free
local fragment. Its actual captures and ordered stores stay literal. Reverse
execution removes the same insertion to recover the original right source.

Eight source constructors and the fragment constructor preserve all fourteen
recursive signatures. The cost judgment moves to an independent definition
module reexported through its old import. Shared body and entry definitions are
unchanged. Original rejection fixtures migrate with identical source and caller
tables. Consumers check generated-binding checkpoints, ordered writes, payload
and child faults, exact fuel and full resumption. Recursive tuples follow below;
source closures, general lt/ge resolution, source-only bounds and store safety remain
separate; this is not a claim about Rust's emitted AST or execution costs.

Canonical tuple roots now admit recursive computation children (ADR-0262).
Binary and longer tuples retain their original ordered elements and caller scope,
with the same right-associated product type, Core and value as the pure adapter.
Longer tuples decompose internally using their unchanged remaining elements and
the original outer/delimited spans. Explicit nesting is not flattened and no
terminal Unit is inserted. Empty tuples retain the old pure Unit rule; parsed
singleton parentheses remain groups, while manual singleton tuple nodes stay
unsupported.

Independent source typing/elaboration and raw/cost pair/many rules preserve
arbitrary component types and actual values. Evaluation threads the actual store
from head to tail and adds three transitions per pair. Generic caller pair
membership and insertion retain both child scopes, actual captures and bound
values, with one paired cost before every continuation. All fourteen contracts
and shared body/entry definitions remain unchanged, without new public helpers.

Six original rejection fixtures now assert independently justified successes
with identical source strings, file/owner identities and ordered caller rows.
Symbolic, parsed and entry consumers check original flat lengths, grouping and
nesting, literal right-associated Core, actual values/effects, strict child
faults, saved pair frames and full residual resumption. Pair construction itself
does not require runtime-typed components. Source closures, global resolution,
other expression forms, source-only bounds and arbitrary-store safety remain
separate; the exact cost is for the existing Lean Core machine.

Shared mixed bodies and original function entries now have three generic
runtime-world safety kernels (ADR-0263), with no executable-definition or
acceptance change. Exact original body elaboration, child Core typing and the
existing child execution/cost/insertion laws connect a same-world typed actual
environment and store to successful evaluation. The result retains an extending
final world, runtime-typed value/store, original-source cost, one cost before
all continuation-local paths and both exact closed-run fuel thresholds.

The entry kernel uses each original actual argument's runtime typing in that
same world. Existing reverse-once value/type layout identifies the exact prepared
environment; structural argument typing alone cannot supply these premises.
Independent original preparation and child checker correctness retain the full
prepared record and every complete stateful runner result at the supplied fuel.
Runtime premise validation is a separate opt-in boundary described below;
no new runner or per-profile wrapper family is introduced.

The state-only kernel requires a typed actual environment, store and pending
continuation, but no source-ID alignment or child execution/cost laws. It gives
all-fuel no-fault and typing/no-fault for the exact saved out-of-fuel state under
every resumed fuel. The checkpoint's world remains existential in StateHasType;
explicit world extension is provided for final body evaluation, not asserted
for that checkpoint. Untyped pending work may fault after a valid body endpoint.

Independent symbolic and parsed consumers cover typed/inferred bindings,
blocks, strict discards, conditional returns, actual reader/writer/allocator
closures, captured-value and same-typed argument swaps, literal saved states
and full resumption. A fixed original body has unbounded actual costs across
well-typed delayed callees. Missing/corrupt stores, structural-only references
and separately incompatible worlds cannot discharge the safety premises.
The old fourteen recursive, twelve shared body and four shared entry contracts
remain unchanged. Empty nominal definitions and existing CellPayload limits
remain in force; there is no unrestricted Solcore termination guarantee,
arbitrary-store safety, source-only bound or new source syntax support.

Actual typed arguments and a supplied store now have an opt-in executable
same-world validator (ADR-0264). Its one public iff theorem identifies success
exactly with runtime typing of every original argument and StoreHasTypes for
the same supplied world/store. These two facts directly supply the existing
generic entry safety kernel; original source checking, preparation, argument
order, values and every full runner result remain unchanged.

The validator checks references in all actual pair components, selected sum
payloads and closure captures, including nested and unused captures. Existing
TypedRuntimeArgument structural evidence already checks closure bodies and
captured types. The validator is not a raw-value, JSON, tag-only or source
checker, and it does not require extra well-formedness of unused signature or
sum-alternative types. Each actual reference must match its world location
and element type.

World and store are checked together to their exact common end. Every cell,
including unreferenced cells, must have an allowed CellPayload type and matching
actual value shape. Functions/references/nominal types remain forbidden in cell
payloads even when they occur only in the unselected side of a sum. Equal
lengths, a matching prefix or valid referenced cells alone are insufficient.
The validator only returns a Bool: it does not infer, extend or repair a world,
change a value/store, reject source preparation or guard an existing runner.

Raw Core values can now independently construct existing TypedRuntimeArgument
records (ADR-0265). The one public Option builder preserves the literal actual
value and its exact tag. Its exact-record iff accepts precisely any existing
typed record whose value is that original input; structural type uniqueness
and proof irrelevance retain the whole record, not just a matching type list.
Ordinary list traversal therefore preserves original arguments and order without
a new list adapter or any change to preparation and full runner results.

The builder checks all actual pair/selected sum payloads and captures, including
unused and nested captures. Closure bodies use the existing complete Core type
checker under the parameter and the actual captured-value types. This is not
typing a newly wrapped lambda: signature and unselected sum types gain no extra
well-formedness conditions. Same-tag malformed bodies, host values and nominal
constructed values under empty definitions are rejected. Actual references are
structurally accepted without asserting allocation; the separate ADR-0264
validator checks the supplied world and complete store before its iff can
supply ADR-0263's safety premises. Neither stage evaluates, repairs or replaces
the input, decodes JSON, enables source closures, or guards an existing runner.

Genuine computation checkpoints now expose extending store worlds (ADR-0266).
One additional shared theorem takes the same original body typing, actual
environment/store and typed pending continuation as the state-only safety kernel,
plus the actual outOfFuel equation. It returns a saved world extending the
original supplied world and typing the literal saved store. Every finite Core
path from that exact saved state has a store typed in a further extension of
the same saved world, including paths recovered from resumed checkpoints.

The prefix relation preserves every old cell's location and type, not its
stored value: typed writes may change values, while allocation appends a type.
Private world uniqueness and the two store-changing transition cases reuse
existing state preservation, allocation and write proofs. An untyped pending
write can instead change a cell's type even when both endpoint stores are typed
and equal in length; a separately typed arbitrary state is not a substitute for
a genuine checkpoint. The earlier state/no-fault kernel remains unchanged.
No source-ID alignment, child execution/cost law, new state relation, runner,
validator or executable definition is added.

Terminal single-scrutinee Word matches now extend the shared computation body
engine (ADR-0267). Its initial profile retains original literal case order,
including duplicates, and requires a default. Every case and default body
is checked in the original caller scope at one common result type. Literal
patterns remain strict in-range Words; binders, constructor patterns,
and multiple scrutinees remain outside this interface.

Independent source selection evaluates the original scrutinee once, keeps its
effects, and executes only the first matching body or the default. Static checks
still inspect unselected bodies. Exact Core uses one hidden let and ordered
Word comparisons, weakening each original branch under the saved actual value
without adding a source name or identity. Each visited comparison adds seven
transitions, and the hidden let adds two, on top of both actual child costs.
These are Core costs, not a claim about Rust/Hull instruction counts.

The existing checker, typing, raw execution, exact-cost and insertion contracts
retain their signatures. Arbitrary case-count consumers preserve actual called
bodies, captures, stores and pending continuations, including allocations and
genuine checkpoints after any visited prefix. A default-only match performs no
Word comparison and may return an arbitrary raw value; nonempty literal cases
instead fault on an actual non-Word operand. The separate runtime input/safety
premises remain necessary. Older local-only body and entry interfaces are
unchanged; general pattern matching and overflow agreement are not claimed.

Ordered wildcard cases now extend that profile (ADR-0268). An original `case _`
selects its body immediately when reached, without a comparison or binding.
Later literal/wildcard cases and any default remain original static
obligations even when unreachable. The checker distinguishes a successful
wildcard tag from failure, checks every body, and only then discards the unused
Core tail. Literal pattern meaning and the existing shared theorem signatures
are unchanged; wildcard marker spans are not identified with enclosing spans.

The scrutinee still runs once through the existing hidden let. Cost counts
executed literal comparisons only: wildcard adds zero, while the outer let
still adds two. Leading wildcard can therefore accept an arbitrary actual raw
value; an earlier literal comparison on a non-Word still faults and retains
prior effects. Original-source consumers retain captures, stores, selected
effects and genuine checkpoints, separately consuming the opt-in runtime
input/safety contracts. This initial interface restricted static scrutinees to
Word; ADR-0271 below relaxes that restriction only for catch-all-only matches.
Binding patterns and general exhaustiveness remain separate.

Original defaults are now optional when an original wildcard covers the Word
cases (ADR-0269). Their absence stays literal in syntax, selection, typing,
elaboration and raw/cost evaluation. A default body still anchors the common
result type when present; otherwise the first original case body does so.
Every original case and any default are checked, including unreachable bodies.
The branch result type is not restricted to the scrutinee's Word type.

Lowering uses an optional Core tail: a literal needs a successful tail, while
a wildcard supplies its own original branch even when a later literal-only
suffix has no Core tail. No source default or Unit/error fallback is fabricated.
Empty cases without a default and missing-default literal-only cases fail
static acceptance even when a supplied actual value produces a raw literal hit. A dedicated checker
decomposition keeps the existing shared 12 theorem signatures unchanged;
choice and match constructors intentionally generalize the default to Option.
Arbitrary prefixes, actual effects/captures, nested scopes, precise costs and
genuine checkpoint/world resumption retain the earlier guarantees.

Original pattern groups now transparently wrap those same literal and wildcard
meanings (ADR-0270). Arbitrary nesting retains every Lean group and its outer
span, as well as the original leaf and marker; the reference parser instead
erases singleton parentheses, including a singleton trailing comma. No syntax
normalization or agreement on those intermediate spans is claimed.

One total pattern interpreter has an exact independent classification law.
Grouped wildcard still supplies optional-default coverage, and every original
unreachable pattern/body remains checked. Group depth adds no comparison or
Core transition: source costs, actual captures/stores, nested scopes and genuine
resumption remain unchanged. Classification generalizes the choice/static and
checker-decomposition pattern premises; the shared 12, recursive 14 and entry 4
signatures and old strict literal meaning remain unchanged. Grouped binders,
Boolean/constructor patterns, tuples (including hand-built singleton tuples),
comptime/error leaves and overflowing literals are not admitted by grouping.

Catch-all-only matches now accept any scrutinee type supported by the existing
child profile, independently of the common branch result type (ADR-0271).
This includes original default-only matches and bare/grouped wildcard cases
with present or absent defaults. The checker retains the inferred scrutinee
type and checks every original pattern/body before requiring Word or all-none
case tags. Independent typing uses original wildcard classifications; exact
elaboration uses original row tags, related by classification uniqueness.
Empty/no-default matches still fail coverage. An unreachable numeric literal
still rejects a non-Word scrutinee despite raw leading-wildcard success.

The same Core fold, raw selection and exact-cost rules remain unchanged.
An ignored scrutinee still executes once and occupies its actual hidden slot;
zero comparisons cost both child executions plus two. Arbitrary types do not
create runtime inhabitants or validate captured references and stores.
Independent consumers cover arbitrary types/row counts/actual payloads,
allocation and full resumption. Exact formerly rejected Bool sources now have
positive evidence; nested Bool/function scrutinees preserve named/discarded
slots, captured closures, writes and genuine saved-world extension. Only match
constructors and checker decomposition generalize; shared12, recursive14,
entry4, strict/grouped pattern laws and older runtime interfaces stay intact.

Explicit function type annotations now have independent structural meanings
when their original parameter list contains exactly one type (ADR-0272).
An absent or empty return list means Unit; a singleton keeps its child type,
and multiple returns form right-associated products without a terminal Unit.
Nested functions and explicit tuple nesting are retained, as are the original
keyword, delimiter ranges, list order and absent/present distinction. Named
leaves use the same caller table and first-match priority; no function alias
row or runtime inhabitant is required. Existing exactness, uniqueness, span,
extension and whole-option lookup laws retain their public signatures.

The existing parameter, recursive typed-let and single outer return annotation
gates inherit this support without changing Core or execution rules. Parsed
consumers use actual supplied factory/writer closures to allocate, capture,
write, invoke and return another closure, preserving exact source/Core costs,
values, stores and genuine resumption. Missing references retain earlier effects;
corrupt stores can still produce raw values, while opt-in same-world validation
rejects them. Static annotation meaning is not a runtime-safety assertion.

Source arity remains explicit: function((A,B)) and function(()) are unary,
whereas zero/multiple-parameter function types and calls remain outside this
profile. Inner function return lists do not broaden the separate outer
declaration policy: it still accepts absence or one written annotation only.
Named-only adapters, source lambdas, global resolution and unsupported type
constructors remain unchanged. Old rejection fixtures migrate with their exact
source contexts; wrong Unit/Word arguments still fail actual binding.

Shared computation bodies now admit typed and inferred same-name let bindings,
including parameter shadowing and repeated same-block bindings (ADR-0273).
Each original initializer uses the old scope; only afterward does the existing
owner-filtered allocator prepend a new identity, type and actual value.
First-match lookup selects the new row in the tail, while every old row and
captured value remains present. A new binding may have a different type.
The Core let, raw evaluation and exact-cost rules are unchanged.

Admission has a deliberate terminal-if boundary. The pinned Rust resolver visits
bare then and else lists sequentially in one scope, whereas explicit blocks and
individual match arms introduce scopes. A source-only occurrence relation and
exact Boolean guard therefore require the then body not to expose any let that
rebinds a current input spelling. Both arms of nested unscoped ifs are inspected;
explicit block and match interiors stop that inspection. Else shadowing is
allowed because these ifs are terminal. Then-only new names are still unavailable
to Lean's else inputs: this is a conservative profile, not complete reference
name resolution or permission for nonterminal sequencing.

Independent typing, checking, execution and cost retain the shared twelve,
recursive fourteen and entry four theorem contracts. The old fresh-name body
adapters and earlier runtime endpoints retain their restrictions and one-way
embedding; duplicate parameters remain rejected. Only three original recursive
rejection fixtures move to positives, preserving their source contexts and costs.
New consumers cover arbitrary repeated spellings and actual values, sparse and
foreign identities, changed types, explicit scope barriers and rejected bare
then shadows despite successful raw else evaluation. Parsed captured-reader and
writer examples retain allocations, writes, exact 45-step paths, genuine saved
worlds and resumption; corrupt stores still fail the separate runtime validator
and preserve preceding effects on raw faults. Source lambdas, global resolution,
general early returns and older non-shadowing endpoint policies are unchanged.

Shared computation bodies and function entries now preserve their complete
results when caller type-name tables preserve existing first-match meanings
(ADR-0274). Four body and eight function laws transport independent typing and
elaboration, compiled records, actual prepared inputs and full runner outcomes.
Original syntax, annotation leaves, all conditional/match branches, fresh local
identities, Core and actual captured values remain fixed. This is an additive
proof layer: every existing executable and earlier theorem body is unchanged.

One-way extension preserves successful results; mutual extension additionally
preserves rejection. Hidden conflicting rows may change while visible meanings
remain identical. A prefix changing the first meaning is not an extension, and
adding an unknown annotation can turn whole-source rejection into acceptance,
even when that annotation is in an unselected branch whose raw counterpart did
not need it. These distinctions are exercised on original parsed declarations.

The operational equations use the same arbitrary child checker on both sides,
without a new correctness premise. Its private success graph is only an
equational proof device, not independent source semantics. Symbolic consumers
retain arbitrary types, nested function/tuple annotations and repeated names;
parsed consumers retain actual captured references, allocations, exact costs,
faults and genuine checkpoints. Same-fuel/store transport does not validate
stores, reconstruct runtime inhabitants or expand source admission.

Recursive local computations now preserve independent elaboration and typing,
complete optional checking, raw evaluation and exact costs under simultaneous
injective local-ID relabeling (ADR-0275). Five additive laws keep the original
AST/ranges, positional Core, type, every actual value and both stores fixed.
Name/context/environment row order and duplicate entries are retained. Maps may
change owners and binder indices and need not be surjective; reflection recovers
original evidence without introducing an inverse or runtime inhabitants.

The raw laws retain the same actual closure body/captures/argument and its Core
path. They require no whole-source acceptance, runtime typing, world, aligned
IDs or unique rows, including skipped unresolved syntax and a selected non-Bool
lazy RHS. Absence of successful raw evaluation is also reflected, but does not
classify faults or prove termination. Checked Core execution and checkpoint
comparisons use their separate original elaboration and actual environments.

This is a child-expression boundary: the profile allocates no named source
binder. General ID relabeling here does not commute with the shared body's fresh
allocator; owner-only body/function integration remains separate. Non-injective
collapse can change first-match meanings, Core positions and actual results.
All old executable definitions, contracts and consumer contexts are unchanged.

Shared computation bodies now retain independent elaboration and typing in
both directions under injective declaration-owner changes (ADR-0276). Three
additive generic laws keep the original body/ranges, type-name table, result
type and exact positional Core. The same fixed child interface supplies its
own covariance; recursive children instantiate it through ADR-0275. Complete
optional checker equality preserves rejection as well as success, without
requiring correctness of an arbitrary covariant child checker.

Fresh typed and inferred lets retain binder indices through the existing
owner-filtered allocation law. Reflection remembers original input scopes;
it requires neither an inverse nor surjectivity. Repeated spellings, sparse
indices and foreign-owner rows remain ordered. Name protection, both if arms,
all match branches and optional defaults retain their independent evidence.
Actual values/stores and complete execution observations are compared through
the same original Core, not a new raw-body owner or runtime-safety theorem.
General binder-index maps, nominal declaration renaming and function/header
owner integration remain separate. No old executable or semantic contract
changes, and source admission does not expand.

Shared raw computation bodies now preserve and reflect successful evaluation
and exact costs under injective owner-only relabeling (ADR-0277). Two additive
generic laws each assume only their own fixed child's covariance. Independent
inductions retain the original source, selected branches, actual values and
both stores; no relation between the raw and cost child interfaces is imposed.

Name tables and environments remain separate ordered inputs. Duplicate IDs or
spellings, missing/reordered rows and environment-only fresh-ID collisions are
allowed. Fresh IDs still come only from the name table, and a new binding
prepends its actual value without repairing or removing existing rows. Strict
initializers/discards retain every effect and cost; the same match choice keeps
the selected source body and visited-comparison count.

Raw success does not inspect typed-let annotations, unselected branches or
static scope guards. Absence of successful evidence is reflected, but is not a
fault or termination classification. Original parsed consumers separate such
raw-only rows from independently elaborated/aligned Core execution examples,
including actual captures, ordered cell effects and full checkpoints. No world,
checker, typing or fresh-in-environment premise is added to either new law.

Shared function compilation, actual-argument preparation and full execution now
also commute with injective owner-only relabeling (ADR-0278). Five additive laws
preserve and reflect independent compilation/preparation judgments, map the
complete optional compiled/prepared records, and retain every full runner result
at the same fuel and initial store. Only local-input IDs change; parameter order,
binder indices, source/ranges, types, Core, actual values and captures remain.

Each independent law assumes covariance of the same child elaboration relation;
the executable laws instead require whole optional covariance of the same child
checker. Neither assumes checker correctness. Private parameter reflection keeps
original input preimages and uses injectivity, not an inverse or covariance under
all owner maps. Existing record dependencies remain; old direct-function owner
proofs are not used to establish the shared-body result.

Consumers distinguish value-free compilation from wrong actual arity/types,
whole preparation rejection from selected raw body success, and preparation
success from actual runtime faults or invalid store payloads. Independent source
and literal Core evidence retain arbitrary closure costs, strict effects, full
saved states and resumption. No source feature, header policy, raw function
evaluator, runtime-world premise or existing executable definition changes.

Independent shared function argument factorization is now available directly
for an arbitrary child elaboration relation (ADR-0279). Five additive laws erase
preparation to compilation, reconstruct preparation from supplied typed arguments
with matching ordered types, characterize a fixed compiled projection, preserve
the reverse-once actual value sequence, and identify preparations having the
same arguments and compiled projection. No child checker or its graph is needed.

Value-free compilation does not invent runtime inhabitants. Reconstruction
retains every supplied value and capture, together with the original source,
parameters, local IDs, Core and return type. Matching type lists preserve arity
and ordered parameter types but do not prohibit same-typed value permutations.
Those different supplied values can produce distinct prepared records and runs.

Uniqueness is deliberately limited to a fixed compiled projection: an arbitrary
child relation need not choose one Core term. Explicit artificial nondeterminism
and hand-built invalid-record consumers check that boundary separately from
actual source semantics. Original symbolic/parsed consumers reconstruct actual
rows and retain raw costs, ordered effects and full saved states without a
runtime-world assumption. Existing operational factorization is unchanged.

Prepared-function checkpoint safety now has two minimal independent entry laws
(ADR-0280). Original preparation and child Core typing suffice once the literal
arguments, supplied store and pending caller frames are typed in one runtime
world. No child checker, source evaluator/cost, fragment/insertion law or source
ID alignment premise is needed. A private ordered-parameter bridge retains the
actual values and captures, reversed exactly once in the Core environment.

The first law types the exact initial state and every genuine checkpoint, with
fault exclusion at all initial and resumed fuel amounts. The caller result type
may differ from the function's return type. The second law extends the original
world to the saved store, then extends that same saved world along every further
finite path, including pending caller allocation and writes. Neither law claims
termination, source-cost correspondence or acceptance by an arbitrary checker.

Missing allocations, incompatible actual stores, untyped pending work and
unrelated typed states remain distinct boundaries. Runtime-world premises are
sufficient for the guarantees, not a necessary condition for every terminating
run. Earlier stronger execution/source-cost laws and all executable definitions
remain unchanged.

Expected-type unary lambda headers now have a separate opt-in declarer
(ADR-0281). With an explicit function domain and codomain, the original single
runtime parameter either inherits the domain or checks its structural annotation
against it. An omitted return annotation keeps the expected codomain, not Unit;
a present annotation must agree. The original outer type-name table is used
before one fresh parameter row shadows any outer spelling without deleting it.

The returned header contains only inner type inputs, the exact original body,
and the expected domain/codomain. Four laws give independent semantic exactness,
absence, uniqueness and original-header/fresh-row provenance. No runtime values,
Core expression or closure are constructed, and no body is checked. Header
success can coexist with a body error or a mismatched actual body return type.

The declarer judges the actual AST, not parser diagnostics or a forbidden name
string. Explicit error parameter nodes and comptime markers remain outside this
runtime profile; a recovered inferred node is not rejected just for its recovery history.
Existing recursive-child/body/function lambda rejection, literal-value insertion
contracts and all old executable definitions remain unchanged. Expected-type
propagation into recursive children and closure semantics remain separate; the
standalone body-checking step is described below.

Expected unary computation lambdas now connect the original header to the
original shared computation body (ADR-0282). The opt-in elaborator checks both
component types in the fixed empty Core data environment and requires the body's
inferred type to equal the expected codomain. It produces a literal Core lambda,
without changing the original syntax, outer rows or fresh parameter scope.

Independent elaboration, exact checking and absence, Core typing, and retained
header/body provenance are available generically. Checker exactness requires
only the child's exact checker law; Core typing separately requires the child's
Core-typing law. Neither actual inhabitants nor blanket outer-context type
well-formedness are required. Unregistered nominal component types remain outside
this fixed Core profile even when the wider header and a variable body succeed.

Symbolic and parsed consumers retain captured-variable positions and typed and
inferred shadowing. Existing Core transitions verify full-environment capture
without body effects at creation, and allocation/writes only on later application.
These are Core consumers, not source-lambda operational correspondence or general
canonical backend closure execution. Existing recursive-child/body/function
entry points still reject source lambdas, and literal insertion contracts remain
unchanged; automatic expected-type propagation and capture semantics are pending.

Expected computation lambdas now also have an independent source-only typing
judgment (ADR-0283). Its definition retains the original header, both component
guards and the original shared body typing, without a Core expression, an
existential elaboration or a checker graph. Source typing corresponds to existence
of a lambda elaboration using only the child's typing/elaboration correspondence;
the child's exact checker law additionally yields successful checking.

These laws need no child Core-typing law, determinism or actual runtime values.
The expected type remains an input: one original inferred identity can be typed
at both Word-to-Word and Bool-to-Bool. Artificial nondeterministic children expose
why elaboration existence does not require an exact optional checker or imply
uniqueness. Original scopes and body guards remain in force, and no new executable
entry point, old source admission branch or source runtime judgment is added.

An opt-in body adapter now connects an original leading explicitly typed let to
its expected lambda initializer (ADR-0284). The original annotation supplies the
expected function type, including first-match named aliases. The initializer uses
the unchanged outer inputs; only the original tail receives the fresh let row.
Independent source-only typing, elaboration, exact checking and Core typing are
proved with their separate child assumptions. Provenance retains the original
head, annotation, initializer, tail and exact fresh-row layout.

The lambda parameter and outer let may reuse one fresh number in disjoint scopes.
An initializer reference may resolve to an existing outer binding, never the new
let row; lambda parameters retain their own inner shadowing scope.
Original tail calls and closure returns are covered, with Core-only actual-capture,
store-write, allocation and checkpoint consumers. This handles one typed lambda
head followed by the unchanged shared body, not inferred-let nominal closure
inference, further lambda heads, new old-entry admission or raw source evaluation.

The separate maximal-prefix adapter now supports consecutive original explicitly
typed lambda lets (ADR-0285). A source-only classifier recognizes direct lambda
initializers without inspecting annotation meaning, arity, markers or body typing.
Recognized heads use their current pre-binder inputs and recurse only into the
fresh-bound original tail. Failure at such a head never falls back to old shared
checking. The first non-head delegates the whole remaining original block to the
unchanged shared body, without restarting prefix handling later in that block.

Disjoint terminal/head elaboration and independent source typing have exact
checker/existence laws with separate child assumptions, Core preservation and
one-layer original provenance. Arbitrary prefix lengths and captures of previous
bindings are covered. Artificial exact children demonstrate why the old one-head
adapter does not embed unconditionally; a non-head tail is a sufficient boundary.
Grouped lambdas and ordinary lets remain terminal shapes, not normalized heads.
Old entry points and raw source/runtime contracts remain unchanged.

A separate mixed frontend value representation now retains source closures as
original code-and-capture data (ADR-0286). All ten Core value forms are mirrored
recursively, including Core closures with mixed captures. Source closures retain
the complete original expression, owner and ordered name/ID/value rows without
typing, uniqueness or alignment assumptions. Even unsupported or nonlambda
syntax can be represented as inert data; this does not admit or execute it.

Total Core embedding, exact roundtrip, successful-image characterization and
injectivity preserve every old value, including arbitrary tags, code and captures.
Structural projection fails on any finite source-closure subterm, including an
unused Core capture or raw store slot. Cell references project without following
the ambient store. No type inference, elaboration, store snapshot or validation
is hidden in conversion. Independent raw source creation/application rules form
a separate layer below; a mixed evaluator, correspondence and safety remain open.

An independent raw source-closure layer now defines original unary creation and
call sequencing over mixed values (ADR-0287). Its shape judgment and exact decoder
retain one original inferred or unmarked typed parameter and the original body.
Annotations are uninterpreted: unmarked syntax does not establish canonical
runtime staging, even with comptime type syntax or parser diagnostics.
Creation preserves the entire source, lexical rows and store without running the body.

Calls evaluate callee then argument in the caller scope, then the saved original
body in the captured scope using the argument's final store. The saved owner and
saved name IDs alone choose the prepended parameter row; arbitrary old captures,
duplicate/foreign rows and environment-only ID collisions remain intact.
Exact creation/call decomposition and separately conditional callback determinism
are proved. This success-only parametric layer does not close its callbacks into
a general evaluator, dispatch Core/host closures, classify unsuccessful effects,
or imply typing, staging, source/Core correspondence, termination or safety.

Original computation bodies now have a separate mixed-value evaluation family
(ADR-0288). It retains the nine raw forms: bare/expression return, terminal block,
typed/inferred let, semicolon discard, the two selected Bool branches and ordered
single-scrutinee Word match. Initializers run before binding; exact names-only
fresh rows and actual stores pass to unchanged original tails. A leading wildcard or
empty-case default accepts source closures, while a visited literal requires a Word.
No unselected branch, annotation meaning or additional scope guard is inspected.

Original choice/count and body value/store determinism are proved, the latter
conditional only on child determinism at the fixed owner. Old body derivations
embed under a one-way child law. On embedded old inputs, exact reflection requires
every actual child result and final store to factor through old values and evaluation.
Real source creation followed by discard refutes weaker endpoint-only agreement,
even with deterministic children. Uniform exact body images also force the strong
child condition through original expression returns. The strong law is conditional,
not full conservativity of a source-lambda extension. This body callback composes
with raw source calls; general expression callback closing, mixed Core interoperability,
canonical name correspondence, failed effects, executable fuel and safety remain open.

Original source expression/body evaluation is now recursively closed for a
syntax-bounded fragment (ADR-0289). Eight expression forms cover first-match
references, empty tuples, strict Words, groups, pairs, larger original tuples,
source creation and unary source calls. Nine original body forms recurse through
these children without externally supplied evaluation callbacks. Calls keep the
callee and argument in caller scope, then use the saved owner's literal rows and
names-only fresh parameter for the original body. Mixed captures remain unrestricted.

Exact body compatibility and original-unary-call compatibility are proved against
the existing open relations. One joint expression/body induction establishes
value/store determinism without child-law premises; body determinism is then derived
through compatibility. Independent consumers prove successful store invariance and
the absence of success for excluded call/tuple shapes and Core/host call targets.
Here closed means recursive judgments, not empty lexical terms or a total runner.
The fragment has no mutating primitives or Core/host dispatch, and untyped higher-order
calls are not guaranteed to terminate. Canonical name/staging correspondence, mixed
Core execution, executable fuel, failure classification, costs and safety remain open.

The existing ordered Core Word less-than expansion now consumes these insertion
foundations directly (ADR-0191). With only the right operand in the local
fragment, typing inversion recovers the Bool result and both original Word
operand typings. Raw evaluation preserves and reflects original left-to-right
operand evaluations with their actual intermediate/final stores. Left Core
effects remain unrestricted; no runtime typing, world, freshness or scope premise
is added. Original continuation-independent operand paths compose at their costs
plus nine without requiring callers to supply a shifted-right path. Whole
expansion membership requires both operands to be local. The right restriction
cannot be dropped: allocating a captured closure may change the literal store
under insertion even when the right operand returns the same Word. This proof
bridge preserves existing Core APIs and does not yet change the Resolved or
canonical source expression representation.

Resolved expressions now have a dedicated identity-free `wordLt` form
(ADR-0192). Both original children lower in the original scope, producing the
existing two-let Core expansion without choosing temporary LocalIds. Independent
Word/Word-to-Bool typing, ordered raw evaluation, and whole-child scope validity
extend through this form. All generic lowering/checker, type/evaluation
correspondence, determinism, store preservation, renaming and fresh insertion/
reflection contracts remain unchanged. Arbitrary structural ID maps introduce no
allocation problem; semantic map preservation keeps its existing injectivity
premise, and duplicate IDs keep first-match lookup. The expansion still belongs
to the local Core predicate. Raw evaluation may skip an unresolved or
ill-typed child, while whole lowering/typing still checks it. The explicit-ID
builder remains available with its original hygiene contract. That representation
unit did not enable canonical source `<`; its adapter integration is described below.

The resolved fragment alone is not a canonical source adapter. It does not interpret literal
spelling, resolve `true`/`false` or overloaded operators, allocate source-wide IDs,
decide source shadowing or mutable-declaration semantics, or cover imports,
polymorphism, functions, and staging. Repeated IDs have explicit first-match
table behavior; that is not a proof that a source resolver allocates unique IDs.
No Oracle or wire interface changes.

### Canonical local-reference semantics

`Solcore.Frontend` now connects canonical identifier/group ASTs to the resolved
local layer using explicit caller-supplied tables (ADR-0155). Resolution uses
exact spelling and ignores source ranges. Independent resolution and reference
typing characterize successful conversion to the exact Core variable and type.
A mapped name whose ID is absent from the type context fails conversion;
neither an index nor a type is invented.

Independent reference evaluation and checked Core execution agree on the
value and unchanged store when the type context and runtime environment have
the same identity order. With a typed environment, existence and value-type
preservation follow as well. Grouped references take exactly one Core transition:
zero fuel retains the initial state, and every positive fuel returns the same
result. This is not a bound on frontend traversal or lookup work.
An executable-semantics counterexample keeps every positional type Boolean
while swapping two runtime identities: the Core position then reads the wrong
value. Thus positional type compatibility alone cannot replace identity-order
agreement. Duplicate-identity examples retain exact first-match behavior.

Only identifiers and grouping are supported by this adapter. Name-table
construction, source shadowing, fresh IDs, literal interpretation, operators,
imports, and complete source typing are still open. `true`/`false` are ordinary
caller-bound names, and unsupported AST forms do not become language rejections.
The canonical parser and every Oracle/wire boundary remain unchanged.

### Canonical local conditional semantics

A separate adapter extends identifiers and grouping with canonical conditional
expressions (ADR-0156). It preserves AST nesting and resolves all three children
using the same explicit name table. Independent source typing requires a Boolean
condition and the same type for both branches, without coercion or truthiness.
Successful elaboration gives exactly the resolved expression, Core expression,
and independently assigned type; unsupported or missing names receive no defaults.

Independent source evaluation evaluates the condition and only its selected
branch. It is deterministic and store-preserving even if a skipped branch cannot
resolve or type-check. Whole-resolution and exact runtime identity alignment
give value-and-store correspondence with Core in both directions. An aligned,
typed local environment guarantees an evaluation of the assigned type, the same
result at every sufficiently large Core fuel, and no machine fault at any fuel.

Executable regressions now start with source text and use the existing canonical
lexer and complete expression parse before checking and executing the actual
returned Core. They cover conditional nesting, grouping, comments, caller-bound
`true`/`false`, static failures, and exact four/seven-transition boundaries.
The narrow reference adapter embeds with the same checked result, including
missing-context failure, and the same value and store endpoints.

This is a monomorphic explicit-table expression fragment, not complete source
typing or a source-text execution service. The narrower reference adapter stays
unchanged. Source declarations, general literal typing, overloaded operations, calls, mutation,
and staging remain separate; no parser or Oracle behavior changes.

Boolean negation `!` now extends this internal adapter (ADR-0158), using the
existing direct Core `boolNot` primitive. Its independent typing rule requires
a Boolean operand and result, and evaluation negates the operand exactly once.
The full resolution/typing/evaluation correspondence, typed execution, and
unused-name insertion laws include this case. A named operand completes in
three Core transitions. Parsed negated conditions, double negation, and nested
conditionals are tested; operator source ranges have no semantic effect.
`true`/`false` still use caller bindings. There is no truthiness or overload
search.

Short-circuit `&&` and `||` also have canonical source semantics (ADR-0159).
They resolve to the established conditional expansions with generated Boolean
constants, independently of any `true`/`false` name bindings. Source typing
requires both operands to be Boolean, including a skipped right operand.
Evaluation visits the left operand once and the right only when selected;
the existing exact correspondence, typed execution, and unused-name laws apply.
Raw untyped evaluation forwards a selected right value even if it is not Boolean,
just as the conditional expansion does. This does not admit such an expression
to checked execution. Tests distinguish this boundary from raw evaluation that
skips a missing or unsupported operand, which still prevents whole checking.
Parsed precedence, grouping, and nested right operands exercise exact fuel
differences between selected and skipped paths. Comparisons other than unsigned
Word `>`/`<`/`<=`/`>=`/`==`/`!=` and arithmetic beyond the separately specified
Word addition, subtraction, multiplication, unsigned division and remainder
remain unsupported.

Word complement `~` is also supported as a fixed Word-only operation
(ADR-0161), using the existing direct Core `wordNot`. Independent typing,
raw evaluation, and checked execution preserve its exact 256-bit result and
store. The operand is evaluated once; named and double-complemented operands
take three and five Core transitions. Bool/reference inputs are not coerced,
and numeric interpretation uses the separate layer below. Tests include arbitrary
Words, double-complement involution, raw selected Word operands that cannot
type-check as Boolean, parsed conditions, and exact fuel boundaries. The
unused-name and identity-relabeling laws also cover this constructor.

Word-only binary `&`, `|`, and `^` now extend the same adapter (ADR-0164),
mapping directly to the existing Core bitwise operations. Independent source
typing requires Word operands and result. Evaluation visits each operand once,
left before right, and passes the intermediate store to the right operand.
These are not short-circuit forms: even a zero mask cannot hide a missing,
invalid, or wrongly typed right operand. Raw Word evaluation inside an operand
may still skip an invalid conditional branch, but whole checking rejects it.
Exact resolution, type/value/store correspondence, typed execution, unused-name
insertion, and ID-relabeling proofs include all three forms.

Parsed tests retain canonical precedence (`&`, then `^`, then `|`) and left
association in the exact checked Core. Mask examples produce `0x88`, `0xEE`,
and `0x66` from `0xAA` and `0xCC`; literal pairs take five transitions and
preserve nonempty stores. Grouping, complement, conditional branches, wrong
Boolean uses, whole-check failure, and unchanged results under input extension
or ID relabeling are tested. Value commutativity does not reorder source operands.
No general overload, assignment, parser, or Core-machine policy changes.

Word-only binary addition now extends the same explicit adapter (ADR-0176).
Both operands must be Words, and the exact resolved/Core tree retains a
`wordAdd` node without constant folding. Independent evaluation visits the
left operand before the right and uses the existing modulo-`2^256` Word sum.
An accepted maximum Word plus one wraps to zero; an out-of-range literal is
still rejected by strict literal conversion. Zero does not bypass an unresolved
or wrongly typed operand, and whole checking still inspects skipped branches.

The independent cost is both child costs plus three transitions. Two leaves
take five, and the exact four-step suspended state retains the right value and
the pending addition of the left value. Resolution, typing, evaluation,
continuation-aware Core correspondence, identity relabeling, and unused-input
cost laws all cover addition. Independent compiled-function evidence and fully
parsed expressions/declarations retain actual Core, source order, canonical
precedence, wrapping results, stores, and exact fuel boundaries. No parser,
evaluator, or general arithmetic-overload policy is changed.

Word subtraction and multiplication now use the same strict adapter (ADR-0177),
retaining ordered `wordSub` and `wordMul` Core nodes. Both independent typing
rules require two Words. Evaluation passes the intermediate store from left to
right, uses the existing modular operations, and costs both children plus three.
Zero minus one yields the maximum Word; maximum times two wraps to modulus
minus two. Neither zero nor one bypasses written operands or whole checking.
Literal range rejection remains separate from arithmetic wraparound.

All generic resolution, type, evaluation, safety, continuation-aware exact-cost,
renaming, and unused-input laws cover these operators. Fresh-input typing and
evaluation proofs are split into smaller modules without changing their public
names or the old import path. Independent arbitrary-Word consumers and complete
parsed declarations check noncommutative subtraction, multiplication precedence,
grouping, all 58 tested ordered parameter pairs across the two operations, and
the exact pending binary frame at four transitions before completion at five.
Unsigned division and remainder are specified separately below; unary signs and
assignments remain outside the restricted expression adapter.

Word-only `/` and `%` now lower to the original ordered `wordDiv` and `wordMod`
nodes (ADR-0199). Their values use the established unsigned `Word.udiv` and
`Word.umod`: a zero divisor gives zero for both, including remainder. Neither
zero dividend nor zero divisor skips an operand. Both Word children evaluate
once, left before right, and exact cost/source bounds add three to the child
costs. Two leaves require five transitions even when the result is zero.

All independent resolution, typing, raw/cost evaluation, Core correspondence,
safety, ID/insertion/store invariance, bounds and genuine-state resumption laws
cover both forms with unchanged premises. Return bodies and integrated terminal
entries retain their actual arguments, exact checked Core and provenance without
extra transitions. Independent and parsed consumers cover unsigned boundary
values, quotient/remainder distinctions, zeros, noncommutative operands, actual
pending binary frames and exact completion thresholds. Obsolete unsupported `/`
and `%` negatives are migrated without discarding call, non-Word, or unselected-arm
rejection. A structural bound may increase even when a Bool/Word mismatch still
rejects checking. No parser, primitive, wire, profile or overload policy changes.

Unsigned Word `>` now produces a Bool through the direct ordered `wordGt`
node (ADR-0178). Both operands must be Words even though the result is Boolean.
The existing unsigned ordering makes equality false and high-bit/max Words
greater than zero; it does not reinterpret them as signed or return Word flags.
Independent evaluation still visits both operands in order and costs both
children plus three. All generic correspondence, safety, exact-fuel, identity,
and unused-input proofs include the new form without changing their premises.

Independent compiled/prepared declarations return Bool, while an otherwise
matching Word return annotation is rejected. An arithmetic comparison used as
a conditional guard has independently proved selected/skipped branch costs.
Fully parsed expressions and declarations retain arithmetic/bitwise/comparison/
Boolean precedence, non-associative comparison boundaries, all 29 tested ordered
parameter pairs, and exact fuel-four pending Word operands followed by a Bool
at five. Existing source range/spelling/grouping laws are split into a small
module with their public names and old import path preserved. `<` and `>=`
remain separate; operand swapping is not a comparison lowering.

Word `==` now also produces Bool through the direct ordered `wordEq` node
(ADR-0184). Both operands must be Words; matching Bool/reference/closure types
do not turn this monomorphic rule into general equality. Raw evaluation visits
both sides and costs their two child costs plus three. All independent typing,
resolution, evaluation, cost, renaming, unused-input, store-replay and structural
fuel-bound proofs cover equality. The generic entry, compiled execution and
genuine-checkpoint residual-path guarantees continue to apply unchanged.
The evaluation rules and determinism proof are split without changing existing
public names or the old import path. Independent and fully parsed consumers
retain equal/unequal/high-bit/max values, ordered fuel-four operands, Bool at
five, computed guards, strict whole rejection and declared return contracts.
Symmetric final results do not license swapping the source/Core operands or
actual argument values. Parsing still preserves equality's non-associative
precedence below relational operators and above Boolean short-circuit forms.

Word `!=` uses ordered equality followed by Boolean negation (ADR-0185). Its
resolved and Core trees retain the outer `boolNot` and inner `wordEq`, and the
independent source rules still require two Word operands. Both child costs plus
five account for the full expansion: two leaves leave equality pending at fuel
five, negation pending at six, and return the inequality Bool at seven. Source
fuel bounds use the same extra five transitions. Evaluation reflection peels
both nodes; continuation-aware paths compose the ordered binary path with the
outer unary path. Generic safety, stores, renaming, unused-input, compiled entry
and genuine-checkpoint resumption proofs cover the form. Cost erasure/existence
and determinism are split without changing prior public names or import paths.
Consumers preserve actual operand positions, both pending frames, whole Word-only
checking, non-associative parsing and exact declared return contracts.

Unsigned Word `<=` is also supported through ordered `boolNot(wordGt(left,
right))` (ADR-0186). The source result is the negation of unsigned greater-than;
equal operands return true, and swapping unequal operands changes the result.
Both children must be Words and are evaluated left to right, with cost and
structural bound equal to both children plus five. Fuel-five/six checkpoints
retain the greater-than application and then its Bool awaiting negation; two
leaves finish at seven. All generic static, evaluation, cost, store and exact
resumption guarantees cover this nested lowering. Parsed order/unsigned boundary
cases and entry contracts retain actual arguments. Relational precedence remains
non-associative and stronger than Word equality; a parsed comparison Bool cannot
serve as a Word operand for another comparison or equality.

Unsigned Word `<` now resolves to the dedicated identity-free resolved form
(ADR-0193). Both original operands resolve under the same table and evaluate
left to right exactly once. The Core expansion uses two positional lets, shifts
the original right references and compares the retained right/left values with
`wordGt`, yielding `decide (leftWord < rightWord)`. Both operands must be Words;
equal values produce false and high-bit/max values retain unsigned order.
Source cost and the structural fuel bound add nine to the child costs, so two
leaves finish at eleven. Genuine checkpoints at two/five/ten retain the left
value, right value and pending comparison, with nine/six/one steps remaining.
All generic type/evaluation, arbitrary structural ID-map, input-extension,
store, bound, resumption and compilation-provenance contracts are unchanged.
Parsed arithmetic/conditional compositions and Bool-returning entries consume
actual arguments. Six obsolete `<` rejection fixtures were migrated in that
unit; parser precedence and chained-comparison rejection remain unchanged.

Unsigned Word `>=` resolves to `boolNot(wordLt(left, right))` (ADR-0194), with
both children under the original table. The two ordered Core lets evaluate each
operand once, and the final negation yields `!(decide (leftWord < rightWord))`.
Independent typing still requires two Words and returns Bool, with equal values
true and high-bit/max values unsigned. Cost and the structural bound add eleven
to child costs; two leaves take thirteen transitions. Genuine checkpoints at
three/six/eleven/twelve retain both binding environments, the comparison frame
and then the pending negation, with ten/seven/two/one transitions remaining.
All generic static/dynamic and exact-store/fuel/resumption/provenance contracts
cover the form without stronger premises. Parsed tests cover actual ordered
arguments, unsigned boundaries, short-circuit and arithmetic/conditional
composition, and whole return-type rejection. Seven obsolete `>=` rejection
fixtures were removed. Parser chain rejection remains; unsigned division and
remainder are now supported separately by ADR-0199.

### Numeric spelling and strict Word interpretation

An independent numeric-literal layer now gives whole canonical decimal and
hexadecimal spellings their natural-number meaning (ADR-0162). Digit and
positional-sequence relations characterize the total decoder exactly. Only
ASCII digits are accepted; hexadecimal requires lowercase `0x`, allows both
letter cases, and has no digit-length cap. Arbitrarily many leading zeroes
preserve the value. Invalid prefixes, signs, separators, Unicode digits,
fractions, trailing characters, and string payloads have no numeric meaning.

A separate strict Word projection succeeds exactly for values below `2^256`.
Larger values retain their natural meaning but have no Word result; they do
not wrap. Located interpretation ignores spans, not raw payload validation.
Public soundness, completeness, uniqueness, and exact failure/range laws are
proved. Consumers cover both range boundaries and malformed manually built
ASTs; actual-source tests require complete diagnostic-free parsing.

The monomorphic local-expression adapter now adopts this strict Word projection
for canonical literal leaves (ADR-0163). Independent resolution, typing, and
evaluation require the mathematical Word meaning; the value is a constant,
has Word type, and preserves the store. Their exact correspondence, typed
execution, unused-input insertion, and ID-relabeling proofs include this case.
Even invalid literal payloads contain no names, so unused-input insertion
preserves their checking failure as well. Both literal and expression ranges
are irrelevant. A literal takes one Core transition; `~7` takes three and
`~~7` takes five, with grouping adding none.

All written branches still check: a skipped invalid or overflowing literal
blocks checked execution. A valid Word on the right of `&&`/`||` resolves but
fails Boolean typing, even though raw selected-branch evaluation can return
that Word. Parsed regressions exercise literals, complement, conditionals,
exact fuel, nonempty stores, and unchanged results after adding unused inputs
or relabeling IDs. The reference-only adapter continues to reject literals.
This limited Word policy does not settle general source literal types,
`fromInteger`, or overload resolution, and does not change the parser, Core,
or Oracle/wire interfaces.

### Typed local input execution

`LocalInputs` now bundles each spelling, unique ID, type, value, and structural
value-typing evidence (ADR-0157). Name, type, and runtime tables are ordered
projections, so callers do not separately prove matching ID order or environment
typing. Unique IDs ensure that a selected name retrieves its own row's type and
value. Repeated names still select the first row. Empty inputs and fresh binding
insertion preserve ID uniqueness within the supplied inputs, not globally.

The convenience checker and runner reuse the supported local-expression fragment and
execute the actual returned Core. The runner retains the checked type and full
Core result: check failure is absent, while fuel exhaustion is present and keeps
the suspended state. Completed runs correspond exactly to independently typed
source evaluations; they preserve value type and store. Typed inputs give
sufficient-fuel execution, and the endpoint never returns a machine fault.
Source-text regressions now also build these inputs through fresh insertion
and exercise their checker and runner for both conditional branch choices.

These are proof-carrying Lean inputs, not validation of arbitrary external
values or source declaration collection. Structural typing of a cell reference
does not assert that its location is allocated. A repeated-name insertion may
change existing source meaning; fresh IDs do not prevent name shadowing.

For a supported local expression that avoids the newly added
spelling in every child, fresh insertion preserves and reflects source typing
and evaluation, including the exact value and both stores. Checking changes
only the free Core positions by one; the assigned type and failure boundary
are unchanged. Completed runs have the same observations even at the same fuel;
the exact-cost strengthening below also preserves exhaustion presence.
Suspended states themselves are not claimed identical.
Avoidance includes both short-circuit operands, even a skipped one. This
condition is not a free-name analysis of unsupported syntax.

### Local identity relabeling

The explicit frontend tables and typed input bundle now support simultaneous
local-ID relabeling (ADR-0160). Source ASTs, spellings, ranges, row order, types,
values, and stores are unchanged. Name lookup and whole expression resolution
commute with arbitrary ID maps, including failed resolution.

An injective map also preserves the exact checked Core and type, source typing,
and raw source evaluation in both directions. Evaluation preservation does not
require whole resolution or typing, so skipped missing/unsupported syntax stays
within the raw judgment's original boundary. Existing repeated names and raw
ID aliases retain their first-match meaning; the typed bundle retains unique IDs.

The bundle's runner has exact result equality at identical fuel, including
failed checking and the entire suspended machine state. This is stronger than
fresh input insertion because neither Core indices nor runtime values move.
Identity/composition laws and same-fuel parsed regressions cover the operation.
Noninjective merging can change which row a reference selects and is excluded.
No global ownership/allocator guarantee or commutation with subsequent fresh
allocation is claimed.

### Exact local-expression execution thresholds

Independent source evaluation now carries an exact Core-transition cost
(ADR-0165). Erasing it recovers the previous evaluation relation, and every
previous evaluation has a positive cost. The value, final store, and cost are
jointly unique even for raw evaluations with unresolved skipped branches.
No checking or executable-run premise is built into the cost relation.

Identifiers and Word literals cost one; grouping adds nothing; unary operators
add two. Strict Word arithmetic, bitwise, greater-than, and equality binaries
cost both operands plus three; derived Word inequality and `<=` add five,
ordered Word `<` adds nine, and `>=` adds eleven. A conditional
costs its condition and selected branch plus two. Short-circuit selection costs
both visited operands plus two; skipping the right costs the left plus three,
including the generated Boolean constant. Both initial and final stores and
left-to-right operand order remain explicit.

Whole resolution and lowering in runtime ID order turn that source derivation
into a Core path of exactly the same length, even with a retained continuation.
The terminal-path instance proves that a checked run completes with the exact
value and store if and only if fuel reaches that cost; less fuel returns an
exhausted result retaining its state. Typed aligned inputs supply the successful
cost derivation and a value of the checked type. `LocalInputs` exposes the same
fixed-fuel correspondence, keeping whole source typing distinct from raw cost.
Failed checking remains absent, not an exhausted execution.

The auxiliary path-length uniqueness theorem is restricted to terminal states.
A return control with pending frames is not final, and recognizing an already
final state needs zero transitions. Consumers protect those boundaries and all
source cost formulas. These counts are not gas, elapsed time, frontend lookup
or numeric-decoding complexity, nor the work performed by failing executions.
The parser, evaluator, and wire interfaces are unchanged.

Source costs are also invariant under injective local-ID relabeling and fresh
insertion of an avoided source spelling (ADR-0166). These proofs preserve raw
cost derivations, including skipped unresolved branches, without adding a
whole-resolution or typing requirement. The bundled runner now has a reusable
exhaustion characterization: whole source typing plus a successful independent
cost strictly above the supplied fuel is equivalent to a present exhausted
result of that type.

Combining those laws preserves completed type/value/store observations and
exhaustion presence at identical fuel after unused input insertion. Old and new
suspended states are quantified separately: their environments and free Core
positions can differ, as a fuel-zero literal test demonstrates. Parsed tests
compare these observations across multiple exact thresholds while keeping the
existing stronger same-fuel full-state equality for ID relabeling. Fresh
same-spelling shadowing can preserve a final Boolean value yet change cost
from four to ten, so the unused-name premise cannot be dropped. This strengthens
proof interfaces only, not executable behavior or allocation policy.

### Direct local-expression evaluation and cost

A total evaluator now follows the original expression and explicit name/actual
environment tables directly (ADR-0223). It returns the selected value and exact
Core-transition cost without resolving, lowering, checking or running Core.
Soundness and completeness construct and consume the existing independent raw
cost rules. Successful pairs, absent raw derivations and the uncosted value
projection are characterized exactly; arbitrary final-store correspondence
retains the necessary `finalStore = initialStore` conjunct.

First-match caller tables may contain duplicate spellings or IDs, sparse owners,
unaligned rows and untyped actual values. Strict Word literals keep their complete
spelling/range checks. Both strict operands execute in their original order,
including division/remainder by zero. Existing unary, binary and derived-comparison
overheads are unchanged. Conditions and short-circuit operators visit only the
selected child; selected short-circuit right values remain arbitrary at this raw
boundary. Opaque values are supplied, not allocated or invoked. Skipped unresolved
or unsupported children may coexist with raw success and whole checking failure.

Whole checking and actual identity alignment separately turn successful output
into exact Core paths and completion/exhaustion thresholds. Actual completed
checked runs recover that same value and cost without a runtime-typing premise.
Typed aligned environments supply successful typed results, and bundled runner
equivalences retain whole source typing explicitly. A retained continuation path
ends before its pending frames execute; no whole-run guarantee follows there.
Independent and parsed consumers exercise exact operator values/costs, literal
boundaries, first-match rows, raw/whole rejection and real machine checkpoints.
No existing checker, evaluator, body/entry, parser/Core/Wire or binding policy
changes within this unit; recursive-body evaluation composes it separately in
ADR-0224.

### Explicit canonical type names

An additive type-name adapter now interprets canonical named types without
arguments through an explicit caller table (ADR-0167). Its independent
first-occurrence lookup and source meaning have exact success/failure,
uniqueness, and supplied-entry provenance proofs. Qualified component lists
remain ordered and separate: raw `"A.B"` is not the path `["A", "B"]`.
All source ranges are ignored, but spelling is not normalized or validated.

Any Core type can be assigned by the table; `Word` and `Bool` do not acquire
implicit meanings, and aliases or duplicate table entries retain exact
caller-specified behavior. Applied names, mapping, proxy, function, comptime,
tuple, and recovery forms remain outside this restricted adapter even when
their source text parses successfully. Complete-source parser tests distinguish
that boundary from malformed or partially consumed text. This prepares explicit
parameter scope construction without yet adding function calls, source type
declaration collection, general inference, or staging semantics.

### Canonical runtime parameter inputs

Canonical runtime parameters now construct the shared typed input tables
(ADR-0168). The caller supplies the owner, explicit type-name meanings, and
arguments carrying structural value-typing evidence. Exact arity, annotation
meaning, and unused parameter spelling are required; comptime/recovery forms
and unsupported or mismatched annotations remain outside this profile.

An independent paired-list judgment characterizes executable success and
failure. Its ordered row relation keeps each parameter with its exact argument
type and value, even when several arguments share a type. Generated IDs run
from zero in source order; prepending makes the final tables reverse that
order. Lengths, argument projections, per-index row correspondence, generated
IDs, unique names, and initial-row preservation are proved. Existing lookup,
checker, typed-environment, and runner guarantees apply to the resulting bundle.

Actual parsed parameter lists and signature parameters now feed local-expression
execution with exact Core positions, selected values, preserved nonempty stores,
and completion/exhaustion thresholds. Consumers cover arity and duplicate-name
failures, aliases, arbitrary ranges, typed captured closures, and unallocated
cell references. A closure's declared type alone does not supply the structural
evidence; structural reference typing does not imply store allocation. No new
function-call, body/return, signature-constraint, argument-decoding, global
allocation, or wire semantics are claimed.

### Single-return canonical bodies

A body containing exactly one canonical return now has independent typing,
evaluation, and transition-cost semantics (ADR-0169). Bare return elaborates
to Unit with cost one; an expression return preserves its actual checked Core,
type, value, both stores, and exact cost. The surrounding block and return do
not add machine operations. Empty, nested, multi-statement, expression-tail,
and return-followed-by-statement bodies are not silently reduced to this shape.

The checked body runner uses the existing typed input bundle. Whole body typing
characterizes checking, checked source evaluation corresponds to Core under
runtime identity alignment, and typed inputs give a correctly typed result and
fault exclusion. Raw store/value/cost properties remain independent of whole
checking. Fixed-fuel completion and exhaustion retain the same exact thresholds;
a skipped unresolved expression branch still prevents checked execution.

Complete-source body and declaration tests connect parsed parameters to parsed
returns and compare actual returned Core, full same-fuel expression results,
nonempty stores, and bare-return zero/one boundaries. The body's inferred type
is deliberately not a signature contract: a parsed Bool-return annotation with
a Word-return body still gives Word at this body-only endpoint. Function calls,
signature checking at this body-only endpoint, general early returns,
continuation unwinding, mutable locals, and loops remain separate, as do all
wire interfaces.

### Terminal conditional return bodies

A separate nonrecursive body adapter accepts exactly one `if` with an explicit
`else`, each arm containing exactly one bare or expression return (ADR-0195).
The condition must be Bool and both arms must have the same type, under the
original inputs. Independent exact elaboration retains all three checked Core
children and lowers directly to `ifE`; no identities or source bindings are added.
Raw evaluation visits the condition and selected arm only, but whole checking
still rejects an invalid unselected arm. Source typing/checking equivalence,
exact Core simulation, value/store/cost determinism and type safety are proved.

Exact cost adds two to condition plus selected-arm costs. The source bound uses
the larger arm, so a four-step selected path may have a conservative bound of
six. Checked runs have exact completion/exhaustion boundaries and cannot fault;
genuine suspended states retain their pending condition/arm frames on resumption.
Independent and parsed tests cover actual typed values including existing cells
and closures, bare Unit returns, unequal arm costs and invalid skipped arms.
Absent else, extra statements, nested statement conditionals and return-type
mismatch are rejected. Existing singleton body APIs remain unchanged. The
body adapter itself does not establish a function header contract; runtime
entry integration is described below (ADR-0198). General early-return unwinding,
source mutation and sequential statement semantics remain separate.

### Common nonrecursive terminal-body interface

The `TerminalReturnBody` interface now unifies singleton returns and the
separate explicit-if/else profile without changing either meaning (ADR-0196).
Original body shape selects the component checker; the independent typing,
exact elaboration, raw evaluation and cost judgments wrap the corresponding
component judgments. Core, returned values, stores and transition costs are
unchanged. The common source bound selects the existing component bound.
Conditional arms still use singleton returns, so this union is not recursive.

The common checked runner has exact typing/Core correspondence, safe typed
execution, all completion/exhaustion thresholds and genuine-state resumption.
Its full optional result equals the original runner at every fuel and store,
including failed checks and complete suspended states. Independent and parsed
consumers retain actual Unit/Word/Bool/cell/closure values, unequal arm costs,
pending frames and invalid-unselected-arm rejection. Singleton execution keeps
its original meaning. Entry integration initially used this union (ADR-0198)
and now extends to recursive trees (ADR-0208), retaining its own header and
parameter requirements.

Body-level identity and store invariance now cover all three return profiles
(ADR-0197). Injective ID relabeling preserves independent exact elaboration,
the full optional checker result and the complete same-fuel runner result,
including suspended states. Store replay preserves raw values and exact costs
at any replacement store. Completed observations carry their respective stores;
fuel exhaustion has equivalent presence, not identical checkpoints across stores.
Noninjective ID merging still changes first-match lookup and may change results.
The three existing singleton body renaming/replay proofs were relocated without
changing their statements or proofs and remain available through the old runtime
imports. Body-level modules have no runtime-function dependency or cycle, allowing
entry integration to reuse these laws without reversing the dependency direction.

### Recursive terminal return-tree semantics

A separate `TerminalReturnTree` adapter now checks finite, arbitrarily nested
explicit if/else bodies whose leaves are singleton returns (ADR-0204). Structural
recursion on the original block establishes totality without fuel or a depth
limit. Bare returns retain Unit; every condition must be Bool and every written
arm must independently have the same result type. Exact elaboration preserves
the original ordered condition and both recursive arms as a nested Core `ifE`.

Independent recursive source typing and exact elaboration characterize success
in both directions. Successful checking yields typed Core, exact Core/type
uniqueness and failure iff there is no source typing. Condition resolution,
positional lowering and typing remain separate premises; another same-typed Core
is not an alternative elaboration. Static inputs may include nominal types with
no runtime inhabitants. Deep invalid unselected branches remain rejected.

Old singleton, one-level conditional and terminal-union successes embed with the
same Core and type. Full optional-result equality is restricted to old body
shapes, including failed expression checks. It is false for arbitrary bodies:
a valid deeper tree is accepted here but rejected by the old nonrecursive
body-only adapters. Entry consumers with valid parameter and header evidence
now establish exact deep compilation success under ADR-0208; the old body-only
rejection contrast is retained.

The static layer is now complemented by independent recursive evaluation and
cost semantics (ADR-0205). Only the selected arm is evaluated; a node costs its
condition plus the selected arm plus two Core transitions. Leaves reuse the
existing return semantics without extra cost. Raw and cost determinism, unchanged
stores, cost erasure/existence and positivity need no whole-tree acceptance.
Aligned, actually typed environments separately give typed evaluation existence
and type preservation. No arbitrary static type is assumed inhabited.

With whole acceptance and identity alignment alone, raw evaluation is equivalent
to evaluation of the exact checked Core. Runtime typing is not required for this
correspondence and cannot be inferred from it. Checked source costs yield exact
Core transition paths retaining any original pending continuation, with an
empty-continuation specialization. The path endpoint does not execute or unwind
that continuation, and no inverse path-length claim is made for arbitrary frames.
Core can observe a pending-frame fault at zero remaining fuel; reaching this
endpoint is not an unconditional claim of fuel exhaustion under arbitrary frames.
Old raw/cost evidence embeds with identical value, stores and cost, even without
whole checking. Deep skipped invalid subtrees retain raw success/whole rejection.

The separate checked tree runner now uses the actual accepted Core, original
ordered runtime values and supplied store (ADR-0206). Exact optional-result and
failure laws preserve complete machine states. Known independent costs give
fixed-fuel completion/exhaustion thresholds; actual typed inputs connect whole
source typing with typed-cost execution and exclude machine faults. Static
acceptance plus aligned IDs alone is not a generic safety guarantee.

A total recursive source bound adds the condition bound, the maximum of both
recursive arm bounds and two. Raw costs obey it without whole-typing premises;
sufficient-fuel completion additionally requires whole acceptance and actual
runtime typing. The bound is conservative, not a minimum. A depth-two variable
tree can cost seven or four with bound seven; its old nonrecursive bound can be
four and is not sufficient for the new long path. Unsupported whole shapes have
zero bounds without acquiring acceptance or an execution guarantee.

Genuine exhausted states retain exact remaining paths of length `cost - spent`.
Resuming the actual checkpoint equals a larger original run, including all
pending frames, environment and store. Old singleton and one-level shapes retain
full optional runner equality at every fuel; arbitrary deeper bodies do not.
Independent and parsed tests distinguish exact threshold, upper bound, preserved
checkpoints and unsafe replacement states.

Body-level identity and store invariance now extends to arbitrary-depth trees
(ADR-0207). Globally injective ID maps retain exact independent elaboration and
the whole optional checker result, including deep rejection. The proof-carrying
input checker and same-fuel runner preserve full results, including genuine
checkpoints, because positional runtime values are unchanged. Source spellings,
row order and allocator policy are not rewritten. Noninjective raw-table maps
can change first-match lookup, checked Core, selected values and costs.

Independent raw and costed paths replay from any replacement store to itself,
with identical value and cost and no checking or typing premise. The store iff
laws retain the original final-equals-initial constraint. Typed-input runners
preserve same-fuel completed value/type observations with each result's own store,
and relate only exhaustion presence between stores. Distinct store-bearing
checkpoints and full results are not identified. Consumers retain raw replay for
deep invalid skipped branches alongside whole rejection, and distinguish full
same-store ID invariance from cross-store observation laws. The new body modules
have no runtime-function dependency or cycle.

Function entries now reuse the recursive tree contracts below (ADR-0208). Old
body-only adapters stay unchanged; no general early return, extra statements,
missing else, local declarations, calls or fallthrough are added.

### Typed local-declaration prefixes: static semantics

A separate `TypedLetReturnBody` adapter now checks a finite outer sequence of
annotated, initialized, non-shadowing local declarations followed by an existing
terminal return tree (ADR-0209). It consumes original statements without a fuel
or length limit. An annotation uses the caller's first matching type meaning;
its initializer is checked in the old inputs with that exact type. Only the
remaining statements see the new name, fresh owner-relative ID and prepended
type. The exact output is nested Core `letE`, with no second reversal or extra
weakening of the already elaborated tail.

Independent source typing and exact elaboration retain annotation meaning,
initializer resolution/lowering/typing and the entire remaining source.
Checker success is equivalent to that provenance; typing, exact uniqueness and
failure characterization require no runtime values or nominal inhabitants.
Every initializer and every terminal branch is checked, including unused or
unselected source. Same-typed wrong Core cannot replace the actual output.
Old terminal-tree successes embed unchanged, and full optional equality holds
on singleton return/if shapes, including rejection, not on arbitrary prefixes.

This is a deliberately restricted static adapter, not a language-wide rejection
of omitted annotations, omitted initializers or repeated names. Inference,
default initialization, shadowing, let prefixes inside conditional arms,
mutation, separate block wrappers and calls are not added. Freshness is relative
to current inputs; no arbitrary-renaming allocator covariance or traversal-global
uniqueness is claimed. Independent and parsed consumers retain exact source
order, old-scope/forward-reference boundaries, nominal inputs and whole failures.
The independent evaluation/cost layer below now complements this static unit.
Existing tree adapters still reject let prefixes. A separate checked prefix
runner follows below, and ADR-0215 now integrates this adapter into the existing
function-entry APIs while preserving their complete header/parameter contract.

### Typed local-declaration prefixes: evaluation and cost

Independent raw and costed judgments now evaluate each original initializer
once in the old name table/environment, then prepend its actual value and the
same fresh ID for the remaining statements (ADR-0210). Terminal paths reuse the
existing tree semantics. Both stores are retained around each child, and each
let costs initializer plus tail plus two existing Core transitions. Unused
initializers still evaluate and contribute their full cost.

Raw rules do not require annotation meaning, an unused name, whole checking or
runtime typing. They may describe paths for a rejected annotation, repeated
name or invalid unselected subtree; this is not a general acceptance/shadowing
policy. Missing values in an evaluated initializer cannot be bypassed. Raw
determinism, unchanged stores, cost erasure/existence, positivity and unique
costs follow independently of the checker. Actual aligned, typed environments
separately give evaluation existence and value typing, extending the tail only
with the value obtained from the initializer.

Whole acceptance and matching environment IDs suffice for evaluation iff with
the actual checked Core and exact-cost transition paths under any original
continuation. The names/ID projection law identifies raw table-relative fresh
IDs with static input allocation; arbitrary inconsistent environments get no
freshness guarantee. Runtime typing is not inferred from alignment. Initializers
retain their pending let frame and old values; tails receive the obtained value
once and the original continuation, without weakening or reversal. An arbitrary
continuation is only retained at the endpoint: a bad pending frame may fault at
zero remaining fuel, so no unconditional exhaustion claim follows.

Independent and parsed consumers retain arbitrary-length paths, noncommutative
old-scope arithmetic, unused initializer costs, asymmetric terminal choices,
actual opaque cell/closure values, distinct stores and whole-rejection contrasts.
Existing tree raw/cost paths embed without checking. ADR-0210 itself added no
parser, Core or entry changes, body runner, source bound, resumption or calls.

### Typed local-declaration prefixes: checked execution and resumption

A separate checked body runner now uses the actual static projection and
original ordered values (ADR-0211). Caller type meanings and owner remain
explicit. Check failure is `none`; successful checking retains the complete
Core machine result, including genuine suspended states. Values are neither
reversed again nor reconstructed from static types. Whole typing and independent
costs characterize completed and exhausted observations. Actual typed inputs
give a typed returned value, exact fuel thresholds and fault exclusion for any
store, while generic known-cost laws require only checking and aligned IDs.

The total source-only bound adds each written initializer's expression bound,
the remaining prefix's bound and two. Its terminal suffix uses the recursive
max-arm tree bound. Raw selected-path costs are bounded without annotation
meaning, unused-name or whole-typing premises. It is an upper bound, not a
minimum: paths costing seven or twelve can share bound fourteen. Rejected
annotations and repeated names may have nonzero budgets and raw paths; neither
zero nor positive bounds supply checking evidence or missing runtime values.
Sufficient-fuel safety additionally requires whole acceptance and actual typing.

Genuine exhausted states retain exact remaining paths of length `cost - spent`.
Resuming them equals a larger original run, preserving pending initializer let
frames, captured old values, the actual value prepended after binding and each
store. These residual costs concern closed empty-continuation body paths, not
the cost of executing arbitrary pending frames. Independent and parsed tests
retain actual multi-chunk states and distinguish resumption from restarting or
dropping a continuation. Old singleton/if shapes retain whole optional result
equality, including checking failure and same-fuel complete checkpoints.

The body-runner unit itself adds no entry integration; ADR-0215 now supplies that
connection below. Let prefixes inside branches, parser/Core/Wire changes, calls,
mutation, inference, default initialization and general shadowing remain outside it.

### Typed local-declaration prefixes: store replay

Independent prefix paths now replay from any replacement store with identical
returned values and exact costs (ADR-0212). Each initializer is replayed in its
original scope, and its actual value is retained in the tail's extended
environment. Owner, names, IDs and value order stay fixed. Raw replay requires
neither checking, usable annotation meanings, fresh spellings, aligned IDs nor
typed values. Whole-source rejection therefore remains distinct from raw replay.

Bidirectional raw/cost laws retain the necessary final-store-equals-initial-store
condition. At the actual typed-input boundary, completed observations agree on
returned type/value at the same fuel and carry their own initial stores; fuel
exhaustion presence is equivalent. These laws keep whole checking and also cover
rejected bodies. They do not equate complete results or suspended states across
distinct stores. Genuine initializer/tail checkpoints must be resumed separately,
retaining their own stores and captured values. Opaque cell/closure returns do
not imply that reading cells or running arbitrary pending continuations is
store-independent. This body-level unit adds no Core, entry, mutation or binding-policy extension.

### Typed local-declaration prefixes: owner covariance

The separate prefix adapter now preserves exact elaboration and whole checking
under a globally injective declaration-owner map (ADR-0213). Every input owner
and the adapter's supplied owner change together; binder indices, source
spellings, types, row order and actual values stay fixed. Fresh allocation
commutes with this relabeling on arbitrary scopes, including mixed owners,
sparse indices and repeated IDs. Value-free fresh binding therefore commutes
without an extra fresh-index premise or inhabitants of arbitrary static types.

Independent exact elaboration and whole typing transport through every original
initializer and freshly extended tail. Structural checker equality retains
both success and rejection even for non-surjective injective owner maps. The
actual typed-input wrapper preserves complete optional results at the same fuel
and store, including identical genuine checkpoints and resumption. Owner-bearing
input IDs themselves are relabeled, not equated. This differs from store replay,
where complete states retain different stores.

This is not allocator covariance under arbitrary index-changing local-ID maps
or owner-collapsing maps. Runtime-parameter owner laws are unchanged; ADR-0215 now
uses this body transport at entries without a reverse body dependency. No
raw/cost owner-transport API, inference, parser, Core or binding policy is added.

### Typed local-declaration prefixes: type-name extension

Preserving existing first-match type meanings now preserves exact prefix
elaboration and whole typing (ADR-0214). The body, owner and input bundle stay
fixed. Only written annotation meanings are transported; old-scope initializer
evidence, declared types, fresh tail inputs, positional Core and result type
are unchanged. Static nominal inputs still require no runtime inhabitants.

One-way semantic extension preserves successful checker results and complete
successful runner pairs, including genuine checkpoints at insufficient fuel.
Mutual extension preserves the whole optional result, including rejection,
without requiring equal tables or unique keys. Actual ordered values, fuel and
store remain fixed. Adding a formerly unknown annotation can change `none` to
`some`, so one-way extension does not preserve rejection. A changed first-match
meaning is not extension merely because all old rows remain present; hidden
duplicates may differ harmlessly when visible meanings are preserved.

Raw paths, exact costs and source bounds do not depend on the caller type table
and acquire no new checking evidence from these laws. This body-level unit adds
no entry, parser, Core, inference, default-initializer or binding-policy extension.

### Recursive typed let/return trees: static semantics

A separate total `TypedLetReturnTree` adapter now admits finite alternating
typed-let prefixes and terminal explicit if/else nodes inside either arm
(ADR-0216). Independent typing and exact elaboration retain the original syntax,
old-scope initializers, fresh tail inputs and ordered Core `letE`/`ifE` structure.
Both arms start in the same original scope: sibling binders can reuse a fresh
identity, even with different declared types, without becoming visible across
branches. Descendants can use ancestor locals but cannot shadow them. Recursion
decreases full syntax size, not merely the outer statement count.

Whole checking covers every initializer and both arms, including unselected
deep failures. Exact provenance characterizes success, fixes Core and type,
and implies Core typing; absence of any independent whole typing characterizes
rejection. Value-free nominal types need no runtime inhabitants or extra input
name-uniqueness premise. Old terminal-tree and outer-prefix successes embed
with exactly the same Core/type; only singleton-return shapes have full Option
equality. Old failures may become new successes and are not preserved generally.

Independent arbitrary-length proofs and complete parsed declarations cover
alternating depth, noncommutative initialization, sibling isolation, original
parameter positions, first-match annotation meanings and qualified keys.
This static unit itself adds no runtime-entry integration. Independent
evaluation/cost and a separate body runner follow in ADR-0217/0218;
ADR-0222 now connects these recursive bodies to existing function entries.
The initial profile excluded absent annotations and separate block wrappers;
ADR-0238 now supports inferred initialized lets, and ADR-0240/0241 add strict
discard prefixes and terminal lexical wrappers. Missing initializers, shadowing,
extra statements after a conditional and general calls remain outside this
adapter. No parser/Core/Wire change or global binding policy is implied.

### Recursive typed let/return trees: evaluation and cost

Independent raw and cost judgments now follow the original recursive body
(ADR-0217). Each initializer evaluates once in the old name table/environment;
its actual value extends only the tail. A condition evaluates only its selected
arm in the original scope. Each let and conditional adds exactly two existing
Core transitions to its evaluated child costs. Unselected arms contribute no
cost, but selected unused initializers still execute fully. Sibling scopes never
exchange locals or allocations.

Raw unchanged-store, value determinism, cost erasure/existence, positivity and
uniqueness laws need no checking, name freshness or runtime typing premises.
Raw paths may exist with unknown annotations, repeated names or invalid
unselected children, without establishing source acceptance. Whole typing plus
an actual aligned, typed environment separately gives evaluation and typed
results; each initializer supplies the real value used in the extended tail.
Nominal static inputs still do not provide inhabitants, while existing opaque
cell references and captured closures need no allocation or invocation.

Whole acceptance and aligned IDs give evaluation iff for the exact checked Core
and exact-cost paths under arbitrary retained continuations. ID alignment alone
does not imply runtime typing. A retained frame is not executed or unwound at
the path endpoint; incompatible frames can fault at zero remaining fuel. Old raw
terminal-tree and outer-prefix paths/costs embed unchanged without new premises.
Independent source proofs and complete parsed argument execution cover depth,
strict/noncommutative initialization, asymmetric selected costs, actual stores
and the raw/checked/continuation boundaries. This evaluation unit itself adds no
entry integration; the separate body runner follows in ADR-0218 below.

### Recursive typed let/return trees: fuel and resumption

The separate recursive body runner now checks the actual `LocalInputs` static
projection and executes its exact Core with the original ordered values and
empty continuation (ADR-0218). Whole checker rejection gives `none`; successful
results retain the complete type and machine result. Independent known cost,
whole acceptance and aligned IDs give exact done/out-of-fuel thresholds without
assuming runtime typing. Whole typing at actual typed inputs separately supplies
cost existence, wrapper threshold characterizations and fault exclusion.

The total syntax-size-recursive bound adds each initializer bound and two,
and each condition bound plus the maximum arm bound and two. Singleton returns
reuse their old bound and other shapes contribute zero. Every independent raw
cost is bounded, without annotation meaning or name freshness assumptions.
Typed sufficient-fuel completion still needs whole acceptance and real typed
values. Positive bounds do not establish acceptance, and are not minimum costs:
an invalid annotation can have a raw path, while a short selected arm can finish
below the maximum. A branch-local let can cost seven where both old bounds are
four, so the old budget cannot serve this new adapter.

Actual exhausted checkpoints retain control, pending conditional/let frames,
captured environments, obtained values and stores. Their exact residual path
has length `cost - spent`, with `spent < cost`. Any additional fuel gives the
same complete result as the original run at the sum, including further genuine
checkpoints across multiple chunks. Restarting the body or dropping frames is
not equivalent. These laws use empty-continuation complete paths, not arbitrary
retained-continuation endpoints.

Old tree and outer-prefix runner successes keep the entire optional payload at
the same inputs, fuel and store. Singleton shapes additionally preserve `none`;
general old conditional/prefix failures may become new successes. Independent
depth proofs and fully parsed actual-argument tests cover bounds, asymmetric
costs, unused work, opaque values, rejection and genuine multi-stage checkpoints.
Existing body adapters, bounds and function entries stay unchanged. No owner
covariance, parser/Core/Wire extension, inferred values or broader binding/call
policy is added by this runner unit; independent store replay follows in ADR-0219.

### Recursive typed let/return trees: store replay

Every independent raw path and cost now replays at any replacement store with
the same source, owner, name table, actual environment, result value and cost
(ADR-0219). Initializers retain their old scope and obtained values, extended
tails retain those same values and fresh identities, and conditions follow the
same selected arm. These raw laws need no annotation meanings, unused names,
whole acceptance, aligned IDs, runtime typing or store validity. Both raw and
cost equivalences explicitly retain `finalStore = initialStore`; that conjunct
cannot be dropped when relating arbitrary final stores.

The existing typed-cost runner contracts give same-fuel completed values at
each run's own store and equivalent exhaustion presence. They do not equate
complete results or checkpoints across distinct stores. Each genuine checkpoint
is resumed separately with its own store and captured frames. Whole rejection
still comes from the unchanged store-independent checker, not raw replay.

Independent depth proofs and complete parsed actual-argument tests cover
asymmetric selected costs, strict unused initialization, opaque values, distinct
stores, unequal complete results and actual conditional/let checkpoints.
Rejected annotations and unselected failures still admit some raw paths. A
pending Core cell-load can instead observe different contents or fault on an
empty store at zero fuel; returning a cell reference is not executing that
pending load. No arbitrary-Core or arbitrary-continuation runner independence,
old entry change or broader source policy is introduced by store replay;
independent owner transport follows in ADR-0220.

### Recursive typed let/return trees: owner covariance

A globally injective declaration-owner map preserves independent exact
elaboration and whole source typing for the same original recursive body,
type-name table, Core and return type (ADR-0220). All supplied input owners and
the current fresh allocator owner are mapped, but indices stay fixed. Existing
freshness laws handle sparse, mixed-owner scopes; allocation is not row count.
Each initializer keeps its old scope, each tail gets its mapped fresh binding,
and both sibling arms start from the same original scope. Sibling IDs may still
coincide locally. No global input-name uniqueness or runtime inhabitants are
required for value-free nominal typing.

Recursion on original syntax proves full optional checker equality, including
rejected shapes and invalid unselected children. Injectivity is required but
surjectivity or an inverse is not. Erased actual inputs and unchanged positional
values lift this to full same-fuel, same-store runner equality, including genuine
conditional/initializer/tail checkpoints. This is distinct from ADR-0219's
own-store observations across different stores. Opaque values remain supplied
values, not new allocations or calls.

Arbitrary local-ID index shifts need not commute with fresh allocation, and
owner-collapsing maps are not admissible. Old function entries, owner helpers,
raw/cost judgments, source bounds and resumption stay unchanged. No type-name
extension, parser/Core/Wire change or broader source policy is introduced here;
type-name extension follows independently in ADR-0221.

### Recursive typed let/return trees: type-name extension

First-match semantic type-name extension preserves independent exact elaboration
and whole typing throughout both recursive arms and every annotated binding
(ADR-0221). Only annotation meaning evidence changes. The original source,
owner, supplied input bundle, Core, result type, old-scope initializers, unused
names and freshly extended tails remain fixed. Static nominal types still need
no runtime inhabitants, and neither parameters nor actual values are rebound.

One-way extension preserves successful complete checker and runner pairs,
including suspended results at insufficient fuel. Mutual extension preserves
full Options, including rejection, without requiring equal tables or unique
keys. At fixed fuel/store, actual positional values give identical full results
and genuine checkpoints. Their usual residual resumption remains applicable.

One-way extension can resolve an unknown annotation in an unselected branch and
repair whole rejection even when the selected raw path was already valid.
Later duplicate entries can preserve meanings, but prepending a conflicting
first match is not semantic extension merely because all old rows remain.
Qualified component keys stay distinct from flattened strings. These boundaries
are exercised by independent depth proofs and complete parsed declarations,
alongside asymmetric costs, unused initializers, opaque actual values and real
checkpoints. No old body/entry, owner, raw/cost, bound/resumption, parser/Core/Wire
or broader binding policy is changed by this unit.

### Recursive typed let/return trees: direct evaluation

A total original-block evaluator composes the direct expression evaluator with
the existing independent recursive raw grammar (ADR-0224). It returns the exact
value and Core-transition cost without checking, lowering or running Core.
Singleton bare returns cost one; expression returns keep the child result.
Annotated, initialized head lets evaluate strictly in the old scope, then place
the actual value under the name-table-relative fresh ID in the extended tail.
Let and selected if/else paths add two to their child costs. Unused initializers
still execute; only the selected conditional arm is visited.

Independent soundness/completeness and exact absence/value-projection laws
preserve the old raw rules. General store correspondence explicitly requires
the final store to equal the initial store. Annotation presence is required,
but its meaning, type agreement and unused-name checks remain whole-checker
obligations. Duplicate spellings, sparse mixed owners, untyped values and
unaligned environments are legitimate raw inputs. Even an extra environment
row colliding with the fresh ID cannot replace the newly prepended actual value.
Missing annotation/initializer/else, empty bodies or trailing statements are
not silently ignored. Opaque values are forwarded, not allocated or invoked.

Whole checking and actual ID alignment separately yield exact Core paths and
fuel thresholds. Checked completion reflects the computed value and cost;
typed aligned actual inputs supply successful typed results. Bundled runner
equivalences retain whole typing, and retained-continuation paths stop before
pending frames run. Independent depth proofs and complete parsed consumers
exercise actual scopes, raw/whole contrasts, strict asymmetric costs, opaque
values and genuine checkpoint resumption with each result's own store.
Existing checkers, raw judgments, bounds, body/entry APIs and parser/Core/Wire
remain unchanged; this adds no new source form or binding policy.

### Raw recursive-body owner covariance

Globally injective owner-only relabeling now preserves complete direct recursive
body results and independent raw evaluation/cost in both directions (ADR-0226).
Unlike the static and typed-runner laws, these contracts apply to arbitrary
caller rows: duplicate names or IDs, sparse mixed owners, unaligned environments
and untyped actual values. They require no whole checking, source-name uniqueness,
ID alignment or runtime/store typing. Source syntax and spans, row order, actual values
and binder indices remain fixed. Non-surjective maps need no inverse.

The direct-result proof follows original syntax size, preserving the strict
initializer's obtained value and exact name-table-relative fresh tail. An extra
environment row may collide with the new identity without defeating the new
head's first match. Selected arms keep the same input scope. General raw laws
retain both stores and exact cost; the existing final-store equality is not
discarded. Success through unknown annotations or invalid unselected children
is still only raw success, not whole acceptance, and genuine absence is preserved.

Independent and completely parsed consumers exercise depth, sparse scopes,
opaque values, raw/whole contrasts and non-surjective maps. Collapsing owners
can merge environment keys and change first-match values. A separate index-shift
example only refutes exact fresh-allocation covariance, not raw result equality.
No evaluator, checker, entry, Core-state or existing owner-runner policy changes.

### Raw lookup-extensional semantics

Equal composed optional actual-value lookup for every spelling now preserves
complete direct expression and recursive-body results, including exact cost and
absence (ADR-0227). The body owners may differ independently. Costed and uncosted
raw iff laws preserve both the specified initial and final stores. This requires
no identity map, injection, inverse, equal lengths/order, uniqueness, alignment,
whole checking or runtime/store typing.

The proof observes identifier values through both first-match lookups. Each let
uses the actual old-scope initializer value; each side then allocates relative
to its own name table. Fresh non-membership makes both extensions implement the
same name update, even when their fresh IDs differ or collide with environment-
only rows. Other names keep their previous optional values. Selected branches
retain the original input scope, and expression/body recursion uses original
syntax size without changing any evaluator or lookup definition.

Independent and parsed consumers contrast different owners/layouts, duplicate
rows, absent names versus names without values, opaque values, genuine absence,
strict initialization and raw success versus whole rejection. Index-changing
relabeling may preserve results without commuting with allocation; changed
visible first matches need not preserve results. The new premise does not imply
equal static tables, accepted provenance, compiled Core or checkpoint payloads.
Checked execution still requires its own whole provenance and matching IDs.

### Explicit restricted runtime function entry

An explicitly supplied canonical declaration now connects its header, runtime
parameters and recursive typed let/return tree in one entry
(ADR-0170, ADR-0198, ADR-0208, ADR-0215, ADR-0222, ADR-0238, ADR-0240, ADR-0241).
Independent exact preparation retains both the actual lowered Core and its declared return type,
not merely some Core of that type. Success and failure correspond to this
independent relation, and a whole-entry typing contract is distinct from
body-only typing. A Bool-return declaration with a Word body is rejected here
while remaining a Word body at the existing body-only endpoint.

The compiler, preparer, whole-entry typing and independent entry cost now use
the recursive typed let/return-tree judgments. Initialized, unused-name declarations
alternate with terminal if/else inside either arm. Each initializer uses the old
scope; its inferred type must agree with any written structural annotation, while
an absent annotation remains absent in the original source (ADR-0238). The freshly
extended tail becomes the actual nested Core `letE`. The original entry APIs and three-field data
record layouts remain unchanged. Records retain only original parameter inputs:
branch-local lets do not alter argument count, ordered type guards or value reversal.
Both arms start from the original scope and can reuse the same fresh ID without
leaking names. Descendants see ancestor lets but cannot shadow them.
Exact-Core factorization, parameter positions, owner/type-name transport, stores
and checkpoints lift through the new provenance. The runner still executes the
prepared Core directly and adds no transitions or second value reversal.
Semicolon-terminated expression prefixes also compose at these positions
(ADR-0240), retaining the source scope while weakening only the tail Core under
a strict hidden binder. They add no parameter rows or source identities.
Singleton terminal lexical blocks recurse on their original inner span and
statements in the same scope (ADR-0241), preserving the exact child Core and cost.

The three entry fuel-bound theorems now use `typedLetReturnTreeFuelBound`, adding
each initializer or discarded-expression bound and two, or a condition bound and
maximum recursive arm bound and two. Terminal wrappers retain the child's bound.
A selected branch-local let costs seven while the old prefix bound is four, so
the old formula cannot remain the general entry guarantee. Other generic
entry theorem statements retain their premises and
conclusions over the broadened judgments. Value-free compilation still requires
no actual inhabitants, while safe execution requires real matching typed arguments
and provenance. Same-typed wrong Core cannot replace the source's actual Core.

Old singleton, terminal-tree and outer-prefix values, costs and complete same-fuel
results remain unchanged. Valid branch-local entry rejection fixtures now become
exact successes while old body-adapter rejection remains. Invalid headers, parameters,
declared return mismatches and unselected deep arms still reject. Missing
initializers, shadowing, self/forward or sibling references,
extra returns, missing else and nonterminal or empty nested blocks remain unsupported;
this is not a global binding policy. All old body-only adapters and bounds are
unchanged. Independent arbitrary-depth source proofs retain static nominal
types without values, exact `10n + 1` costs, original parameter rows and actual
conditional/initializer/tail checkpoints. Parsed whole declarations additionally
retain alternating `6n + 1` bounds, noncommutative/unused initialization, asymmetric
paths and full multi-chunk results at every below-cost checkpoint. Selected raw
success cannot hide an invalid unselected annotation. Exact-Core uniqueness
excludes equally typed substituted code; opaque values remain actual arguments.

The restricted header excludes generics, where clauses, and contract modifiers.
No return clause means Unit; an explicit clause has exactly one supported
structural type whose named leaves have caller-provided meanings. Empty and
multiple return lists are outside this entry, not classified as invalid source. Parameter arity, exact
argument rows, types, names, and owner-relative identities retain the existing
binding contract. No declaration lookup or global identity allocation is added.

Checked-entry cost combines the independent preparation and existing raw body
cost. The exact Core runner adds no transitions to that cost. Completion and
exhaustion correspond to the same fixed-fuel thresholds; typed entry contracts
supply a typed result, a preserved store, sufficient fuel, and fault exclusion.
These guarantees require valid preparation, not a hand-built data record.
Raw body evaluation remains unchanged, including its skipped-branch distinction
from whole checking. Fully parsed declarations test accepted and rejected
contracts, actual Core/input order, every fuel boundary, and typed closure or
unallocated cell-reference returns. This external entry is not general function
calling, mutable statement/control-flow semantics, or a new wire interface.

### Direct checked runtime-entry evaluation

An additive entry evaluator now returns the declared type, actual result and
exact Core-transition cost directly from the original declaration and supplied
typed arguments (ADR-0225). Existing preparation remains the whole-entry gate:
headers, ordered argument types and arity, every body child, local annotations
and names, and the declared return contract are unchanged. The gate performs
static lowering; only result computation is independent of Core execution.
The original parameter-only names and actual values feed the direct body
evaluator without rebinding, a second reversal or extra entry transitions.

The computed triple corresponds exactly to existing independent entry-cost
evidence. General store correspondence explicitly retains final-store equality.
Absence is exactly preparation failure: actual typed prepared inputs guarantee
that direct evaluation cannot introduce a further failure after acceptance.
Raw body success alone still cannot bypass invalid headers, unused wrong-typed
arguments, mismatched returns or unknown unselected annotations. Static nominal
types do not manufacture arguments, and arbitrary hand-built records gain no
provenance or safety.

Independent source proofs and complete parsed declarations use this correspondence
to consume existing fuel, compiled-execution, store and real resumption
contracts, rather than duplicating them as new APIs. Exact original Core, actual
parameter rows, strict asymmetric costs and opaque values remain explicit.
Existing preparation/compilation/runners, raw judgments, bounds, records and
parser/Core/Resolved/Wire are unchanged; this adds no source calls or allocation.

### Arbitrary runtime parameter positions

The ordered parameter layout now connects to semantic lookup and execution at
every source position (ADR-0171), not only the small fixed-arity examples. An
independently bound parameter at index `k` selects its exact argument type/value,
identity `(owner, k)`, and Core position `n - 1 - k`. Actual source and argument
lookups establish the index bound; unique names and identities justify the
first-match name, context, and environment lookups. No out-of-range meaning is
inferred from natural-number subtraction.

The selected canonical reference and its singleton-return body retain that
exact variable, value, unchanged store, and one-transition cost. An entry also
requires its complete independent header contract and parameter binding; the
selected argument alone cannot bypass an invalid declaration. Arbitrary-index
proof consumers and fully parsed functions cover mixed and repeated types,
every position across one through eight arguments, typed closures, and
unallocated references. This strengthens existing semantics without changing
the executable adapters or adding a public synthesis interface.

### Static preparation under changed runtime values

Equal ordered argument types now preserve the full static preparation result
(ADR-0172): acceptance or rejection, names, context, identities, exact Core,
and declared return type. The independent binding transport works from arbitrary
initial inputs with equal names and contexts and uses the replacement values
and their structural typing evidence in the new rows. It does not require an
extra initial-name uniqueness assumption or introduce a new executable interface.

This is deliberately not execution equivalence. Independent consumers and
fully parsed declarations show equal static Core but different environments,
zero-fuel states, returned values, or costs. A Boolean example returns false
under both inputs but takes four versus six transitions; fuel five therefore
completes only one run. Unresolved, ill-typed, or return-mismatched whole
declarations remain rejected for both value choices. Typed closures and
unallocated references may be replaced as opaque arguments without implying
application or allocation safety.

### Owner-independent runtime entries

Changing only the caller-supplied declaration owner now preserves entry
acceptance, exact Core, return type, runtime value sequence, and the complete
same-fuel execution result (ADR-0173). Independent parameter and preparation
relations are transported by an injective owner map that fixes binder indices.
For arbitrary old and new owners, an owner swap supplies the required global
injectivity. Input IDs, name tables, and typed contexts are relabeled rather
than asserted equal; their runtime value projections are unchanged.

The allocation argument follows the existing empty-start fresh-ID chain and
does not claim commutation with arbitrary injective ID maps. A binder-index
shift is an explicit counterexample to that stronger claim. In contrast to
changing argument values, changing only the owner preserves entire suspended
states, not merely exhaustion presence. Independent consumers and completely
parsed entries cover distinct/equal owners, changed real ID tables, identical
Core and values, exact fuel boundaries, opaque typed values, and rejected whole
declarations. No global allocator, function lookup, or runtime adapter is added.

### Type-only runtime parameter declarations

Canonical runtime parameter annotations now prepare an ordered static input
bundle without any supplied values (ADR-0174). Each row contains a spelling,
fresh identity, and explicit Core type; unique identities align the name table
and typing context. The independent declaration relation exactly characterizes
the executable empty-start adapter. Parameters retain their written allocation
order and reverse storage order, and duplicate spellings are rejected.

Existing typed runtime inputs erase to these exact static rows. Independent
runtime binding implies static declaration; conversely, a static declaration
and an actual typed argument list with the exact source-order types reconstruct
runtime binding with identical erasure. Type-list equality preserves arity and
order as well as each type. No arbitrary type is assumed inhabited, and no
dummy value is manufactured.

Independent consumers and fully parsed parameters cover arbitrary explicit
types, nominal data references with no supplied values, fresh IDs, erasure,
ordered argument reconstruction, and static success with runtime arity/type
rejection. Unsupported annotation forms and repeated names remain outside the
adapter profile. This is annotation-only preparation, not whole-function
compilation, source calls, or a new runtime evaluator.

Static parameter layout and source positions are now proved without actual
arguments (ADR-0201). Independent row judgments pair each original annotation,
spelling and type with the exact source-ordered row. General declaration evidence
retains arbitrary initial rows as a suffix, with newly allocated rows in reverse
source order. Generated indices start at the actual owner-relative fresh index,
including sparse/mixed-owner input tables. Distinct-name preservation retains its
initial distinctness premise; static bundles themselves require only unique IDs.

For empty-start declaration, a real parameter lookup at source position `k`
proves `k < n`, exact identity `(owner, k)`, the row at `n - 1 - k`, first-match
name/type lookups and positional Core lowering. References and singleton returns
therefore elaborate to exactly `Core.var (n - 1 - k)` with the annotation's type,
for arbitrary spans and types, including nominal types without runtime values.
Same-type parameters are not interchangeable. A truncated out-of-range index,
row membership or typing alone cannot establish this source-position evidence.

Independent and parsed consumers exercise all tested positions, retained source
order, nominal and repeated types, owner transport, sparse initial identities,
repeated initial spellings and range boundaries. Valid static parameters do not
license an invalid whole body or return contract. No allocation, declaration,
compilation, parser or runtime policy changes.

### Value-free restricted function compilation

Type-name table extension now preserves already established annotation meanings
and exact static compilation (ADR-0203). `TypeNameTable.Extends` preserves every
first-match lookup, not merely entry membership. Arbitrary right append is safe,
even with duplicate keys; fresh-key prepend is also safe. Same-meaning duplicate
prepend can be safe without freshness, while meaning-changing shadowing is not
an extension. Qualified component lists are never flattened into dotted strings.

Independent annotation, return-clause, complete header and parameter-declaration
evidence transports directly, including arbitrary initial static inputs. The same
types retain the same allocated identities and row order. Compilation reuses its
original exact body evidence and preserves the entire compiled record. Successful
interpretation, declaration and compilation therefore preserve their exact results.
One-way extension does not preserve failure: adding an unknown nominal type can
enable static compilation without supplying any runtime value.

Mutual extension gives full optional-result equality, including absence, for
lookup, interpretation, parameter declaration and compilation. Nonidentical tables
may satisfy this relation, including reordered distinct keys and pruned shadowed
duplicates. Existing same-Core execution and cost contracts consume transported
compilation evidence on common actual arguments, preserving rejection and genuine
checkpoints without asserting prepared-record equality from a projection. No
lookup, compiler, header/body or runtime policy changes.

The actual runtime side now has direct transport laws (ADR-0242). Independent
paired binding preserves arbitrary initial and final typed input bundles, the
original parameter and argument lists, owner, fresh identities and actual values.
Only annotation evidence changes. This composes with existing header and body
transport to retain the complete prepared record and whole-entry typing, without
recovering value equality from an erased compiled projection.

Successful binding, preparation and whole execution retain their exact optional
payloads. Whole run equality includes present exhaustion and its genuine saved
state at the same fuel and store, so existing resumption retains the same
residual computation. Mutual extension additionally preserves rejection at all
three endpoints. One-way extension can supply missing annotation meanings and
enable actual preparation; changing an existing first-match meaning is not an
extension. Equal argument types alone do not make different actual values or
prepared records interchangeable. All executable definitions, the private
general binder and source acceptance remain unchanged.

Independent source and complete parsed consumers retain sparse mixed-owner
rows, duplicate initial spellings, structural tuple parameters and actual
opaque values. Hand-built whole provenance and manual paths fix the original
Core and exact costs before comparing tables. Mutual lookup-equivalent tables
preserve both outcomes, while unknown parameter/return/unselected annotations,
changed first matches and same-type argument replacements expose the separate
boundaries. Full machine states and genuine residuals are checked across
multiple stores; nominal static cases never fabricate runtime arguments.

The restricted explicit function profile now compiles before runtime arguments
are supplied (ADR-0175). Independent compilation combines the existing header
meaning, type-only parameter declaration, and exact return-body elaboration.
The executable compiler agrees exactly with that relation, including rejection,
and retains the actual Core and declared return type. The output is typed in
the parameter context: it is open Core, not a closed function value or a source
call implementation. A hand-built compiled record has no unconditional guarantee.

Existing runtime preparation factors exactly into static compilation followed
by an ordered argument-type guard. Erasing values from any successful runtime
preparation gives the exact compiled record; independent compilation and a
matching actual typed argument list reconstruct runtime preparation. The guard
preserves individual types, arity, and order, and the optional-result equality
also includes rejected compilations and mismatched arguments.

Independent proofs and completely parsed declarations cover arbitrary type
aliases, nominal types without a default typed runtime argument inhabitant,
exact open-Core typing, equally typed but incorrect hand-built Core, header and
body rejection, and different actual values sharing one compiled result.
Existing checked execution retains its full initial/suspended states, returned
values, stores, and exact fuel boundaries. Compilation alone does not supply
arguments or assert completion. No parser, Core evaluator, or source-call
policy is changed.

Owner relabeling is now proved directly for value-free compilation (ADR-0200),
including nominal types for which the current runtime argument representation
has no inhabitant. Type-only input rows support injective ID maps with exact
name/context projections and identity/composition laws. Erasing already supplied
runtime values commutes with this map; no inverse value construction is added.

Independent empty-start parameter declarations follow their own fresh-ID chain
under an injective owner map that retains binder indices. Independent compilation
then retains the exact Core and return type through both terminal body shapes.
An injective swap connects arbitrary owners and preserves the complete optional
`(core, returnType, context.values)` projection, including rejection. IDs and
whole compiled records are relabeled, not asserted equal. The old owner helpers
and runtime import path remain available with unchanged definitions and proofs.

Independent and parsed consumers cover arbitrary types, uninhabited nominal
inputs, changed owners with retained source spelling/order/index, full failure
results and erasure compatibility. Binder-index shifts still do not commute
with fresh allocation, and a same-Core/type hand-built record need not satisfy
compilation provenance. Executable compilation and header/body policies are
unchanged; runtime argument availability and arity remain separate obligations.

Positional parameter returns now have direct whole-compilation proof interfaces
(ADR-0202). A singleton identifier return compiles to the exact source-selected
`Core.var (n - 1 - k)`. A terminal parameter selector compiles to the ordered
`Core.ifE` of its guard, then and else positions. Forward proofs retain the whole
parameter declaration, annotation meanings, complete header and actual body shape;
their executable corollaries retain the exact static input bundle and return type.
Inverse proofs recover that exact Core and return type from existing compilation
provenance, without requiring another header or parameter proof.

Distinct parameter indices are not required. Both arms may select one position;
a Bool-returning selector may also return its condition parameter. Arbitrary and
nominal types need no runtime inhabitants. Independent and parsed consumers
distinguish equally typed alternative variables or swapped branches from the
source-selected Core and preserve whole-header/parameter/branch rejection.
These proof profiles do not exhaust compiler acceptance: an expression conditional
inside a singleton return remains independently supported. No compiler, runtime,
parser, allocation or body policy is changed, and actual execution still requires
matching supplied typed arguments.

The execution bridge is now a generic proof contract, not only a parsed-test
observation (ADR-0179). The unchanged runtime endpoint equals value-free
compilation followed by the ordered argument guard and Core execution using
the actual compiled expression and reversed supplied argument values. This
unconditional Option equality includes compile failure, guard rejection, and
all full stateful results at every fuel and initial store. An independent
existential characterization recovers compilation evidence, matching types,
the return type, and exact Core execution from a present runtime result.

Independent function cost evidence fixes a path of that exact length from the
compiled initial state, and gives both completion and exhaustion thresholds.
Matching actual typed arguments and independent compilation produce a typed
result, unchanged store, and a no-fault guarantee. Neither matching types alone
nor a forged compiled record supplies this provenance. No second runner or
evaluation relation is introduced. Cached-compilation regressions exercise
same-type distinct values and source positions, zero/intermediate states,
different-cost short-circuit paths, wrong arity/type order, whole rejection,
and supplied closure/reference values without assuming type inhabitation.

Independent compilations can now be compared across different declarations,
type-name tables, and owners (ADR-0180). Equal ordered parameter types and exact
compiled Core imply equal return types by Core typing uniqueness, and equal
full runtime results for every shared actual argument list, fuel, and initial
store. Mismatched argument lists are rejected on both sides. Names, generated
identities, and complete static input records need not be equal. The same
conditions transport independent function cost evidence in both directions,
retaining the exact value, type, initial/final stores, and cost.

This is conditional on proven compilation and exact Core/context equality;
it does not infer those equalities from renamed source text. Independent and
fully parsed pairs exercise renamed/aliased/grouped declarations, while
counterexamples retain the necessary boundaries: unused parameters can change
argument acceptance, adding zero preserves a final value but changes the Core
and cost, and matching argument types cannot replace the actual supplied values.
No optimizer, source transformation, runner, or evaluation relation is added.

The current restricted frontend is also independent of initial store contents
(ADR-0181), not just store-preserving. Induction on independent expression cost
evidence replays the same value and exact cost on any replacement store; raw
evaluation, singleton return bodies, and independently prepared entry costs
inherit this transport. Raw skipped invalid branches require no whole typing
or resolution, while checked entry execution still requires its complete contract.
At every fixed fuel, terminal values and whether fuel is exhausted agree across
stores, including proven compiled Core with matching actual typed arguments.
Each result retains its own store: full results and suspended states are not
equated across distinct stores. Returned references/closures are not dereferenced
or called, and arbitrary effectful Core is outside this theorem. Independent
consumers include a store-preserving Core read with store-dependent results;
fully parsed entries cover distinct empty/nonempty stores, selected arithmetic
and short-circuit costs, supplied references/closures, and whole guard rejection.

Source-computable sufficient fuel bounds now strengthen existential termination
(ADR-0182). Structural expression bounds follow the existing transition costs,
using a maximum of branches instead of inspecting actual values; short-circuit
forms also budget for their inserted Boolean constant. Every independent raw
cost is below this bound, including raw evaluation that skips an invalid branch.
Singleton return bodies inherit the bound without extra wrapper steps. Checked
expressions, typed bodies/entries, and proven compiled functions with matching
actual typed arguments finish with a typed value and unchanged store at every
fuel at least the source bound. The same numerical budget applies across actual
argument values but can overestimate a selected path. It is neither a checker,
an exact/minimal cost, nor a gas/time estimate; zero for unsupported syntax/body
shapes does not bypass whole rejection or create an inhabitant of a declared type.

Actual fuel-exhaustion checkpoints now support exact resumption (ADR-0183).
The unchanged Core runner on a genuine checkpoint with additional fuel returns
the same full result as the original state with the combined budget, without
assuming typing or termination. A known final path of cost `cost` additionally
proves `spent < cost` and exactly `cost - spent` remaining transitions, with
both exact completion/exhaustion thresholds. Source cost correspondence lifts
this residual path through resolved/checked expressions, singleton return
bodies, complete runtime entries, and independently compiled functions.
The original local/body/entry endpoints also agree with resumed actual Core
results. This retains the actual control, frames, values, and store; it does
not recreate an initial state, edit a checkpoint, recover faults, or resume host
requests. Parsed tests cover every checkpoint on known paths, two/three-chunk
full-result equality, exact residual thresholds, and a dropped-frame counterexample.

### Semantic Core

Semantic Core is the syntax-independent language consumed by the evaluator.
The current Core Wire v3 boundary supports:

- unit, Boolean, Word, product, sum, and function values;
- immutable bindings, conditionals, and local mutable cells;
- program-local algebraic data with normalized constructor matching;
- the current unary, binary, and ternary Word operations; and
- a frozen 14-entry host context for contract execution.

Core Wire v3 has canonical encoders and strict, resource-bounded decoders.
Unknown fields, missing fields, invalid tags, noncanonical scalar encodings,
and duplicate JSON keys are rejected deterministically.

Well-typedness is mandatory. Oracle v5 checks each Wire v3 program against the
frozen host context and admits it only on success. Unchecked Core cannot enter
the contract executor through the public boundary.

### Reproducible checked-Core inputs

`Solcore.Synthesis.CoreV3` provides a syntax-independent input source for
semantic testing. A caller supplies a 64-bit seed and a Program-node bound. The
versioned generator builds Core Wire v3 directly, restricts variables to Word
locals introduced by generated `let` expressions, and seals every result with
the frozen v3 checker.

The initial generated subset contains Word and Boolean literals, Word locals,
`let`, `if`, every current Word unary, binary, and ternary operation, and no
host effects or recursion. Its shrinker preserves binder scope, rechecks every
candidate, and returns only candidates that are strictly smaller by the fixed
node/literal order.

Generated cases use one explicit account and checked contract, then execute
through both the strict Oracle v5 text handler and the same one-record
dispatcher used by the command-line service. A fixed 256-seed corpus reaches
all 29 tracked forms and operators, returns normally at the declared regression
fuel, and freezes its request bytes and final generator states with a replay
fingerprint.

### Checked-contract execution

An execution request supplies all state and environmental inputs explicitly:

- a finite package of contract definitions expressed as Core Wire v3 programs,
  which the Oracle checks and admits before materialization;
- a finite initial `WorldState` with balances, nonces, sparse storage, and code;
- nested-call bindings and checked creation templates;
- an explicit creation-address policy;
- target, caller, call value, calldata, and evaluation fuel; and
- a finite list of state locations to observe.

The executor currently provides:

- one top-level checked-contract invocation;
- ordinary and value-bearing checked nested calls to depth one;
- non-wrapping, atomic balance transfer;
- checked creation with initializer execution and runtime-code installation;
- a static `uint256 -> uint256` ABI dispatcher;
- storage reads/writes and explicit caller, call-value, and calldata inputs;
- ordered Word logs; and
- one explicit shared evaluator-fuel budget. Internal resumption laws prove
  that completed effects are not replayed; Oracle v5 publishes no resume token.

The transaction lifecycle is explicit. A top-level return commits the working
world and journal. Top-level balance-preflight rejection, revert, or trap
selects the checkpoint.

Failed child calls and failed initializers roll back their local state and
journal effects before control returns to the parent.

### Total observations

A v5 execution response distinguishes:

- preflight rejection, such as an unavailable sender balance;
- normal return or revert, each with its data;
- trap with a Word reason;
- resource exhaustion or an internal invariant failure.

Every terminal `executed` result includes the rollback-selected journal and
the requested initial/committed state observations. Probes can observe account
presence, storage, balance, nonce, and installed code. Logs and successful
creation addresses preserve order and duplicates.

Fuel exhaustion is reported as `inconclusive`; the Oracle does not invent a
terminal state observation for an unfinished execution. The fuel counter is a
formal evaluator bound, not an EVM gas model.

## Public Oracle interfaces

All versions coexist in one NDJSON command-line service. A request's exact
`schema` selects its decoder and handler; adding v5 does not reinterpret older
requests.

| Interface | Purpose | Status |
| --- | --- | --- |
| Oracle v1 | Legacy general envelope and capability discovery | Frozen compatibility interface |
| Oracle v2 | Semantic Core v1 checking and evaluation | Frozen |
| Oracle v3 | Semantic Core v2 checking and evaluation | Frozen and supported |
| Oracle v4 | Surface v1 restricted single-file parsing | Frozen historical compatibility interface |
| Oracle v5 | Core v3 checking and checked-contract execution | Implemented and public |

Oracle v5 publishes three queries:

- `capabilities` reports the exact profile, schemas, limits, and feature set;
- `coreCheck` checks one Core Wire v3 program; and
- `execute` validates and runs one complete contract scenario.

The command-line executable reads one compact JSON object per line and emits
one result per line in order. Capability reports are also available directly:

```text
lake exe solcoreOracle capabilities-v3
lake exe solcoreOracle capabilities-v4
lake exe solcoreOracle capabilities-v5
```

`--version` intentionally retains its legacy v1 meaning. Use a versioned
capability command to discover a newer protocol contract.

The human-readable wire catalogs are [Core Wire v3](CORE_WIRE_V3.md) and
[Oracle v5](ORACLE_V5_WIRE.md).

Requests, typed responses, and protocol errors have canonical encoders and
strict decoders. They reject unknown or duplicate fields, query/verdict
mismatches, invalid catalog entries, and rollback observations that claim
committed effects.

## Canonical syntax status

Source identities, UTF-8 byte spans, the complete token catalog, the
source-preserving parsed AST, exact Unicode identifier classification, a
public identifier validator, and the canonical lexer and parser are
implemented under `Solcore.Syntax`. `import Solcore` exposes this API.

`Solcore.Syntax.Parser.parse` accepts a complete `SourceFile` and returns its
tokens, retained nested comments, lexical and parse diagnostics, and parsed
file. The executable grammar covers imports, exports, pragmas, aliases, enums,
derive attributes, traits, implementations, contracts, fields, constructors,
fallbacks, functions, types, expressions, patterns, statements, blocks, and
inline Yul. It applies the pinned nesting policy, preserves UTF-8 byte ranges
and written distinctions, and recovers ordinary malformed input without using
the exceptional result branch.

The checked-in suite embeds all 23 dedicated positive fixtures from the pinned
Rust parser and adds focused acceptance, rejection, recovery, comment, Unicode,
span, legacy-spelling, and deterministic source-mutation tests. A development
comparison against the same revision also parsed all 490 `corpus/ok` sources
without lexical or parse diagnostics. No acceptance or source-AST gap was found
in the fixed-revision parser audit. Four malformed inputs differ only because
Lean retains an additional explicit recovery diagnostic; exact diagnostic
kinds, byte ranges, order, and recovery ASTs are now regression-tested.

The public lexer is proved total. Its character-count bound always suffices,
and every returned token, nested comment, and lexical diagnostic belongs to
the input file and uses a valid UTF-8 byte span. Tokens and comments remain in
source order without overlap.

The parser is also proved total at its public boundary. Every `SourceFile`
produces an ordinary `ParseOutput`; the internal lexer- and parser-invariant
error branches are unreachable. Malformed source is therefore represented by
ordinary diagnostics and recovery syntax rather than by an internal failure.
The same guarantee holds when `parseLexed` is called with a lexer result that
satisfies the public lexical contract.

The proof is compositional across types, expressions, patterns, statements,
Core blocks, inline Yul, imports, exports, aliases, enums, traits,
implementations, functions, contracts, derive attributes, recovery, and the
complete file loop. Recursive expression, pattern, statement, type, and Yul
parsers have sufficient production fuel, while list and recovery loops either
advance or terminate. All top-level declarations and contract-member forms are
included in the unconditional result.

Every public output also has a source-provenance contract: its parsed file has
the input identity and full-file span, retained lexer carriers are unchanged,
and all token and diagnostic spans belong to that same file. These properties
cover recovered output as well as diagnostic-free output.

An independent declarative grammar now covers pragma declarations, maximal
dotted qualified names, both local and `@`-prefixed external module paths, and
identifier or parenthesized-operator selector names. Shared declarative rules
and parser-soundness theorems now also cover nonempty comma-separated lists
with an optional trailing comma, selected import names and aliases, nonempty
selected-import lists, hiding clauses, optional hiding dispatch, and both
allow-empty delimiter policies. Export coverage additionally includes
nonempty lists without trailing commas, constructor selections, prioritized
export names, local export items, and remote selections. Derive coverage now
includes ordinary and diagnosed reserved target components, maximal dotted
targets, and exact normal `#[derive(...)]` attributes; diagnostic-free public
attribute soundness excludes its malformed recovery path.

Generic delimited outcomes now transport the stronger exact contract through
all four required-or-empty and trailing-or-no-trailing policies. Given exact
nested outcomes, tail relations fix forward elements, closing span, and final
remainder; complete relations fix the full `DelimitedList` AST; and every
delimiter rejection policy fixes its first failing remainder. The four exact
spec constructors are exported and compile-time consumed. This is a reusable
conditional law and does not assert that every existing nested production has
already acquired an exact contract.

Prioritized transactional fallback now has the matching generic exact
transport. Exact primary and fallback outcomes determine one successful value
and final remainder; success in the primary excludes fallback selection; and a
double rejection returns the unique original-input endpoint. The constructor
is exported and compile-time consumed, while each concrete use must still
supply exact contracts for both alternatives.

Shared generic parameters now have an exact nonempty `<...>` grammar with an
optional trailing comma. Required-list rejection records the exact delimiter
or nested checked-identifier failure. `requireGenericParameters` has no reject
branch; its defensive empty-list invariant is unreachable after a successful
required-list parse. An absent leading `<` is a nonconsuming optional success,
while a present guard commits from the original input and retains positive
evidence for that `<`. Required and optional success endpoints are
deterministic and each is exclusive with exact rejection. Both parsers also
retain unconditional success soundness and source-validity compositions.

Algebraic enums now have complete parser-independent ordinary success and
rejection coverage from the contextual `enum` marker through the closing
brace. A leading `(` commits constructor payload parsing; payloads may be empty
but cannot have a trailing comma. The custom body loop is reflected into the
allow-empty, allow-trailing delimited outcome relation with forward constructor
order and exact rejection remainders. Full declarations distinguish marker,
name, optional-generic, and body rejection. Constructor, body, and declaration
outcomes have deterministic success endpoints and disjoint success/rejection.
Their stronger exact contracts now unconditionally fix the constructor and
body ASTs, final remainders, and rejection endpoints. Complete declaration
exactness holds for each fixed supplied derive attribute, not across different
attributes. These laws are exposed by declarative and executable APIs.
An already supplied derive attribute consumes no input, remains in the AST,
and supplies the outer span start; source validity composes with its existing
contract.

Recursive type expressions now have exact parser-independent coverage for
named, mapping, comptime, proxy, tuple, and function forms. Their mutually
recursive delimiter judgments retain empty and nonempty lists, optional
trailing commas, optional nonempty named arguments and function returns, exact
token windows, and written element order. The named branch also records the
failed `comptime<` and `mapping(` composite lookaheads that give the executable
dispatcher its priority. Soundness is unconditional for both the fuel-bounded
and public recursive type parsers and composes with the established source
validity contract. The same recursive family now has exact outcomes: every
successful derivation fixes the complete `TypeExpr` AST and final remainder,
and every rejection fixes its first failing endpoint, both at fixed fuel and
at the public fuel boundary. Exact composite theorems also expose recursive
type-list tails, complete delimited lists, optional named arguments, and
optional function returns without leaking parser state or fuel into the
grammar.

Transparent type aliases now reuse that recursive type grammar after an exact
`type` keyword, name, prioritized optional parameter list that may be empty and
may have a trailing comma, equals sign, and semicolon. Their public theorem
requires diagnostic freedom only to exclude the alias-RHS recovery branch; the
normal alias path and recursive type theorem do not otherwise need that
premise. Recursive type, shared generic-parameter, type-alias, and
enum-declaration theorem families have compile-time consumers and public
`Solcore.Syntax` registration. The full build and `lake test` pass with those
registrations.

The complete broad type-alias outcome is now exact. Its allow-empty,
allow-trailing optional parameter list fixes the complete optional identifier
list, final remainder, and committed rejection endpoint. Malformed RHS
recovery fixes its error type and final remainder and has one nonconsuming
rejection endpoint. Core `TypeExpr` exactness makes the recovery-aware alias
value contract unconditional, and the full `type`/name/parameters/`=`/value/
semicolon sequence consequently fixes the complete declaration AST and every
first failing endpoint. Executable reflection and dedicated/public consumers
expose these laws; diagnostics, failure payloads, and whole parser states
remain outside the claim.

Backward diagnostic reflection is now a reusable parser proof boundary. A
diagnostic-free successful result can only have started from a diagnostic-free
parser state; this property composes through pure parsing, sequencing,
transactional choice, token consumers, and delimiter policies. Concrete
instances cover recursive types, named and delimited function parameters,
individual predicates, bare and grouped predicate sequences, optional `where`
clauses, and the generic-parameter, modifier, and return-clause leaves of a
function signature. Parameter recovery has a complementary commitment
theorem: every successful recovery or missing-type error retains a diagnostic.

`FunctionParameterParses` now describes exactly the ordinary and contextual
`comptime` typed forms, including the composite prefix absence that selects the
ordinary branch. `FunctionParametersParses` lifts that strict grammar through
the possibly empty parenthesized list with an optional trailing comma. Their
public success theorems require diagnostic freedom precisely to exclude error
and recovery values; both compose with the established source-validity
contracts.

The single public `namedParameter` also has a broad ordinary-outcome relation.
A missing colon is a diagnosed `.error` Core success at the post-name
remainder, not recovery. Only a Core rejection rewinds to the original cursor:
end, comma, or right parenthesis gives exact nonconsuming rejection; otherwise
the parser emits the failure diagnostic and performs its mandatory-first-token
maximal recovery scan. A carrier hole is reflected as recovery rejection.
Success endpoints are deterministic and exclusive with rejection, while the
strict `FunctionParameterParses` relation remains diagnostic-free. The broad
relation is also exact: fixed recovery-prefix spans determine the recovery
scan, complete recovery fixes its error parameter and remainder, and Core
`TypeExpr` exactness lifts through ordinary, `comptime`, missing-type, and
recovered parameter outcomes. Public executable reflection exposes unique
parameter AST/result and rejection-endpoint theorems.

The canonical `TypeExpr` and recovery-aware `namedParameter` outcomes now lift
to the `(` / `)` parameter list, with empty contents and a trailing comma
allowed. Delimiter and nested rejection endpoints are exact: recovery stops
leave an outer comma or right parenthesis unconsumed, a carrier hole remains a
nested rejection, and recovery to the window end may then yield exact
`delimiterMissing` rejection. The generic allow-empty trailing-list exactness
theorem now lifts those element outcomes to the complete parameter-list AST,
final remainder, and every delimiter or nested rejection endpoint. Strict
`FunctionParametersParses` remains the diagnostic-free list relation, while
the broad declarative and executable exact contracts are public and
compile-time consumed.

Predicates and optional `where` clauses also have exact component grammars and
unconditional success soundness. Bare sequences retain forward predicate
order and distinguish a final predicate from a trailing comma; grouped
sequences reuse the nonempty trailing-delimiter grammar. `PredicateSequenceParses`
now records the transactional parser's exact grouped-first priority. Its bare
constructor carries `GroupedPredicateSequenceUnavailable`: this follows either
from absence of the opening `(`, or from an exact grouped rejection whose
`no_parse` theorem excludes every grouped derivation before transactional
fallback runs the bare parser from the original input. Exact rejection traces
now also cover bare tails, complete bare sequences, and the grouped-first
dispatcher. The fallback rejection retains the grouped attempt's intermediate
remainder separately from the final bare rejection reached from the original
input. Bare and complete sequence outcomes are deterministic and success/reject
exclusive. For optional `where`, an absent contextual marker is a nonconsuming
success, while a present marker commits to the prioritized predicate sequence.
Executable ordinary rejection is reflected exactly as that committed sequence
rejection; the successful remainder is deterministic and success/rejection are
exclusive. Predicate ASTs, grouped and bare nonempty sequences, grouped-first
dispatch, and optional `where` values are now exact as well. Bare-tail value
uniqueness keeps the necessary shared preceding span explicit; complete
sequences discharge it and fix their AST, final remainder, and rejection
endpoint. Executable leaf APIs re-export the same result and endpoint laws.

For optional `returns`, an absent contextual marker is likewise a nonconsuming
success, while a present marker commits to the allow-empty, allow-trailing
parenthesized `TypeExpr` list. Executable rejection reflects the exact nested
type or delimiter remainder. The successful endpoint is deterministic and
success/rejection are exclusive. Core `TypeExpr` exactness now lifts through
the complete optional clause, fixing the return AST, remainder, and committed
rejection endpoint.

Function modifiers are parsed in the fixed optional `public`-then-`payable`
order, with unconditional grammar soundness. A diagnostic-free module parse
proves both markers absent because either marker commits an
outside-contract diagnostic, while every syntactically ordered pair is
allowed in a contract. Complete diagnostic-free function signatures, ending
before a function body or trait-method semicolon, now derive
`FunctionSignatureParses` under the corresponding module or contract policy.
The proof reflects diagnostic freedom backward through `where`, returns, and
modifiers before applying strict parameter-list soundness, and it matches the
parser and declarative signature endpoint definitions exactly. Source
validity composes with the same result. These parameter, predicate/`where`,
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
diagnostic-free, location-policy judgment. All six component stages now have
exact child contracts, so the broad signature unconditionally fixes its
complete AST and final remainder and fixes every rejection endpoint. These
laws are reflected for every executable location and compile-time consumed.

A broad ordinary `functionDecl` outcome is likewise independent of location.
Success composes the ordinary signature directly into an isolated `.allow`
Core body, retaining the exact declaration AST, signature-to-body order, outer
cover span, and final remainder. Rejection has exactly two externally visible
stages: signature rejection, or an uncaptured body rejection after ordinary
signature success. A rejection inside a balanced captured child block does not
escape; isolation emits its diagnostic and returns an ordinary empty-body
recovery success at the parent remainder. Declaration success endpoints are
deterministic and exclusive with rejection. The existing location-policy-aware
`FunctionDeclParses` theorem remains the stricter diagnostic-free judgment.
Exact signatures and unconditional isolated `.allow` bodies now give complete
function-declaration AST and endpoint exactness without additional premises.
The earlier body- and statement-parameterized APIs remain available.

A broad ordinary `constructorDecl` outcome now follows the executable stages
exactly: the required `constructor` keyword, recovery-aware parameters,
optional `public` then `payable`, and an isolated `.require` Core body. An
explicit `public` marker emits its constraint diagnostic but is discarded from
the AST, while diagnostic emission leaves the declarative remainder unchanged.
Success preserves the parameter and payable fields, exact final remainder, and
the marker-to-body cover span of the complete constructor AST. Rejection has
exactly three external stages: missing marker, rejected parameters, or an
uncaptured body rejection after modifier success. A balanced captured child
rejection instead yields diagnosed empty-body recovery success at the parent
remainder. Outcomes are deterministic and exclusive, while the existing
`ConstructorDeclParses` relation remains the strict diagnostic-free judgment.
Exact parameters, modifiers, and isolated `.require` bodies now make constructor
ASTs, final remainders, and rejection endpoints unconditionally unique.

A broad ordinary `fallbackDecl` outcome now begins with the exact `fallback`
keyword and recovery-aware parameters, followed by a pure validation stage.
Empty parameters pass silently; nonempty parameters remain in the AST and emit
the fallback-specific diagnostic without changing the declarative remainder.
Parsing then keeps the fixed optional `public`-then-`payable` modifier order and
enters an isolated `.require` Core body. Success preserves the complete AST,
marker-to-body cover span, retained parameters, payable marker, and exact final
remainder. Rejection exposes exactly three external stages: missing marker,
rejected parameters, or an uncaptured body rejection after validation and
modifier success. A balanced captured child rejection instead becomes a
diagnosed empty-body recovery success at the parent remainder. Outcomes are
deterministic and exclusive; strict diagnostic-free `FallbackDeclParses`
remains. Exact parameters, validation, modifiers, and isolated `.require` bodies
now make the complete fallback AST and rejection-endpoint contract unconditional.

Implementation outcomes now cover the optional `default` prefix, contextual
marker, optional generics, trait name, required nonempty trailing-comma head
types, optional `where`, custom method body, and complete AST. The default
prefix cannot reject, and the pure nonempty refinement adds only an invariant
branch. The right-brace-first body loop retains positive `function` guards,
strict progress, forward method order, and exact unexpected or nested
rejection remainders. Full declarations expose six rejecting stages after the
default prefix: marker, generics, name, head arguments, `where`, and body.
Default, head, method, body, and declaration successful remainders are
deterministic, and success/rejection are exclusive; module diagnostics and
captured-body recovery remain successes.
The optional default marker and required head arguments now unconditionally
fix their ASTs and final remainders, with exact head rejection endpoints and
no default-marker rejection. Unconditional isolated `.allow` Core-body exactness
now also fixes complete method, body, and declaration ASTs, final remainders,
and rejection endpoints without further assumptions.

Trait methods now extend the broad module-signature outcome through an exact
semicolon, retaining diagnostic-producing signature successes and separating
signature from missing-semicolon rejection. Trait bodies reflect the custom
right-brace-first loop with positive `function` guards, strict progress,
forward method order, and exact unexpected, nested-method, and recursive
rejection remainders. Complete declarations distinguish contextual marker,
name, required generics, optional `where`, and body rejection. Method, body,
and declaration success endpoints are deterministic and success/rejection
exclusive. Exact signature and child contracts now also make all three levels
unconditionally fix their complete ASTs, final remainders, and rejection
endpoints, including the forward method list and closing/body spans. These
stronger laws concern declarative values and remainders, not diagnostic traces,
failure payloads, or whole parser states. The strict diagnostic-free
`TraitDeclParses` family and its source-validity compositions remain available
beside the publicly exported broad outcomes.

Ordinary function declarations and strict diagnostic-free implementations
retain parametric parser-independent judgments over an abstract block
relation. Function soundness composes the exact location-specific signature,
isolated body, outer cover span, and final remainder. Implementation soundness
additionally retains optional-`default` priority, nonempty trailing-comma head arguments,
module-policy methods, right-brace-first body dispatch, strict method progress,
and forward method order. These APIs reflect diagnostic freedom through every
nested body and have source-validity compositions, consumers, and public
registration.

Contract declarations now lift the same abstract expression and block
relations through fields, functions, constructors, fallbacks, aliases, and
enums in exact executable priority order. Attribute-aware members accept a
derive attribute only on enums; body soundness preserves exact braces,
right-brace priority, strict member progress, forward member order, and rules
out every recovery success using its required diagnostic. Complete contract
soundness retains the marker, name, optional generics, body span, members, and
final remainder, with source-validity composition and public consumers.

The same abstract relations now extend through complete top-level dispatch and
the complete-file parser. `PlainTopItemParses` records the exact negative
lookaheads for every earlier declaration branch, while `TopItemParses` records
leading-hash priority and permits derive attachment only to enums.
`TopItemsParses` preserves declaration order, strict cursor progress, and
end-of-window termination. `SourceFileParses` additionally specifies the exact
pure attachment of the complete source-order comment stream. Diagnostic
reflection through every declaration and top-item branch rules out all file
recovery successes, so every diagnostic-free `sourceFile` result derives this
parameterized complete-file grammar and composes with source validity.
Parser-independent judgments now cover raw, balanced, isolated, and canonical
Core blocks; the complete Core expression layer; the ordered public Core
pattern layer; Core `let`, `return`, assignment, `for`, `match`, assembly,
block, `while`, `if`, `break`, and `continue` statements, and their complete
ordered dispatcher. Their mutually recursive executable expression, pattern,
statement, and block parsers are now closed by fuel-indexed ordinary/reject
outcome families. The public fuel bounds are explicit: expressions and
patterns use the active-window remainder plus one, statements use it plus two,
and blocks use the fixed statement fuel of the remainder plus one. Public
success and rejection soundness, deterministic outcome specifications, and
diagnostic reflection are registered for all four entry points. A single fuel
induction now proves unconditional AST and endpoint exactness for all three
mutually recursive term families. This covers lambda parameters and bodies,
maximal postfixes, operator precedence, tuple/pattern order, diagnosed statement
successes, prioritized transactional fallback, and recovery with fixed first
and last spans. Exact statements lift through raw block items, public blocks,
balanced capture/recovery isolation, and both tail policies, fixing complete
block ASTs, closing spans, final remainders, and external rejection endpoints.
Public executable APIs and consumers compare results with independently derived
grammar outcomes. The full build and tests pass; no diagnostic-free assumption,
diagnostic-trace equality, failure-payload equality, or whole-state equality is
required or claimed by these exactness laws.

Inline-Yul coverage includes name sequences, the public expression layer,
exact braced blocks, `let`, assignment, expression and source-level
`return(...)` statements, `if`, `for`, `switch`, function definitions,
keyword controls, optional semicolons, the complete ordered dispatcher, and
the diagnostic-free recovery boundary. Transactional constructor,
call-argument, and Yul-assignment fallbacks carry concrete parser-independent
rejection witnesses whose disjointness laws preserve parser priority. The
public recursive Yul expression, statement, and braced-body parsers are closed
by fuel-indexed clean/ordinary/reject outcome families, including recovery,
transactional rewind, exact statement priority, optional semicolons, and block
boundaries.

Inline-Yul expressions, statements, and bodies now also have unconditional
exact AST and remainder contracts, including fixed-fuel and public recursive
boundaries. Expression names, literals, identifier/call selection, and
transactional argument rewind fix their successful values. Statement priority,
optional semicolons, switch/default selection, diagnosed empty switches, and
brace-delimited bodies preserve complete ASTs, forward order, and retained
spans. Recovery-scan exactness shares both accumulated endpoint spans.
Expression and statement rejection rewind to the input; body rejection fixes
its first-failing endpoint. Declarative and executable APIs and dedicated
consumers expose these laws, and the full build and test suite pass. Diagnostic
traces, failure payloads, and whole parser-state equality remain outside this
contract.

`CoreTopItemOrdinaryParses` now supplies the public Core expression relation
and the isolated `.allow` and `.require` block relations to the abstract
top-item grammar. `CoreSourceFileOrdinaryParses` lifts that specialization
through exact item order, complete-window consumption, and comment attachment.
`CoreSourceFileOrdinaryParsesFromStart` fixes both the root token window and its
canonical terminal remainder: the carrier and `endIndex` are preserved and the
final cursor is exactly the token count. Every diagnostic-free successful
`parseLexed` result derives that judgment over the supplied lexer tokens and
comments; the public `parse` theorem states it over the tokens and comments
retained in its output. Paired theorems add canonical parsed-file source
validity at both boundaries.
The component relations deliberately remain recovery-aware ordinary
over-approximations, while the outer diagnostic-free premise excludes actual
recovery successes at the complete-file boundary.

Import leaves and payload helpers now have exact broad outcomes. Selector names
choose a checked identifier when `(` is absent; a positive `(` commits to a
nonempty maximal operator-symbol scan and exact `)`. An absent selected-name
`as` is a nonconsuming `none`, while a positive guard commits to one checked
identifier. Module paths similarly choose a local qualified name when `@` is
absent and commit to an external qualified name after exact `@`. Selected
entries parse source then alias, and both selected-import and hiding braces
require a nonempty, trailing-comma-permitting list. Optional hiding is
nonconsuming when its contextual marker is absent and commits to the complete
clause when present.

The import terminator consumes an exact semicolon. If it is missing immediately
before one of the exact top-item starters, it instead records a diagnostic,
returns the last payload span, and succeeds without consuming that starter;
every other missing terminator rejects. Plain, namespace, wildcard, and
selective payload outcomes compose these leaves in executable order, retain
the exact AST, covering span, cursor, token carrier, and active window, and
separate the first rejecting stage. Every endpoint is deterministic and its
success and rejection relations are exclusive.

The complete broad `importDecl` outcome also records the exact leading
`import` token and nonconsuming dispatch evidence. A leading `*` selects
namespace import exactly when offset-one lookahead is hard `as`; otherwise it
commits to wildcard import. Without `*`, `{` selects the selective branch and
every other token selects plain import. Branch failure never falls through to
a later alternative, and the complete outcome remains deterministic and
exclusive while preserving terminator recovery success. Stronger unconditional
contracts now fix complete import ASTs, successful remainders, and first
rejecting endpoints, including every alias, selected list, hiding clause, and
payload form. Terminator exactness shares the preceding span; payload exactness
shares the outer start. Selector operator parts are unique at a shared stopping
index, while the maximal scan and complete selector are unconditionally exact.
Public APIs and independent grammar-result consumers cover this full chain.

Export leaves, payloads, and the complete `exportDecl` now likewise have exact
broad outcomes. Export paths consume maximal dotted checked names. Constructor
selection prioritizes the `(*)` form over a nonempty, no-trailing-comma name
list; export names prioritize `*`, then a parenthesized operator selector, then
a checked identifier with optional constructor selection. A local item uses
identifier-plus-offset-one-dot lookahead to commit to qualified `path.*`, and
otherwise parses an export name. Remote selection chooses either `*` or an
allow-empty, trailing-comma-permitting braced export-name list.

Local payloads compose an allow-empty, trailing-comma-permitting item list with
an exact, nonrecovering semicolon. Path payloads parse a maximal path, then
prioritize dot plus selection, absent-dot `as` plus checked alias, and finally
the bare module form; every branch ends at the same exact semicolon boundary.
The aggregate consumes exact `export`, dispatches on a nonconsuming `{` guard,
and retains exact AST, covering span, carrier, window, cursor, and first
rejection. Successful endpoints are deterministic and success/rejection
exclusive. Stronger unconditional exactness now also fixes every complete
export AST and rejecting endpoint, from constructor/name selection through
local or remote payloads and the aggregate declaration. Supplied outer spans
remain shared explicitly where required.
The declarative and parser outcome packages are exported publicly and checked
by dedicated and public-boundary consumers. Their declaration-local guarantees
feed the broader top-item boundary described below.

Pragma item scanning and complete `pragmaDecl` now also have exact broad
ordinary outcomes. An immediate `;` gives an empty, nonconsuming item scan;
otherwise checked identifiers remain in forward order. Comma absence ends the
scan without consumption, while comma followed by `;` consumes only the
trailing comma. Complete pragmas compose exact `pragma`, a raw-identifier name
(which deliberately omits the checked-name hyphen diagnostic), the item scan,
and an exact semicolon. Rejection separates missing keyword,
rejected name, rejected items, and missing semicolon. Item-tail, item-list, and
declaration successful remainders are deterministic, and success is disjoint
from rejection. Unconditional exactness additionally fixes all item lists,
complete located declaration ASTs, and first rejecting endpoints. Production
tail consumers share the reverse prefix, retaining forward result order.
The public packages are compile-time consumed and feed the broader top-item
and file outcomes described below.

Dotted derive targets now have exact broad ordinary outcomes at the component,
recursive dotted-tail, and complete-target layers. Components retain both
checked identifiers and diagnosed reserved hard keywords; rejection records
that neither branch is available. Tail rejection preserves the consumed dot
and the exact first or later component failure. Successful remainders are
unique and success is disjoint from rejection at every layer. The stronger
exact outcome contract now also fixes each successful identifier/component
list/complete target AST and every rejecting remainder. Executable success and
rejection reflection expose these exactness laws publicly and are checked by
dedicated and umbrella consumers.

Complete derive attributes now also have exact broad ordinary outcomes. The
valid path records five rejection stages: hash, opening bracket, contextual
`derive` marker, no-trailing target list, and closing bracket. Recovery gives
current `]` first priority and consumes it as malformed recovery; otherwise it
stops without consumption at the window end, a top-item start, an
identifier-plus-colon contract field, `}`, or a missing carrier slot inside
the active window. Any other raw token advances the scan and updates its last
span. After exact `#[` consumption, that tail has no ordinary rejection. The
public transactional choice retries recovery from the original input after a
valid-path rejection, and a public rejection records rejection of both
attempts. Generic no-trailing lists now lift exact nested outcomes to a unique
complete list AST and rejecting remainder. Consequently the valid path, the
complete recovery path, and the public prioritized choice each fix the exact
successful attribute AST and final remainder as well as every rejecting
remainder. Recovery-tail value uniqueness is stated only for one fixed hash and
last-retained span, which is exactly what the complete recovery prefix proves.
Executable reflection exposes the public result and rejection-endpoint laws,
and dedicated and public-boundary consumers compile against them. These laws
concern declarative ASTs and remainders; they do not equate parser diagnostics,
failure payloads, or complete parser states.

Attribute-free `contractMemberCore` now has complete broad ordinary coverage for
its prioritized six-way dispatcher. Identifier-plus-colon field lookahead runs
first, followed by `function`, `constructor`, `fallback`, `type`, and contextual
`enum`; a selected branch never falls through after rejection. Success retains
the wrapped member AST, declaration span, empty leading comments, carrier,
window, cursor, and final remainder. Rejection records the selected leaf or an
exact nonconsuming unrecognized-member case. Successful remainders are
deterministic and success is disjoint from rejection. Its stronger AST and
endpoint contract is now unconditional: public Core expressions fix field
initializers, isolated `.allow`/`.require` bodies fix the three body-bearing
declarations, and type aliases and enums are independently exact. Existing
conditional APIs and strict member soundness remain available.

Contract-member derive attachment now has an exact pure relation for all seven
member variants, with one unique AST result for every input. Only enums retain
the attribute; the five other declaration variants keep their payload while
extending both their member and nested declaration spans, and the error variant
extends only its member span. Every branch preserves leading comments.
Executable attachment unconditionally reflects this transformation and leaves
the declarative remainder unchanged, including the non-enum branches that emit
`deriveOnlyEnum`; attachment itself therefore has no rejecting outcome.

The public derive-aware `contractMemberWithAttribute` boundary now has complete
broad ordinary success and rejection coverage. An absent hash selects the
attribute-free core directly. A present hash commits to the public derive
parser, then the core member parser, and finally the pure attachment above.
Rejection records exactly one of three first failing stages: plain core, derive,
or core after a successful derive. Successful remainders are deterministic and
success is disjoint from rejection. Exact attribute-free members and pure
attachment now make derive-aware member ASTs and rejection endpoints
unconditionally unique; the generic conditional lift remains available.

Standalone contract-member recovery now has exact broad outcomes. Success
consumes one mandatory token, scans to the window end, a recovery boundary, or
a missing carrier slot, and returns the exact error-member span without
consuming the boundary. Rejection records only an unavailable mandatory first
token. Successful remainders are deterministic and success is disjoint from
rejection. For fixed first and last retained spans the scan fixes its error AST;
the complete recovery path fixes those spans, the member AST, and final
remainder, while rejection has one exact nonconsuming endpoint. These stronger
laws are re-exported at the executable boundary and compile-time consumed.

The recovery-aware contract body now composes right-brace priority, direct
member progress, window-preserving rejection rewind, boundary-aware recovery,
forward member order, exact braces, and every first rejecting remainder. Broad
contract declarations then compose exact `contract`, name, optional generics,
and body stages with four matching rejection cases. Both layers have
deterministic successful remainders and disjoint success/rejection. Stronger
unconditional exactness now lifts from derive-aware members through the
recovery-aware body and complete declaration, fixing the full AST, final
remainder, and rejection endpoint. Core terms discharge the earlier shared
premises. The earlier conditional declarative and executable APIs remain
public and compile-time consumed. These
claims do not equate diagnostic traces, failure payloads, or whole parser
states.

Attribute-free top-item dispatch now has exact broad outcomes for import,
export, pragma, type alias, function, enum, trait, implementation, and contract
declarations in executable priority order, followed by an exact nonconsuming
unrecognized case. Pure top-item derive attachment covers all ten item variants:
enums retain the attribute, while every other item retains its payload and
extends the appropriate outer and nested spans. The public derive-aware
dispatcher records hash absence or commits to derive parsing, plain dispatch,
and attachment, with each first rejecting stage represented. Successful
remainders are deterministic and success is disjoint from rejection.

Top-item recovery and the complete file loop now also have exact broad
outcomes. Recovery consumes one mandatory malformed token, updates the last
span while scanning, and stops without consuming the next top-item boundary;
an unavailable first carrier is its only rejection. The file loop retains
source order without exposing its reverse accumulator, enforces direct-item
progress, rewinds a window-preserving item rejection, treats rejection at a
recognized item start as a nonconsuming diagnostic success, and otherwise
inserts the exact recovered error item. The complete `sourceFile` outcome keeps
the input source id, full-file span, pure comment attachment, comments, and
first rejection remainder exactly. These relations, executable reflection
packages, and outcome specifications are public and compile-time consumed.
Unlike strict diagnostic-free acceptance, the broad boundary-stop outcome does
not claim that every successful final cursor is at the window end.

Complete syntax exactness is now unconditional. Exact import and export leaves
close plain top-item dispatch; derive attachment closes the public dispatcher;
and recovery and comment attachment lift the contract through the file loop to
the complete parsed-file AST. Success fixes the full AST and declarative
remainder, and rejection fixes its endpoint, without recursive exactness or
diagnostic-free premises. Public `parseLexed` and `parse` results agree with
every independently derived public AST over the same file, tokens, and comments.
The public AST theorem does not invent a final cursor that `ParseOutput` does
not expose, or equate complete diagnostic traces and parser states.

Ordinary grammar completeness now pairs those uniqueness laws with soundness
and invariant-free execution. Independent success is equivalent to executable
success with the same AST and remainder; independent rejection is equivalent
to executable rejection at the same endpoint. Public Core types, expressions,
patterns, statements, lambda parameters, both raw/isolated block policies,
Yul expressions/statements/blocks, all top-level declarations, derive paths,
top-item dispatch, recovery, and the file loop have compile-time consumers.
Most internal boundaries require only a valid input state; pragmas and the
unconditionally total recovery/derive leaves need no such premise. File-loop
correspondence keeps the fixed forward prefix outside the grammar suffix and
discharges its fuel condition at the production boundary.

At `parseLexed`, a specified AST is returned exactly when the supplied lexical
carriers pass validation and the public grammar derives that AST. At `parse`,
the corresponding condition uses carriers produced by canonical lexing.
Neither direction requires diagnostic freedom or nesting clearance. This is
the recovery-aware syntax boundary, not a claim that every source is accepted
without diagnostics, nor an independent characterization of lexer payloads.
The public correspondence theorems depend only on the allowed standard axioms.

Validated carriers also have exactly one independently derived public AST, and
every such derivation satisfies recursive source provenance for its complete
Core syntax, top-level items, and comments. No executable parser reply is needed
as a caller premise. Contract-internal fields, plain/derive-aware members,
braced bodies, and standalone member recovery have matching completeness APIs.

The public nesting preflight now has its own parser-independent exact outcome
grammar. It classifies each token as conditional, group-open, block-open,
close, reset, or preserving; carries the exact delimiter and conditional scope
bases; and either clears the full token list or returns the first overflowing
span, dimension, and shared canonical limit. The executable checker is proved
equivalent in both the `none` and `some` directions, so the implementation and
declarative limit cannot drift.

Already-tokenized input validation now also has a parser-independent exact
outcome grammar. It checks source identity first, then the first invalid token
span, comment span, or lexical-diagnostic span in that priority order, retaining
the exact zero-based index and span. The scans and whole outcome are total and
functional, and declarative acceptance is equivalent to `LexedFile.ValidFor`.
The executable validators reflect those outcomes exactly. For every arbitrary
`LexedFile`, a public `parseLexed` error is precisely the mapped first
validation rejection; otherwise production parsing returns a broad public AST
outcome with exact retained lexical carriers and canonical output validity.

Broad successful `parseLexed` and `parse` syntax is now covered at the public
boundary as well. A nesting overflow returns the exact empty parsed file with
source id, full-file span, and retained comments. A clear nesting scan runs the
recovery-aware `SourceFileOrdinaryParses` relation from the exact root token
window while existentially hiding the final remainder that `ParseOutput` does
not expose. Both the direct token boundary and the complete source boundary
compose with the full canonical output-validity contract. The overflow branch
additionally fixes the entire `ParseOutput`: retained tokens, lexical
diagnostics, and the unsuppressed singleton nesting diagnostic. The normal
branch's complete parse-diagnostic trace is not yet claimed by this broad
relation because the current declarative remainder deliberately carries no
diagnostic accumulator. When nesting clears, a separate exact executable
witness exposes the successful underlying `sourceFile` reply, final state, and
the diagnostic-filter equation used to assemble the public output.

A first normal-branch diagnostic-trace slice is now exact independently of that
executable witness. Standalone top-item recovery appends exactly one recovery
event at the recovered AST span, while rejecting an unavailable first token
adds none. Independent trace rules preserve prior diagnostic order explicitly.
An independent lexical-cascade relation keeps or drops candidate spans in
input order, retaining duplicates and the existing same-source, LF-line,
overlap, inclusive endpoint, and horizontal-whitespace rules. Its interpretation
as top-item recovery diagnostics agrees with the executable filter both ways.

When all top-item starts are absent and one independent recovery reaches the
root-window end, these laws fix the complete `parseLexed` or `parse` output:
the comment-attached error AST, retained tokens and lexical diagnostics, and
the entire filtered parse-diagnostic list. Validation and nesting clearance
remain explicit, and canonical lexing supplies validation at the source boundary.

A recognized-start trace is also complete when `pragma` has no following raw
identifier. Independent current-input observations fix the exact found token
and failure span, including EOF and unavailable carrier slots, with source and
window-end byte supplied explicitly. Raw and checked identifier rejection add
no diagnostic themselves. The file boundary rewinds only the cursor, preserves
the failed attempt's diagnostics, and appends its unexpected report. This
missing-name prefix therefore fixes every public output field, including the
empty item list, retained comments and lexical carriers, and exact filtered
expectation diagnostic. Its public correspondence needs no assumed parser reply.
Other recognized-start failures, nested isolation, and arbitrary declaration
diagnostic traces remain outside these completed slices.

Identifier success now has an independent exact trace too. Raw names emit
nothing; checked names append exactly one located hyphen diagnostic when their
spelling contains `-`, even if it occurs repeatedly. The grammar fixes the full
name, token remainder, and added diagnostic suffix, with a bidirectional
executable correspondence and no input-validity or diagnostic-free premise.
Filtering also has a total, unique independent relation over arbitrary mixed
diagnostic lists, not only fixed-kind span lists. It preserves every retained
report's metadata and occurrence order; identifier, grammar-constraint, and
nesting diagnostics are protected even when their spans match lexical errors.
Exact hard-keyword, symbol, and contextual-word primitives now also have
bidirectional trace correspondence. A successful token step emits nothing;
rejection preserves the input and its existing diagnostics while fixing the
uncommitted report. Contextual words remain identifier tokens with contextual
expectations, not hard keywords. Protected identifier traces can be appended to
an independently filtered mixed prefix without losing either order or metadata.

These rules now cover successful complete pragma declarations. Only checked
items contribute diagnostic events, in written order; the raw pragma name and
punctuation are silent, and an accumulated item prefix is never diagnosed again.
Empty item lists and trailing commas are included. One independent pragma
derivation reaching the root-window end fixes every public output field,
including the comment-attached singleton AST and all protected item diagnostics.
No assumed declaration or item reply is needed at that public boundary.
Ground canonical-source proofs fix the raw-name/checked-item distinction,
multiple hyphens per item, trailing commas, same-line lexical errors with
protected item diagnostics, and retained/attached comments. Normalization is
also proved idempotent and compatible with concatenating independently filtered
traces, so repeated filtering cannot remove an already retained occurrence.

The same complete-output boundary now covers any finite sequence of successful
pragmas through the token-window end, including the empty sequence. Independent
grammar fixes the declaration list, final remainder, and concatenated protected
trace. Existing reverse item prefixes are restored once and are never diagnosed
again. Declaration count supplies a sufficient execution bound, and the usual
production bound is proved adequate. Public token/source theorems retain every
wrapped and comment-attached declaration in order; a proposed output diagnostic
list is correct exactly when it equals the complete independent trace.

Pragma rejection now has its own complete independent trace contract. Keyword,
raw-name, checked-item, and final-semicolon failures are distinguished in first
failure order. The grammar fixes the exact remainder, every uncommitted failure
field, and all events from completed checked items. Source-file and full-window
context are preserved without a validity assumption, including arbitrary prior
diagnostics and malformed windows. At the public boundary, a recognized initial
pragma stop produces no AST item, retains every lexical field and comment, and
normalizes the earlier item events followed by exactly one committed failure.
All earlier events are protected: only that final report can be suppressed.
Canonical regressions cover missing items, missing semicolons, same-line lexical
suppression, and ordered protected events across two successful declarations.

The recognized-stop contract also extends across any successful pragma prefix.
Independent grammar fixes the ordered retained declarations, the start of the
final rejected pragma, its complete report, and all preceding events. Production
execution rewinds only to that final start, retains earlier items, and appends
the final report once. Complete public outputs preserve comments and all lexical
fields, with exact mixed filtering. Canonical successful-then-rejected examples
retain the first AST and both hyphen events; a same-line lexical error suppresses
only the final expectation report, including its exact EOF byte position.

Balanced block isolation now has exact compositional diagnostic laws and an
independent conditional trace grammar. The child starts with an empty trace and
uses its captured closing-byte boundary; the parent resumes after that capture
with its original file, tokens, and full window. Child events follow parent
events, and only recovered ordinary rejection appends its report once. Invariants
remain invariants. Independent grammar erases to the existing ordinary isolation
outcomes and lifts inner AST/remainder/report/trace uniqueness. Explicit inner
success/rejection soundness and completeness contracts yield outer trace iff
theorems, including suffix existence for every execution and exact duplicate
order. These are lifting contracts, not a claim that all concrete Core block
traces have already been specified. Repeated isolation does not recommit a
failure already recovered by an inner wrapper.

Core block closing now has complete independent tail-validation traces. Every
non-final unterminated expression emits one constraint at its full statement
span; only the final expression is exempt under `allow`. These traces are total,
unique, ordered, and protected from lexical suppression. An empty trace is
equivalent to the existing tail-validity predicate. Exact right-brace recognition,
the source-order body, remainder, and complete appended trace characterize
successful closing. A missing brace rejects before any tail validation and
preserves the whole input, with an exact uncommitted failure. Mixed filtering
acts on preceding diagnostics while retaining the full validation suffix.
The existing parser behavior is unchanged; a small proof-only seam exposes
the private validator's diagnostic effect.

Raw Core blocks now have independent successful and rejecting trace grammars,
with exact braces, branch priority, AST order, remainders, and full reports.
Success concatenates all statement events before the single whole-body tail
validation pass. Rejection retains earlier statement events without performing
that validation. Statement trace soundness/completeness and source/full-window
preservation lift to raw success/rejection iff theorems, including sufficient
production fuel, arbitrary prior diagnostics, and fixed complete failures.
These contracts also compose through balanced isolation: successful raw traces
are retained, and recovered raw rejection appends one report at the parent
resume point. Independent statement outcome exactness supplies joint raw and
isolated block exactness; no totality claim is inferred from uniqueness alone.
Normalization keeps the entire delayed validation suffix after filtering earlier
statement events. Concrete general statement trace contracts remain separate.

A test-only checked-identifier statement adapter exercises these contracts on
nonempty hand-constructed token carriers. Two hyphenated names emit both name
events before either delayed termination event; allowing the final expression
removes only its termination event. Rejection after the first name emits no
termination event, and isolation commits the unexpected-token report once while
restoring the parent window and leaving the next token untouched. These examples
do not claim a Core statement grammar or canonical-lexer correspondence.

The real Core `break` and `continue` leaves now have unconditional independent
diagnostic traces, with success/rejection correspondence, complete failure
records, and all five statement execution contracts. Success changes only the
cursor by two tokens and is silent; rejection is also silent and selects the
missing keyword before the missing semicolon. Independent outcome existence,
uniqueness, and disjointness cover arbitrary carriers, including exhausted
windows and missing array slots. These leaf laws instantiate raw and isolated
restricted-block exactness without abstract statement assumptions. Concrete
token-carrier consumers exercise two-statement success and later-semicolon
rejection under both tail policies, retaining arbitrary prior events and the
post-recovery parent window and following token. Two canonical source fixtures
also connect actual lexing to break-pair success and break/continue rejection
priority, including recovered parent continuation. Their lexer results are
kernel checked; parser outcomes follow the independent trace proofs. General
statement and whole-file traces remain separate.

Return statements now have independent optional-value and full-statement
success/rejection traces. A current semicolon selects no value without invoking
the expression parser. Otherwise the expression's AST, complete event order,
and first rejection report are preserved; a later missing semicolon keeps the
successful expression's events and its own report remains uncommitted.
Expression trace contracts lift to all five return statement contracts and
exact execution iff theorems, including the full failure record and arbitrary
prior events. Successful trace correspondence needs no expression context
assumption; source/full-window preservation is explicit for the frame and final
semicolon-failure report. The empty `return;` execution is unconditional and
changes only the cursor by two tokens. Independent expression exactness and
existence are separate assumptions: the former lifts to return and restricted
raw/isolated block exactness, while the latter supplies return outcome existence.
General expression trace contracts are still abstract at this boundary.

Core literal and Boolean primitives now have unconditional exact silent
success/rejection traces. Decimal, hexadecimal, and string spellings are retained
verbatim; Boolean keywords retain the existing identifier-shaped AST. Success
changes only the cursor by one token; rejection retains the whole input state
and fixes the complete failure, including the distinct literal versus expression
expectations. Independent existence, uniqueness, and disjointness cover arbitrary
carriers and windows. The actual literal-expression leaf supplies all five
expression execution contracts and both independent expression laws, discharging
the abstract assumptions for empty/one-literal returns and restricted raw/isolated
return block exactness. General expressions are not implied by this leaf result.

Concrete consumers now connect canonical lexing to `return 42;` and the exact
window-end semicolon failure for `return 42`. Empty `return;` bypasses an arbitrary
expression parser. A separate explicit-token block mixes literal and empty
returns under both tail policies and proves raw/isolated success with arbitrary
prior diagnostics, restored parent context, and an unread following token.

Raw block statements now have independent traces and all five execution
contracts under explicit inner statement laws. They wrap `coreBlock .require`:
the successful AST is mapped to a block statement with the same output state,
and rejection propagates the complete failure and state without committing a
report or performing isolation. Erasure, progress, token-window laws, and joint
exactness compose from the raw block relations. Successful file/full-window
preservation is proved from the inner frame alone, including delayed validation;
the parser file adds only a proof exposing its existing validator frame.

Expression names and the real identifier-expression leaf now have unconditional
exact traces. Boolean keywords take priority and remain silent identifier-shaped
values; ordinary identifiers retain the checked spelling event when they contain
hyphens. Independent ordinary erasure, output shape, uniqueness, disjointness,
and outcome existence match the executable branch order. Successful execution
fixes the entire state: one token is consumed and the fresh trace is appended
to existing diagnostics. Rejection preserves the whole input and reports the
identifier expectation after both Boolean guards fail. The identifier-expression
leaf supplies all five expression contracts and independent expression laws,
including concrete nonempty returns that retain a single hyphen event.

Protected event traces now compose through optional return values, returns,
raw block items/blocks, and block statements on both success and rejection.
Checked-name events and delayed termination constraints survive arbitrary
lexical cascade filtering with all metadata, order, and duplicates intact.
Executable filter consumers show that prior diagnostics may be normalized while
the complete fresh suffix remains unchanged, including nested return blocks.
Uncommitted failure reports are kept separate, and reports appended by isolated
recovery are deliberately not presumed protected.

Concrete two-level break-block consumers verify nested AST order and spans,
direct propagation of an inner semicolon failure without skipping closing
braces, and one-report recovery only when isolation is applied to the outer
block. Checked-name return blocks have canonical lexer fixtures for successful
two-name events and later semicolon failure, with exact raw/recovered diagnostic
order, restored parent contexts, and unread following tokens. These remain
restricted statement/leaf instances rather than general expression/file traces.

Generic no-trailing lists now have independent successful and rejecting traces
for either empty-list policy. Child contracts give exact AST/remainder/report
and complete appended-event correspondence, with arbitrary prior diagnostics
and reverse element prefixes. Successful children preserve source and the full
active window; token-carrier preservation is separate and needed only when
erasing whole-list success to the older ordinary grammar. Completeness uses
the actual production fuel measured immediately after the opening delimiter.
Commas take priority over closing symbols, even when both symbols are comma;
after a comma the child runs directly without a closing-absence guard. Missing
delimiters report comma then closing, retaining duplicate expectations. Joint
independent exactness and protected-suffix normalization compose from child
laws without asserting child totality or general expression trace completion.

Array-literal wrappers lift these list laws to all five expression trace
contracts and exact success/rejection/full-failure correspondence. Mapping
changes only the AST, preserving the full output state and uncommitted failure.
Independent structure, joint exactness, and protected-event laws compose under
explicit child assumptions. Concrete identifier and literal children cover
two checked names, empty arrays, numeric arrays, later-child rejection, missing
delimiters, and a trailing comma rejected by the identifier child. Four canonical
lexer fixtures connect directly through initial parser states to actual array
outcomes, with exact spans, ordered diagnostics, and unread following tokens.
These wrappers do not yet supply the general recursive expression contracts.

Checked-name arrays also compose through actual return-only raw and isolated
blocks. Canonical source examples connect directly to both successful execution
and exact child-failure propagation; only outer isolation commits that report
once, recovers an empty body, and restores the parent window and unread tail.
Independent restricted block exactness and raw protected-suffix normalization
use the concrete child laws, with no general expression assumptions.

Leading-dot constructors and their optional argument lists now have independent
successful and rejecting traces, conditional execution contracts, and exact
AST/remainder/report/event correspondence. Boolean-first checked-name events
precede argument events; absent arguments leave the entire state unchanged,
while written empty parentheses remain a present empty list. No-argument and
empty-list consumers require no child contract. Raw dot invocation also covers
missing-dot rejection; erasure into the older dispatcher-selected rejection
grammar explicitly separates that case. Dot/name/argument failures remain
uncommitted, and protected name/argument suffixes retain all metadata and order.
Joint independent exactness requires only child uniqueness and disjointness,
not outcome existence or concrete recursive expression execution.

Canonical constructor fixtures connect actual lexing and initial states to a
three-name successful trace and a two-name prefix before argument rejection.
They retain the separate dot/name/list spans, full parent window, unread tail,
and uncommitted identifier failure with arbitrary incoming diagnostics.

Parenthesized expressions and their comma tails now have independent success
and raw rejection traces, conditional sound/complete correspondence, and joint
uniqueness/disjointness. Empty parentheses form an empty tuple; a singleton
remains a group even with a trailing comma, while larger tuples preserve source
order. Immediate closing bypasses any child and is silent. After a successful
child without a following comma, a failed close expects only `)`, not the generic
comma/closing pair. Raw missing-opening and missing-comma failures are separated
from the older selected ordinary grammar. The tail uses the actual production
fuel after the first child, retains arbitrary reverse prefixes and prior events,
and needs successful child file/full-window preservation, not input validity.
Protected child traces survive normalization; the final report is uncommitted.
Canonical checked-name fixtures verify empty/group/tuple ASTs and two closing
failures, including exact spans, remaining tokens, windows, and ordered events.
These are concrete restricted-child consumers, not general recursive-expression
or mixed-file trace completeness.

Proxy expressions now have independent success/raw-rejection traces and exact
execution correspondences under explicit contracts for the real type parser.
The silent `@` marker retains its own span while the full type AST and every
child event are propagated unchanged. Missing-marker rejection keeps the whole
input state and is separated from selected ordinary erasure; type rejection
retains its complete failure and returned state without committing its report.
Independent joint exactness and protected-suffix laws remain conditional on
type properties. Canonical `@a-b tail` and `@+ tail` consumers independently
execute the real simple-name and rejecting type paths, fixing the hyphen event
or type-specific failure, full windows, cursors, and unread tokens. They do not
establish general recursive type diagnostic contracts or full-file traces.

Named-type finishing now has an unconditional independent diagnostic trace:
exactly an unqualified `mapping` spelling emits the canonical-form constraint,
with a span covering any supplied type arguments. Qualified and other spellings
are silent. Execution always succeeds and changes only the appended events;
the entire type AST, input carrier/window/cursor, prior reports, and duplicates
are exact. Constraint events survive normalization. This finishing-only result
is one compositional stage; recursive type traces remain separate.

Optional lambda return annotations now have independent exact success/rejection
traces under real type-parser contracts. Arrow absence returns `none` with the
whole state unchanged and cannot reject; a present arrow silently forwards the
type AST or complete failure and all child events. The raw missing-arrow case
is therefore not a rejection rule. Structural erasure, joint exactness, and
protected-suffix normalization are separated from child progress/window laws.
Consumers keep duplicate events and failed child states exactly; they remain
conditional, not complete traces for lambda parameters, bodies, or full lambdas.

Qualified names now have unconditional independent success/rejection traces,
five generic execution contracts, and exact complete output-state laws. Every
checked component contributes its spelling event in source order; dots are
silent and absence of the next dot ends the maximal name. A selected dot with
no following identifier rejects at that position, retaining earlier events and
the complete context-specific failure without committing it. Raw tail laws
support arbitrary first/last/reversed prefixes and adequate or production fuel;
the full parser uses its actual post-first-name fuel. No input-validity premise
is needed. Independent joint exactness and protected normalization are public.
Canonical three-name success and two-name-prefix rejection fix all spans,
carriers, windows, cursors, and following tokens in every context and phase.
These close the name component, not argument-list or recursive type traces.

Generic trailing-enabled lists now have independent success/rejection traces
and five execution contracts under explicit child contracts. Commas retain
priority over closing delimiters, including a comma-valued closing symbol;
an immediate post-comma close bypasses the child entirely. Both empty policies,
strict child progress, arbitrary reverse prefixes/prior events, and the actual
post-opening production fuel are exact. Successful child file/full-window
preservation suffices for execution; separate carrier laws support ordinary
erasure. Joint exactness asserts uniqueness/disjointness, not existence.
Canonical checked-name lists cover trailing success, child failure after a
comma, and the distinct ordered comma/closing report when neither is present.
Protected fresh events survive normalization with order and multiplicity intact;
final rejection reports remain uncommitted. This generic boundary does not yet
close real type-argument, lambda-parameter, or recursive expression traces.

Optional named-type arguments now compose the nonempty trailing-enabled list
into independent exact success/rejection traces under nested type contracts.
Absent `<` returns `none` with the entire state unchanged, bypassing every
child. Present arguments retain their complete nonempty carrier and span;
the silent `requireNonempty` conversion cannot fail its defensive invariant
after successful nonempty parsing. Rejection requires positive `<` lookahead
and forwards the complete list failure/state without committing its report.
Independent erasure, uniqueness/disjointness, and protected suffix laws remain
separate from execution and child carrier preservation. Canonical consumers
use the real `typeExpr` child for `<a-b,> tail` and `<a-b,+> tail`, preserving
the prior events, checked-name event, complete state, and unconsumed tail.
These are concrete examples, not general recursive type trace contracts.

Raw named types now compose exact qualified-name, optional-argument, and
finishing traces in that order, with five execution contracts under nested
type contracts. Successful ASTs and all spans are fixed; name/argument failures
retain the exact uncommitted failure and earlier events, without running the
finishing stage. Independent success erases componentwise, while rejection
erases to the existing raw named-type rejection; neither silently assumes the
type dispatcher's priority guards. Joint exactness and protected normalization
are public. Consumers fix arbitrary argument states and events before the
mapping constraint, bypass every nested child when arguments are absent, and
verify canonical `mapping tail` success versus `mapping<+> tail` rejection
with a real type child. The latter emits no premature mapping constraint.
Prior reports, complete states, and unconsumed tokens are retained. General
recursive type traces and prioritized type dispatch still remain separate.

Raw `mapping(key => value)` types now have independent exact success/rejection
traces and five execution contracts under recursive child contracts. The
contextual marker is the actual identifier token, and key events precede value
events. Every AST span and each first failure at marker/open/key/arrow/value/close
is fixed, including the expected contextual marker or single punctuation and
the complete uncommitted report. Raw missing-marker/opening cases stay separate
from the older selected mapping rejection. No child progress is assumed: this
straight-line parser accepts successful non-advancing children, unlike list
loops. Ordinary carrier laws remain separate from runtime source/window framing.
Joint exactness and protected suffixes are public. Canonical real-type-child
success and closing failure retain both checked-name events, full output states,
and following tokens. A reusable positive-fuel checked-name leaf helper supplies
these concrete children without asserting general recursive type contracts.

Raw proxy types `@T` now have independent exact success/rejection traces and
five execution contracts. Success and rejection forwarding require only the
corresponding child contracts, with successful source/window framing proved
separately. The marker and complete proxy AST spans, child state, events, and
uncommitted failure are exact; a missing marker bypasses every child on the
unchanged state. Raw marker failure remains separate from selected ordinary
rejection. Joint uniqueness/disjointness and protected ordered suffixes are
public. Canonical `@a-b tail` and `@+ tail` consumers use the real type child and
verify complete states and unconsumed tails. These type results are distinct
from proxy-expression traces and do not complete general recursive type traces.

Raw `comptime<T>` types now retain the contextual identifier marker, inner AST,
angle and outer spans, and exact nested events under child trace contracts.
All four first failures (marker/opening/child/closing) have exact uncommitted
reports; raw prefix failures remain distinct from selected ordinary rejection.
Success forwarding needs no child frame, while a closing report uses the
successful child's source/full-window frame. Joint uniqueness/disjointness and
protected suffixes are public. Canonical real-type-child success and closing
failure preserve the whole state, remainder, prior events, and following tokens;
raw prefix failures bypass every child.

Raw tuple-type traces now reuse trailing-enabled lists with empty-list priority,
strict child progress, and exact production fuel. Every list arity remains a
tuple type, including `()` and `(a-b,)`; no expression-group reinterpretation
is introduced. Five execution contracts, independent ordinary erasure with
separate carrier laws, joint uniqueness/disjointness, protected suffixes, and
raw/selected rejection separation are public. Canonical real-type-child empty,
singleton, two-element, and missing-separator cases fix the full AST/state,
checked-name event order, and ordered comma/right-paren expectation. These two
raw type slices do not complete recursive type or prioritized dispatch traces.

Optional function-type `returns(...)` clauses now have independent exact
success/rejection traces and five contracts under nested type contracts. An
absent contextual identifier succeeds with `none` on the unchanged whole state;
a present marker delegates to the empty-allowed trailing list, including raw
opening failure. Exact list ASTs, spans, emitted events, and uncommitted failures
are retained. Joint uniqueness/disjointness and protected ordered suffixes are
public. Canonical empty returns bypass every possible child; real-type-child
singleton success and separator failure retain full states and following tokens.
This optional clause does not itself complete function-type or recursive traces.

Raw function types now compose the keyword, parameter list, and optional
returns with exact parameter-before-return diagnostic order. The complete AST
uses the returns-list end span when present and the parameter-list end span
otherwise. Five contracts, exact component success/failure equivalences,
independent ordinary erasure, joint uniqueness/disjointness, and protected
suffixes are public under nested contracts. Raw missing-keyword failure stays
separate from selected ordinary rejection. Canonical real-type-child success
and return-list failure retain both checked-name events, complete states, and
following tokens; missing keywords and absent returns preserve their exact
component states. Reusable checked-type singleton-list helpers supply these
concrete executions without general recursive diagnostic-trace assumptions.

Every successful recursive type parse now unconditionally preserves its full
source file and active window, both at arbitrary explicit fuel and at the
actual production bound. This composes the six raw type frames without
`ValidFor`, carrier-validity, or diagnostic-silence assumptions. Consumers combine
the frame with existing token preservation and execute a deliberately invalid
carrier/window fixture. The frame is not a general recursive trace correspondence;
prioritized trace dispatch and recursive success/rejection composition remain
separate obligations.

One prioritized type-dispatch trace layer now composes all six raw forms and
the final expected-type rejection. Independent selection records every earlier
absence and the exact positive marker or two-token contextual prefix. Raw
prefix failures cannot masquerade as selected failures; named ordinary erasure
receives the comptime/mapping exclusions. Joint uniqueness/disjointness,
carrier-preserving erasure, and protected suffixes are public. Actual positive
fuel has five compositional contracts and success/rejection/full-failure
equivalences under the preceding parser's trace contracts; its source/window
frame is supplied unconditionally. Consumers distinguish keyword tokens from
same-spelling identifiers, bare/mismatched contextual names from special forms,
and hidden backing-array tokens from visible window tokens. Final failure keeps
the whole state and reports the active-window EOF span without emitting an
event. This is one-layer correspondence, not general recursive production
trace completion or an assertion that every input has an ordinary outcome.

Child-relation implication now lifts through trailing lists, all raw type
forms, and the prioritized dispatcher. These monotonicity laws preserve every
indexed AST, token carrier, window, cursor, diagnostic event, and failure report;
they neither add outcomes nor reorder or deduplicate events. Public consumers
forget auxiliary child protection annotations while retaining exact events and
protected normalization. This is infrastructure for recursive trace proofs,
not a recursive completeness or outcome-existence result.

A generic bridge now derives trace completeness from both execution soundness
laws, independent uniqueness/disjointness, and explicit exclusion of invariant
failure. Pointwise and unrestricted versions impose no hidden state-validity or
frame premise. The actual checked-name leaf consumes all four bridges with
arbitrary prior diagnostics. Formal countermodels show why soundness plus joint
exactness cannot replace invariant exclusion, and why even both completeness
contracts can be vacuous rather than assert an ordinary outcome's existence.

General recursive type execution now has unconditional success and rejection
trace soundness, both at explicit resource bounds and at the production parser.
The independent specification is the least closed relation of the selected
type layer, with simultaneous success/rejection queries and exact roll/unroll
and induction laws. It contains no executable parser or resource parameter.
Successful traces erase to ordinary types and preserve the token carrier and
active end index. Both outcomes preserve protected, ordered, duplicate-retaining
events after arbitrary earlier diagnostics; the final rejection report remains
separate. Public consumers use these recursive contracts without child premises
or state validity. Soundness alone does not imply completeness or ordinary
outcome existence.

Canonical public-parser consumers now cover the three-level nested success
`@comptime<a-b> tail` and missing-closing rejection `@comptime<a-b +> tail`.
Constructive component execution and recursive soundness retain the exact
single hyphen event after arbitrary prior diagnostics, complete AST spans and
states, active windows, and untouched following tokens. Rejection reports only
the missing greater symbol and does not commit that report as an event.

Independent recursive type outcomes now have unconditional AST/remainder/event
uniqueness, rejection remainder/report/event uniqueness, and success/rejection
disjointness. A pairwise agreement contract compares distinct child relations
through trailing lists, all raw forms, and the selected dispatcher. Simultaneous
strong induction compares an annotated left derivation with an arbitrary right
derivation, without assuming recursive uniqueness as a premise. Actual-reply
consumers fix every independently claimed event and rule out an opposite
outcome. Pointwise reverse correspondence isolates invariant exclusion as an
explicit premise; the joint specification itself still asserts only uniqueness
and disjointness.

That execution premise is now discharged on arbitrary states. A minimal child
resource contract requires only ordinary execution below its bound, successful
end-index preservation, and strict cursor progress. Actual opening/comma tokens
pay for decreasing bounds before nested execution, so no source, token-carrier,
diagnostic, rejected-state, or global-validity premise is needed. The generic
list loops and all raw type forms compose into unrestricted production totality.
Recursive types consequently have all five diagnostic-trace contracts and
success/rejection/full-Failure equivalences with arbitrary prior diagnostics,
including noncanonical token windows. This is complete type-trace correspondence,
not general expression, statement, or whole-file diagnostic-trace completion.

Separate execution-derived existence theorems provide an actual traced ordinary
reply for every State and a success or rejection derivation for every independent
remainder/source/endByte. They use unrestricted totality plus soundness, not
joint exactness. Reverse-correspondence consumers include foreign reversed token
spans, empty source text, oversized windows, missing backing tokens, and cursors
past the active window, while retaining arbitrary prior events and full
State/Failure results. A synthetic-child list consumer independently verifies
the minimal resource contract: changing source, tokens, endByte, and diagnostics
and overshooting endIndex still permits ordinary execution. That synthetic
contract is not a diagnostic-preservation contract.

Recursive type trace equivalences now reconstruct the complete success and
rejection State. Source preservation is proved separately for primitives,
delimiter loops, raw types, and all recursive bounds without input validity.
Reconstruction retains the independent remainder's tokens, endIndex, and cursor,
the original source/endByte, and exactly the appended diagnostic suffix.
Nested reverse consumers retain full Failure values and following tokens;
separate counterexamples rule out forgetting tokens or endIndex in cursor-only
state updates.

Raw proxy expressions and optional lambda return annotations now instantiate
the concrete unrestricted type contracts. Their five execution contracts,
success/rejection/full-Failure equivalences, independent joint exactness, and
protected suffixes no longer require caller-supplied child contracts. Consumers
start from independent type derivations and preserve arbitrary earlier events.
These are two type-bearing components, not complete expression or lambda traces.

Typed and error parameter finishers now have independent event judgments with
existence, uniqueness, and cascade protection. Exact execution fixes their full
AST and State: only an outer comptime type adds its type-span constraint;
proxy-of-comptime remains silent. Finishing never replays earlier name/type
events, and duplicate constraints retain their order. Both missing-type error
constraints retain their specified spans. These are finishing-only components;
full parameter composition remains separate from these finishing leaves.

Named-parameter tails now compose those finishers with the actual recursive
type parser. Independent success and rejection judgments have unique, disjoint
outcomes and protected events. All five execution contracts, whole-State and
full-Failure equivalences, and ordinary execution hold on arbitrary inputs.
An absent colon produces an error-valued success without advancing; a present
colon runs the type before finishing, and a type rejection skips finishing.
Constructive reverse consumers retain nested comptime/name events in order,
duplicate earlier constraints, exact spans and windows, and untouched following
tokens. Terminal type-failure reports remain uncommitted. This is the raw tail,
not itself selected parameter-core or public recovery trace completion.

Ordinary parameter-name checking now has an independent finishing trace and
a checked-prefix composition that retains identifier-before-warning order.
Whole-Reply continuation laws preserve all earlier events without replay or
deduplication. The same exact contextual-name pair guard is reflected for both
function and lambda cores, including active-window limits and missing backing
tokens. Separate source laws cover all raw function/lambda parameter helpers
and cores, not public recovery. Consumers verify window-dependent selection,
duplicate warnings, and the absence of an ordinary-name warning after a
selected comptime marker. Guard reflection remains separate from a full core
trace contract.

Both raw named-parameter paths now have unconditional five trace contracts,
independent exactness/protection, ordinary execution, and complete State/Failure
equivalences. Ordinary names run their spelling check before the tail, while
names after a comptime marker receive identifier checking only. Every raw
first-failure stage is represented. Reverse consumers distinguish the raw paths
on the same input and retain name-before-type-before-finishing events.

The selected non-recovering function-parameter core now has the same complete
trace correspondence on arbitrary states. Explicit pair guards exclude the
raw comptime marker/name failures when that branch is selected. Independent
joint exactness is distinct from execution-derived outcome existence, which is
also provided for every State and independent remainder. Consumers reconstruct
whole replies, preserve arbitrary earlier events through lexical filtering,
and verify that diagnosed ordinary success wins over a bypassed raw failure.
Public named-parameter and lambda-parameter rewind/recovery are composed below;
whole-file traces remain a separate obligation.

Lambda-parameter tails now have unconditional five trace contracts and exact
whole-State/full-Failure correspondence. Typed paths preserve the named-tail
trace while retagging its complete AST. Missing colons infer ordinary names
silently but produce a covered missing-type error for comptime names. Reverse
consumers preserve earlier duplicates and forward child rejection unchanged;
these are tail contracts, not full lambda-parameter or expression completion.

Standalone function-parameter recovery now has unconditional exact traces and
whole-State/full-Failure equivalences. It consumes a mandatory first token before
checking later comma/right-paren stops. Missing backing ends an established scan
but rejects an initial recovery attempt, even inside the numeric window. Only
one recovery event is appended; an earlier committed report is not re-emitted.
Recovery events are lexical-cascade candidates, with separate explicit keep/drop
conditions, not unconditional protected events. Public named rewind composition
is covered separately below.

The public named-parameter parser now has unconditional five trace contracts,
complete State/Failure equivalences, and separate execution-derived outcome
existence on every State and independent remainder. Its independent judgment
preserves the failed carrier and end index while rewinding only the cursor.
Boundary rejection commits no terminal report; otherwise the original report is
committed once before recovery. A recovery rejection retains its distinct,
uncommitted terminal report even when its payload equals the committed original.
Reverse consumers check cursor rewind, unchanged prior duplicates, no repeated
identifier checks while skipping, and protected name events through conditional
filtering of the committed report and recovery event. This completes the public
named-parameter slice, not general expressions or file traces; lambda parameters
are handled separately below.

Both raw lambda-parameter paths and their selected non-recovering core now have
unconditional five trace contracts and exact whole-State/Failure equivalences.
Explicit pair guards select ordinary inference, typed parameters, or marked
missing-type error success without admitting bypassed raw failures. The core has
separate actual and independent outcome existence on arbitrary inputs. Reverse
consumers reconstruct nested name/type/finishing events, silence after a second
comptime name, exact missing-type covers, and full child failure; arbitrary
earlier events and protected core suffixes are retained. Public lambda rewind
and recovery are handled below; lambda expressions remain a separate composition.

Standalone lambda recovery now inherits exact function-recovery traces, changing
only the recovered error AST's carrier. It has unconditional five contracts,
whole-State/Failure equivalences, independent joint exactness, and conditional
recovery-event filtering. Reverse consumers reuse the function fixtures for
mandatory consumption, later delimiter stops, missing backing, and prior reports.

The public lambda-parameter parser now also has unconditional five contracts,
exact whole-State/Failure equivalences, and separate actual/independent trace
existence. Its cursor-only rewind, boundary report policy, and one original-report
commitment match the independent specification without validity assumptions.
Reverse consumers preserve prior duplicates and mixed diagnostic filtering;
ordinary inference and marked missing-type error success explicitly bypass
recovery. Both public parameter slices are complete at this trace boundary.
Parameter lists are composed below; lambda expressions, general recursive
expressions, and whole-file traces remain separate obligations.

The actual function-parameter list and inline lambda-parameter list now have
unconditional five trace contracts, complete State/Failure equivalences, and
independent joint exactness. Production totality uses the public parameter's
strict progress and successful end-index frame, with no validity requirement;
separate totality and soundness prove trace existence for every State and
independent remainder. Both lists allow empty input lists and a trailing comma,
and retain all child recovery events. The lambda law targets the existing inline
parser rather than adding a new runtime helper. These list results do not assert
unconditional cascade protection, signature traces, or complete lambda expressions.

Independent reverse consumers now cover both actual lists on shared token
carriers: empty, single and optional-trailing-comma success, comma-first
`[comma, rightParen]` delimiter failure, first-child boundary rejection, and
recovered children with arbitrary duplicate prior diagnostics. The same untyped
name is erroneous for a function but inferred for a lambda; the exact AST,
remaining semicolon, complete Failure, and ordered event suffix are checked.
Separate consumers retain outcome existence on a numerically invalid window.

Raw lambda-expression traces now compose the concrete recovering parameter list,
optional recursive return type, and an explicitly supplied body relation. The
five contracts require only the corresponding body contracts; success and reject
soundness/completeness do not require a body frame. Whole-State equivalences state
successful or rejected body file/window preservation separately. Independent
joint exactness requires the body's joint specification, while separate trace
existence uses body ordinary execution and its two soundness laws, not completeness
or joint exactness. All four first failures preserve complete terminal reports,
and pointwise laws show early failures bypass any body parser. Parameter and body
events are filtered explicitly around the protected return-type events. This is
a raw, body-conditional composition, not a complete recursive expression parser
or an atom-dispatch result. Concrete `lam(+) -> a-b {}` consumers retain parameter
recovery reports/events before the return-name warning and supplied body events,
including arbitrary prior diagnostics and complete body Failure/State forwarding.
Marker, hidden list-opening, and return-type failures bypass any body parser;
mixed filters explicitly suppress recovery events while retaining the return
warning. A real empty Core block bypasses any supplied statement parser and
leaves the following semicolon unread; general nonempty body behavior stays
explicitly conditional.

Expression-atom lookahead now has a separate independent eight-way selection
judgment, including the final fallback. Every later branch retains all earlier
failed guards. Selection exists uniquely on arbitrary token remainders, and
equal current-token observations suffice even across different carriers and
cursor positions. The actual core has exactly the selected raw parser's whole
Reply with no recursive-child contract. Concrete consumers cover all branches,
Boolean keywords versus identifiers, hidden/missing backing, invalid windows,
unselected child independence, and the final uncommitted expression report.
These are dispatch-selection laws, not recursive trace outcome existence.

One selected atom-core layer now has independent success/rejection traces and
all five execution contracts over explicit nested-expression and body relations.
Literal/name leaves, proxy types, lambda parameters, and return types use their
concrete contracts. Nested collection traces require successful child file/window
frames; a final lambda body needs only its corresponding soundness/completeness
law. No rejection frame, progress, validity, or ordinary premise is needed for
these four trace laws. Suffix and full-Failure equivalences retain all ordered
events; successful whole-State reconstruction adds the body success context,
while rejected reconstruction states only a core file/end-byte frame and permits
the returned token carrier/endIndex to differ. Independent exactness assumes
nested/body joint exactness. Neither these contracts nor uniqueness establishes
recursive production totality or trace outcome existence.

Separate raw-collection, lambda, and selected-core rejection context laws now
preserve the file and an explicitly chosen window observation. The whole-window
and end-byte-only specializations require corresponding rejected-child frames
and the nested expression's success context, but no body success, token-carrier,
progress, validity, or ordinary contract. The weaker law permits rejected children
to change both token arrays and end indices without preventing exact State
reconstruction or later cursor-only rewind.

Standalone expression-atom recovery now has unconditional five trace contracts,
independent joint exactness, source/full-window frames, and complete State/Failure
equivalences. It consumes a mandatory first token, follows the existing boundary
scan, and emits exactly one recovered-expression event at the error AST's span.
An unavailable initial token rejects without committing its report; missing
backing after consumption terminates the scan successfully. Recovery-event
filtering is explicitly conditional. Caller report commitment and the public
atom's rewind/recovery composition are covered separately below under explicit
core contracts.

Independent recovery consumers now reconstruct exact replies for initial
semicolon/else consumption, subsequent else/semicolon stopping, skipped
hyphenated identifiers without replayed checks, initial missing-backing rejection
versus established-scan success, and hidden first/following tokens. They retain
arbitrary prior and duplicate events, leave the stopping token unread, and show
both concrete lexical-filter retention and removal of the recovery event.

The public atom wrapper now has independent core-or-recovered success and
boundary-or-recovery rejection traces over explicit core relations. Runtime
soundness/completeness and complete State/Failure equivalences require the
matching core contracts and rejected file/end-byte frame, not unchanged token
arrays or end indices. Successful State reconstruction additionally uses the
core's successful file/end-byte frame. Only the cursor is rewound; the original
report is committed exactly once on the non-boundary path, and the recovery
terminal report remains separate. Full-window context is a stronger, separately
stated law. Independent joint exactness is conditional on core exactness;
non-vacuous State/remainder outcome existence separately requires core ordinary
execution and soundness. This is a conditional wrapper, not general expression
or file trace completion.

A concrete stationary-child counterexample now verifies the limit of the trace
contracts: both children have all five contracts, ordinary execution, and exact
joint specifications, yet the selected parenthesized atom reports a `noProgress`
invariant. Completeness together with that exact execution rules out both
independent trace outcomes for this input. Neither child ordinary execution nor
joint uniqueness substitutes for the strict progress needed by collections.

The selected core and public wrapper are now instantiated as one independent
atom-layer trace relation over only nested-expression and block relations. Four
trace laws use the corresponding child contracts and weak rejected file/end-byte
frames; the separate full-window success context states stronger rejected-child
frames explicitly. Raw groups/tuples, dot arguments/constructors, arrays, selected
core, and public recovery additionally have ordinary execution on arbitrary States
under an explicit remaining-count bound and a three-field nested contract:
successful endIndex preservation, strict cursor progress, and bounded ordinary
execution. The body needs only ordinary execution for this totality result.
It does not require child validity, token/source/end-byte preservation, or any
rejected-state frame. Combining totality with soundness separately establishes
actual core/public traced outcomes and independent public outcomes under the
same bound; this is not a completed general recursive expression parser.

A changed-carrier reverse consumer now exercises a rejected child that replaces
both the tokens and endIndex. The original opening parenthesis is not a boundary,
but the failed carrier's leading semicolon is a boundary after cursor-only rewind.
Exact core and public State/Failure equivalences retain that carrier, the child
event, and arbitrary duplicate prior events without committing the terminal report.

Concrete public-atom reverse consumers use the real literal leaf as the nested
parser. In `.a-b(+) ;`, the checked-name event precedes the exact literal failure;
rewind/recovery then commits that report once and stops before the right parenthesis,
without replaying the skipped name warning. Full State/Failure checks also cover
name-success bypass, immediate boundary rejection, and missing backing where the
core and recovery reports have equal payloads but only the original is committed.
Mixed lexical filtering drops the committed report/recovery event while retaining
the protected name warning and arbitrary prior duplicates remain intact.

Literal-child totality consumers now instantiate the three-field contract at
every child budget. They cover overshot cursors, stored-but-hidden tokens, missing
backing storage, exact end-byte failures, and the single report commitment at a
numerical gap. Independent group/tuple derivations reconstruct full successful
States even when source/window validity fails. These are one-layer consumers;
the displayed loop and child bounds remain explicit.

Maximal postfix tails now have independent success/rejection traces for index,
call, and checked-identifier field suffixes, retaining branch priority, exact
AST spans, ordered child/name events, and all seven first-failure positions.
Nested joint exactness supplies result uniqueness and disjointness, not existence.
Both runtime soundness directions hold at every tail fuel under nested trace
soundness and successful source/full-window context. They add no child progress,
validity, ordinary-execution, or rejected-state frame premise. Index traces do
not inherit the call-argument list's strict-progress check.

Each finite postfix derivation now executes at every fuel above its own threshold
under child completeness and successful context; rewinding index children remain
allowed, so that threshold is not identified with remainingCount. Separately,
the minimal child endIndex/progress/bounded-ordinary contract and explicit loop
and child budgets establish unrestricted ordinary execution, including the
production tail budget. Soundness then supplies actual and independent trace
existence without joint-exactness premises. Joint exactness plus this invariant
exclusion supplies fixed-fuel completeness. Pointwise success and rejection
equivalences reconstruct every State/Failure field; only rejection reconstruction
needs the explicit weak child file/endByte frame. All-fuel context laws preserve
full successful windows or a caller-selected rejected window observation. These
remain tail-layer results, not complete recursive expression traces.

Concrete progress-boundary consumers now show why these distinctions matter.
A stationary child has an independent successful index trace, while a call
with the same child reaches noProgress and has no independent success. A child
that rewinds and replaces tokens still satisfies all five trace contracts,
full-window context, and ordinary execution. Its finite two-index derivation
executes at fuel three, yet the initial production budget of two is exhausted.
Both independent derivations feed reverse completeness; arbitrary incoming
diagnostic multiplicity and the exact final carrier are retained.

Literal-child reverse consumers additionally derive `.a-b[1](2)` from independent
name/index/argument judgments and reconstruct the fully located nested AST and
entire output State. A later dot followed by semicolon or `true` retains the prior
name event but does not commit the terminal identifier report: field names use
checked identifiers, not Boolean expression names. Duplicate prior events, unread
boundary tokens, hidden dots, and missing backing slots are checked separately.

The actual atom-plus-maximal-postfix parser now composes independent atom and
nested relations with exact atom-before-tail event order. Atom/nested joint laws
give independent uniqueness/disjointness; observed success/rejection soundness
uses their explicit trace and successful context contracts. Pointwise invariant
exclusion yields both completeness directions and complete State/Failure iff
laws, with weak rejected file/endByte frames only when reconstructing rejection
States. Separate numerical totality accepts an ordinary atom outcome and a bound
at each successful atom endpoint; a stronger form takes independently supplied
atom/nested progress contracts and two input bounds. Soundness plus that totality
gives actual and independent traced outcome existence without joint assumptions.
The atom progress contract is still a premise here, not a result of child trace
contracts or a claim of recursive expression closure.

One concrete selected-core/recovery/postfix trace layer now leaves only nested
expression and body relations supplied. Its soundness uses explicit successful
and rejected full-window contexts to frame recovered atom successes; the layer
joint bundle remains uniqueness/disjointness only. Separately, raw lambda,
selected-core, and public-atom ordinary execution now accept bounded body
contracts instead of global body totality, under two explicit remaining-count
bounds. The real lam marker pays one body-budget unit before concrete parameters
and return annotations. This ordinary law still permits replacement rejected
windows and does not establish the atom's success endIndex/progress contract.

Numeric-only frames now compose through delimiter loops, raw collections,
selected atoms, and public recovery. They preserve only endIndex on both ordinary
outcomes and leave invariant replies unconstrained; source, tokens, endByte,
diagnostics, progress, and validity are not part of this frame. Combined with
the bounded child contracts and existing cursor-progress laws, rejected-child
endIndex preservation constructs an actual public-atom contract at any budget
A with A ≤ N+1 and A ≤ B+1, including the equal-budget successor step.
A reverse consumer demonstrates why the rejected endpoint premises are needed:
two always-rejecting children satisfy every three-field fuel contract, but one
changes endIndex from three to four and public recovery succeeds with that
changed endpoint. Independent core/recovery traces reconstruct the exact State
and ordered report/recovery events for arbitrary content and prior diagnostics.
This supplies a conditional atom-layer contract, not recursive expression closure.

The actual postfix contract now constructs that intermediate atom contract
internally. Numeric-only frames lift through every suffix and both ordinary
outcomes; nested/body fuel contracts and rejected endpoint preservation give
ordinary execution and the next postfix-layer contract without an abstract atom
premise. Success endpoint/progress laws hold on all States, while ordinary
execution retains the explicit two-budget bound. Combining this result with
the concrete layer soundness and explicit full-window child contexts supplies
actual and independent postfix-layer trace existence using only child premises.
No independent joint law or completeness assumption replaces totality.

Prefix unary diagnostic traces now reuse the exact maximal source-order operator
grammar and preserve the entire postfix event suffix and terminal report. The
scanner is silent at every successful fuel/accumulator and never rejects; its
production scan has unconditional full-State correspondence and separate actual
and independent successful existence on arbitrary numerical carriers. Each of
the four postfix trace directions lifts independently through the unary layer,
without child framing, progress, joint exactness, or totality assumptions.
Successful full-window context is separate; complete success/rejection State iff
laws need only the corresponding postfix file/endByte frame. Independent unary
joint exactness remains conditional on postfix joint exactness and does not give
complete-expression outcome existence.

Unary numeric endpoint and strict-progress laws now lift the actual postfix
contract at the same fuel: an empty unary prefix cannot pay an extra unit.
Bounded ordinary execution and no-invariant laws need no source/token/endByte
or validity frame; constructed nested/body postfix contracts also lift to unary.
Combining ordinary execution with the two corresponding postfix soundness laws
separately gives actual and independent bounded unary trace existence, without
joint exactness or completeness premises.

Concrete reverse consumers use a real literal child and an explicit rejecting
body. Independent traces for `!~a-b(1).c` fix bang outside tilde outside the complete
postfix AST, all spans, the full State, a single name event, and arbitrary prior
duplicates. Later field rejection preserves the earlier name event but does not
commit its terminal report. Independent scanner-absence judgments also verify
that minus is not a canonical unary operator and hidden/missing prefixes remain
silent. These are one-layer consumers, not recursive block/expression closure.

An empty token carrier has its own complete normal-output contract: retained
comments and lexical diagnostics, no AST items, and no parser diagnostics.
Validation alone suffices at the token boundary; canonical lexing supplies it
for empty, whitespace-only, comment-only, and lexically diagnosed tokenless
source. Separate compositional laws distinguish ordinary sequencing, which
retains both executed diagnostic suffixes, from transactional choice, which
retries the right alternative on the original state and discards the rejected
left alternative's diagnostics. Those laws explicitly assume branch execution
and are not presented as independent grammar judgments.

At the complete diagnostic-free declaration level, strict soundness now covers
all four canonical import forms—plain, namespace, wildcard with or without a
hiding clause, and selective imports—transparent type aliases, and traits.
Unconditional strict soundness also covers all four canonical export forms:
local, module, module alias, and items-from-module, together with complete
algebraic enums. Parser-independent `ImportDeclParses` and `ExportDeclParses`
judgments combine their respective forms without caller-supplied AST shape
guards. `EnumDeclParses` directly characterizes complete enum success while
retaining the supplied derive attribute. Export and enum soundness need no
diagnostic-free premise. These declaration judgments now feed the exact
`PlainTopItemParses` and derive-aware `TopItemParses` correspondences. The
complete file-loop and `sourceFile` theorems preserve forward item order,
strict cursor progress, end-of-window termination, exact comment attachment,
and recovery exclusion by diagnostic commitment. The generic theorem remains
reusable with abstract expression and block relations, and its concrete Core
ordinary specialization is now public and compile-time consumed. Recovered
malformed output remains separate so that recovery is not confused with
language acceptance.

Full source resolution, source type checking, and elaboration into checked
Semantic Core remain separate later stages. Canonical local references, Boolean
operators, Word addition/subtraction/multiplication/unsigned division/remainder,
bitwise operations, unsigned `>`/`<`/`<=`/`>=` and Word equality/inequality, strict
Word literals, and conditionals connect through the explicit-table adapters above.
No new frontend result is published through Oracle
v4; that interface continues to mean only its frozen Surface v1 format.

## What is not yet claimed

The current public system is not yet an end-to-end implementation for arbitrary
Solcore source text. In particular, it does not yet provide:

- source resolution, typing, elaboration, and execution as one pipeline;
- unbounded recursive contract-call depth;
- a general dynamic ABI, memory model, or bytecode interpreter;
- Ethereum gas, fees, block context, address derivation, or full EVM equivalence;
- generation beyond the current pure Word/Boolean Core subset, including
  functions, data, cells, and host effects; or
- an automated semantic differential-testing harness against other Solcore
  implementations.

The intended longer-term direction remains aligned with those last two items:
expand generation to more well-typed programs, run the same programs through
independent implementations, and compare normalized semantic observations.
Oracle v5 is
the execution and observation boundary needed for that work, not the completed
differential-testing system itself.

## Validation boundary

The repository checks different kinds of claims at different layers:

- Lean types prevent incompatible checked-program and response combinations;
- proofs connect evaluator, state, checkpoint, and rollback operations to laws;
- general materialization theorems prove exact pointwise lookup, absence,
  balance, nonce, storage, code, registry, template, route, and default-address
  behavior for every successfully accepted finite world and environment;
- executable tests cover checking, admission, materialization, fuel boundaries,
  return, revert, trap, nested calls, balances, creation, logs, and encoding;
- a public-handler regression repeats the same execution request with the same
  fuel and checks identical typed, canonical JSON, and canonical text results;
- the synthesis regressions check all tracked constructors and operators,
  exact corpus replay, normal public execution, and type-preserving strict
  shrinking;
- strict wire tests fix canonical JSON shapes and deterministic error priority;
- metadata validation checks published profiles, digests, and capability output;
  and
- the kernel audit checks the compiled declaration trust boundary.

These checks establish the behavior of the formal model that is present. They
do not establish source-language conformance for features that have no current
frontend-to-Core path, nor do they establish equivalence with the EVM or either
external Solcore compiler.

From the repository root, the full local validation entry points are:

```text
lake build
lake test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
```

For protocol-level details, use the wire catalogs rather than internal Lean
module names. For supported-feature comparisons and external implementation
boundaries, see the [compatibility matrix](COMPATIBILITY_MATRIX.md).
