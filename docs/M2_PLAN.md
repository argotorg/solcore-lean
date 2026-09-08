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
eight-form predicate is closed under weakening and includes every currently
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
eight-form local predicate. Raw skipped-child success does not excuse whole
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
not recursive unions; both shapes now connect to whole entries through ADR-0198.

The body identity/store layer (ADR-0197) now gives injective exact-elaboration
transport and unconditional optional checker/full same-fuel runner equality for
single, conditional and terminal profiles. Raw/cost replay keeps value and cost
at arbitrary stores; completed observations and exhaustion presence retain each
store rather than equating entire results. Existing singleton map/replay laws
move unchanged out of runtime-owner/store modules into acyclic body-only modules,
with old-import availability retained. Noninjective lookup counterexamples remain
explicit. This layer itself does not change entries, input-shadowing policy or
accepted syntax; its acyclic imports allow the entry integration below.

The explicit runtime entry (ADR-0170) now connects a restricted header's return
contract, typed parameter binding, and exact body elaboration. Independent
preparation characterizes success/failure and fixes the actual Core, while
whole-entry typing and source cost characterize checked execution at each fuel.
Absent returns mean Unit; one explicit named type is supported, but empty or
multiple return lists, generics, where clauses, and modifiers stay outside this
profile. Actual complete declarations exercise this boundary. Neither hand-built
prepared records nor arbitrary source functions receive unconditional safety.

Terminal entry integration (ADR-0198) connects the existing compiler/preparer to
the common body checker and their independent provenance, typing and cost to
the terminal judgments. Original singleton Core/value/store/cost behavior is
retained. Valid explicit terminal if/else entries now compile and run using
actual ordered arguments, with the same factorization, owner/store invariance,
safe compiled execution and genuine-state resumption. The three entry-bound
theorems explicitly migrate to `terminalReturnBodyFuelBound`; the unchanged old
singleton bound cannot justify execution of conditionals. Both written arms are
checked. Headers, parameter policy, nested/extra-statement rejection and the
absence of general source-call/early-return semantics remain unchanged.

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
