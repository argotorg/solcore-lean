# Feature matrix

This is the human-readable implementation ledger. It does not enable a profile
or alter a published protocol.

Status meanings:

- complete: executable behavior and the required proof boundary exist;
- active: implementation is currently being developed;
- planned: the feature has an implementation order but no complete code;
- blocked: a semantic decision or prerequisite is missing;
- frozen: retained at a versioned boundary with no active expansion;
- unsupported: the selected public profile deliberately has no meaning for it.

## Published and stable features

| Feature | Specification | Implementation and proof | Published | Syntax coupling |
| --- | --- | --- | --- | --- |
| Version and profile separation | Normative | Complete | Oracle v1 and later | None |
| Verdict categories | Normative | Complete | Oracle v1 and later | None |
| Core unit, bool, word | Normative | Complete | Oracle v2/v3/v5 | None |
| Immutable Core binding | Normative | Complete | Oracle v2/v3/v5 | None |
| Core conditional | Normative | Complete | Oracle v2/v3/v5 | None |
| M1c primitive subset | Normative | Complete | Oracle v3/v5 | None |
| Core v3 extended algebra | Normative | Complete | Core Wire v3 / Oracle v5 | None |
| Checked-contract execution | Normative | Complete | Oracle v5 | None |
| Canonical execution observations | Normative | Complete | Oracle v5 | None |
| Static Word ABI profile | Normative | Complete | Oracle v5 `staticWordAbiV1` | None |
| Surface v1 parser | Normative | Complete | Oracle v4 | High; frozen |

The M1c primitive subset contains boolean and word negation, modular word
addition/subtraction/multiplication, total unsigned division/modulo, word
equality and greater-than, bitwise operations, and bounded logical shifts.

## Canonical source frontend

This is the active source-language replacement selected by ADR-0153. It is not
published through Oracle v4.

| Feature | Status | Missing work | Syntax coupling |
| --- | --- | --- | --- |
| Source identity and UTF-8 byte spans | Complete executable and proof boundary; every public output retains one source owner, full-file provenance, and valid token, comment, AST, and diagnostic spans | Workspace admission belongs to the later resolution stage | High |
| Already-tokenized parser preflight | Complete exact independent outcome; total and functional first-failure scans enforce source, token, comment, and lexical-diagnostic priority with exact index/span payloads, executable correspondence, and complete `parseLexed` error classification | This validates retained provenance and source order, not that arbitrary supplied token payloads were produced by the canonical lexer | High |
| Token and parsed AST catalog | Complete executable representation | Contextual well-formedness layer | High |
| Unicode identifier classification | Complete | None at the executable syntax boundary | High |
| Canonical lexer | Complete executable and proof boundary; every source returns a full valid lexical carrier and the exceptional fuel branch is unreachable | None at the current lexical contract | High |
| Canonical parser | Complete executable and total source-to-AST boundary; every source returns an ordinary output, arbitrary tokenized input has an exact validation-error or certified-success branch, diagnostic-free outputs derive `CoreSourceFileOrdinaryParsesFromStart`, and every successful `parseLexed` or `parse` output has an exact broad public AST branch with canonical validity; nesting-overflow `ParseOutput` is exact through its singleton diagnostic | General normal-branch diagnostic traces remain a separate declarative milestone; resolution, typing, and elaboration remain later stages | High |
| Lexer and parser foundation proofs | Complete for source provenance, parser-state preservation, progress, production-fuel adequacy, public totality, backward diagnostic reflection through declarations and the complete file loop, and concrete fuel-indexed public Core and Yul outcomes | None at the current foundation boundary | High |
| Ordinary syntax completeness | Complete public Core/Yul, declaration, derive, top-item/recovery, file-loop, and source-file AST correspondence; independent grammar success/rejection iff executable success/rejection with the same AST and declarative endpoint | Public token input requires validation; source input retains canonical lexical provenance. General normal diagnostic traces, strict diagnostic-free acceptance completeness, and independent lexer-payload characterization are not claimed | High |
| Declarative grammar and parser soundness | Active; complete for declarations and complete files, mutually recursive public Core expressions/patterns/statements/blocks, exact grouped-first predicate success and rejection outcomes, exact Yul blocks and statement forms, transactional rejection witnesses, concrete complete-file Core specialization, total exact nesting preflight, and broad public source-file AST outcomes | Full normal-branch diagnostic traces and contextual well-formedness remain separate later boundaries | High |
| Declaration, type, and Yul parser proofs | Complete source/state, totality, and concrete clean/ordinary/reject soundness boundaries for recursive types and every public Yul expression, statement, and braced body parser, including the assignment fallback | None at this boundary | High |
| Core expression parser proofs | Complete source/state, totality, ordinary/reject soundness, diagnostic reflection, and unconditional AST/remainder/rejection-endpoint exactness at fixed-fuel and public boundaries across atoms, lambda, maximal postfix, unary, binary, conditional, and block interaction | Diagnostic traces, failure payloads, and whole-state equality are not claimed | High |
| Pattern and statement parser proofs | Complete executable contracts, ordinary/reject soundness, and unconditional AST/remainder/rejection-endpoint exactness for mutually recursive patterns and statements, including recovery and diagnosed successes in exact dispatcher order | Diagnostic traces, failure payloads, and whole-state equality are not claimed | High |
| Public Lean source interface | Complete | None; resolution, typing, and elaboration remain separate stages | High |
| Independent diagnostic traces | Complete raw traces for primitives, pragma success/rejection, and standalone top-item recovery; complete `ParseOutput` for empty tokens, one recovery-to-end, arbitrary successful pragma-only windows, and successful pragma prefixes ending in recognized pragma rejection | Other recognized-start failures and concrete nested/mixed arbitrary-declaration traces | High |
| Primitive traces and diagnostic normalization | Complete raw/checked identifier AST, remainder, and event suffix; exact silent keyword/symbol/contextual success and rejection reports; total unique mixed-report filtering with full metadata, protected kinds, and retained duplicate order | Composition across arbitrary declarations and nested blocks remains separate | High |
| Balanced block isolation traces | Complete compositional execution laws and conditional independent trace soundness/completeness/exactness; child context, parent frame, report commitment, and duplicate order are exact | Concrete inner Core block trace contracts remain separate | High |
| Core block closing traces | Complete independent tail-validation traces and exact brace-closing success/rejection correspondence; policy, full spans, ordered protected events, and failure reports are exact | Concrete statement-event traces remain separate | High |
| Raw and isolated Core block traces | Complete conditional success/rejection grammar, exactness, production execution correspondence, and diagnostic normalization under explicit statement contracts | Concrete general statement trace contracts and whole-file composition remain separate | High |
| Break/continue diagnostic traces | Unconditional independent leaf existence/exactness, complete success/rejection correspondence, and statement execution contracts; concrete raw/isolated restricted-block consumers | Other statement forms, mixed-statement dispatch, and whole-file traces remain separate | High |
| Return diagnostic traces | Conditional optional-value and return success/rejection correspondence, full reports, joint exactness, and separate outcome existence under expression laws; unconditional empty-return execution | Concrete general expression contracts, mixed-statement dispatch, and whole-file composition remain separate | High |
| Literal/Boolean diagnostic traces | Unconditional exact silent primitive traces and complete literal-expression contracts; independent existence/exactness closes literal-return instances | Other expression leaves/layers and mixed statement/file traces remain separate | High |
| Public source wire interface | Planned | New additive protocol after the frontend semantic stages are coherent | High |

Recursive type, type-alias, shared generic-parameter, and enum soundness are
exported by the public syntax umbrella and checked by compile-time consumers.
Required generic parameters are a nonempty `<...>` list with an optional
trailing comma; exact rejection retains either the delimiter or nested checked
identifier failure. `requireGenericParameters` contributes no rejection, only
an unreachable defensive empty-list invariant. For optional generics, an
absent `<` is a nonconsuming success, while a positive guard commits from the
original input and preserves its `<` evidence. Required and optional success
endpoints are deterministic and success/rejection exclusive. Enum constructor
payloads commit on a leading `(`; when present, they may contain zero fields
but cannot have a trailing comma. The custom enum-body loop has exact
allow-empty, allow-trailing success and rejection outcomes while preserving
forward constructor order. Full declarations distinguish contextual-marker,
name, optional-generic, and body rejection. Every constructor, body, and
declaration outcome has a deterministic success endpoint and disjoint
success/rejection. Stronger exact contracts unconditionally fix constructor
and body ASTs, final remainders, and rejection endpoints. Full enum declarations
have the same exact contract for each fixed supplied derive attribute; no
equality across different attributes is claimed. Supplied derive attributes
remain non-consuming AST inputs and determine the outer span start. These
registered theorem families are included in the successful full build and
`lake test`.

Generic delimited-list exactness transport covers all combinations of required
or allow-empty contents and trailing-comma permission. From an exact nested
outcome it fixes the forward element list, closing span, complete
`DelimitedList` AST, final remainder, and first rejecting remainder. All four
spec constructors are exported and compile-time consumed; the theorem remains
conditional on each concrete nested production's exact contract.

Generic transactional fallback has the corresponding exactness transport:
exact primary and fallback branches determine the successful value and final
remainder, while double rejection has the unique original-input endpoint.
Concrete uses supply both branch contracts.

Recursive Core `TypeExpr` outcomes now unconditionally fix the successful AST
and final remainder and every rejecting endpoint, at fixed fuel and at the
public boundary. Transparent type-alias parameters and malformed RHS recovery
have exact contracts, and the Core type result lifts through recovery-aware
alias values and the complete declaration. The resulting alias AST, remainder,
and all first-failure endpoints are unconditional and publicly consumed.

Backward diagnostic reflection composes through parser sequencing,
transactional choice, token consumers, and delimiters. Its concrete instances
cover recursive types, named and delimited function parameters, predicates,
bare/grouped predicate sequences, optional `where`, and the remaining
function-signature leaves. Parameter error and recovery success always commit
a diagnostic, so `FunctionParameterParses` and `FunctionParametersParses`
characterize diagnostic-free typed parameters without admitting recovery
nodes.

The single public `namedParameter` also has a broad ordinary-outcome relation.
A missing colon is a diagnosed `.error` Core success at the post-name
remainder, not recovery. Only a Core rejection rewinds to the original cursor:
end, comma, or right parenthesis gives exact nonconsuming rejection; otherwise
the parser emits the failure diagnostic and performs its mandatory-first-token
maximal recovery scan. A carrier hole is reflected as recovery rejection.
Success endpoints are deterministic and exclusive with rejection, while the
strict `FunctionParameterParses` relation remains diagnostic-free. Complete
recovery, ordinary and contextual parameter forms, and rejection endpoints now
also have an exact contract, instantiated by the Core `TypeExpr` exactness law.

The canonical `TypeExpr` and recovery-aware `namedParameter` outcomes now lift
to the `(` / `)` parameter list, with empty contents and a trailing comma
allowed. Delimiter and nested rejection endpoints are exact: recovery stops
leave an outer comma or right parenthesis unconsumed, a carrier hole remains a
nested rejection, and recovery to the window end may then yield exact
`delimiterMissing` rejection. Generic trailing-list exactness fixes the
complete broad parameter-list AST, final remainder, and delimiter or nested
rejection endpoint. These declarative and executable laws are public and
compile-time consumed; strict `FunctionParametersParses` remains the
diagnostic-free list relation.

Bare and grouped predicate sequences have unconditional soundness with exact
grouped-first priority, and optional `where` retains exact marker priority. A
bare `PredicateSequenceParses` derivation carries
`GroupedPredicateSequenceUnavailable`, obtained either from absence of its
opening token or from exact grouped rejection and `no_parse` before the
transactional fallback restarts at the original input. Bare-tail, bare-sequence,
and complete-dispatch rejection traces are also exact. A double rejection keeps
the grouped attempt's intermediate remainder distinct from the final bare
remainder returned after retrying from the original input; deterministic outcome
specifications exclude simultaneous success and rejection. An absent contextual
`where` marker is a nonconsuming success, while a present marker commits to the
prioritized predicate sequence. Executable ordinary rejection is reflected
exactly as that committed sequence rejection; optional-`where` success has a
deterministic remainder and is exclusive with rejection. Predicate ASTs,
grouped and bare sequences, grouped-first dispatch, and optional `where` now
also fix successful values/remainders and rejecting endpoints. Bare-tail
exactness explicitly shares the preceding span supplied by the complete list.

For optional `returns`, an absent contextual marker is likewise a nonconsuming
success, while a present marker commits to the allow-empty, allow-trailing
parenthesized `TypeExpr` list. Executable rejection reflects the exact nested
type or delimiter remainder. The success endpoint is deterministic and
success/rejection are exclusive. Core `TypeExpr` exactness now fixes the
optional return AST, final remainder, and committed rejection endpoint.

Function modifiers have unconditional fixed-order `public`-then-`payable`
grammar soundness. Diagnostic-free module success excludes both markers,
whereas contract policy permits every syntactically ordered pair. A complete
diagnostic-free function signature therefore derives the corresponding
module- or contract-indexed `FunctionSignatureParses` judgment, with exact
component order, remainders, AST fields, endpoint span, and source-validity
composition. The signature judgment ends before a function body or
trait-method semicolon. These parameter, predicate/`where`, modifier, and
function-signature theorem families are exported through `Solcore.Syntax` and
checked by compile-time consumers.

A broad ordinary `functionSignature` outcome is now independent of location
and modifier policy. Success preserves the exact keyword, name, generics,
recovery-aware parameters, modifiers, returns, and `where` order, complete AST,
signature cover span, and final remainder. Rejection records the first failing
keyword, name, generics, parameter-list, returns, or `where` stage. Modifiers
always succeed; module-location markers may instead emit diagnostics without
changing the declarative remainder. Success endpoints are deterministic and
exclusive with rejection, while `FunctionSignatureParses` remains the strict
diagnostic-free, location-policy judgment. The broad signature is now
unconditionally exact: every component AST and final remainder and every
first-failure endpoint is unique, with executable reflection.

Broad ordinary `functionDecl` outcomes are now location independent. Success
threads an ordinary signature into the isolated `.allow` Core body while
retaining the exact declaration AST, signature/body cover span, and final
remainder. Exact rejection exposes only two stages: signature rejection, or an
uncaptured body rejection after ordinary signature success. A rejection in a
balanced captured child is absorbed as diagnostic recovery and returns an
ordinary empty body at the exact parent remainder. Successful endpoints are
deterministic and exclude simultaneous rejection. The existing
location-policy-aware `FunctionDeclParses` relation continues to describe the
strict diagnostic-free declaration boundary. Exact signatures and isolated
`.allow` bodies now make full declaration exactness unconditional.

Broad ordinary `constructorDecl` outcomes now preserve the exact required
keyword, recovery-aware parameter list, fixed optional `public`-then-`payable`
order, and isolated `.require` body. An explicit `public` marker emits a
constraint diagnostic, is discarded from the AST, and leaves the declarative
remainder unchanged. Success retains the exact parameters, payable marker,
marker/body cover span, constructor AST, and final remainder. Rejection has
only three external stages: marker absence, parameter rejection, or uncaptured
body rejection after modifier success. A balanced captured child rejection is
absorbed as diagnosed empty-body recovery success at the parent remainder.
Endpoints are deterministic and success/rejection are exclusive. The strict
diagnostic-free `ConstructorDeclParses` judgment remains available alongside
this broader malformed-source outcome contract. Exact parameters, modifiers,
and isolated `.require` bodies now make complete constructor ASTs, final
remainders, and rejection endpoints unconditionally unique.

Broad ordinary `fallbackDecl` outcomes now retain the exact `fallback` keyword
and recovery-aware parameter list through a pure validation stage. Empty
parameters pass silently; nonempty parameters remain in the AST, emit their
constraint diagnostic, and leave the declarative remainder unchanged. The
fixed optional `public`-then-`payable` modifiers and isolated `.require` body
follow in exact order. Success preserves the fallback AST, marker/body cover
span, payable marker, and final remainder. Rejection exposes only marker
absence, parameter rejection, or uncaptured body rejection after validation
and modifier success. A balanced captured child rejection becomes diagnosed
empty-body recovery success at the parent remainder. Endpoints are deterministic
and success/rejection exclusive; strict diagnostic-free `FallbackDeclParses`
remains available as the canonical acceptance judgment. Exact parameters,
validation, modifiers, and isolated `.require` bodies now make complete fallback
exactness unconditional.

Broad ordinary contract-field outcomes preserve the exact checked name, colon,
Core type, prioritized optional `=` initializer expression, and semicolon order.
Success retains the exact field AST, name/semicolon cover span, and final
remainder. Rejection records exactly five first-failing stages: name rejection,
missing colon, type rejection, committed initializer-expression rejection after
the exact `=`, or missing semicolon. Success endpoints are deterministic and
success/rejection exclusive. The stronger exact field contract fixes the full
AST, final remainder, and rejection endpoint unconditionally through exact
public Core initializer expressions and recursive Core types. The
existing parametric `ContractFieldParses` relation remains available alongside
this broad outcome as the strict acceptance judgment.

Broad ordinary type-alias outcomes preserve optional allow-empty,
allow-trailing parenthesized parameters and the exact declaration order. A
Core RHS may succeed directly; otherwise a nonempty malformed RHS is recovered
as `.error` through the prefix before an unconsumed semicolon. An empty or
immediate-boundary RHS rejects. Rejection records exactly six first-failing
stages: missing `type`, rejected name, committed parameter-list rejection,
missing `=`, RHS rejection, or missing semicolon. Success retains the exact
alias AST, keyword/semicolon cover span, and final remainder; endpoints are
deterministic and success/rejection exclusive. The strict diagnostic-free
`TypeAliasDeclParses` relation remains available alongside this broad outcome.

Implementation broad outcomes now cover the infallible optional `default`
prefix, contextual marker, optional generics, trait name, required nonempty
trailing-comma head types, optional `where`, method loop, and complete
declaration. The body retains closing-brace priority, positive `function`
guards, strict progress, forward method order, and every rejecting remainder.
Full rejection has exactly marker, generics, name, head-argument, `where`, and
body stages after the default prefix. Default, head, method, body, and full
declaration successful remainders are deterministic and success/rejection
exclusive; module diagnostics and balanced-body recovery remain successful
outcomes.
The optional default marker and required head arguments have unconditional
exact contracts for their ASTs and final remainders, plus head rejection
endpoints; the default marker cannot reject. Unconditional isolated `.allow`
Core-body exactness now also fixes method, body, and complete declaration
ASTs and outcome endpoints without further assumptions.

Trait methods, brace-delimited method bodies, and complete trait declarations
now have exact broad success and rejection outcomes. Module-signature
diagnostics remain successful before the exact method semicolon. The custom
body loop retains closing-brace priority, positive `function` guards, strict
progress, forward method order, and every rejecting remainder. Declarations
separate marker, name, required-generic, optional-`where`, and body rejection.
Each level has deterministic success endpoints and disjoint success/rejection.
Exact signatures now also make each level unconditionally fix its complete
AST, final remainder, and rejection endpoint, including forward method order
and retained spans. The strict diagnostic-free and source-validity families
remain available. These stronger laws do not equate diagnostic traces, failure
payloads, or whole parser states.

Import leaf outcomes now preserve selector, alias, and module-path priorities.
Without `(`, a selector is a checked identifier; with it, parsing commits to a
nonempty maximal operator-symbol scan and exact close, separating identifier,
empty-operator, and missing-close rejection. No `as` gives a nonconsuming
`none`, while a positive guard commits to one identifier. No `@` selects a
local qualified name, while positive `@` commits to an external name. Each
endpoint is deterministic and success/rejection are exclusive; complete import
declarations still retain their existing strict diagnostic-free judgments.
Unconditional exactness now fixes full ASTs, final remainders, and rejecting
endpoints across every import leaf, list, payload form, and complete declaration.
Outer start and preceding spans are shared explicitly where required. Maximal
selectors, module/export paths, and both terminators have exact public APIs and
independent grammar-result consumers.

Exact broad export outcomes now cover maximal dotted export paths, constructor
selection, prioritized export names, local items, wildcard or braced remote
selection, both payload forms, and complete `exportDecl`. Constructor
selection chooses `(*)` before a nonempty no-trailing-comma name list; export
names choose `*`, parenthesized operator, then checked identifier with optional
constructors. Identifier-plus-offset-one-dot lookahead alone commits a local
item to qualified `path.*`; otherwise it remains an export name. Braced remote
selections and local-item lists allow empty content and a trailing comma.

Local exports end their list with an exact nonrecovering semicolon. Path
exports prioritize dot-selection, absent-dot `as` alias, then bare module, and
use the same terminator. The aggregate consumes exact `export` and dispatches
on a nonconsuming `{` guard while retaining exact AST, covering span, carrier,
window, cursor, and first rejection. Every success endpoint is deterministic
and exclusive with rejection. Declarative and parser outcome packages are
publicly exported and compile-time consumed; these declaration-local results
feed the broader top-item outcome below.

The stronger exact contract is unconditional throughout the export chain:
complete constructor/name, selection, payload, and declaration ASTs and every
rejecting endpoint are unique. Supplied outer spans are explicitly shared.

Pragma item scanning and complete `pragmaDecl` also have exact broad ordinary
outcomes. An immediate `;` is empty and nonconsuming. Otherwise checked names
remain in forward order; comma absence stops without consumption, and comma
followed by `;` consumes only that trailing comma. Complete pragmas compose
exact `pragma`, a raw-identifier name that deliberately omits the checked-name
hyphen diagnostic, the item scan, and an exact semicolon, with separate
keyword, name, items, and semicolon rejection. Item-tail,
item-list, and declaration successful remainders are deterministic, and
success is disjoint from rejection. Unconditional exactness also fixes item
lists, complete declaration ASTs, and rejection endpoints. Public APIs and
consumers retain the production tail's shared reverse prefix and forward order;
their results feed the broader top-item and file outcomes below.

Dotted derive targets now have exact broad ordinary outcomes for components,
recursive dotted tails, and complete targets. Success retains checked
identifiers as well as diagnosed reserved hard keywords. Rejection records
that neither component alternative is available, or preserves the consumed
dot and exact first or later component failure. Successful remainders are
unique and success/rejection are disjoint at each layer. Exact deterministic
outcome contracts additionally fix successful component lists and complete
target ASTs together with every rejection endpoint. Executable reflection is
exported through the public syntax umbrella and checked by dedicated and
public-boundary consumers.

Complete derive attributes now also have exact broad ordinary outcomes. The
valid path exposes five rejection stages: hash, opening bracket, contextual
`derive` marker, no-trailing target list, and closing bracket. Recovery gives a
current `]` priority and consumes it; otherwise window end, a top-item start,
an identifier-plus-colon contract field, `}`, or a missing active-window
carrier stops unclosed recovery without consumption. Every other raw token is
scanned while updating the last span, and the tail has no ordinary rejection
after exact `#[` consumption. Transactional public fallback retries from the
original input after valid-path rejection; public rejection records both
failed attempts. Valid, recovery-tail, complete-recovery, and public outcomes
have unique successful remainders and disjoint success/rejection. Generic
no-trailing lists lift exact nested outcomes to exact list ASTs and rejection
endpoints; this fixes the valid, complete-recovery, and public attribute ASTs
and rejecting remainders as well. The recovery-tail theorem correctly shares
its last-retained span. Public executable reflection and dedicated consumers
check the resulting exact outcome contract. Diagnostics, failure payloads, and
whole parser states remain outside that contract.

Attribute-free `contractMemberCore` now has complete broad ordinary coverage for
field, function, constructor, fallback, type-alias, and contextual-enum
dispatch in executable priority order. Identifier-plus-colon field lookahead
wins, including for `enum:`, and a selected rejecting branch never falls
through. Success retains its wrapped AST, declaration span, empty leading
comments, carrier, window, cursor, and final remainder. Rejection records the
selected leaf or an exact nonconsuming unrecognized-member case. Successful
remainders are deterministic and success is disjoint from rejection. Stronger
AST/remainder/rejection-endpoint exactness is now unconditional through exact
Core expressions, isolated `.allow`/`.require` bodies, type aliases, and enums.
Earlier conditional APIs and strict member soundness remain available.

Exact pure derive attachment now covers all seven contract-member variants and
gives every input one unique AST result. Enums alone retain the attribute. Other
declaration variants preserve their payload while extending the outer and
nested declaration spans, the error variant extends its outer span, and every
branch preserves leading comments. Executable attachment always succeeds,
reflects that exact transformation, and leaves the declarative remainder
unchanged; diagnosed non-enum attachment introduces no rejection stage.

Derive-aware `contractMemberWithAttribute` now also has complete broad ordinary
coverage. Hash absence runs the attribute-free core. Hash presence commits in
order to public derive parsing, core member parsing, and pure attachment.
Rejection distinguishes plain-core failure, derive failure, and core failure
after derive success. Executable success and rejection reflect these relations;
successful remainders are deterministic and success/rejection are disjoint.
Exact attribute-free members and pure attachment now make the derive-aware
AST and rejection-endpoint contract unconditional. The earlier conditional
lift remains available.

Standalone contract-member recovery has exact broad success and rejection: it
consumes one mandatory token, scans to but not through the next recovery
boundary, and rejects only when that first token is unavailable. The
recovery-aware contract body adds right-brace priority, strict direct-member
progress, exact rejection rewind, recovered members in source order, and exact
opening or tail rejection. Broad contract declarations compose exact `contract`,
name, optional-generic, and body stages with four matching rejection cases.
Every layer has deterministic successful remainders and disjoint
success/rejection; its declarative API, executable reflection package, and
outcome specification are public and compile-time consumed. Standalone recovery
also has a unique error-member AST and final remainder and a unique rejection
endpoint; its scan theorem fixes both retained endpoint spans.
Unconditional exactness lifts from derive-aware members through the body and
complete declaration, preserving the full AST, final remainder, and rejection
endpoint. Core expression and statement exactness discharge the earlier shared
prerequisites for this contract chain. Diagnostic traces, failure payloads,
and whole parser-state equality remain outside these laws.

Attribute-free top-item dispatch now has exact broad outcomes for all nine
declaration branches plus the final unrecognized case, with executable priority
encoded by positive and earlier-negative guards. Total derive attachment covers
all ten item variants, and the public hash-aware dispatcher composes derive,
plain-item, and attachment outcomes with exact first rejection stages.
Successful remainders are deterministic and success/rejection are disjoint.

Top-item recovery, recovery-aware file-item accumulation, and the complete
`sourceFile` wrapper now have exact broad outcomes. Recovery consumes one
mandatory token and preserves the next recognized item boundary. The file loop
keeps forward order without exposing its reverse accumulator, preserves exact
rewind carrier/window/cursor state, records strict direct progress, treats a
rejected recognized start as nonconsuming diagnostic success, and otherwise
adds the exact recovered error item. The final wrapper preserves source id,
full-file span, comment attachment, comments, and the first rejection endpoint.
The declarative and executable APIs and deterministic outcome specifications
are public and compile-time consumed. Because boundary-stop may succeed inside
the window, only the strict diagnostic-free grammar claims full consumption.

Unconditional exactness now extends through plain and derive-aware top items,
recovery-aware file items, and the complete source-file AST with comment
attachment. It fixes full ASTs and declarative success/rejection endpoints
without recursive exactness or diagnostic-free premises. Public `parseLexed`
and `parse` value uniqueness compares independently derived ASTs over fixed
file/tokens/comments, including both nesting branches. The public AST boundary
does not expose a final cursor or claim diagnostic/whole-state equality.

Validated carriers additionally determine one independently derived public AST,
and every derivation has recursive Core/item/comment source provenance without
requiring a parser-reply hypothesis. Contract-internal fields, both member
dispatchers, bodies, and recovery expose matching completeness boundaries.

The canonical nesting preflight now has a total and functional independent
scan grammar over six exact token actions. It carries delimiter depth,
conditional depth, and scope bases, and identifies the first overflow span,
dimension, and shared limit. Executable `checkNesting` is equivalent to its
clear and overflow outcomes. Above it, every successful public parser result
has one of two exact AST shapes: the canonical empty file after overflow, or a
recovery-aware `SourceFileOrdinaryParses` derivation from the root token window
after clearance. These direct and source-level theorems use the exact retained
tokens and comments and compose with canonical output validity. Overflow also
fixes the complete public output and singleton parse diagnostic; the normal
branch does not yet expose a complete declarative diagnostic trace.

A separate normal-branch trace contract covers one unrecognized recovery to the
root-window end. It fixes the raw singleton recovery event, its independent
lexical-cascade keep/drop decision, and every field of the public output.
Earlier raw diagnostic order and duplicate retained spans are preserved.
A recognized pragma marker followed by an unavailable raw name also determines
the complete public output: no AST item, retained carriers and comments, and
the exact unexpected report after independent cascade filtering. Source and
window-end byte remain explicit in the current-token observation, including
EOF. Primitive rejection emits nothing; the file boundary keeps failed-attempt
diagnostics and appends the failure while rewinding only the cursor. Other
declaration and nested-isolation traces remain open.

Raw identifiers are independently proved silent, while checked identifiers
append exactly one located report iff their spelling contains a hyphen. The
full name, remainder, and added trace agree with execution in both directions.
Independent filtering also covers arbitrary mixed diagnostic lists, preserving
expectation/context/text/constraint payloads and repeated surviving occurrences.
Identifier, constraint, and nesting reports stay protected even at a suppressed
failure's span; input order is preserved without sorting or deduplication.
Exact keyword, symbol, and contextual-word success preserves a silent trace,
while rejection selects the precise expectation report without committing it.
Contextual words retain their identifier spelling and contextual expectation.
The correspondence permits arbitrary prior diagnostics and needs no input
validity premise. Independent filtering composes over appended traces, so a
protected identifier suffix survives normalization of a mixed earlier prefix.

Successful pragma traces now cover the entire declaration, including empty
item lists and trailing commas. Only checked item names emit events; raw names
and punctuation are silent, and tail accumulators are not re-diagnosed. A root
pragma reaching the end fixes the complete comment-attached singleton public
output, with every protected spelling report retained. Empty token carriers
also fix complete normal outputs with retained comments/lexical diagnostics and
no parser events. Separate executable composition laws preserve both suffixes
under sequencing but discard rejected-left traces under transactional choice;
these laws retain explicit branch-execution premises.
Canonical-source regressions exercise raw-name hyphens, multiple checked items
and a trailing comma, non-vacuous same-line lexical suppression with protected
reports, and exact comment attachment. Repeated normalization is idempotent,
and filtering concatenated traces equals concatenating their filtered results.
Complete-output equality now extends to any finite successful pragma sequence,
including empty input. Independent grammar fixes every declaration, endpoint,
and concatenated protected trace and erases to the ordinary file-item grammar.
Production fuel suffices, reverse item prefixes are restored without renewed
diagnostics, and all wrapped/comment-attached output items retain written order.
All four pragma rejection stages fix exact remaining input, complete failure
payloads, and earlier checked-item events, with no validity or empty-prior-trace
assumption. Full file/window frame laws preserve diagnostic context. Recognized
initial pragma rejection has complete public output equality after committing
one failure report. Only this final report is eligible for suppression; earlier
protected events survive unchanged. Canonical item/semicolon rejection examples
and two-declaration examples verify actual lexical carriers and diagnostic order.
Recognized rejection may also follow any successful pragma prefix. Exact raw
and public results retain its ordered items, rewind to the rejected declaration's
start, and commit its report once after every earlier event. Independent grammar
fixes all four result components, with sufficient production bounds derived from
token progress. Canonical successful-then-rejected examples cover both final
report retention and same-line suppression without losing earlier AST or events.
Balanced isolation now has conditional independent trace grammar and exact
execution correspondence, in addition to compositional merge/reset/frame laws.
Children use their captured byte endpoint, and the original parent window is
restored after either success or recovered rejection. Only recovery adds the
failure report; invariants propagate. Exactness and trace iff lift explicit
inner contracts without asserting concrete Core trace completeness. Nested
isolation consumers verify that an already recovered report is not committed again.
Core closing independently fixes the required expression-semicolon reports,
including the final-expression policy and complete statement spans. Trace
existence, uniqueness, protection, and equivalence between an empty trace and
the old validity predicate are proved. Successful closing fixes the brace,
source-order AST, remainder, and diagnostic suffix; a missing brace rejects
without running validation or changing the input. Mixed normalization preserves
the complete validation suffix after any earlier filtered events.
Raw Core block traces now compose all statement events before delayed tail
validation and exclude that validation on rejection. Independent branch and
report grammars have exact ordinary erasure, uniqueness, and success/rejection
disjointness under statement outcome laws. Statement execution contracts lift
to raw and isolated block success/rejection iff theorems, with sufficient
production fuel, arbitrary prior events, fixed failures, and exact parent resume
points. These are conditional block contracts; concrete general statement
diagnostic traces have not yet been supplied.
A test-only checked-name adapter supplies nonempty token-carrier consumers of
these contracts, including ordered name/tail events and recovered rejection
with parent-window and next-token preservation; it is not a Core grammar or
canonical-lexer claim.
Actual break/continue leaves also have unconditional silent trace contracts,
exact two-token successful state updates, first-failure reports, and independent
existence/uniqueness/disjointness even on malformed carriers. The same laws
provide joint exactness for raw and isolated blocks restricted to either leaf.
Concrete token-carrier examples cover two-statement success, later semicolon
failure, keyword-first priority, and one-report recovery before a parent token.
Two canonical-source consumers connect actual lexing to these restricted-block
success and rejection proofs; broader mixed-statement/file traces remain open.
Return traces now preserve the optional expression's full event list and first
failure, with semicolon-first omission and exact later semicolon reports.
Expression contracts provide return execution correspondence and restricted
block composition; empty returns bypass expression execution unconditionally.
Independent expression exactness and outcome existence remain separate inputs,
and no general concrete expression trace claim is implied.
Core literal and Boolean primitives now have unconditional silent traces with
exact payloads, one-token successful state updates, and unchanged-state failures
whose expectations remain distinct. Their independent outcomes are total and
exact. The real literal-expression leaf supplies all execution and independent
expression contracts, closing empty/one-literal return and restricted-block
exactness without extending that claim to general expressions.
Canonical `return 42;` and `return 42` consumers verify success and exact EOF
failure. A separate token-carrier block combines literal and empty returns and
preserves the full parent context and next token after isolation.

Function declarations, implementations, and contracts now extend the strict
boundary over abstract expression and block judgments. Exact signature policy,
optional `default`, nonempty implementation heads, member and method order,
brace priority, strict progress, outer spans, and remainders are preserved.
Exact plain and derive-aware top-item soundness feeds a complete-file judgment
with source-order comment attachment, full-window consumption, and recovery
exclusion. These theorem families are publicly registered. The fuel-indexed
mutual Core closure and public Yul outcomes now instantiate that judgment as
`CoreSourceFileOrdinaryParses`, with concrete public expression and isolated
body relations for both block-tail policies. Exact fixed-fuel statement
outcomes now lift through raw block item order, public blocks, and balanced
isolation/recovery for both policies, fixing block ASTs, closing spans,
remainders, and external rejection endpoints. The shared Core fuel induction
discharges the statement premise, so these contracts are unconditional.
`CoreSourceFileOrdinaryParsesFromStart` fixes both the root window and the
canonical terminal remainder, with the same carrier and `endIndex` and a final
cursor equal to the token count. Diagnostic-free successful `parseLexed` and
`parse` results derive it over their exact public carriers and pair it with
canonical parsed-file validity; its component relations remain recovery-aware
ordinary judgments.

Inline-Yul expression, statement, and body ASTs, final remainders, and rejection
endpoints are now unconditionally unique, including fixed-fuel and public
recursive boundaries. Exactness covers identifier/call priority, transactional
rewind, optional semicolons, switch/default selection, diagnosed empty
switches, and recursive blocks with source-order lists. Recovery shares its
first/last spans. Expression and statement rejection rewind to the input;
body rejection fixes its first-failing endpoint. Declarative and executable
APIs and compile-time consumers are included in the passing full build and
tests. Diagnostic traces, failure payloads, and whole-state equality remain
outside these contracts.

## Semantic Core v3 feature inventory

Rows marked Complete in this section are included in the closed Core Wire v3
language. Planned and Blocked rows are not part of that public algebra. Core
Wire v1 and v2 remain frozen and reject their later forms.

| Feature | Decision | Lean status | Required proof boundary | Syntax coupling |
| --- | --- | --- | --- | --- |
| Binary products and projections | ADR-0019 Accepted | Complete | typing/checker equivalence, CEK/big-step correspondence, safety, sufficient fuel, and old-wire rejection complete | None |
| Functions and application | ADR-0020 Accepted | Complete | typing/checker equivalence, ordered application, correspondence, logical-relations totality, safety, and old-wire rejection complete | None |
| Lexical closures | ADR-0020 Accepted | Complete | capture typing, environment correspondence, invocation, and fault exclusion complete | None |
| Sum values | ADR-0021 Accepted | Complete | injections, exhaustive elimination, checker equivalence, CEK correspondence, logical-relations totality, safety, and old-wire rejection complete | None |
| First-order local cells | ADR-0022 Accepted | Complete | explicit store threading, checker correspondence, CEK/big-step correspondence, store-indexed safety, sufficient fuel, and old-wire rejection complete | None |
| Named algebraic data | ADR-0023 Accepted | Complete | whole-table validity, nominal constructor typing, recursive and mutually recursive finite-value safety, totality, sufficient fuel, diagnostics, and old-wire rejection complete | None |
| Direct normalized matching | ADR-0023 Accepted | Complete | constructor-order exhaustiveness, payload binding, selected-branch store threading, CEK/big-step correspondence, safety, exact fuel, and diagnostics complete | None |
| Boolean/word conversions | ADR-0024 Accepted | Complete | derived-expression typing and inference, exact values, exactly-once store-threaded evaluation, weakening, and version-boundary tests complete | None |
| Word zero test | ADR-0025 Accepted | Complete | derived word-to-word expansion, typing, inference, zero/nonzero and store-threaded evaluation, weakening, effects, fuel, and version-boundary coverage complete | None |
| Short-circuit boolean operators | ADR-0026 Accepted | Complete | expansion, typing, inference, four store-threaded branches, selected effects/faults, exact fuel, weakening, and exact v1/v2 wire projection complete | None |
| Word nonzero test | ADR-0027 Accepted | Complete | canonical expansion, typing, inference, general and zero/nonzero store evaluation, weakening, exactly-once effects, exact fuel and v1/v2 boundaries complete | None |
| Word comparison flags | ADR-0028 Accepted | Complete | named expansions, typing, inference, general and four-case store evaluation, weakening, effects, exact fuel, bool preservation, and v1/v2 boundaries complete | None |
| Renaming and environment insertion | ADR-0029 Accepted | Complete | syntax renaming, typing preservation, value/environment/store relations, full evaluation simulation, CellPayload exactness, head-insertion word theorem, and static/dynamic tests complete | None |
| Derived boolean word comparisons | ADR-0030 Accepted | Complete | four expansion/typing/infer/rename/weaken APIs, untyped wordNe/wordLe and typed wordLt/wordGe store evaluation, eight truth cases, values/types/fuel/fault/effects, v1 rejection, and exact v2 projection/round-trip tests complete | None |
| Derived word comparison flags | ADR-0031 Accepted | Complete | four builders and expansion/type/infer/rename/weaken APIs, four general and eight case evaluations, value/type/fuel/fault/effect tests, v1 rejection, and exact v2 projection/round trips complete | None |
| Derived-builder arbitrary renaming laws | ADR-0032 Accepted | Complete | exactly eight laws in their owning modules, rename_boolToWord relocation, swap01 free-variable goldens, and three-family runtime-environment regressions complete | None |
| Direct unary primitive interface | ADR-0033 Accepted | Complete | named raw boolNot/wordNot APIs, zero/maximum/involution facts, exact fuel, fault/effect/store tests, v1 rejection, and exact v2 projection/round trips complete | None |
| Totalized unsigned division and modulo interface | ADR-0034 Accepted | Complete | four Word, two apply, and six evaluation theorems; ordered zero-divisor effects/faults, exact fuel, and v1/v2 regressions complete | None |
| Bounded logical shift interface | ADR-0035 Accepted | Complete | six Word, two apply, and six evaluation theorems; value-left/shift-right boundaries, effects, exact fuel, and v1/v2 plus JSON round trips complete | None |
| Modular word arithmetic interface | ADR-0036 Accepted | Complete | eight Word, three apply, and three evaluation theorems; normal/wrapped values, strict order, effects/fuel, and v1/v2 Core plus JSON round trips complete | None |
| Binary bitwise logic interface | ADR-0037 Accepted | Complete | nine Word, three apply, and three evaluation theorems; masks, strict order, effects/fuel, and v1/v2 Core plus JSON round trips complete | None |
| Direct word comparison interface | ADR-0038 Accepted | Complete | two apply and six evaluation theorems; boolean equality and strict unsigned greater-than with values, types, ordered faults/effects, exact fuel, and v1/v2 Core/JSON regressions complete | None |
| Word leading-zero count | ADR-0039 Accepted | Complete | internal UnaryOp.wordClz and Word.clz; five Word, one apply, and five evaluation theorems; value/type/fault/effect/fuel tests and frozen v1/v2 rejection complete | None |
| Word byte selection | ADR-0040 Accepted | Complete | internal BinaryOp.wordByte and big-endian Word.byteAt; five Word, one apply, and three evaluation theorems; values/types/faults/effects/fuel and frozen v1/v2 plus v2-op rejection complete | None |
| Arithmetic right shift | ADR-0041 Accepted | Complete | internal BinaryOp.wordSar and two's-complement Word.shiftArithmeticRight; five Word, one apply, and five evaluation theorems; values/types/faults/effects/fuel and frozen v1/v2 plus v2-op rejection complete | None |
| Modular exponentiation | ADR-0042 Accepted | Complete | internal BinaryOp.wordPow and proved square-and-multiply Word.pow; eight Word, one apply, and five evaluations; values/types/faults/effects/fuel and frozen v1/v2 plus v2-op rejection complete | None |
| Signed word greater-than | ADR-0043 Accepted | Complete | exact eleven-theorem boolean wordSgt basis; sign boundaries, types, ordered faults/effects, exact fuel, and frozen v1/v2 plus v2-op rejection complete; audit clean | None |
| Derived signed word less-than | ADR-0044 Accepted | Complete | effect-safe nested-let wordSlt; five static and five evaluation theorems; values/types/fault order/effects/store/fuel and frozen v1/v2 rejection complete; audit clean | None |
| Signed word comparison flags | ADR-0045 Accepted | Complete | two exact builders; ten static and ten evaluation laws; sign/value/type/fault/effect/store/fuel and frozen v1/v2 rejection complete; audit clean | None |
| Signed non-strict word comparisons | ADR-0046 Accepted | Complete | derived boolean wordSle and wordSge; exact twenty-theorem interface; sign/type/fault/effect/store/fuel and frozen-Wire regressions complete; audit clean | None |
| Word sign extension | ADR-0047 Accepted | Complete | internal index-left/value-right wordSignExtend; exact ten theorems and index/value/type/fault/effect/store/fuel/frozen-Wire regressions complete; audit clean | None |
| Signed word division and remainder | ADR-0048 Accepted | Complete | internal dividend-left/divisor-right wordSdiv and wordSmod; exact fourteen theorems and sign/zero/minimum/type/fault/effect/store/fuel/frozen-Wire regressions complete; audit clean | None |
| Signed non-strict comparison flags | ADR-0049 Accepted | Complete | derived wordSleFlag and wordSgeFlag; exact twenty theorems and canonical/truth/type/fault/effect/store/fuel/frozen-Wire regressions complete; audit clean | None |
| Ternary modular arithmetic | ADR-0050 Accepted | Complete | internal wordAddMod/wordMulMod and Expr.ternary; full-precision reduction, exact fourteen focused theorems, generic static/safety support, exact fuel, and frozen v1/v2 rejection complete; audit clean | None |
| Further Core conversions and primitives | Per-feature decisions needed | Planned | separate closed decisions, total application, and typed results | None |
| Recursion and divergence | Decision incomplete | Blocked | divergence/resource model and replacement for finite termination | None |

## Static semantics after Core

| Feature | Status | Missing work | Syntax coupling |
| --- | --- | --- | --- |
| Abstract resolved-name language | Planned | structured identities, declarations, occurrences, scopes | Low |
| Source type checking | Planned after resolved IR | type and effect rules over abstract identities | Medium |
| Parametric polymorphism | Planned | type application and preservation | Low |
| Tabled class resolution | Planned | evidence language, finite search, inconclusive boundary | Low |
| Comptime/runtime staging | Blocked | staging decision and effect rules | Low |
| Canonical Syntax-to-Resolved adapter | Planned | connect parsed declarations and occurrences to structured identity | High |
| Resolved-to-Core elaboration | Planned after source typing | type, effect, and stage preservation | Medium |

## Contract and runtime semantics

| Feature | Status | Missing decision or implementation | Syntax coupling |
| --- | --- | --- | --- |
| Canonical runtime scalar observations | Complete | Strict Bytes/Address/Word text and Word big-endian bytes; exact sixteen theorems; boundary, rejection, canonicality, `Word.byteAt`, and frozen-Wire output compatibility tests complete; Wire codecs unchanged; audit clean | None |
| Contract frame halt outcomes | Complete | Parametric return/revert/trap carrier and four observations; exactly six laws and 10 executable runtime assertions cover empty versus absent payloads, zero-octet preservation, distinct trap reasons, and constructor boundaries; no state or publication; audit clean | None |
| Strict Address↔Word bridge | Complete | Lossless widening and strict non-truncating narrowing; two definitions, exactly six axiom-free laws, and 10 runtime assertions cover zero, one, middle, maximum, and overflow rejection; no source, ABI, state, or publication; audit clean | None |
| Strict 20-byte Address representation | Complete | Two definitions, exactly six laws, and 10 runtime assertions cover leading zeros, exact width, 19/21-byte rejection, representative round trips, injectivity, and all 20 widened-Word suffix indices; no ABI, state, or publication; audit clean | None |
| Address text and byte coherence | Complete | No public executable API; 15 private helpers, exactly four public laws, and eight runtime assertions connect canonical text, exact bytes, and arbitrary-input decoder agreement; no ABI, state, or publication; audit clean | None |
| Minimal Account and WorldState carrier | Complete | Two public carriers backed only by private semantic lookup functions, eight public operations, exactly twelve laws, and twelve runtime assertions; no concrete map representation, rollback, balances, code, calls, ordering, serialization, or publication; audit clean | None |
| Frame-outcome WorldState resolution | Complete | One internal operation, exactly three constructor laws, and three runtime assertions select working/checkpoint state while leaving trap disposition open; no nested rollback, surviving effects, ABI, EVM, or publication | None |
| WorldState observational update algebra | Complete | No executable API, carrier, or instance; exactly six extensionality/overwrite/commutation laws, two compile-time examples, and four runtime assertions complete; no new state meaning or publication | None |
| WorldState storage-write algebra | Complete | No executable API, carrier, or instance; one private helper, exactly four sequential/commutation/zero-deletion laws, and four runtime assertions complete; no operational or publication decision | None |
| External-checkpoint frame run result | Complete | One public semantic carrier and one named resolver; exactly three constructor laws and three runtime assertions pair speculative working state with an outcome while checkpoint ownership remains external | None |
| Parametric frame effect journal policy | Complete | One public two-snapshot carrier and one resolver; exactly five axiom-free laws and five runtime assertions separate rollback-scoped state from an opaque surviving trace without concrete event order | None |
| Synchronized frame state/effect resolution | Complete | No new carrier, instance, or helper; one resolver, exactly five laws, and three runtime assertions select WorldState and effects from one outcome branch | None |
| Synchronized child-frame composition | Complete | Proof-only; no carrier, API, instance, or helper; exactly two nested non-simp laws and two runtime assertions complete with opaque accumulated trace ownership | None |
| Unresolved trap propagation | Complete | Proof-only; no carrier, API, instance, or helper; exactly one generic non-simp `rfl` bind law and one definition-only sentinel runtime assertion complete | None |
| Resolved frame continuation laws | Complete | Proof-only; no carrier, API, instance, or helper; exactly two generic non-simp `rfl` bind laws and two definition-only sentinel assertions complete the returned/reverted continuation boundary | None |
| Caller-owned frame continuation | Complete | Exactly one higher-order resolver/bind operation, three simp `rfl` constructor laws, and three definition-only assertions complete without creating checkpoints or traces | None |
| Caller-owned frame continuation context | Complete | One four-field nominal carrier, one delegating operation, one non-simp `rfl` coherence law, and three definition-only assertions complete without a full frame model | None |
| Total frame resolution result | Complete | One three-constructor total carrier, one context resolver, exactly three simp `rfl` laws, and three definition-only assertions preserve payloads and trap reasons without choosing trap disposition | None |
| Ordered frame trace algebra | Complete | One constructor-private opt-in trace carrier, four operations, exactly seven axiom-free laws, and six definition-only assertions complete finite chronological extension without fixing event kinds | None |
| Frame trace prefix relation | Complete | One proof-only non-strict prefix relation, exactly four non-simp axiom-free laws, and four definition-only compile examples complete value factorization without runtime provenance claims | None |
| Trace-prefixed frame continuation context | Complete | One refined carrier binds prefix evidence to its exact checkpoint/working traces; three definition-only compile examples complete with no new operation, theorem, runtime checker, or provenance claim | None |
| Indexed frame trace extension | Complete | One constructor-private indexed carrier, three operations, three axiom-free theorems, three runtime assertions, and one ADR-0071 integration example complete event-only extension without a same-typed fragment input | None |
| Parent-indexed frame continuation context | Complete | One indexed carrier with one checkpoint-equality field, exactly three non-simp laws, and three definition-only runtime assertions characterize inherited return/revert resolution and parent trace-prefix evidence without a new operation or provenance claim | None |
| Parent-indexed frame continuation construction | Complete | One restricted operation derives both relationship proofs from an indexed trace extension; exactly four simp `rfl` projection laws and three definition-only assertions complete construction without a new carrier, resolver, or provenance claim | None |
| Parent-indexed trapped-frame rollback selection | Complete | One opt-in selector chooses parent checkpoint state and rollback with the accumulated internal trace only for traps; exactly three non-simp laws and three definition-only assertions complete frame-local selection without duplicating reason or prefix interfaces or changing generic resolvers | None |
| Parent-indexed trap propagation payload selection | Complete | One opt-in operation maps the selected rollback pair and original trapped outcome into a caller-designated prospective enclosing payload; exactly three non-simp laws and three definition-only assertions complete value construction without executing or proving propagation | None |
| Parent-indexed trap propagation payload coherence | Complete | Two non-simp laws characterize successful payload selection and carry existing non-strict trace-prefix evidence to the selected journal; exactly two private compile regressions complete the proof boundary without a new operation or runtime provenance claim | None |
| Heterogeneous frame-outcome trap-reason mapping | Complete | One caller-supplied pure operation preserves return/revert bytes and maps only trapped reasons; exactly five axiom-free simp laws and three definition-only assertions complete the mapping algebra without a Functor instance, taxonomy, or propagation policy | None |
| Heterogeneous frame-run-result trap-reason mapping | Complete | One pure lift preserves the exact working state and delegates only the outcome to ADR-0078; exactly five `[propext]` simp laws and three definition-only assertions complete the result mapping without a resolver, payload, trace, or propagation policy | None |
| Heterogeneous frame-resolution-result trap-reason mapping | Complete | One pure operation preserves returned/reverted state, effects, and bytes while mapping only trapped reasons; exactly five `[propext]` simp laws and three definition-only assertions complete the algebra without a context mapper, resolver coherence, payload, or propagation policy | None |
| Heterogeneous frame-continuation-context trap-reason mapping | Complete | One pure lift preserves all checkpoint and working fields while delegating only the frame result to ADR-0079; exactly seven `[propext]` simp laws and three definition-only assertions complete the context algebra without continuation, resolver coherence, payload, or propagation policy | None |
| Frame trap-reason mapping resolution naturality | Complete | One `[propext]` proof-only simp law makes context mapping commute with total resolution; exactly two private compile regressions complete without an operation, branch duplicate, continuation behavior, payload, or propagation policy | None |
| Frame trap-reason mapping continuation-result invariance | Complete | One `[propext]` proof-only simp law equates the `Option Next` values before and after context reason mapping; exactly two private compile regressions complete without an operation, branch duplicate, cost, step-count, exactly-once, payload, or propagation claim | None |
| Heterogeneous trace-prefixed continuation-context trap-reason mapping | Complete | One pure lift maps the base context while reusing exact prefix evidence; exactly four `[propext]` simp laws and three definition-only compile regressions complete without trace, event, rollback, provenance, parent-index, payload, or propagation policy | None |
| Heterogeneous parent-indexed continuation-context trap-reason mapping | Complete | One pure lift maps the trace-prefix context while reusing the exact parent index and checkpoint equality; exactly four `[propext]` simp laws and three definition-only compile regressions complete without rollback, payload, provenance, propagation, or nested-runtime policy | None |
| Nominal frame checkpoint snapshot | Complete | One carrier and from-pair adapter retain caller-supplied synchronized state/effects; exactly two `[propext]` projection laws and three compile-only regressions complete without capture time, ownership, provenance, working initialization, or transition policy | None |
| Frame checkpointed working pair | Complete | One carrier stores a nominal checkpoint beside an independent raw working pair; generated construction/projection and exactly three compile-only regressions complete without a custom operation, relation proof, initialization, lifecycle, or transition policy | None |
| Continuation context from checkpointed working pair | Complete | One pure adapter maps every checkpoint/working value plus an opaque outcome into the existing context; exactly four `[propext]` projection laws and three compile-only regressions complete without execution, provenance, resolution, continuation, or transaction policy | None |
| Bytes-aware frame resolution continuation | Complete | One result-first partial dispatcher passes selected state/effects and bytes to separate return/revert callbacks while trap yields none; exactly three generated equations, three `[propext]` constructor laws, and three runtime assertions complete without delivery, mutation, scheduling, trap handling, or transaction policy | None |
| Frame continuation branch/byte erasure coherence | Complete | One `[propext]` proof-only non-simp law equates bytes-erasing identical result callbacks after total resolution with the existing context continuation; exactly two private compile regressions complete without an operation, runtime assertion, delivery, scheduling, trap handling, or transaction policy | None |
| Frame-resolution continuation trap-reason mapping invariance | Complete | One `[propext]` proof-only simp law removes heterogeneous result reason mapping from bytes-aware continuation; exactly two private compile regressions complete without an operation, runtime assertion, callback-count claim, trap handling, or transaction policy | None |
| Checkpointed working-pair storage write | Complete | One conditional lift updates only the working WorldState while preserving the exact checkpoint and working journal; exactly two `[propext]` branch laws and three runtime assertions complete without authorization, account creation, checkpoint lifecycle, outcome, scheduling, trap, gas, or transaction policy | None |
| Checkpointed working-pair storage address | Complete | One retained selector supplies every working-storage write without adding current-contract identity, authorization, or account creation | None |
| Conditional WorldState storage read | Complete | Account absence remains `none`; every slot of a present Account reads as `some value`, with missing storage represented by zero | None |
| Address-bound working storage read | Complete | The retained selector supplies working-storage reads without consulting the checkpoint or accepting a fresh address | None |
| WorldState storage read/write coherence | Complete | Three proof-only laws show how same-slot, different-slot, and different-address reads observe conditional writes while preserving failure stages | None |
| Address-bound working storage read/write coherence | Complete | Two proof-only laws expose the written value and preserve a different-slot read through the retained selector | None |
| Parent-indexed frame initialization | Complete | A payload-free carrier derives the initial trace extension and checkpointed working pair while leaving initial state and rollback caller-supplied | None |
| Parent-indexed initialization storage-address adapter | Complete | ADR-0099 binds a caller-supplied storage selector to initialized values without a new carrier or authority claim | None |
| Checkpointed working-pair storage-write algebra | Complete | ADR-0100 proves three proof-only overwrite and commutation laws over the existing address-parameterized write | None |
| Address-bound working storage-write algebra | Complete | ADR-0101 proves same-slot overwrite and distinct-slot commutation through the retained selector | None |
| Address-bound working storage-write preservation | Complete | ADR-0102 proves three stage-preserving observations of the selector, checkpoint, and working effect journal | None |
| Address-bound working storage-write values coherence | Complete | ADR-0103 proves one exact relation from the wrapper write to its underlying values write | None |
| Parent-indexed initialization continuation-context coherence | Complete | ADR-0104 proves equality of the two pure base-context construction routes | None |
| Present working storage Account refinement | Complete | ADR-0105 retains the exact address-bound context, selected working Account, and lookup evidence for total consumers | None |
| Present working storage Account total read | Complete | ADR-0106 reads the proven-present Account without another lookup and proves conditional-read coherence | None |
| Present working storage Account total write | Complete | ADR-0107 synchronizes the retained Account, working-state entry, and fresh evidence without another lookup | None |
| Present working storage Account total read/write coherence | Complete | ADR-0108 proves same-slot and distinct-slot observations of total writes | None |
| Present working storage Account total-write algebra | Complete | ADR-0109 normalizes overwrite and commutes distinct-slot total writes | None |
| Present working storage Account total-write isolation | Complete | ADR-0110 preserves every non-selected working Account across total writes | None |
| Present working storage Account total-write projections | Complete | ADR-0111 exposes four direct data projections for total writes | None |
| Present working storage Account total-write presence | Complete | ADR-0112 proves zero deletion and nonzero sparse-entry presence | None |
| Present working storage Account total-write sparse preservation | Complete | ADR-0113 preserves an optional sparse entry at every distinct slot, first on Account and then on the proven-present carrier | None |
| Present working storage Account optional/total re-refinement coherence | Complete | ADR-0114 equates optional write plus canonical Account refinement with the total writer | None |
| Parent-indexed initialization present storage Account refinement | Complete | ADR-0115 checks initial Account presence and returns the existing proven-present carrier used by total storage operations | None |
| Address-selected closed Core code | Complete historical foundation | ADR-0116's pure carrier and completion theorems remain; ADR-0118 supersedes its Account association and selected runner | None |
| Typed Core storage requests | Complete | Internal and unpublished. ADR-0117 and ADR-0119 provide runtime-only `word -> word` reads and `(word × word) -> unit` writes, request-indexed responses, exact suspension/resumption, preservation, progress, no-fault safety, fuel accounting, and frozen-Wire rejection without importing WorldState into Core | None |
| Generic and address-selected working-storage driver | Complete | Internal and unpublished. ADR-0118's read loop is the historical foundation; ADR-0119 supplies the request-generic driver, combined read/write handler, exact remaining-fuel reuse, selected-code safety, and separate code/storage addresses. Writes update only the returned working context; commit and rollback are not implied | None |
| Handled-execution completeness and terminal fuel stability | Complete | ADR-0120 makes the generic handled-step relation and executable driver result equivalent. Done and fault results are unchanged by additional fuel; storage, checked, and successful address-selected done specializations retain the exact final context. Out-of-fuel is not stable and has no such theorem. This proof-only slice adds no runtime behavior or request kind | None |
| Retained storage-selector observation | Complete | ADR-0121 appends the internal `storageAddress : unit -> word` capability at index 2 while keeping storage read and write at indexes 0 and 1. The handler losslessly widens the retained Address in Semantics and leaves its context unchanged for this request, although the same driver can still handle writes. The value is only a storage selector, not the code address, current contract, `self`, caller, or an authority identity. Out-of-fuel remains non-stable, and no Wire, Oracle, Surface, Parser, or public runtime schema changes | None |
| Address-selected handled execution exact specification | Complete | ADR-0122 makes `some result` equivalent to exact selected-code fuel evidence and `none` equivalent to working-WorldState code lookup failure. Evidence replays to the same optional result, and selected out-of-fuel remains `some`. This proof-only slice changes no runtime behavior, address role, lifecycle policy, parser, or public format | None |
| Handled-execution relational metatheory | Complete | ADR-0123 composes Core and handled paths, proves direct handled-relation and fuel-evidence type safety, makes all results unique at one exact fuel, and makes done/raw-fault results unique across sufficient budgets including final contexts. Out-of-fuel remains budget-relative. This proof-only slice changes no runtime behavior or public format | None |
| Selected code-address observation | Complete | ADR-0126 appends internal `codeAddress : unit -> word` at index 3. One Address now drives both selected checked-code lookup and the same run's exact handler response, with fuel, safety, strict recovery, and larger-budget stability proofs. It remains distinct from storage, current, caller, callee, and authority roles | None |
| Parent-indexed resolution view | Complete | ADR-0127 pairs the existing total frame resolution with the existing opt-in trap rollback selection. Four exact non-simp laws and compile consumers preserve return, revert, trap, bytes-aware callbacks, parent-context coherence, and larger-fuel completion without applying rollback, flattening selected-execution failures, or claiming transaction finalization | None |
| Resolution-view trap-reason mapping naturality | Complete | ADR-0128 proves with one `[propext]` simp law that heterogeneous reason mapping changes only the total-resolution component and preserves the exact optional trap rollback pair. Direct, identity, composition, and bytes-aware continuation consumers pass without adding a mapper, execution path, rollback application, or transaction policy | None |
| Parent-indexed trap-aware resolution fold | Complete | ADR-0129 selects one caller-owned return, revert, or trap function and supplies the exact resolved pair, bytes, or reason. Four `[propext]` laws, three runtime branches, and compile consumers tie it to ADR-0127 and ADR-0125. The total generic fold applies no rollback, resumes no parent, adds no optional layer, and defines no transaction policy | None |
| Resolution-fold trap-reason mapping naturality | Complete | ADR-0130 adds one `[propext]` proof-only simp law that moves heterogeneous reason mapping through ADR-0129 by precomposing only the trap function. Four compile consumers cover direct use, identity, composition, and ADR-0128 view coherence without an operation, runtime branch, rollback application, or transaction policy | None |
| End-to-end call-value observation | Complete | ADR-0131 places the selected code Address and one caller-supplied Word in an immutable execution input and appends internal `callValue : unit -> word` at index 4. Exact handling, fuel evidence, selected and parent-indexed completion, value-derived resolution-fold consumption, larger-fuel stability, and distinct observe-write-observe regressions are complete. The Word implies no balance transfer, address identity, ABI rule, or publication | None |
| Run-fixed caller-address observation | Complete | [ADR-0132](adr/0132-run-fixed-caller-address-observation.md) appends one explicit Address to immutable `ExecutionInputs` and internal `callerAddress : unit -> word` at index 5, making both host tables length 6. Exact handling and completed-driver laws preserve the full context; regressions cover Account absence, caller-only variation, fuel, caller-derived storage, parent-indexed completion, the resolution fold, and frozen-Wire rejection. No provenance, authority, parent, origin, current/callee, nested-call, parser, or public-format meaning is added | None |
| Bounded optional input-byte observation | Complete | [ADR-0133](adr/0133-bounded-optional-input-byte-observation.md) adds bounded run-fixed `InputData` and internal `inputDataByte? : word -> sum unit word` at index 6. Exact indexing, optional response injection, context identity, byte-derived storage, parent completion, fuel, safety, and frozen-Wire rejection are complete. Size, wider loads, endianness, padding, ABI, calldata, syntax, Wire publication, and other public formats are excluded | None |
| Run-fixed input-size observation | Complete | [ADR-0134](adr/0134-run-fixed-input-size-observation.md) derives the exact bounded length as `sizeWord`, appends internal `inputDataSize : unit -> word` at index 7, and proves byte lookup is present exactly below that size. Handler/driver safety, size-derived storage, parent completion, fuel boundaries, and frozen-Wire rejection are complete. ABI, calldata, multi-byte decoding, nested calls, syntax, Wire, and publication are excluded | None |
| Strict optional input-word BE observation | Complete | [ADR-0135](adr/0135-strict-optional-input-word-be-observation.md) implements exact natural-number full 32-byte big-endian windows with explicit absence for incomplete input and no padding or offset wrap. Internal `inputDataWordBE? : word -> sum unit word` is index 8, with table length 9 and first-unbound index 9. Optional-response safety, full handler context identity, direct present/zero/absent, storage and parent fuel boundaries, triple-option/fold behavior, terminal bytes, and frozen-Wire rejection are proved and tested; ABI, calldata, memory, nested calls, syntax, and publication are excluded | None |
| Resumable handled fuel slices | Complete | [ADR-0136](adr/0136-resumable-handled-fuel-slices.md) resumes only exhausted results from their exact retained context and Core state. Same-handler split execution equals a single summed-budget run; done and fault remain terminal. Sequential addition covers arbitrary results, actual-run zero identity excludes forged exhausted values, typed results remain safe, and the storage specialization keeps identical `ExecutionInputs` while preserving completed writes and unrelated context. Gas, persistence, changed-handler/input resumption, lifecycle, syntax, and publication are excluded | None |
| Canonical host capability registry | Complete | [ADR-0137](adr/0137-canonical-host-capability-registry.md) makes `HostFunction.all` the only production order literal and derives both host tables and arbitrary-list typing from it. Its original nine-entry compatibility facts remain valid; ADR-0139 appends index 9, ADR-0146 appends typed call at index 10, ADR-0147 appends value-bearing call at index 11, ADR-0148 appends checked creation at index 12, and ADR-0149 appends word-log emission at index 13. The current tables have length 14 and index 14 is first unbound; all earlier indexes remain compatible | None |
| Branch-complete resumable parent-indexed selected execution | Complete | [ADR-0138](adr/0138-branch-complete-resumable-parent-indexed-selected-execution.md) proves six exact branch laws and checked no-fault for storage absence, code absence, exhaustion, raw fault, unsupported policy, and completion. Exhaustion resumes with exact split, zero, addition, and inversion laws; unsupported remains suspended and accumulates offered fuel. Whole-result erasure preserves the unchanged nested-`Option` API; completion recovers the exact plain continuation and existing return/revert/trap fold. Fuel 9/10/15/16 and terminal regressions pass. Exhaustion and fault receive no frame meaning; parser and syntax were outside that slice | None |
| Run-fixed current-address observation | Complete | [ADR-0139](adr/0139-run-fixed-current-address-observation.md) adds explicit immutable `currentAddress` and internal `unit -> word` index 9. Exact read-only variation, absent-Account behavior, direct 4/5 and end-to-end 16/17/23/29/30 fuel, 17+13 and 23+7 resumption, derived write/pair, parent folds, frozen-Wire rejection, and full audits pass. Storage, code, caller, current, and future callee roles remain independent | None |
| Proof-refined parent-indexed selected-execution session | Complete | [ADR-0140](adr/0140-proof-refined-parent-indexed-selected-execution-session.md) retains one fixed selected-run configuration and certifies its exact result against the one-shot run at cumulative provided fuel. Resumption accepts only an additional `Nat`; whole-session zero/addition, six branches, no-fault, compatibility, folds, and measured 9/10/15/16 and 17+13=30 regressions pass. This is neither consumed gas nor nested invocation, ABI, parser, or public-format policy | None |
| Checked Word completion to canonical return bytes | Complete | [ADR-0141](adr/0141-checked-word-completion-to-canonical-return-bytes.md) refines checked Word results, retains successful context/Word/Core Store, reuses `HostDriverResult` for raw branches, and builds the canonical 32-byte big-endian returned frame. Checked `none` is exactly exhaustion or unsupported policy; exact fuel 9/10/15/16, split/stability, zero/nontrivial/maximum frame, nonempty-Store, proof-consumer, and full-audit regressions pass. Non-Word fallback, selected-code refinement, ABI, parser, and public changes are excluded | None |
| Branch-complete selected Word-code classification | Complete | [ADR-0142](adr/0142-branch-complete-selected-word-code-classification.md) classifies existing optional checked code as absent, non-Word, or Word while retaining exact code and result-type evidence. Bidirectional erasure, injectivity, Word-refinement and WorldState coherence, empty/no-code specialization, storage preservation, 31 proof consumers, runtime regressions, and full audits pass. Execution, fallback policy, parent results, ABI, parser, and public changes are excluded | None |
| Proof-refined selected checked Word execution | Complete | [ADR-0143](adr/0143-proof-refined-selected-checked-word-execution.md) retains exact absent/non-Word/Word selection, executes only checked Word code, reuses existing raw and canonical completion carriers, and proves fixed-input fuel resumption. Thirty-two theorem consumers, 0/64 and 9/10/15/16 runtime boundaries, exact and associative splits, terminal stability, Store/context/byte/decode/frame recovery, full validation, and independent audits pass. ADR-0144 now supplies storage-presence and parent integration; non-Word fallback, ABI, parser, and public changes remain separate | None |
| Parent-indexed selected checked Word execution | Complete | [ADR-0144](adr/0144-parent-indexed-selected-checked-word-execution.md) uses one outer option only for storage absence, retains exact parent provenance, delegates fixed-input fuel resumption, and pairs canonical Word completion with the matching returned parent continuation. All 49 public theorems have external consumers; measured branch, fuel, split, state, byte, and limited legacy-coherence regressions and full validation pass. ADR-0145 and ADR-0146 supply the later top-level and nested lifecycle; ABI, parser, and public changes remain separate | None |
| Static Word contract entry | Complete | [ADR-0150](adr/0150-static-word-abi.md) admits checked `uint256 -> uint256` methods and generates one checked dispatcher with stable routing reverts | None |
| General contract entry | Planned | payability, fallback, receive, and broader constructor rules | Low |
| Contract runtime foundation | Complete | Storage/frame handling, selection, completion, fixed host inputs, direct top-level commit/rollback, depth-one checked child calls, checked value transfer, checked creation, ordered rollback-aware transaction observations, and shared-fuel resumption are complete | None |
| Executable checked-Core top-level lifecycle | Complete | [ADR-0145](adr/0145-executable-checked-core-top-level-lifecycle.md) executes an installed checked contract from explicit state, commits return, rolls back revert/trap, preserves resumable exhaustion, and returns terminal data with exact queryable target-state observations. Actual Core programs cover mutation, all terminal branches, no-write execution, and direct host inputs; all 45 theorem contracts have external consumers | None |
| Nested checked-Core invocation | Complete | [ADR-0146](adr/0146-one-level-nested-checked-core-execution.md) adds typed Word calls, current-world checked-contract resolution, one shared root/child fuel budget, exact resumption sealed by scheduler reachability, child checkpoint commit/rollback, root-wide commit/rollback, arbitrary-address delta queries, and actual checked-program regressions | None |
| Balance semantics | Complete | [ADR-0147](adr/0147-checked-balance-transfer-and-value-calls.md) adds explicit Account balances, non-wrapping atomic transfer, preservation and conservation laws, installation transport, arbitrary-address balance deltas, append-only value-call typing, nested and top-level rollback, sealed rejection, and exact resumption. Actual checked-Core regressions cover every transfer branch plus root, child, and post-child fuel splits without replaying effects | None |
| Checked contract creation | Complete | [ADR-0148](adr/0148-checked-contract-creation-lifecycle.md) adds non-wrapping Account nonces, explicit address derivation, checked initializer/runtime templates, fresh provisional Accounts, shared-fuel initializer execution, runtime installation, call-site and root rollback, fixed-environment resumption, and exact nonce/code/creation delta queries | None |
| Rollback-aware transaction observations | Complete | [ADR-0149](adr/0149-rollback-aware-logs-and-transaction-observations.md) adds ordered duplicate-preserving word logs and successful-creation enumeration to total results. Root, child, and initializer commit/rollback, balance and creation preflight identity, and exactly-once fuel resumption are proved and tested. Frozen Wire v1/v2 reject the append-only index-13 host value | None |
| Source storage layout and declaration mapping | Blocked | A layout/elaboration ADR is still required; this is separate from the completed internal Core slot read/write runtime | Low |
| Additional call kinds | Planned | Recursive depth and delegate/static-call policy remain later work | None |
| Canonical public execution observations | Complete | Oracle v5 publishes terminal outcomes, requested initial/committed state endpoints, committed Word logs, and successful creation addresses | None |
| Reproducible checked Core synthesis | Complete | [ADR-0152](adr/0152-reproducible-checked-core-case-synthesis.md) generates a bounded pure Word/Boolean Core v3 fragment from a versioned seed, seals every Program with the frozen checker, packages minimal Oracle v5 cases, and rechecks scope-preserving strict shrink candidates. A fixed 256-seed corpus covers all 29 tracked forms/operators and freezes public replay bytes; independent differential adapters and broader typed fragments remain later work | None |
| General ABI events and logs | Planned | Event signatures, multiple topics, arbitrary byte payloads, and source-level event declarations are not part of the Word-log profile | Medium |
| Static Word ABI support rule | Complete | Oracle v5 profile `staticWordAbiV1` publishes explicit `uint256 -> uint256` methods, derived selectors, checked admission, calldata routing, and lifecycle execution | None |
| Selector collision rejection | Complete | Duplicate signatures and distinct-signature four-byte collisions are rejected before dispatcher generation, with canonical error selection and permutation-invariant acceptance/rejection class | None |
| EVM revision policy | Direction accepted | execution implementation absent | None |
| Gas observation | Deferred | fork and gas schedule | None |
| Inline Yul execution | Unsupported | separate future language boundary | High |

## Historical frontend snapshot

| Internal component | State at freeze |
| --- | --- |
| Workspace identity and validation | Complete and proved |
| Multi lexer | Complete for the frozen token language |
| Multi chart parser | Total selected result and soundness for the frozen grammar |
| Structural validator | Complete executable/declarative correspondence |
| Source locations | Parser-wide validity and nesting proof complete |
| Retained tokens | Exact correspondence complete for all frozen grammar rules |
| Certified one-file frontend | Complete internal proof-carrying result |
| Fast parser | Finite schedule and terminal base only; full executor incomplete |
| Structural identity | Accepted design, no implementation |
| Module/name resolution | Proposed design, no implementation |

These rows describe the old grammar only. Canonical Syntax is implemented
separately and does not reuse this AST or parser.

## Public compatibility rule

Semantic Core v1, Semantic Core v2, Semantic Core v3, and Surface v1 are closed
algebras. Core Wire v3 and Oracle v5 publish the current checked language and
contract runtime without reinterpreting v1-v4. A later Core constructor outside
v3 must fail projection to every older wire that does not contain it. Any new
public tag or behavior requires an additive Core and Oracle version.

The public v5 boundary does not provide the frozen source frontend's missing
resolution, source typing, or elaboration stages. It also does not expand the
Static Word ABI into a general ABI; those remain separate rows above.
