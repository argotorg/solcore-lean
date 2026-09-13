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
| Block-statement diagnostic traces | Conditional exact raw required-tail block trace mapping, five statement execution contracts, joint exactness, and successful full-context preservation | Concrete recursive statement dispatch and whole-file traces remain separate | High |
| Identifier-expression diagnostic traces | Unconditional Boolean-first name and identifier-expression correspondence, full state updates, checked-name events, independent existence/exactness, and five expression contracts | Recursive expression layers and mixed statement/file composition remain separate | High |
| Protected statement trace normalization | Success/rejection composition through returns and raw/nested block statements, retaining complete fresh protected traces while filtering prior events | Final uncommitted reports and isolated-recovery reports are not presumed protected | High |
| No-trailing delimiter diagnostic traces | Conditional independent success/rejection exactness and execution correspondence for both empty policies, actual production fuel, arbitrary prior/reverse prefixes, comma priority, ordered duplicate expectations, and protected child suffixes | Child execution/frame laws remain explicit; token-carrier preservation is separate for ordinary success erasure; recursive expression and file traces remain separate | High |
| Array-literal diagnostic traces | Conditional five expression contracts, independent structure/exactness/protection, unchanged output-state and failure mapping, and concrete canonical identifier/literal-child consumers through return-only raw/isolated blocks | General recursive expression contracts and full-file trace composition remain separate | High |
| Leading-dot constructor diagnostic traces | Conditional exact optional-argument and raw constructor success/rejection, five expression contracts, Boolean-first name events before argument events, protected suffixes, unconditional absent/empty child bypass, and canonical success/rejection consumers | General recursive argument contracts and full-file traces remain separate; raw missing-dot rejection is separated from selected ordinary erasure | High |
| Parenthesized diagnostic traces | Conditional exact group/tuple and raw comma-tail success/rejection, after-first-child production fuel, reverse-prefix and prior-event preservation, protected suffixes, and canonical empty/group/tuple/closing-failure consumers | General recursive child and full-file traces remain separate; raw missing markers are separated from selected ordinary erasure | High |
| Proxy-expression diagnostic traces | Unconditional concrete five contracts, independent success/raw-rejection exactness, full-Failure propagation, protected suffixes, silent marker bypass failure, and independent-type reverse consumers | Raw type-bearing component; general expression and full-file composition remain open | High |
| Named-type finishing diagnostic traces | Unconditional exact AST and full-state success, independent event existence/uniqueness, bare-mapping canonical-form diagnostics with full argument span, qualified/other-name silence, and protected duplicate-preserving normalization | Finisher-only boundary; recursive type composition is covered separately | High |
| Optional lambda return diagnostic traces | Unconditional concrete five contracts and exact type success/rejection, independent joint exactness/protection, absent-arrow same-state success, and independent-type reverse consumers | Parameter recovery and full lambda/file traces remain open | High |
| Qualified-name diagnostic traces | Unconditional maximal checked-name success/rejection, five generic contracts, exact complete States and Failure, arbitrary raw prefixes/production fuel, protected ordered events, and canonical success/rejection consumers in every context/phase | Name-only boundary; recursive type composition is covered separately, whole-file traces remain open | High |
| Trailing-enabled list diagnostic traces | Conditional exact success/rejection, five generic contracts, both empty policies, comma-first/immediate-close priority, arbitrary reverse prefixes and actual production fuel, independent joint exactness, protected events, and canonical checked-name consumers | Conditional generic interface; concrete recursive types are covered separately, lambda parameters remain open | High |
| Optional named-type argument diagnostic traces | Conditional five contracts, exact optional/nonempty AST, silent whole-state absence/conversion, selected exact failures, independent joint exactness/protection, and canonical real-type-child success/rejection | Conditional raw interface; unconditional recursive type composition is covered separately | High |
| Raw named-type diagnostic traces | Conditional five contracts and exact name/argument/finishing event order, independent joint exactness/protection, complete component states and failures, and canonical mapping success/argument rejection | Raw interface omits dispatch guards; unconditional recursive type composition is covered separately | High |
| Raw mapping-type diagnostic traces | Conditional five contracts, exact contextual marker and AST spans, key/value event order, six first failures, independent raw/selected erasure and joint exactness/protection, canonical real-type-child success/closing failure | Raw interface assumes no child progress; unconditional recursive type composition is covered separately | High |
| Raw proxy-type diagnostic traces | Conditional five contracts, exact child AST/state/failure forwarding without extra frame premises, raw/selected rejection separation, joint exactness/protection, and canonical real-type-child success/failure | Raw interface; unconditional recursive type composition is covered separately | High |
| Raw comptime-type diagnostic traces | Conditional five contracts, exact contextual marker/angle/outer spans, four first failures, raw/selected rejection separation, joint exactness/protection, and canonical real-type-child success/closing failure | Raw interface; unconditional recursive type composition is covered separately | High |
| Raw tuple-type diagnostic traces | Conditional five contracts with trailing-list priority/progress, exact empty/singleton/multiple-element tuples, raw/selected rejection separation, joint exactness/protection, and canonical real-type-child success/separator failure | Raw interface; unconditional recursive type composition is covered separately | High |
| Optional function-return diagnostic traces | Conditional five contracts, silent whole-state absence, contextual marker and trailing-list outcomes, joint exactness/protection, arbitrary empty child bypass, and canonical real-type-child success/separator failure | Optional-clause interface; unconditional recursive function-type composition is covered separately | High |
| Raw function-type diagnostic traces | Conditional five contracts, exact parameter-before-return events and AST end span, full component States/Failures, independent erasure/joint/protection, and canonical real-type-child success/return failure | Raw interface; unconditional recursive type composition is covered separately | High |
| Recursive type success source/window frame | Unconditional full source and active-window preservation at explicit and production fuel, existing token-frame composition, and a deliberately noncanonical-carrier execution | Framing alone is not recursive diagnostic-trace soundness/completeness | High |
| One-layer type-dispatch diagnostic traces | Exact independent priority selection and six raw/final outcomes, ordinary erasure/joint/protection, conditional positive-fuel trace correspondence with unconditional framing, and keyword/contextual/window boundary consumers | One-layer contract alone supplies neither recursive completeness nor outcome existence | High |
| Type-trace relation monotonicity | Pointwise child implication lifts through trailing lists, all raw type forms, and dispatch with unchanged ASTs, remainders, events, and reports; protected-annotation erasure consumers | Infrastructure only; does not establish recursive completeness or outcome existence | High |
| Generic trace completeness bridge | Both soundness laws, independent exactness, and explicit invariant exclusion yield pointwise or unrestricted completeness; actual checked-name consumers and formal nonexistence countermodels | Does not supply invariant exclusion, independent exactness, or outcome existence for a new parser | High |
| Recursive type diagnostic-trace soundness | Fuel-free least closed success/rejection relation, fixed-point induction laws, unconditional explicit-bound and production soundness, successful ordinary/carrier erasure, protected events, and canonical three-level nested success/failure with arbitrary prior diagnostics | General expression, statement, and whole-file trace composition remain separate | High |
| Recursive type diagnostic-trace exactness | Heterogeneous agreement through lists/raw forms/dispatch closes independent recursive uniqueness and disjointness by strong induction; pointwise completeness under explicit invariant exclusion and valid-state full-failure equivalences | Joint exactness is uniqueness/disjointness; existence uses a separate execution argument | High |
| Unrestricted recursive type trace correspondence | Minimal end-index/progress/resource contract proves generic-list and raw-type totality on every State; production has all five trace contracts, full-Failure equivalences, separate trace existence, and noncanonical reverse consumers with arbitrary prior diagnostics | Does not complete general expression, statement, or whole-file traces; the minimal resource contract alone does not preserve diagnostics | High |
| Recursive type whole-State traces | Unconditional source frames and exact whole-State success/rejection equivalences; nested independent reverse consumers and separate token/end-index omission counterexamples | Cursor-only reconstruction requires explicit carrier/window equalities | High |
| Parameter-finishing diagnostic traces | Independent event existence, uniqueness, protection, exact AST/full-State execution, outer-comptime-only validation, specified missing-type constraints, and duplicate-preserving consumers | Finishing leaf; named-core composition is covered separately, public recovery remains open | High |
| Named-parameter tail diagnostic traces | Unconditional five contracts, ordinary execution, whole-State/full-Failure equivalences, independent exactness/protection, missing-colon error success, and nested reverse consumers with ordered type/finishing events | Raw tail; selected core and public recovery are covered separately | High |
| Parameter-name diagnostics and pair selection | Independent ordinary-name finishing and checked-prefix traces, exact continuation replies, raw/core source preservation, and shared window-aware pair reflection with duplicate/missing-token consumers | Prefix/selection laws; full named-core traces are covered separately, complete lambda parameters and public recovery remain open | High |
| Raw named-parameter diagnostic traces | Unconditional five contracts, ordinary execution, independent exactness/protection, all first failures, full-State/Failure equivalences, and same-input branch/ordered-event reverse consumers | Raw paths omit pair-selection guards and public recovery | High |
| Selected named-parameter core diagnostic traces | Unconditional five contracts, exact pair priority and whole-State/Failure equivalences, independent joint exactness, separate outcome existence, and protected reverse consumers on arbitrary inputs | Non-recovering core; public named rewind/recovery is covered separately | High |
| Lambda-parameter tail diagnostic traces | Unconditional five contracts, whole-State/Failure equivalences, exact typed retagging, inferred versus comptime missing-type outcomes, and ordered duplicate-preserving reverse consumers | Tail only; complete public lambda parameters are covered separately | High |
| Standalone parameter recovery diagnostic traces | Unconditional five contracts, independent joint exactness, complete State/Failure equivalences, mandatory consumption and boundary/missing-backing consumers, and conditional recovery-event filtering | Does not itself compose public core rewind or commit its caller's original report | High |
| Public named-parameter diagnostic traces | Unconditional five contracts, whole-State/Failure equivalences, independent exactness and separate outcome existence, cursor-only rewind, exact report commitment/recovery order, and conditional mixed-filter reverse consumers | Complete named-parameter slice; lists, general expressions, and whole-file traces remain separate | High |
| Raw lambda-parameter diagnostic traces | Unconditional five contracts, whole-State/Failure equivalences, all first failures, independent exactness/protection, and inferred/typed/marked-error reverse consumers | Raw forms omit pair selection and public rewind/recovery | High |
| Selected lambda-parameter core diagnostic traces | Unconditional five contracts, exact pair priority and State/Failure equivalences, independent exactness/protection, separate outcome existence, and nested ordered-event reverse consumers | Non-recovering core; public lambda recovery is covered separately | High |
| Standalone lambda-parameter recovery traces | Unconditional five contracts, whole-State/Failure equivalences, independent exactness, conditional filtering, and shared-fixture consumers proving AST-only retagging | Caller report commitment and public rewind are separate | High |
| Public lambda-parameter diagnostic traces | Unconditional five contracts, whole-State/Failure equivalences, independent exactness and separate outcome existence, cursor-only rewind, ordered report/recovery events, and inference/error-success reverse consumers | Complete parameter slice; lists are covered separately, lambda/general expressions and file traces remain open | High |
| Function and lambda parameter-list diagnostic traces | Unconditional five contracts, whole-State/Failure equivalences, independent exactness and separate existence, plus shared-carrier reverse consumers for trailing commas, ordered failures, mixed recovery, and invalid windows | Actual list parsers only; no signature/lambda-expression completion or unconditional cascade protection | High |
| Raw lambda-expression diagnostic traces | Body-conditional five contracts, full-State/Failure equivalences, independent exactness and separate existence, with ordered mixed-event, early-body-bypass, and concrete empty-Core-block consumers | Concrete parameters/returns but body-conditional raw composition; not complete recursive expressions or atom selection | High |
| Expression-atom dispatch selection | Independent eight-way priority, unique selection existence on arbitrary remainders, current-token observation congruence, exact raw Reply reflection, and all-branch/window/child-independence consumers | Selection only; not recursive trace outcome existence | High |
| Selected atom-core diagnostic traces | One-layer five contracts, exact priority, nested/body-conditional joint exactness, State/Failure equivalences, and separate rejection frames preserving full windows or only byte ends | No hidden validity/progress/ordinary premise; recursive totality and trace existence remain separate | High |
| Atom trace progress boundary | Concrete stationary children satisfy all five contracts, ordinary execution, and joint exactness, while a selected parenthesized atom reaches noProgress and has no independent trace outcome | Trace correspondence and uniqueness do not establish recursive progress or totality | High |
| Standalone expression-atom recovery traces | Unconditional five contracts, independent joint exactness, complete State/Failure equivalences, and reverse consumers for mandatory-first scans, missing/hidden tokens, duplicate events, and conditional filtering | Caller report commitment and public atom rewind remain separate | High |
| Public atom rewind/recovery diagnostic traces | Core-conditional exact State/Failure traces, weak frames, separate outcome existence, and concrete reverse consumers for ordered rewind/recovery, duplicates, missing backing, boundary reports, and mixed filtering | Conditional wrapper; recursive expression and whole-file completion remain open | High |
| Composed public atom-layer traces | Actual selected core plus recovery with nested/body contracts, weak rejected frames, and separate bounded actual/independent trace existence | One layer only; nested expression and body relations remain supplied | High |
| Unrestricted atom-layer totality | Raw tuple/group/dot/array and core/public ordinary execution from minimal child progress/budget contracts, with literal-child consumers for overshot/hidden/missing carriers and independent invalid-window group/tuple successes | Explicit loop/child bounds; no child validity/token/source/rejection frames; recursive expression totality remains separate | High |
| Changed-carrier atom trace consumer | Exact core/public Failure and State reconstruction when a child replaces tokens/endIndex and cursor-only rewind changes boundary observation | Demonstrates why rejected carrier preservation cannot be silently assumed | High |
| Maximal postfix-tail diagnostic traces | Independent prioritized index/call/field ASTs, seven failures, joint exactness, all-fuel soundness, derivation-threshold completeness, and pointwise whole-State/Failure equivalences | Child-conditional; threshold is not remainingCount; invariant exclusion and rejected source/end-byte frames stay explicit | High |
| Unrestricted postfix-tail totality | Minimal child endIndex/progress/bounded-ordinary contract gives explicit-budget and production ordinary execution, separate actual/independent trace existence, and fixed-fuel completeness with joint exactness | No source/token-storage validity; tail layer only, not recursive expression closure | High |
| Postfix progress/fuel boundary consumers | Stationary index succeeds while call reaches noProgress; a rewinding child has finite independent traces and five contracts but production fuel two fails where fuel three succeeds | Full-window frames, ordinary children, and trace exactness do not imply production adequacy | High |
| Concrete postfix-tail trace consumers | Literal-child reverse derivations fix mixed field/index/call ASTs, full States, ordered prefix events, later exact field failures, Boolean-name distinction, duplicates, and hidden/missing termination | Tail consumers with separately discharged production adequacy; not complete recursive expressions | High |
| Actual atom-plus-postfix diagnostic traces | Independent ordered composition, atom/nested joint exactness, observed soundness, pointwise State/Failure iff, and separate bounded actual/independent existence | Atom/nested contracts and invariant or endpoint-budget conditions remain explicit; no recursive expression closure | High |
| Concrete atom/postfix trace layer | Selected core, recovery, and postfix specialize independent joint exactness and both soundness laws to nested-expression/body relations | Explicit full-window child frames; no recursive closure or existence from joint exactness | High |
| Atom totality with bounded bodies | Raw lambda, selected-core, and public atom ordinary/no-invariant laws consume bounded expression/body contracts and two explicit input budgets | No global body totality; rejected window replacement remains allowed, so atom success-window contract is separate | High |
| Numeric-window atom contract composition | Numeric-only endIndex frames lift through raw/core/recovery; bounded child contracts and rejected endpoint preservation construct actual atom contracts up to both child successor budgets | No source/token/endByte/validity frame; conditional layer step, not recursive closure | High |
| Rejected-endpoint recovery consumer | Always-rejecting children have every fuel contract, yet a changed rejected endIndex becomes public success; independent reverse traces retain full State and ordered diagnostics | Demonstrates why child success-only endpoint laws cannot frame public recovery | High |
| Constructed postfix child contracts | Actual atom contract is built internally; numeric suffix frames and bounded children give ordinary execution, successor contracts, and separate child-only layer trace existence | Numeric totality and stronger trace context frames remain separate; recursive closure still open | High |
| Prefix unary scanning | Exact maximal operators and complete silent States, no rejection, unconditional production success, and separate independent existence on arbitrary carriers | Scanning only; postfix execution remains separate | High |
| Unary diagnostic traces | Independent exact wrapped ASTs and postfix event/report forwarding, four independently lifted contracts, separate success context, and weak-frame whole-State iff | Postfix-conditional; joint exactness does not establish complete-expression existence | High |
| Unary numeric contracts and existence | Actual postfix contracts lift at the same fuel, including constructed child contracts; bounded ordinary execution and soundness give separate actual/independent trace existence | Empty prefixes do not justify successor fuel; source/token/byte validity is not required | High |
| Concrete unary trace consumers | Reverse literal-child derivations fix prefix order around maximal postfix ASTs, complete States, ordered name events/duplicates, later reports, and minus/hidden/missing boundaries | Explicit rejecting body and one expression layer; not general recursive execution | High |
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
Raw block statements now inherit exact traces under explicit inner statement
laws. Their AST wrapper preserves the successful output state, while raw failure
propagates unchanged without isolation or report commitment. Independent
structural/exactness laws and successful full-context preservation are proved.
Expression names now have exact Boolean-first traces, with silent Boolean values
and located spelling diagnostics for checked identifiers. The actual identifier
expression fixes the full successful state and unchanged-state first failure,
and supplies unconditional execution and independent expression contracts.
Protected event lists compose through returns and raw block statements on both
success and rejection; executable filtering retains the complete fresh suffix
while independently normalizing prior events. Concrete nested break blocks and
canonical checked-name return fixtures verify inner failure propagation,
single outer recovery, and exact parent continuation. Final failure reports are
not included in the protected raw trace claim.

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
| Abstract resolved-name language | Local-expression foundation implemented (ADR-0154) | module/library-owned IDs, exact lookup, non-dangling references, and scope-relative fresh allocation; source declaration collection and global allocation remain open | Low |
| Resolved local typing and evaluation | Implemented for monomorphic unit/Boolean/Word, references, selected primitives, ordered unsigned Word less-than, immutable expression bindings, and conditionals | independent checker/elaborator correspondence, type preservation/reflection, exact value/store simulation, determinism and sufficient-fuel execution; no source spelling semantics | Low |
| Source type checking | Explicit-table local reference/Boolean/Word-literal/arithmetic/bitwise/unsigned `>`/`<`/`<=`/`>=`/Word equality/conditional fragment implemented | independent source typing iff checked elaboration; declarations, general literal typing, overloaded operators, general source types/effects remain open | Medium |
| Resolved scope and identity renaming | Complete for the local-expression fragment | scope iff elaboration existence; injective renaming preserves exact Core output, types, values, and store; non-injective capture counterexample; no source allocator claim | Low |
| Fresh local binding insertion | Implemented for explicit scopes | owner-relative non-collision, exact free-index weakening, type/evaluation preservation under inner binders; evaluation reflection requires original scoping, freshness covers only the supplied scope | Low |
| Explicit-ID ordered Word less-than foundation | Proved over existing resolved lets (ADR-0187) | exact Core wordLt lowering, Word typing, explicit-ID renaming and ordered evaluation with fresh first/distinct temporaries; second temporary may reuse an outer ID; reflection requires original right scoping; exact continuation paths add nine given the weakened right path, eleven for leaves; not canonical `<` support or general Core insertion | Medium |
| Exact local-Core environment insertion | Proved for the independent nine-form fragment (ADR-0188, pair extension ADR-0228) | retained-prefix positional weakening preserves/reflects identical successful values and stores without typing, original scoping, freshness or runtime-world premises; lowering membership is structural and acyclic; arbitrary existing values may return, but closure creation/calls and cell access are excluded; no full-state or exact-cost equality claim | Medium |
| Exact local-Core typing insertion | Proved for the independent nine-form fragment (ADR-0189, pair extension ADR-0228) | retained-prefix weakening preserves/reflects identical types and executable inference results, including rejection, under arbitrary data definitions and inserted/context types; no runtime inhabitant or extra well-formedness premise; does not generalize to reflection at clamped out-of-range insertion positions or excuse untyped skipped children | Medium |
| Exact local-Core cost insertion | Proved for the independent nine-form fragment (ADR-0190, pair extension ADR-0228) | one shared cost before arbitrary outer continuations; closed final paths transport/reflect at the exact length with identical value/stores and unconsumed continuation; original and shifted suspended states may differ; no type, scope or runtime-world premise, new cost relation or canonical `<` support | Medium |
| Binary pair local-fragment prerequisite | Proved without changing Core semantics (ADR-0228) | both pair children are local, ordered actual values/stores and L+R+3 cost survive insertion/reflection under arbitrary retained prefixes/continuations; original typing/inference/path APIs retain their premises, actual checkpoints keep their own frames/environments; no Resolved/source tuple acceptance, projection support or wire-policy change | High |
| Resolved binary products | Implemented with exact ordered correspondence (ADR-0229) | pair syntax and independent lowering/product typing/whole scoping/raw evaluation retain original child scopes, actual values and ordered stores; 54 affected generic contracts preserve names/premises across checking, Core execution, renaming, freshness and reflection; duplicate/nominal/opaque and raw/whole boundaries remain explicit, no new runner or canonical tuple/wire acceptance | High |
| Canonical binary tuple expressions | Implemented with exact original-syntax semantics (ADR-0230) | exactly two written children resolve/type/evaluate as ordered products in the original scope, actual values and L+R+3 costs agree with direct execution and independent Core paths; 80 existing proof contracts retain names/premises, explicit nesting/grouping/trailing commas and named-product function returns preserve parameter gates; empty tuples follow separately in ADR-0231; manual-singleton/larger tuples, tuple types, projections, multiple returns and frozen wire formats remain outside this change | High |
| Canonical empty tuple Unit expressions | Implemented with exact one-step constant semantics (ADR-0231) | original empty tuples independently resolve/type/avoid names/evaluate without caller lookup, actual typing or alignment; cost and source bound are one with the same store; all 80 generic expression proof contracts remain unchanged (56 in 25 changed production modules); independent source/parsed/entry consumers cover Unit versus binary products, strict lets, aliases, unused-argument gates and real checkpoint resumption; no reserved Unit spelling, tuple type/header expansion, parser/diagnostic/Core/resolved or wire change | High |
| Opt-in canonical structural product types | Implemented as an independent prerequisite (ADR-0232) | original named/empty/singleton/binary tuple types have independent meanings and exact total interpretation, ordered nesting, caller lookup/extensionality and semantic extension proofs; old named-only API including whole-result membership is unchanged; source/parsed consumers separate non-inhabited nominal types and strict unknown leaves; return, parameter and recursive-let integration follow in ADR-0233/0234/0235, larger tuple types in ADR-0236; older prefix lets, other type forms and frozen interfaces remain unchanged | High |
| Structural single-return annotations | Implemented at the existing shared entry gate (ADR-0233) | one original annotation uses independent structural meaning; Unit/singleton/ordered nested products reach unchanged compile/prepare/run with exact Core, strict body costs, parameter-only records and real resumption; seven generic header/extension and 110 affected legacy source-test contracts stay unchanged in this slice; absent Unit, empty/multiple clause rejection and all other entry/wire boundaries remain; parameters and recursive lets follow in ADR-0234/0235 | High |
| Structural parameter annotations | Implemented atomically in static and actual adapters (ADR-0234) | four constructor premises and two position conclusions explicitly widen; original parameters each retain one row/ID/typed actual without product flattening or Unit erasure; general erase/restore, factorization, source order, sparse owner allocation and named specialization contracts remain; independent nominal/opaque, parsed whole-entry Core/cost/store/resumption coverage; four parsed negatives become positives and one source boundary is explicitly renamed, with 152 other affected source-test statements unchanged; recursive lets follow in ADR-0235 | High |
| Structural recursive let annotations | Implemented at the existing recursive body/entry gate (ADR-0235) | two binding premises and one decomposition conclusion explicitly widen, with 15 other affected generic statements preserved; strict old-scope initialization, fresh tail-only binding, complete arm checking and exact Core remain; independent arbitrary-depth and parsed consumers check nominal/opaque values, extension, eight-step unused product initialization and real resumptions; three old declarations across eight actual vectors become positives, 106 legacy source statements stay unchanged and one old named-only/prefix boundary is explicitly renamed; raw evaluation, bounds, Core, diagnostics and wire remain unchanged | High |
| Arbitrary finite structural tuple types | Implemented through the shared annotation adapter (ADR-0236) | a new many rule retains all four old rules and 13 generic contracts; same-table meanings fold right without a terminal Unit or flattening explicit children; independent arbitrary-length, strict-missing, span/lookup/extension and nominal proofs plus parsed original-range/one-actual/entry Core-cost-store-resumption consumers; three parsed rejection claims become positives, two obsolete source boundaries are explicitly renamed and 26 other source statements retained; expression tuple arity, old named-only membership, multiple clauses and runtime/parser/wire policies remain unchanged | High |
| Arbitrary finite canonical tuple expressions | Implemented through the existing expression and entry adapters (ADR-0237) | five independent many rules retain all 80 generic contracts and original scopes/spans; right-associated pairs have no implicit Unit tail or explicit-child flattening; exact three/four-leaf costs are 9/13 and strict unused four-element initialization plus return costs 16; arbitrary-length source and parsed consumers retain exact Core, first matches, nominal/opaque boundaries, raw/whole separation and actual checkpoint/residual execution; five parsed rejections become positives and one obsolete source boundary is explicitly narrowed/renamed with ten other statements preserved; manual singleton nodes, projections, inference, shadowing, multiple clauses, Core/Resolved, parser, diagnostics and wire remain unchanged | High |
| Inferred initialized local bindings | Implemented in the recursive body and existing function entry (ADR-0238) | original absent annotations stay absent; initializer typing and exact Core use the old scope, fresh tails retain the inferred type without whole-type table membership; four inferred rules retain old annotated constructors and all 53 affected generic statements, with a new exact child-decomposition theorem; independent mixed-prefix/parsed consumers retain nominal/opaque boundaries, strict costs, original parameter records and genuine residuals; eleven parsed rejection claims become positives, older prefix and neighboring invalid boundaries remain; no general inference, default initialization, assignment, shadowing, Core/Resolved, parser, diagnostic or wire change | High |
| Exact frontend local-fragment provenance | Proved without changing source acceptance (ADR-0239) | four body-level and four entry-level bridges derive membership from exact lowering and complete source children, not same-type replacements or arbitrary records; independent source/parsed consumers compose existing typing/value/exact-cost insertion under retained prefixes and nested lets, preserving nominal static types and actual opaque values; captured environments can differ, with original and inserted checkpoints resumed separately; no evaluation or valid-index guarantee from membership alone, and no definition, generic contract, parser, diagnostic or wire change | High |
| Strict expression-statement prefixes | Implemented through existing recursive bodies and entries (ADR-0240) | explicit semicolon and strict original head/tail order; no source binding or parameter row, exact hidden Core let weakens only the original tail; four discard rules retain previous constructors and 58 generic contracts, with one exact decomposition; insertion/reflection preserves typing, values and costs at head+tail+2, independent mixed/parsed consumers and four original rejection-to-success migrations retain scopes and genuine residuals; no missing-tail, unterminated-prefix, assignment, call, early-return, Core/Resolved, parser, diagnostic or wire policy change | High |
| Terminal lexical block wrappers | Implemented through recursive bodies and existing entries (ADR-0241) | original inner list/span and caller scope retain exact child Core/type/value/stores/cost with no extra binder or transition; four block rules preserve old constructors and 59 generic contracts, with full-Option wrapper/child equality; independent finite-depth source/parsed consumers retain mixed scopes, nominal/opaque boundaries, parameter rows and identical genuine checkpoint states; six legacy parsed consumers migrate original block fixtures, including six buried nominal declarations, while empty/nonterminal blocks, scope escape, shadowing, implicit/general early returns and narrower adapter boundaries remain unchanged; no Core/Resolved, parser, diagnostic, wire or runtime-record change | High |
| Static single-argument local function application | Implemented as a separate opt-in prerequisite (ADR-0243) | known Function arity-one builtin case, both original pure children and caller scope yield exact Core.apply with independent whole typing/provenance, complete checker correspondence and uniqueness; nominal static contexts need no runtime values, Unit/products stay one argument; old pure/body/entry acceptance is unchanged, and no general Invokable/global resolution, nested call, source lambda, runtime-call relation, store/fuel guarantee or Core/parser/wire change is implied | High |
| Actual local function application evaluation | Proved for the separate original-call profile (ADR-0244) | independent raw/cost rules retain caller-evaluated children, actual closure annotations/body/captures, actual argument and all stores; erasure, cost existence and value/store/cost uniqueness, with exact provenance and ordered-ID Core correspondence both ways; child+actual-body+3 cost is uniform under every retained continuation, without pending-frame completion, structural-typing allocation, store independence or source-only bound assumptions; no source-call evaluator, entry integration, runtime-world safety or executable-definition change | High |
| Runtime-world safety for actual local applications | Proved with explicit actual environment/store premises (ADR-0245) | same-world typing includes captures, allocated locations and allowed store payloads; original whole typing yields successful exact cost and runtime-typed result/final store in an extending world, exact provenance gives uniform paths and closed fuel thresholds, and supplied raw/checked completions preserve typing; typed continuations and genuine checkpoints retain all-fuel fault exclusion without source-ID requirements for state-only claims; existing restricted Core reducibility, no arbitrary-store/source-bound claim, evaluator/entry integration or executable-definition change | High |
| Checked local application execution | Implemented separately on actual LocalInputs (ADR-0246) | exact static checking and full-result execution with the same values/store; absence iff static rejection, completion at some fuel iff whole typing plus independent raw evaluation, actual-cost fuel thresholds, genuine residual paths and full-tag/full-result resumption; explicit runtime-world premises yield typed completion, a sufficient actual cost and all-fuel fault exclusion; missing cells and wrongly typed payloads remain observable, old pure/body/entry acceptance unchanged, no direct source-call evaluator or world validator | High |
| Singleton application-return body | Implemented as a separate opt-in body (ADR-0247) | original block/return/child syntax with independent whole typing, exact elaboration and raw/cost rules; static and closed Core correspondence, uniform continuation paths, full-Option child/body checker and runner equality at all fuel/store, exact whole-body outcome factorization and typed-cost reflection; no extra transitions or changed checkpoints, existing runtime-world/resumption laws transfer, old pure/recursive bodies and whole entries remain unchanged | High |
| Explicit application-return function entry | Implemented as a separate whole-entry profile (ADR-0248) | original header/parameter/exact-body provenance for value-free compilation and actual preparation, declared return agreement, exact success/rejection and record uniqueness; full-Option compilation/preparation factorization with ordered argument guard, full-result entry/body and compiled execution on actual values reversed once; same-typed swaps remain distinct actual inputs, body cost/resumption/runtime-world guarantees transfer, old endpoints and data records unchanged, no global source-call or closure construction semantics | High |
| Exact insertion for checked application Core | Proved from exact child provenance (ADR-0249) | arbitrary retained-prefix caller slot, literal actual closure/argument/body/captures and stores; raw and typing equivalences, paired uniform-cost paths and exact closed-path insertion/reflection; no runtime-world/inhabitation/source-ID assumptions, intermediate checkpoints need not agree, retained continuations need not be final, closure-producing children excluded; no new relation or executable change, recursive mixed-body closure remains separate | High |
| Shared pure-or-application computation child | Implemented with independent semantics (ADR-0250) | nonrecursive union preserving original root/children, exact checker and whole typing, independent raw/cost with zero wrapper cost, joint outcome/cost determinism, same-ID raw/Core and fixed-cost correspondence, uniform paths and three caller-insertion kernels; old pure/application checkers unchanged, no general nested expression or standalone body/entry integration, no inherited store/source-bound/total-evaluator guarantees | High |
| Mixed local-computation bodies | Implemented with independent semantics (ADR-0251) | original bare/expression returns, terminal blocks, typed/inferred lets, strict discards and terminal if/else with pure or root-application children; exact syntax/scope/Core/type, actual intermediate stores and returned callables, recursive caller-fragment weakening and raw/cost insertion, whole checker/typing and exact Core/cost correspondence, unchanged pure embedding; old entries unchanged, no nested expression calls, general early returns, source-only bound or arbitrary-store safety | High |
| Explicit mixed-computation function entry | Implemented with four shared contracts (ADR-0252) | original header/ordered parameters/declared return and independent exact mixed-body compilation/preparation; value-free checking and same actual bound record, exact-record Some iff and full-Option compile/type-guard factorization, actual values reversed once with all faults/checkpoints retained; same-typed swaps remain observable, old pure/application successes embed one way with old endpoints unchanged, runtime-world evidence still required for safety | High |
| Recursive local computation expressions | Implemented with independent semantics (ADR-0253) | original nested single-argument calls, computed callees and zero-cost groups around pure leaves; fourteen shared checking/typing/raw/cost/Core/embedding/insertion kernels retain actual captures and ordered effects, pure/group overlap and arbitrary inserted caller values; old endpoints unchanged; direct binary recursion and shared body/entry integration are recorded below; no source closure construction, source-only bound or arbitrary-store safety | High |
| Shared bodies with recursive computation children | Implemented with twelve shared proof kernels (ADR-0254) | separate child checker/typing/elaboration/raw/cost parameters and concrete recursive specialization; original typed/inferred lets, strict discard, terminal blocks/if/returns retain scopes, owner-filtered fresh IDs, actual values/stores and exact costs; unit/leaf/let/if closure handles whole-tail literal insertion before every continuation, old mixed elaboration/cost embeddings preserve all indices; existing whole-function endpoints unchanged, no general early return, source closure, source-only bound or arbitrary-store safety | High |
| Shared explicit recursive-computation entries | Implemented with four shared proof kernels (ADR-0255) | original Header/Declare/actual Bind/body/declared-return provenance, separate child checker and elaboration parameters, exact-record Some iff with child correctness and full-Option compile/type-guard/actual-run factorization for arbitrary checkers; recursive specializations retain actual values reversed once, supplied stores, same-typed swaps, declared tags, faults and genuine checkpoints; old endpoints unchanged, no source closure/global resolution, store validation or arbitrary-store safety | High |
| Recursive direct Word binary computations | Implemented with unchanged recursive contracts (ADR-0256) | independent finite ten-tag operator relation/map correspondence; original children/spans/scope, exact Word operand and Word/Bool result checking, actual left-to-right stores then primitive application with child costs plus three, private pure/binary overlap, literal caller insertion and uniform paired costs; existing fourteen proof signatures and shared body/entry definitions unchanged, explicit old-addition fixture migration, nonrecursive endpoints still reject nested operators; conditional/unary/fixed-lazy/ordered/negated-comparison and tuple recursion are recorded below; no generic operator-class resolution or arbitrary-store safety | High |
| Recursive conditional computations | Implemented with unchanged recursive contracts (ADR-0257) | original Bool guard and both written branches retain exact scope/spans/Core and common type; raw evaluation uses actual Bool and selected branch only, actual intermediate stores and guard-plus-branch-plus-two cost; seven constructors with private pure overlap, unchanged fourteen proof signatures and shared body/entry code; literal insertion, original ternary fixture migrations, returned/computed callables, actual guard/selected effects, faults and genuine ifBranches checkpoints; unselected static rejection remains compatible with raw success, old endpoints unchanged, no source-only bound or arbitrary-store safety | High |
| Recursive direct unary computations | Implemented with unchanged recursive contracts (ADR-0258) | original prefix spans/order and operand retain exact fixed Bool negation or Word complement Core; independent static/raw/cost rules use actual payloads, child final stores and cost plus two; nine constructors with private pure overlap, unchanged fourteen proof signatures and shared body/entry code, literal caller insertion and uniform paired costs; original well-typed unary fixtures migrate while wrong types and old endpoints stay rejected, actual effects/faults and genuine unaryApply resumption remain observable; no generic overload resolution, source-only bound or arbitrary-store safety | High |
| Recursive fixed short-circuit computations | Implemented with unchanged recursive contracts (ADR-0259) | original Bool-checked children and fixed conditional expansion with internal constants; actual left Bool selects arbitrary right value/store at child costs plus two or skips at left cost plus three; twelve constructors, unchanged fourteen signatures and shared body/entry code, no new caller-fragment or insertion rules; original three rejection cases migrate exactly, effects/faults and genuine ifBranches resumption remain observable, selected Word payload can retain declared Bool entry tag; not general Rust named-operator resolution, source-only bounds or arbitrary-store safety | High |
| Recursive negated Word comparisons | Implemented with unchanged recursive contracts (ADR-0260) | original Word-checked children retain exact Bool negation of ordered equality/greater comparison, actual left-to-right stores and both child costs plus five; eight constructors and unchanged fourteen signatures, cost determinism/private overlap relocation with old import preserved, no new caller-fragment/insertion rules or shared body/entry changes; original two rejection fixtures migrate exactly, right effects precede wrong-left-payload comparison failure, distinct binary/negation checkpoints and full resumption; ordered less/greater-equal recursion follows below; no general named ne/le resolution, source-only bound or arbitrary-store safety | High |
| Recursive ordered Word comparisons | Implemented with unchanged recursive contracts (ADR-0261) | original Word children retain left-to-right evaluation in exact positional two-let Core, with optional outer Bool negation and child costs plus nine/eleven; eight source constructors and generic caller letE preserve fourteen signatures, arbitrary-prefix literal insertion and one cost before every continuation; right recursive calls need no call-free membership, saved values/captures/stores and full generated-binding checkpoints remain exact; cost definition split preserves old imports, shared body/entry unchanged, original rejection fixtures migrate intact; recursive tuples follow below; no source closures, general named lt/ge resolution, source-only bound or arbitrary-store safety | High |
| Recursive canonical tuple computations | Implemented with unchanged recursive contracts (ADR-0262) | original binary/longer lists retain same-scope arbitrary component types and actual values in right-associated Core, with unchanged spans/tail decomposition and no terminal Unit; eight source constructors and generic caller pair preserve fourteen signatures and shared body/entry definitions, exact left-to-right stores and three transitions per pair, literal insertion and one cost before every continuation; six original source/caller rejection fixtures migrate intact, independent arbitrary-length/parsed/entry consumers check saved pair frames, effects, strict child faults and full resumption; empty stays pure and singleton parentheses stay groups, no manual-singleton/source-closure/global-resolution expansion, source-only bound or arbitrary-store safety | High |
| Shared computation runtime-world safety | Proved with three generic kernels (ADR-0263) | original body and entry evidence plus actual same-world environment/arguments/store yield an extending runtime-typed final result and original-source cost, uniform continuation-local paths and exact closed fuel thresholds; private reverse-once argument bridge retains exact preparation/full runner results; typed pending frames preserve the actual checkpoint and all-fuel resumed no-fault without source-ID or child execution premises, with checkpoint worlds existential; old fourteen/twelve/four contracts and executable definitions unchanged, missing/corrupt/structural-only/incompatible-world boundaries retained, no source-only bound or arbitrary-store safety; executable premise validation follows below | High |
| Actual typed runtime-input validation | Implemented with one Bool validator and exact iff (ADR-0264) | checks every original typed argument's actual references/captures and the complete supplied store in one explicit world; existing structural argument evidence supplies closure body typing, with no extra unused-signature/sum-alternative restrictions; strict world/store length and all CellPayload/value-type rows include unreferenced cells; success supplies the two runtime premises of existing shared entry safety without changing original preparation or full runner results, no raw/JSON validator, world inference/repair, new runner or automatic guard | High |
| Exact structural runtime-argument construction | Implemented with one Option builder and exact-record iff (ADR-0265) | preserves literal raw Core values, unique tags and full evidence-carrying records; ordinary list traversal retains original order/preparation/full runner results, actual closure bodies use existing inference under actual captured types and all unused/nested captures are checked; no extra signature/unselected-type well-formedness, malformed bodies/host/empty-definition constructed values rejected, structural cell references retain separate supplied-world/store validation; no JSON decoding, value repair, source closure expansion or automatic entry guard | High |
| Extending worlds at genuine computation checkpoints | Proved with one shared theorem (ADR-0266) | original body typing, actual same-world inputs and typed pending frames plus exact outOfFuel yield a saved store world extending the original, with further extension along every finite path from that same saved state; old locations/types persist through typed writes and allocation, actual values may change; private world uniqueness and two mutation cases reuse old state preservation, unrelated typed states/equal-length separately typed stores are insufficient, old checkpoint no-fault and executable definitions unchanged | High |
| Terminal single-Word literal matches | Implemented through the shared body engine (ADR-0267) | one original Word scrutinee, ordered strict in-range literals with duplicate first-match priority and required default for literal-only cases; all original bodies share caller scope/result typing, only the selected body executes after scrutinee effects; hidden Core let plus seven transitions per visited comparison, old checker/typing/raw/cost/insertion signatures retained; arbitrary case counts, actual captures/stores and genuine resumption; default-only raw non-Word success is distinct from nonempty comparison fault; broader patterns and overflow agreement remain separate | High |
| Ordered wildcard cases in Word matches | Implemented in the same shared body engine (ADR-0268) | original `case _` with exact marker spans chooses the first reached body without binding/comparison, while every later case/default remains statically checked; tagged entries distinguish wildcard success from failure and discard only the checked Core tail; scrutinee once and hidden let cost two, seven per executed literal test and zero for wildcard; arbitrary actual-value leading success is distinct from preceding literal non-Word fault, captures/stores/full resumption and old theorem contracts retained; initial Word-only restriction generalized for catch-all-only matches in ADR-0271, no general exhaustiveness or binder semantics | High |
| Original optional Word match defaults | Implemented through the same body/entry contracts (ADR-0269) | original None retained throughout; static acceptance requires original default or wildcard, with all branches checked at the default or first original body's arbitrary result type; wildcard recovers an absent literal-only Core tail without fabricated source/Core fallback; raw literal-hit success remains distinct from coverage and empty cases without a default reject; dedicated checker decomposition, old shared12/recursive14/entry4 signatures retained with explicit Option generalization of choice/match constructors; arbitrary prefixes, actual effects/captures, nested scopes, exact costs and genuine checkpoint/world resumption | High |
| Transparent original Word pattern groups | Implemented through the same pattern/body/entry contracts (ADR-0270) | arbitrary group depth and each original outer/inner span retained, including singleton trailing commas; independent literal/wildcard classification and exact total-interpreter iff, grouped wildcard coverage and every unselected pattern/body checked; same Core fold, zero grouping transitions and seven per visited literal comparison, actual effects/captures/stores and genuine resumption; old shared12/recursive14/entry4 and strict literal meaning retained with explicit classification-premise changes; tuple/binder/Boolean/constructor/comptime/error and overflow boundaries unchanged | High |
| Type-general catch-all-only matches | Implemented through the shared body/entry engine (ADR-0271) | independent scrutinee/result types supported by existing children, original default-only or bare/grouped wildcard rows with present/absent defaults; all original rows checked, non-Word with any unreachable Word literal rejected, empty/no-default still rejected; unchanged Core fold/raw/cost rules with once-only scrutinee effects and two hidden-let transitions; arbitrary rows/actual payloads, Bool effects and nested Bool/function slots retain captures, stores and genuine resumption with separate runtime-world evidence; match constructors/checker decomposition generalize while shared12/recursive14/entry4 remain unchanged, without adding nominal construction or global/pattern resolution | High |
| Unary structural function type annotations | Implemented through existing annotation gates (ADR-0272) | exactly one original parameter, absent/empty Unit returns and singleton/right-associated multiple returns; independent recursive meanings preserve original AST/ranges/lists, first-match leaves and thirteen old contracts; parsed parameters, recursive typed lets and single outer function-valued return annotations retain actual closures/captures, effects, exact costs, faults and genuine resumption with separate world evidence; zero/multiple-parameter function types and local calls, outer empty/multiple return clauses, named-only adapters, source lambdas and global resolution remain unchanged | High |
| Scoped shared-computation let shadowing | Implemented with a conservative terminal-if boundary (ADR-0273) | original typed/inferred initializers use old inputs before fresh-ID prepend; repeated/parameter spellings and changed types retain every old row/value/capture; independent exposed-name predicate and exact Bool guard protect parent names across bare then traversal, inspect both nested if arms and stop at explicit blocks/match scopes; terminal else shadowing allowed, then-only new names still unavailable to else; unchanged Core/raw/cost and shared12/recursive14/entry4 contracts, old fresh-name endpoints and duplicate-parameter rejection retained; original three fixture migrations, arbitrary repetitions, exact actual effects/faults and checkpoint/world resumption, no general source resolver or nonterminal sequencing | High |
| Shared computation type-table transport | Proved with twelve additive laws (ADR-0274) | independent body typing/elaboration and exact compiled/actual prepared/full runner results retain original source, every branch, IDs, Core and captured values under first-match meaning preservation; one-way success versus mutual whole-Option equality for the same arbitrary child checker, hidden duplicate rows allowed; unknown unselected annotation repair and meaning-changing prefixes remain explicit boundaries; independent symbolic/parsed costs, effects, faults and genuine checkpoints, no admission change or runtime-world inference | High |
| Recursive local computation identity relabeling | Proved with five additive laws (ADR-0275) | independent elaboration/typing, complete optional checker and raw/cost iff retain original AST, positional Core, types, literal values/captures and all stores under simultaneous injective LocalId maps; duplicate rows and non-surjective owner/index changes allowed without inverse or runtime inhabitants; raw skipped/untyped success remains separate from whole acceptance and fault classification; non-injective first-match collapse and fresh body allocation are separate boundaries, all existing definitions/contracts unchanged | High |
| Shared computation body owner covariance | Proved with three additive generic laws (ADR-0276) | independent elaboration/typing iff and whole optional checker equality under fixed-child covariance; original AST/type table/Core, fresh binder indices, sparse foreign rows, repeated spellings, scope guard, all branches and match defaults retained without inverse or surjectivity; same-Core actual execution comparisons do not infer raw-body covariance, child correctness or runtime safety; general index maps and function/header owner integration remain separate, all old contracts unchanged | High |
| Shared raw computation body owner covariance | Proved with two additive generic laws (ADR-0277) | independent raw/cost iff under each fixed child's own covariance; original AST/selected body/comparison count and literal values/stores/costs retained on arbitrary duplicate or misaligned rows; fresh IDs use only names even with environment-only collisions, no row repair, checker/typing/world/inverse/cost-bridge premise; raw success/absence remains separate from whole acceptance and fault classification, checked Core paths require separate original evidence | High |
| Shared computation function owner covariance | Proved with five additive generic laws (ADR-0278) | independent compilation/preparation iff, complete optional compiled/prepared input-ID maps and full same-fuel/store runner equality under one injective owner map and each fixed child's own covariance; original parameter/argument order, indices, AST/ranges, Core/type, actual values/captures retained; private parameter reflection without inverse or all-maps covariance, no checker-correctness/runtime-safety claim; preparation absence and actual faults/checkpoints remain distinct, old definitions/contracts unchanged | High |
| Independent shared function argument factorization | Proved with five additive generic laws (ADR-0279) | arbitrary independent child elaboration, preparation erasure and reconstruction from supplied typed arguments, exact fixed compiled-projection iff, reverse-once actual values and same-arguments/same-projection uniqueness; no checker graph, child determinism, invented inhabitants or runtime world; same-typed values/captures can change prepared records/effects, artificial nondeterminism and invalid-record boundaries explicit, old operational laws and source admission unchanged | High |
| Minimal prepared-function checkpoint safety | Proved with two independent entry laws (ADR-0280) | original preparation and child Core typing plus actual arguments/store/typed caller frames in one world give exact initial/saved-state typing and all-fuel resumed fault exclusion; genuine saved worlds extend the original and every further finite path extends that same saved world, including caller allocation/writes and a different caller result type; no checker/source-cost/fragment/ID-alignment premise, termination or acceptance conclusion, old contracts unchanged; common-world premises are sufficient, not necessary for each terminating run | High |
| Expected-type unary lambda headers | Implemented as a standalone type-only foundation (ADR-0281) | one original runtime parameter inherits or checks the explicit function domain, omitted return annotation keeps the expected codomain; one owner-filtered fresh inner row shadows and preserves outer rows, first-match annotation meanings and original body/spans retained; one declarer and four independent exactness/absence/uniqueness/provenance laws, no inhabitants/Core/closures/body checking, recovery judged by actual AST; old lambda rejection and insertion contracts unchanged, expected-type propagation and closure semantics remain separate | High |
| Expected unary computation lambda elaboration | Implemented as a standalone opt-in adapter (ADR-0282) | original expected header, both component well-formedness guards and original shared body at the expected codomain produce a literal Core lambda; independent exactness/absence, child-typing-only Core preservation and retained provenance, no runtime inhabitants or blanket outer-context well-formedness; captured positions/shadowing and Core-only delayed effects tested, no source operational/backend execution claim, old recursive/function lambda rejection and insertion contracts unchanged | High |
| Independent expected lambda source typing | Proved for the standalone profile (ADR-0283) | original header/component guards/shared body HasType define source-only typing without Core output, existential elaboration or checker graph; typing iff elaboration existence needs only child typing correspondence, checker-result existence adds only exact child checking; no determinism, child Core typing, inhabitants or source-only type uniqueness, old executables/admission/runtime contracts unchanged | High |
| Explicitly typed lambda-let initializer | Implemented as an opt-in original-head adapter (ADR-0284) | original annotation meaning supplies the expected lambda type before the let binder enters scope; untouched shared tail alone uses bindFresh, including same-name captures and disjoint-scope fresh-ID reuse; independent source typing, elaboration/checking correspondence, Core preservation and exact head/tail provenance, with actual-capture/effect/checkpoint Core consumers; no inferred-let nominal inference, later-lambda recursion, old-entry admission or raw source execution change | High |
| Maximal consecutive typed-lambda let prefix | Implemented with disjoint source-only dispatch (ADR-0285) | pure original direct-lambda head classification, sequential pre-binder initializers and fresh recursive tails; true-head failure never falls back, first non-head delegates the whole unchanged shared body without restart; independent source typing/existence, exact checking, Core preservation and one-layer provenance, arbitrary prefix consumers and explicit generic-child non-embedding boundary; no old-entry or raw source-runtime change | High |
| Mixed frontend value representation | Implemented with exact Core retraction (ADR-0286) | recursively mirrored Core values and mixed Core captures, original source code/owner/ordered name-ID-value rows as unrestricted inert data; total embedding, roundtrip, exact successful image and injectivity, source subterm rejection even in unused captures/raw slots, references never dereference; no total source type, elaboration, evaluator, admission change or runtime safety | High |
| Independent raw source closure creation and call | Implemented as a parametric unary profile (ADR-0287) | original unmarked unary shape/decoder, exact full captures and unchanged creation store, caller callee-then-argument sequence followed by saved original body with names-only fresh parameter rows; exact creation/call decomposition and separate callback determinism, arbitrary mixed values/current stores, no annotation/staging judgment, recursive callback closing, Core/host dispatch, unsuccessful-effect classifier or runtime safety | High |
| Original computation bodies over mixed values | Implemented as a separate raw family (ADR-0288) | original nine body forms and four ordered choices, names-only fresh binding after initializer, actual mixed captures/stores and selected branches; choice/count and conditional body determinism, one-way old embedding and stronger all-actual-image reflection, genuine discarded-closure counterexample to endpoint-only agreement; open expression callbacks, no whole-language conservativity, canonical name alignment, executable costs/faults or safety | High |
| Recursively closed original source evaluation | Implemented for eight expression and nine body forms (ADR-0289) | explicit mutual owner-indexed judgments, original source capture and unary higher-order calls, literal lexical rows and tuples; exact open-body/unary-call compatibility, unconditional value/store determinism and successful-store invariance consumers; no supplied callbacks, Core/host dispatch, mutation, general canonical name/staging correspondence, total executable runner or safety | High |
| Executable closed source search | Implemented with soundness and eventual completeness (ADR-0290) | original expression/body depth-bounded functions, exact ordered selector body/comparison-count iff, every finite successful derivation found at all sufficiently large depths with literal actual endpoints; zero/insufficient depth and unsupported paths share none, self-application absence consumer, no general termination/divergence classifier, Core fuel/cost, resumption, mutation, Core/host dispatch or runtime safety | High |
| Original closed source conditional expressions | Implemented in the same judgment/runner family (ADR-0291) | actual Bool guard and only the selected original branch, independent marker ranges and actual intermediate store, same predecessor depth, unconditional determinism/compatibility/soundness/eventual completeness retained; exact decomposition/equation, arbitrary nested-depth and saved-capture consumers, actual returned parsed closure/store reuse; old ordinary headers/body rules retained but generated recursors gain cases, no universal old-none preservation, canonical typing, effects or termination guarantee | High |
| Closed source depth monotonicity and exact thresholds | Proved without changing existing execution (ADR-0292) | actual successful expression/body endpoint preserved at every larger budget, larger none implies smaller none, independent finite derivation gives positive hole-free full-Option threshold; original source/owners/captures/stores retained, independent direct boundary consumers, all old implementation/headers/constructors/recursors unchanged; no none-upward, total minimum finder, cost, source-size bound or termination classifier | High |
| Closed source data/Core image correspondence | Proved on independent common syntax (ADR-0293) | seven-form original syntax gate, all actual value/whole-store images from arbitrary embedded Core inputs, exact Local iff and explicit whole-resolution/runtime-ID Core iff; duplicate/foreign rows and opaque payloads retained, independent original/actual-result consumers; no gate success guarantee, maximal dynamic overlap, operators, creation/calls, body-wide correspondence or old implementation change | High |
| Closed source data-body/Core image correspondence | Proved for original terminal bodies (ADR-0294) | independent seven-form syntax gate covers nine raw body rules with all written branches; full actual value/store image iff to generic-local bodies and separate existing whole-checker/exact unique-ID Core iff; pre-shadow initialization, raw duplicate/foreign rows and opaque payloads retained; no endpoint-only shortcut, gate success guarantee, added runtime-typing premise, source creation/calls, effects, totality or old implementation change | High |
| Checked data-lambda invocation/application | Proved for expected unary lambdas (ADR-0295) | actual caller prefixes and exact saved-owner/capture/ordered-ID body image; separate direct original application iff with whole-resolved/lowered gated argument; every actual value/full store, opaque Core payloads and mixed caller rows retained; independent original and parsed returned-closure witnesses; no whole-call typing, source/Core closure identification, broader gates, effects, totality or old implementation change | High |
| Original closed unary primitive evaluation | Implemented for actual Bool logical-not and Word bit-not (ADR-0296) | original operand/operator spans, saved lexical rows and full actual stores retained; four exact decomposition/successor-budget laws, independent nested cost/depth and parsed returned-closure/both-saved-body consumers; nineteen old clauses and ordinary headers retained with explicit mutual-eliminator type changes; former raw unary-impossibility fixtures superseded, seven-form data gates unchanged; fixed Lean primitive profile, no canonical not / BitNot.bnot dispatch, instances, staging, effects or totality | High |
| Recursive unary data-image bridges | Proved for Bool logical-not and Word bit-not (ADR-0297) | expression gate seven-to-nine, body seven forms recursively reuse six unchanged exact value/whole-store image contracts; three historic gate negatives become positives; independent source/parsed actual-closure consumers keep lexical rows and separate depth/cost; no gate success guarantee, runtime typing, canonical overload dispatch, source/Core closure identity or totality | High |
| Original closed short-circuit evaluation | Implemented for conjunction and disjunction (ADR-0298) | four original rules, two runner branches and four exact laws; actual Bool left, no skipped-right premise, unrestricted selected value/full store; ordinary compatibility/determinism/soundness/completeness/monotonicity headers retained while mutual eliminators expand; independent exact-depth, non-Bool/missing-right and actual returned-closure/foreign-call consumers; separate Local/Core costs; nine/seven-form data gates unchanged, no binary data-image bridge, canonical dispatch, effects or totality | High |
| Ordered Core Word less-than with local right operand | Proved through exact insertion (ADR-0191) | exact type inversion and original-operand ordered evaluation equivalence with only right-local membership; arbitrary left effects and actual stores; original paths cost both children plus nine; stored-closure allocation prevents dropping the right boundary; no Resolved/source operator change | Medium |
| Identity-free resolved Word less-than | Implemented with unchanged generic contracts (ADR-0192) | dedicated form lowers original-scope children to positional Core lets with no temporary LocalIds; Word typing, ordered evaluation, scope, checker, renaming, store and fresh-insertion/reflection proofs extended; explicit-ID builder unchanged; canonical source `<` still awaits adapter integration | Medium |
| Parametric polymorphism | Planned | type application and preservation | Low |
| Tabled class resolution | Planned | evidence language, finite search, inconclusive boundary | Low |
| Comptime/runtime staging | Blocked | staging decision and effect rules | Low |
| Canonical Syntax-to-Resolved adapter | Identifier/group/Boolean/Word-literal/arithmetic/bitwise/`>`/`<`/`<=`/`>=`/`==`/`!=`/conditional fragment implemented | exact structure/type/value/store correspondence for explicit tables; whole-program declaration collection/ID assignment and general expression resolution remain open | High |
| Canonical local conditional execution | Implemented for the explicit-table fragment | Boolean condition, same-type branches, selected-branch-only evaluation, typed open-environment totality and sufficient Core fuel; no general source literal or overload policy | High |
| Typed local input construction and execution | Implemented (ADR-0157) | unique IDs, fresh insertion, exact row lookup and automatically aligned typed tables; checked runner preserves type/value/store and separates check failure from fuel exhaustion; not source declaration collection | Low |
| Unused-name local input extension | Proved for the supported local-expression fragment | source typing/evaluation equivalence, exact checked Core weakening and failure preservation, identical completed observations; spelling avoidance covers all branches and operands and is essential | High |
| Canonical Boolean negation | Implemented (ADR-0158) | fixed Bool-only `!`, independent typing/evaluation, exact direct-Core lowering and three-transition named operand; no truthiness or general overload resolution | High |
| Canonical Boolean short-circuit operators | Implemented for the fixed adapter profile (ADR-0159) | both operands checked as Bool; selected-right-only execution, exact conditional expansion/value/store/fuel correspondence, and generated constants independent of source-name bindings; not general named and/or resolution in the pinned Rust implementation (ADR-0259) | High |
| Frontend local identity relabeling | Implemented (ADR-0160) | unchanged source AST; arbitrary-map resolution and injective-map exact checker/raw evaluation invariance; typed inputs preserve same-fuel results including suspended states; no allocator commutation | High |
| Canonical Word complement | Implemented (ADR-0161) | fixed Word-only `~`, exact 256-bit result, independent correspondence/safety and double-complement involution; no Bool coercion, literal policy, or general overload resolution | High |
| Numeric spelling and strict Word interpretation | Implemented (ADR-0162) | independent ASCII digit/positional natural meaning, exact decoder correspondence, strict non-wrapping Word range, arbitrary leading zeroes, raw-payload validation and span irrelevance; general source literal typing remains separate | High |
| Canonical local Word literals | Implemented for the monomorphic adapter (ADR-0163) | independent resolution/type/value/store correspondence, exact one-transition execution, complement/conditional composition, whole-branch checking, unused-input and ID-relabeling invariance; no universal literal or overload policy | High |
| Canonical binary Word bitwise operators | Implemented for the monomorphic adapter (ADR-0164) | fixed Word-only `&`/`|`/`^`, ordered strict two-operand evaluation, exact Core correspondence and five-transition literal pairs, canonical parsed precedence, input-extension and ID-relabeling laws; no overload or assignment semantics | High |
| Exact frontend execution thresholds | Proved for the supported expression fragment (ADR-0165) | independent positive and unique source costs, exact continuation-local Core paths, checked fixed-fuel completion/exhaustion iff cost bounds; raw cost retains whole-checking boundaries, terminal recognition is free; not gas or frontend runtime complexity | High |
| Direct local-expression evaluation and cost | Implemented with independent exact correspondence (ADR-0223) | total original-syntax evaluation on explicit first-match actual tables, exact value/cost and absence iff existing raw rules, uncosted projection and explicit final-store equality; all existing strict operator costs and selected-only short-circuit behavior, no Core execution oracle; whole checking/ID alignment separately give exact machine paths/fuel thresholds and completed-run reflection, actual typed inputs give existence, bundled laws retain whole typing; no new acceptance, body/entry or language policy | High |
| Source cost and same-fuel input invariance | Proved (ADR-0166) | injective-ID and unused-name raw cost iff, typed-cost exhaustion characterization, same-fuel completion and exhaustion-presence preservation; suspended states after input insertion may differ, same-name shadowing can change cost without changing the result | High |
| Explicit canonical type names | Implemented restricted bridge (ADR-0167) | named/no-arguments ASTs, exact qualified component-list keys, caller-provided arbitrary Core types, independent first-match meaning and exact success/failure/provenance; no built-in spellings, normalization, declaration collection, or general type inference | High |
| Canonical runtime parameter inputs | Implemented restricted profile (ADR-0168) | independent paired binding iff executable success, exact arity/type/unused names, source-order IDs and reversed aligned rows, per-position argument values, actual parsed parameters feeding existing checked execution; not function calls, staging, global allocation, or runtime argument decoding | High |
| Single-return canonical bodies | Implemented restricted profile (ADR-0169) | bare Unit and expression-return independent typing/value/store/cost, exact checked Core and fuel correspondence, typed execution and fault exclusion; parsed body/parameter composition, no dropped surrounding statements or implied signature/call/early-return semantics | High |
| Terminal conditional return bodies | Implemented separate nonrecursive adapter (ADR-0195) | explicit singleton if/else, Bool condition and two same-typed singleton-return arms, independent exact ifE elaboration and selected-arm evaluation, exact costs and max bounds, safe checked execution and genuine-state resumption; no nested statement conditions, extra statements or general early returns; entry integration in ADR-0198 | High |
| Common terminal return-body interface | Implemented nonrecursive union (ADR-0196) | original-shape dispatch to singleton or conditional body judgments, exact component Core/value/store/cost and whole optional runner results, typed safety, fuel bounds and genuine-state resumption; conditional arms remain singleton returns; reused by runtime entries in ADR-0198 | High |
| Recursive terminal return-tree static semantics | Implemented separate total static adapter (ADR-0204) | arbitrary-depth explicit if/else trees with singleton-return leaves, independent whole typing/exact ordered Core elaboration, success/typing/failure equivalences and uniqueness; old successes embed, old-shape full Option equality only; evaluation/cost in ADR-0205, runner/fuel in ADR-0206 and invariance in ADR-0207; entry integration in ADR-0208 | High |
| Recursive return-tree evaluation and cost | Proved against exact checked Core (ADR-0205) | selected-arm raw/cost rules, child costs plus two per node, unchanged stores and determinism without checking; typed existence uses actual typed inputs, Core iff needs only whole acceptance and aligned IDs, exact paths retain arbitrary continuations; old raw/cost evidence embeds; runner/fuel in ADR-0206 and entry integration in ADR-0208 | High |
| Recursive return-tree fuel and resumption | Implemented separate checked body runner (ADR-0206) | actual checked Core/ordered values, exact typed-cost fuel and fault exclusion, total recursive max-arm upper bound and typed sufficient-fuel safety; genuine checkpoints retain exact residual paths, full chunk resumption and old-shape optional runner equivalence; replay invariance in ADR-0207 and entry integration in ADR-0208 | High |
| Recursive return-tree identity and store invariance | Proved in independent body-level modules (ADR-0207) | global injective ID relabeling preserves exact elaboration, full optional checking and same-fuel complete results; arbitrary-store raw/cost replay retains values and costs without typing, typed completed observations carry their own stores and exhaustion presence is equivalent; no cross-store checkpoint equality or noninjective-map safety; entry integration in ADR-0208 | High |
| Typed local-declaration prefix static semantics | Implemented separate value-free adapter (ADR-0209) | arbitrary-length outer annotated/initialized/non-shadowing let prefix before an existing terminal tree; independent whole typing/exact elaboration, old-scope initializer and fresh tail context, exact nested Core letE, uniqueness and failure equivalences without runtime inhabitants; evaluation/cost in ADR-0210, entry integration in ADR-0215, no inference/default initialization or arm-local lets, rejected forms mean adapter unsupported | High |
| Typed local-declaration prefix evaluation and cost | Proved against exact checked Core (ADR-0210) | strict once-only old-scope initializers and actual value extension, child costs plus two per let even when unused; independent store/value/cost laws and typed existence, acceptance+aligned IDs Core iff and arbitrary-continuation exact paths, raw tree embeddings and whole-rejection contrasts; no inferred runtime typing or unconditional pending-frame exhaustion; runner/bound/resumption in ADR-0211, entry integration in ADR-0215 | High |
| Typed local-declaration prefix fuel and resumption | Implemented separate checked body runner (ADR-0211) | actual static projection/Core/ordered values, whole optional results and exact typed-cost thresholds/fault exclusion; additive source bound with terminal max-arm bound, genuine initializer/tail checkpoints and exact residual multi-chunk resumption, old-shape full Option equality; rejected nonzero bounds are not acceptance, entry integration in ADR-0215 without broader binding policy | High |
| Typed local-declaration prefix store replay | Proved in a separate body-level module (ADR-0212) | arbitrary-store independent raw/cost replay retains initializer values and extended environments; bidirectional laws preserve final-store equality, checked same-fuel done values and exhaustion presence retain their own stores; no cross-store full-result/checkpoint equality, arbitrary-continuation or general Core store independence, or arbitrary-ID renaming; reused at entries in ADR-0215 | High |
| Typed local-declaration prefix owner covariance | Proved for owner-only relabeling (ADR-0213) | exact fresh allocation on arbitrary mixed/sparse/repeated-ID scopes, value-free binding, independent elaboration/typing and whole optional checker equality under global injective owner maps; actual ordered values give full same-fuel/store result and checkpoint equality; no surjectivity or static inhabitants required, no arbitrary index-changing maps, or raw/cost owner API; reused at entries in ADR-0215 | High |
| Typed local-declaration prefix type-name extension | Proved for first-match semantic extension (ADR-0214) | independent exact elaboration/typing and successful complete checker/runner pairs preserve fixed source, inputs, Core/type, fuel/store and actual checkpoints; mutual extension preserves whole Options without equal tables or unique keys; unknown meanings may repair rejection, retained rows do not justify changed-head overrides, reused at entries in ADR-0215 without broader binding policy | High |
| Recursive typed let/return-tree static semantics | Implemented separate total value-free adapter (ADR-0216) | finite alternating typed prefixes and terminal if/else inside either arm; independent exact ordered Core and whole typing, old-scope initialization/fresh tails, scope-local sibling ID reuse and isolation; success/rejection/uniqueness/Core typing without inhabitants, old successes embed and singleton full Option equality; evaluation/cost in ADR-0217, body runner in ADR-0218 and entry integration in ADR-0222; the initial annotation-only profile is extended with inferred initialized lets in ADR-0238; no general inference/defaults/shadowing/general calls | High |
| Recursive typed let/return-tree evaluation and cost | Proved against exact checked Core (ADR-0217) | strict old-scope initialization and actual extended tails, selected original-scope arms and child costs plus two per let/if; raw store/value/cost laws without checking, typed existence with actual environments, acceptance+aligned IDs Core iff and exact arbitrary-continuation paths; old raw/cost embeddings, whole-rejection and pending-frame contrasts; runner/fuel/resumption in ADR-0218 and entry integration in ADR-0222 | High |
| Direct recursive typed let/return-tree evaluation | Implemented with independent exact correspondence (ADR-0224) | total original-block evaluation composed from direct expressions, strict old-scope actual initializers and name-table-relative fresh tails, selected arms and unchanged exact costs; raw success/absence/projection iff and explicit final-store equality, duplicate or unaligned first-match inputs without extra annotation/name checks; whole acceptance+ID alignment separately give exact Core paths/thresholds and completion reflection, typed actual inputs give existence; no checker/entry/bound or source-policy change | High |
| Raw recursive-body owner covariance | Proved without checking or runtime typing (ADR-0226) | globally injective owner-only maps preserve full direct value/cost Options and raw costed/uncosted iff with both stores, including non-surjective maps and arbitrary duplicate/sparse/unaligned/untyped caller rows; original syntax/values/order/indices and actual name-table-relative fresh tails retained, raw/whole and first-match collapse boundaries explicit; index-shift example only limits exact allocator transport, no existing evaluator/entry/owner-runner change | High |
| Raw lookup-extensional semantics | Proved for equal composed actual-value lookup (ADR-0227) | full expression/body value-cost Options and costed/uncosted raw iff with both stores, independently chosen owners and fresh IDs, arbitrary duplicate/unaligned/untyped rows without any identity-map or checking premise; strict old-scope values and fresh name updates preserve observations despite different layouts or missing-versus-unbound names; no equality of static tables, compiled Core or checkpoints, no existing definition or source-policy changes | High |
| Recursive typed let/return-tree fuel and resumption | Implemented separate checked body runner (ADR-0218) | actual static projection and ordered values, exact cost thresholds and typed fault exclusion; syntax-size-recursive additive/max-arm bound, raw cost upper bound versus typed sufficient-fuel safety, genuine initializer/conditional/tail checkpoints and full residual multi-chunk replay; old runner Some payloads and singleton full Options preserved, positive rejected bounds are not acceptance; store replay in ADR-0219 and entry integration in ADR-0222, no old body adapter/bound changes | High |
| Recursive typed let/return-tree store replay | Proved in a separate body-level module (ADR-0219) | arbitrary-store raw/cost replay preserves old-scope initializer values and selected recursive paths without checking/type/ID premises; bidirectional laws retain final-store equality, checked same-fuel done values and exhaustion presence keep own stores; genuine checkpoints resume separately, no cross-store full-result/checkpoint equality or arbitrary-Core/pending-continuation independence; old entries and owner policies unchanged | High |
| Return-body identity and store invariance | Proved in acyclic body-level modules (ADR-0197) | injective exact-Core/type and optional checker/full same-fuel runner preservation; raw/cost store replay, same completed values and exhaustion presence with distinct store-bearing states; original singleton helper contracts and old imports retained, no new entry or noninjective-map semantics | High |
| Recursive typed let/return-tree owner covariance | Proved in separate body-level modules (ADR-0220) | globally injective owner-only maps preserve independent exact elaboration/whole typing and full checker Options, including rejection without surjectivity; sparse mixed-owner fresh allocation and scope-local sibling ID reuse, unchanged source/Core/type/indices and actual positional values; full same-store runner/checkpoint equality, no arbitrary index-map/collapsing-owner guarantee or entry/helper/raw-cost/bound change | High |
| Explicit runtime function entry | Implemented restricted profile (ADR-0170) | independent header/parameter/exact-Core preparation, declared return agreement, whole-entry typing and fixed-fuel cost correspondence, parsed declaration execution; no generics/modifiers/where or empty/multiple return clauses, no general calls or safety for arbitrary prepared records | High |
| Recursive typed let/return-tree type-name extension | Proved for first-match semantic extension (ADR-0221) | independent exact elaboration/whole typing transports every annotated binding and both arms; fixed source/owner/inputs/Core/type and actual values preserve successful complete checker/runner pairs, mutual extension preserves full Options and genuine checkpoints without equal tables or unique keys; unknown unselected meanings may repair rejection, conflicting new heads are not extension, no old entry/owner/raw-cost/bound/policy change | High |
| Terminal-body runtime entries | Integrated with existing entry API (ADR-0198) | singleton and explicit terminal if/else compile/prepare/type/cost through the common body judgments; exact Core and actual ordered arguments, provenance/factorization/owner/store/safety/resumption retained; the earlier nonrecursive profile is subsumed by recursive entry integration in ADR-0208; old body-only bounds and rejection remain unchanged | High |
| Recursive terminal runtime entries | Integrated with the existing entry API (ADR-0208) | finite explicit if/else trees with singleton leaves, exact value-free compilation and actual ordered argument preparation; provenance/factorization/positions/type-table/owner/store/safety/resumption retained, the recursive max-arm entry bound is extended by ADR-0215; old accepted behavior preserved, invalid unselected deep branches and whole contracts still reject; no new record layout, calls or general early returns | High |
| Typed let-prefix runtime entries | Integrated with the existing entry API (ADR-0215) | annotated initialized nonshadowing outer lets with old-scope initializers and fresh tails; exact value-free compilation and actual ordered preparation, original parameter-only records and direct Core runner; provenance, factorization, owner/type-name/store laws, exact costs and genuine checkpoints retained; the initial additive prefix entry bound and profile are extended by ADR-0222, old body adapters unchanged; no inference, defaults or general calls | High |
| Recursive typed let/return-tree runtime entries | Integrated with the existing entry API (ADR-0222) | finite typed lets and terminal if/else inside either arm, independent exact compilation/preparation/whole typing/cost, original parameter-only records and one actual-value reversal; unchanged header/argument/return guards, direct Core, provenance/factorization/owner/type-name/own-store/safety/resumption contracts; only three generic fuel formulas switch to the recursive additive/max-arm bound; old body-only rejection/bounds and old successful complete results retained, genuine branch-local checkpoints and invalid unselected arms covered; the initial annotation-only profile is extended with inferred initialized lets in ADR-0238; no general inference/defaults/shadowing/general calls or new record policy | High |
| Direct checked runtime-entry evaluation | Implemented with exact entry-cost and rejection correspondence (ADR-0225) | unchanged preparation gate followed by direct original-body evaluation on actual parameter-only rows, exact declared type/value/cost and explicit final-store equality; no further evaluation failure after accepted preparation, no Core result oracle or second argument reversal; raw selected success cannot bypass header/argument/return/unselected-body checks, existing fuel/compiled/store/resumption laws reused; no entry-record or language-policy change | High |
| Arbitrary runtime parameter positions | Proved (ADR-0171) | source-index bounds and exact name/ID/Core-position/type/value correspondence, reference and matched entry return in one transition, mixed types and every parsed position across several arities; no new evaluator, call semantics, or out-of-range subtraction policy | High |
| Static runtime argument invariance | Proved (ADR-0172) | equal structural argument type lists preserve independent binding/preparation and optional names/context/IDs/exact Core/return type, including rejection; values, suspended states, outcomes, and costs may differ | High |
| Runtime entry owner invariance | Proved (ADR-0173) | injective owner-only binding/preparation transport, identical optional Core/type/runtime values and full same-fuel results for arbitrary owners; ID tables are relabeled, no general allocator covariance for binder-index changes | High |
| Type-only runtime parameter declarations | Implemented with exact independent semantics (ADR-0174) | value-free static rows, exact annotation declaration, runtime erasure and reconstruction from matching ordered typed arguments; no type-inhabitation assumption or whole-function compiler | High |
| Value-free parameter layout and source positions | Proved directly from static declarations (ADR-0201) | exact annotation-row correspondence, arbitrary initial suffix and owner-relative fresh IDs, conditional distinct-name preservation; source lookup at k yields owner/k and exact Core index n-1-k, independent reference/return elaboration with no runtime values; sparse/duplicate/range boundaries retained | High |
| Value-free restricted function compilation | Implemented with exact independent semantics (ADR-0175) | header, static parameters, and exact body compile to typed open Core; runtime preparation factors through an ordered argument-type guard, including rejection; no closure generation or source-call implementation | High |
| Value-free compilation owner invariance | Implemented without runtime inhabitants (ADR-0200) | injective type-only ID maps and erasure commutation, direct static parameter/compilation transport, complete optional Core/return-type/context-type projection equality across arbitrary owners; retain binder indices and distinguish changed ID-bearing records; no allocator covariance for arbitrary index maps | High |
| Value-free positional function compilation | Proved for singleton parameter returns and terminal parameter selectors (ADR-0202) | forward whole-entry evidence and exact compile success, inverse exact Core/type from provenance; whole declarations/header/body shapes retained, arbitrary nominal types and repeated guard/arm positions allowed; no runtime values or new acceptance policy | High |
| Meaning-preserving type table extension | Proved through exact static compilation (ADR-0203) | first-match meaning extension, safe append/fresh prepend, annotation/header/declaration/compiled record transport; one-way exact success preservation and mutual full Option equality, qualified keys and shadowing boundaries retained; no runtime inhabitants or new lookup policy | High |
| Actual runtime type-table extension | Proved through full preparation and execution (ADR-0242) | ten laws retain arbitrary initial/final actual binding rows, original arguments, identities and complete prepared records; successful exact binding/preparation/run payloads survive one-way extension, mutual extension preserves rejection; whole states and genuine checkpoints retain the same fuel/store, while unknown-name repair and different actual values remain distinct from static projection equality; no executable definition, source acceptance or private binder change | High |
| Canonical binary Word addition | Implemented for the monomorphic adapter (ADR-0176) | actual binary Core, strict ordered Word operands, modulo-2^256 sum and child costs plus three, wrapping/range and whole-check distinctions, static/runtime function bridges and identity/input invariance; no general overload policy | High |
| Canonical binary Word subtraction and multiplication | Implemented for the monomorphic adapter (ADR-0177) | exact ordered Core and modular results, strict two-Word typing/evaluation, child costs plus three, exact pending frames, noncommutativity/grouping/precedence and 58 parsed position pairs; generic safety, compilation, renaming and unused-input proofs; no unary signs or assignment | High |
| Canonical unsigned Word division and remainder | Implemented for the monomorphic adapter (ADR-0199) | direct ordered wordDiv/wordMod, two Word operands and Word result, zero divisor returns zero for both without skipping evaluation; child costs/bounds plus three, exact checkpoints/resumption, all generic safety/invariance and terminal-entry provenance guarantees; parser/Core/Resolved/wire definitions unchanged | High |
| Canonical unsigned Word greater-than | Implemented for the monomorphic adapter (ADR-0178) | strict Word operands produce Bool through exact wordGt; unsigned high-bit/equality boundaries, ordered child costs plus three, arithmetic guards, Bool-return compilation and wrong-return rejection, 29 parsed position pairs and full fuel-four/five states; other comparisons remain separate | High |
| Exact compiled-function execution factorization | Implemented as a proof interface over the unchanged runtime endpoint (ADR-0179) | independent compilation and ordered actual arguments determine full same-fuel Core results; unconditional failure/guard factorization, independent result characterization, exact cost paths/bounds and provenance-dependent safety; cached parsed regressions; no new runner or source-call semantics | High |
| Compiled-function observation invariance | Implemented for independently compiled pairs (ADR-0180) | equal ordered parameter types and exact Core derive return-type equality, full all-argument/all-fuel execution equality and independent exact cost iff across declarations/type tables/owners; names/IDs may differ; no surface transformation or final-value-only equivalence | High |
| Initial-store-independent frontend observations | Proved for the current restricted fragment (ADR-0181) | arbitrary replacement stores retain independent raw/body/entry values and exact costs, fixed-fuel terminal/exhaustion observations, and provenance-dependent compiled observations; full store-carrying states are not equated; no general Core-effect or closure-call independence | High |
| Source-derived frontend fuel bounds | Proved for the current restricted fragment (ADR-0182) | computable structural upper bounds cover every independent raw/body/entry cost; whole typed execution and proven compiled Core with matching actual arguments finish at or above the bound; conservative rather than exact/minimal, no acceptance or type-inhabitation inferred from a numeric budget | High |
| Exact frontend checkpoint resumption | Proved over the unchanged Core runner (ADR-0183) | genuine exhausted states resume with full combined-budget result equality; known source costs give exact residual paths and fuel thresholds through checked expressions/bodies/entries and proven compiled Core; no checkpoint editing, fault recovery, host responses or replacement continuations | High |
| Canonical Word equality | Implemented for the monomorphic adapter (ADR-0184) | strict ordered Word operands yield Bool through direct wordEq, with both child costs plus three; generic typing/evaluation/cost/store/fuel-bound/resumption guarantees, exact pending frames, source precedence and whole entry return contracts; no polymorphic equality or operand swapping | High |
| Canonical Word inequality | Implemented for the monomorphic adapter (ADR-0185) | ordered boolNot(wordEq) expansion has Word operands and Bool result, exact child costs plus five, distinct pending equality/negation frames and seven-step leaf completion; generic typing/reflection/store/bound/resumption and whole entry guarantees retained; no new primitive, constant folding or polymorphic inequality | High |
| Canonical unsigned Word less-than-or-equal | Implemented for the monomorphic adapter (ADR-0186) | ordered boolNot(wordGt) expansion preserves unsigned Word-to-Bool comparison, equality-true boundary, exact child costs plus five and seven-step leaves; generic typing/reflection/store/bound/resumption and compiled entry contracts retained with non-associative relational precedence; no signed interpretation or operand swapping | High |
| Canonical unsigned Word less-than | Implemented through identity-free resolved comparison (ADR-0193) | original-scope children lower to ordered positional lets, unsigned Word-to-Bool result, exact child costs plus nine and eleven-step leaves; arbitrary structural maps and all generic typing/evaluation/store/bound/resumption/entry provenance contracts retained; actual parsed arguments and checkpoints, no temporary LocalIds or parser change | High |
| Canonical unsigned Word greater-than-or-equal | Implemented as Boolean negation of ordered less-than (ADR-0194) | original-scope Word operands, unsigned Bool result with equality true; exact child costs plus eleven and thirteen-step leaves, genuine comparison/negation checkpoints; generic typing/evaluation/store/bound/resumption and own compiled-entry contracts retained without new premises or parser changes | High |
| Resolved-to-Core elaboration | Exact local-expression fragment implemented | full source coverage, effects beyond the store-preserving fragment, and stage preservation remain open | Medium |

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
