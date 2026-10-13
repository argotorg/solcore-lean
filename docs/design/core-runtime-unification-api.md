# Migration to the common Core execution API

Last updated: 2026-10-14.

Runtime unification and removal of the old typed-source evaluator were completed in `a3168382`. This document describes the current public API. The second goal, the proof of meaning preservation for the complete public compiler, remains in progress. See the [implementation record](core-runtime-unification-progress.md) for the latest implementation and validation checkpoint.

## Complete compiler profiles issue public sessions (2026-10-14)

`84536b5b` builds the full program certificate from finite checks of the actual compiled cache. `45b1d994` connects that producer to the original seven-call evidence program at checker budgets `1024` and `1000`.

The executable profile visits every actual cache index and accounts for every original lambda node in each cached source. It checks original forms, operand membership, metadata, direct targets, full replacement ranges and method evidence origins. Actual accepted compiler trees and expression traces then produce the body proofs internally. Callers provide neither a recursive syntax proof nor a completion function for each row.

The public constructor consumes the successful profile and the original checking, compilation, bootstrap and startup receipts. It issues the same automatic catalog and physical session used by later calls. The new seven-call path performs no example-specific program-certificate assembly. Both checker budgets retain twelve cached rows, ten direct targets, three distinct closures, results `33 / true / 33 / 55` and reached public store sizes `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`.

Validation: 8 affected modules checked together, full build (7,272 jobs), registered tests (14,382 build jobs), kernel policy and 840 endpoint audits pass. The original lexical-failure program also passes the profile. Checks reject missing operands and direct targets, invalid metadata, mismatched assignment types, unsupported statements, unaccounted lambdas and outer fallthrough. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The profile remains a supported-fragment condition. It currently accepts scalar/direct/indirect/method expressions, monomorphic lexical declarations, bare assignments, loops and ordinary factories with a singleton-return lambda body. The original scoped-closure example is rejected by that factory check and retains its earlier verified execution path. Independent Source well-formedness, public input typing and finite staged Source traces remain explicit. Full compiler and pass coverage remain unfinished.

`CompilerProgramStaticProfile.validateProfile` performs the finite whole-cache checks. `AcceptedCompilerProgramAdmission.of_profile` constructs the complete certificate internally. `CertifiedPublicSession.of_profile`, `from_profile_initial_start` and `from_profile_initial_row` connect it to actual initialization. Later outcomes use the existing shared-state endpoints. Public runtime APIs are unchanged.

## Method bodies come from actual cached compilation (2026-10-14)

`fdbd1f8e` derives method body admission from the actual retained selection and cached compilation. `3624d72d` connects both method rows to the existing whole-program certificate and public sequences.

Final compilation provenance supplies the genuine selected implementation method at its exact cache index. Agreement with the original successful checker result retains its full typed body and ordered evidence. The complete parameter replacement range and original Source well-formedness establish the method instantiation. Accepted body and expression actions then supply its syntax and lexical binding proofs.

The unchanged evidence program now completes all ten ordinary roots, both factory closure sources and both method rows using compiler receipts. Its twelve cached rows, ten direct targets, dictionaries, substitutions and three captured closures are preserved. The original seven-call sequence, automatic-catalog sequence and checker-budget companion still prove Source traces and public results `33 / true / 33 / 55`.

Validation: 16 affected modules checked together, full build (7,266 jobs), registered tests (14,370 build jobs), kernel policy and 792 endpoint audits pass. Method checks reject missing direct targets and insufficient replacement-type traversal. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The pending certificate may exist before deferred bodies have proofs. Completion still requires the original direct targets and a certificate for every actual method row. Source well-formedness, supported forms, monomorphic local bindings, metadata, method-origin catalog checks and staged Source traces remain explicit. Complete compiler and pass coverage remain unfinished.

`AcceptedMethodBodyReceipts` recovers actual body and expression actions. `AcceptedMethodBodyAdmission.of_selection` derives the original method Source certificate. `AcceptedProgramMethodCompletion.Pending.complete_receipts` connects all indexed method certificates with ordinary roots and closure sources. Public runtime APIs are unchanged.

## Certified sessions begin with scalar results or Source failures (2026-10-14)

`071edd23` connects initial scalar success and Source failure to the common physical session. `64a72bde` applies those endpoints to the existing lexical-failure program and its identity continuation.

Actual bootstrap and startup receipts supply the initial inputs and physical state. A scalar result creates an empty retained-handle history; a Source failure does the same while preserving the failed heap and decoded reason. Forward theorems use an independent finite Source trace and provide sufficient execution budgets. Successful output also has a sufficient output budget. Reflection starts from the actual finite public outcome. Later failure endpoints preserve the current history and input registry.

The unchanged program is checked at `1000` and compiled at `100`; the complete certificate is accepted at `64`. Its first uninitialized read allocates an absent Word cell. The subsequent `identity(37)` runs in the returned session, allocates its own parameter and preserves the absent cell. A separate fresh bootstrap proves initial `identity(37)`. All three operations retain Source traces and public forward bounds, with genuine automatic catalogs and no fabricated handle.

Validation: 12 affected modules checked together, full build (7,261 jobs), registered tests (14,356 build jobs), kernel policy and 765 endpoint audits pass. Earlier seven-call catalog, checker-budget, handle-reuse and data-output sequences remain connected. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Source well-formedness, the complete program certificate, ordinary eligibility, public input typing and staged Source traces remain explicit. Complete compiler coverage and preservation across all actual passes remain unfinished.

`CertifiedPublicSessionOutcomes` adds `Initial.forward_scalar`, `Initial.reflect_scalar`, `Initial.forward_failure` and `Initial.reflect_failure`, plus later `Issued.forward_failure` and `Issued.reflect_failure`. Initial outcomes return states with an empty handle history. Descriptor and body-support construction are internal. Public runtime APIs are unchanged.

## Actual public calls issue one certified session (2026-10-14)

`7c290567` constructs a common public session from actual checking, compilation, opening, bootstrap and call receipts. `d39d7ad2` connects all seven original evidence-program operations to that session.

The common constructor issues the complete automatic catalog, diagnostic receiver and physical body support. It recovers the initial function from the actual selected public root. Later calls retain the same catalog, Source heap, registry and handle history. Exact cached rows, singleton global slots and complete ordinary eligibility identify each selected function. No assumed catalog order or separately assembled example inventory is needed.

The public companion retains all seven independent SourceCall judgments and sufficient-fuel public conclusions. Three distinct closures survive intervening calls and return `33 / true / 33 / 55`; public store sizes remain `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. Its original source, checker/compiler settings and existing sequence theorem are unchanged. The earlier differing-checker-budget companion remains checked alongside it.

Validation: 10 affected modules checked together, full build (7,251 jobs), registered tests (14,336 build jobs), kernel policy and 747 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connects certified programs to a common public session. Original Source well-formedness, the complete static certificate, ordinary eligibility, typed public inputs and staged Source traces remain explicit. It does not establish that every successful compilation supplies the certificate or cover every actual compiler pass.

`CertifiedPublicSession.from_initial_start` admits an original valid Source entry; `from_initial_row` uses an authentic eligible cached row. Both issue `Issued` and `Initial` from real public receipts. `Issued.recover_start_row` identifies later selected functions. Initial and later function/scalar forward and reflection endpoints use the same `Issued.State`. Public runtime APIs are unchanged.

## Original checker budgets supply method coherence (2026-10-14)

`4351f151` removes the extra requirement to check all original method bodies at budget `1024`. `66e74cdd` carries the actual checker receipt at budget `1000` through the existing seven-call Source/public sequence.

Successful pattern and expression inference preserves its entire result and state when the structural budget increases. Two successful function checks therefore return the same complete checked function, including the typed graph, substitutions and ordered solved requirements. The corresponding program theorem preserves every ordered function and method record.

Method coherence now retains the original successful checking budget. Actual compiler selection supplies its own successful method recheck at `1024`; equality of those complete results identifies the retained method. Unselected methods need no extra fixed-budget success premise. The ordinary and automatic catalog issuers derive coherence from the supplied original checker receipt.

The companion performs an actual check at `1000` and proves equality with the original fixture program. That receipt constructs the static support used by all seven Source traces and public forward conclusions. The original method remains present, with results `33 / true / 33 / 55`, three retained closures and the same eight reached heap sizes. Existing defaults and checker implementations are unchanged.

Validation: 2,114 affected modules checked together, full build (7,243 jobs), registered tests (14,320 build jobs), kernel policy and 719 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Independent Source well-formedness, remaining metadata and body certification, complete compiler syntax and preservation across all actual passes remain unfinished. The agreement results compare successful checks; they do not treat exhausted budgets as successful completion.

`checkFunctionBody_success_unique_fuel` proves equality of complete checked functions; `checkProgram_success_unique_fuel` extends this to the full original program. `CallableMethodBodyCoherence.Checked` now records an existential successful original budget. `of_loaded`, `of_checked`, `Certificate.issue_for_checked` and `Certificate.issue` accept that actual budget. Code that destructed the previous fixed-budget relation must unpack the budget first. Runtime APIs are unchanged.

## Factory closure bodies come from actual compilation (2026-10-14)

`956ced51` derives ordinary closure admission from the actual lambda body action. `dde742cb` completes both factory closure source rows in the original evidence program.

The accepted factory receipt supplies the inner returning-body compiler and its exact expression trace. Source ownership and parameter order come from the original checked function and prepared origin. The closure certificate retains the captured scope and original lambda metadata. Finite source-node coverage accounts for every lambda in each selected cache row.

The shared program certificate now consumes compiler receipts for all ten ordinary roots and both factory closure source rows. Its twelve cache rows, ten direct-table rows and seven Source/public operations are unchanged: results remain `33 / true / 33 / 55`, with three retained closures, the same reached heaps and all public fuel conclusions. Selected closure checks are completed by exact indexed certificates. Unselected closures, method selection, metadata and table coverage still run through the existing checks.

Validation: 10 affected modules checked together, full build (7,237 jobs), registered tests (14,308 build jobs), kernel policy and 693 endpoint audits pass. Earlier public sequences remain connected. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This completes closure-body admission for the two original factories. Independent Source well-formedness, finite metadata and catalog checks, method certification, broader compiler syntax and preservation across all actual passes remain explicit work.

`AcceptedNamedClosureAdmission.of_produced` uses the accepted factory's actual inner compiler trace. `source_of_header` transports its ordinary-body certificate to the original source. `AcceptedProgramClosureCompletion.Pending.complete_receipts` requires exact cache-indexed root and whole-source closure certificates. Its two position lists are validated before any deferral. Runtime APIs are unchanged.

## All ordinary roots in the evidence program use compiler receipts (2026-10-14)

`646f46e7` derives factory admission from actual outer-return and lambda compilation. `c2817faf` connects both original factory functions, completing all ten ordinary roots in the existing evidence program.

The factory receipt retains the original returned lambda, parameter allocation, captured scope, body, production hooks and emitted callable. Its inner return action comes from the actual lambda body equation and selected body compiler. Original Source typing supplies the declared return type; equality of native representations is insufficient. Cache transport retains the exact selected position and compiled roots.

All ten ordinary roots now enter the common program certificate through accepted compiler actions. The original program still has twelve cache rows, ten direct-table rows and the same seven Source/public operations, with results `33 / true / 33 / 55`, three retained closures, identical reached heaps and all public fuel conclusions. The program still checks every closure and method. Both selected factory rows reject a zero closure budget; deferring their roots does not bypass that obligation.

Validation: 11 affected modules checked together, full build (7,234 jobs), registered tests (14,302 build jobs), kernel policy and 674 endpoint audits pass. Earlier public sequences remain connected. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This completes root admission for this original program. Independent Source well-formedness, finite metadata and catalog checks, closure and method certification, broader compiler syntax and preservation across all actual passes remain explicit work.

`AcceptedNamedFactoryAdmission.of_header` returns the accepted factory receipt or an unsupported case indexed by the same actual body or expression action. `of_returning` accepts original finite shape and gate facts; `source_of_header` transports its certificate to the same cache row. `Pending.complete_receipts` consumes each proof-wrapped root within the existing row proof and preserves table, selection and closure certification. Runtime APIs are unchanged.

## Compiler receipts cover mutable relay bodies (2026-10-14)

`1d90a8c7` extracts actual method-operator, assignment and while-loop actions. `77d9e3c8` connects both original relay functions and both identity functions to the existing public execution certificate.

Loop receipts retain the condition, loop body, continuation, scope and compilation budgets. Assignment refinement uses the genuine Header callback policy to obtain the actual right-hand action, original binder, place layout and emitted code. It preserves exact Source target types separately from their native representation. The original trait-operator receipt retains its dictionary and ordered operands.

The complete certificate now obtains eight ordinary function roots from accepted compiler actions. The original program still has twelve cache rows, ten direct-table rows and the same seven Source/public operations. Relay-local writes, captured environments, reached heaps, outputs `33 / true / 33 / 55` and public fuel conclusions are preserved. Separate recursive body or expression scans are no longer required for those selected roots.

Validation: 48 affected modules checked together, full build (7,231 jobs), registered tests (14,296 build jobs), kernel policy and 660 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Ordinary primitive operators, operators with output coercions, projected or compound assignments, generalized locals and other body forms retain explicit unsupported branches in this producer. Factory roots, closure and method bodies, metadata and catalog formation still have complementary checks. Complete compiler coverage and preservation across all actual passes remain unfinished.

`AcceptedBareAssignmentReceipt.of_accepted` authenticates the selected compatible callback and right-hand compilation. The extended accepted body tree records while loops and distinguishes raw assignment actions from refined bare equal writes. Header refinement supplies the real callback policy; the same refined receipt feeds body and expression admission. Runtime APIs are unchanged.

## Accepted indirect calls supply retained closure execution (2026-10-14)

`375099a2` derives indirect-call structure from actual accepted compiler actions. `f7f43e37` connects the original `useWord` and `useBool` callers to the same complete certificate as the two evidence-bearing entry roots.

The indirect receipt retains the original callee first, followed by every argument in order, with each accepted child action and its actual compilation budget. The expression proof constructs the indirect-call grammar from those children and the original lookup. It does not require an independently supplied recursive grammar. Unsupported special actions remain attached to their actual compiler trace.

Success of the existing metadata-only check now supplies raw facts for each original supported node. The two caller proofs transport that exact success to the genuine Header, close the remaining indirect branch conditions, and derive body admission before the shared program certificate is completed. The original twelve cache rows, ten direct-table rows, captured closures, reached heaps and seven Source/public operations remain. The same public preservation and reflection endpoints retain outputs `33 / true / 33 / 55` and sufficient-fuel guarantees.

Validation: 30 affected modules checked together, full build (7,225 jobs), registered tests (14,282 build jobs), kernel policy and 636 endpoint audits pass. The original six-call relay and earlier public sequences remain connected. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Four actual cached roots now derive admission from accepted compilation. The remaining roots, closure bodies, methods, catalog formation and global metadata retain their explicit checks. General compiler coverage and meaning preservation across all actual compiler passes remain unfinished.

`AcceptedIndirectExpressionReceipt.of_head` extracts an indirect receipt from the actual selected compiler head. `AcceptedNamedExpressionMetadata.at_of_accepted` projects facts from successful metadata checking at an original supported node. `AcceptedNamedBodyExpressionAdmission.of_returning_calls` uses the accepted callee and ordered argument tree to supply the existing named-body admission. Runtime APIs are unchanged.

## Compiler evidence roots complete shared public support (2026-10-14)

`670dd39f` connects accepted returning expressions to a certificate with several selected cache positions. `795ad95e` uses it for both original evidence-bearing three-argument entry roots.

Both roots now obtain body and expression admission from their actual Header compiler actions. Their original node forms and ordered argument edges rule out unsupported branches. The observed evidence, target receipts and Source lookup remain unchanged. Each root is proved before the complete program certificate is constructed; the final certificate does not supply its own missing root proof.

The pending certificate retains every original cache row and checks all remaining roots, closures, methods, direct targets and catalog obligations. Completion identifies a selected function by its actual cache position and successful lookup. The original program still has twelve cache rows and ten direct-table rows. The same completed certificate supplies the existing Source and public execution proofs, including all seven operations, outputs `33 / true / 33 / 55`, retained captures and sufficient-fuel conclusions.

Validation: 11 affected modules checked together, full build (7,222 jobs), registered tests (14,276 build jobs), kernel policy and 619 endpoint audits pass. Both selected roots work with zero body-scan fuel. Missing cache positions, an unselected root with zero fuel, an insufficient program budget and missing evidence targets are rejected. Empty and repeated selections preserve full coverage. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Global metadata, original Source well-formedness and complementary finite certification remain explicit. Other compiler branches and preservation across all actual compiler passes remain unfinished.

`AcceptedProgramRootCompletion.Pending.complete` fills any finite list of authentic cache positions with exact root certificates. `AcceptedNamedExpressionBoundaryExclusion.Residual.impossible` excludes a residual through original reached forms and actual argument edges. `AcceptedNamedBodyExpressionAdmission.of_returning` composes those facts with the actual accepted body and existing expression producer to return body admission. Public runtime interfaces are unchanged.

## Accepted expression actions supply public relay support (2026-10-14)

`cc411eaf` derives original expression structure from accepted compiler actions. `cf93e645` connects those receipts to the existing six-call relay proof.

The producer retains the original occurrence, selected special callback, ordinary or evidence-bearing direct-call receipt, and every ordered argument action. Recursion follows the actual decreasing compiler budget. It constructs expression syntax or identifies an unsupported action within that same accepted trace. Body admission obtains its expression children internally and retains the exact body when a branch remains unsupported.

The relay now obtains its statement and expression admission from its genuine Header compilation. The executable observer checks the actual cache, metadata, requirements and direct targets. Its old statement and recursive expression scanners are no longer required. The original Source, execution sequence, captured environments and public fuel guarantees remain, including `make10 / make20 / A10 / make30 / B20 / A11`.

Validation: 33 affected modules checked together, full build (7,218 jobs), registered tests (6,800 build jobs and final pass marker), kernel policy and 602 endpoint audits pass. The original three-row cache supplies the three-row direct table; removing the required target is rejected. The earlier coercion, method-evidence, failure/reuse, direct-issued and nested-output sequences still pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Global metadata, complete target formation and independent Source well-formedness remain explicit. Other expression branches, contextual local initialization and full compiler coverage still require proof. Meaning preservation across every actual compiler pass remains unfinished.

`AcceptedNamedExpressionFlow.Head.of_accepted` retains the actual selected expression action. `Trace.of_accepted` recovers its ordered children; `syntax_of_header` derives syntax or an exact `Residual`. `AcceptedNamedBodyExpressionAdmission.of_actual` uses those receipts to construct the existing body admission without a caller-supplied expression grammar. Public runtime interfaces are unchanged.

## Actual compilation supplies named body admission (2026-10-14)

`2f8a51b8` extracts named statement structure from accepted compiler actions and derives local declaration facts from original Source typing. `c5522652` uses those receipts in the existing seven-call coercion and retained-closure proof.

The producer retains the exact return or let action, child order, lexical scope, lowering budget, binder allocation and emitted body. Original Header typing supplies monomorphic binder ownership and requirements. Unsupported statement branches and generalized locals retain the same actual compiled body as an explicit remaining obligation.

The original `keep` function now receives its body admission from the genuine Header compilation. A complementary program check validates every other cached root, every closure and method, the complete direct table and coercion selection. The exact selected cache position is filled by the compiler-derived root proof, producing the existing full `ProgramAdmission.Certificate`. Both the selected-inventory and automatic-catalog issuers consume this certificate. The old `keep` body-scanner success is no longer a premise of that route.

All seven original Source traces and sufficient-fuel public conclusions remain, with results `41 / 7 / 41 / 7`, three retained closures and the same reached heaps. Original Source, runtime, support family and final sequence theorem files are unchanged. A separate existing relay regression confirms that an actual let/direct/return body obtains its local declaration receipt from Header typing.

Validation: 34 affected modules checked together, full build (7,207 jobs), registered tests (14,244 build jobs and final pass marker), kernel policy and 576 endpoint audits pass. The actual four-row cache and three-row table also verify that the chosen root needs no body-scan fuel, while an unchosen root, a missing cache position and insufficient fuel for the other program checks are rejected. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This covers the selected actual compiler branches. Original return/read facts, expression syntax and metadata, independent Source well-formedness and certification of the other bodies remain explicit. The next connection derives expression structure from the actual accepted expression actions; complete compiler coverage and all-pass preservation remain unfinished.

`AcceptedNamedBodyFlow.of_compilation` exposes actual named lowering. `AcceptedNamedBodyBindings.of_header` derives local declaration receipts or retains an actual generalized binding. `AcceptedNamedBodyAdmission` constructs current Source admission and transports it to the exact cached row. `AcceptedProgramBodyCompletion.certify` leaves one actual cache position pending; `Pending.complete` requires that position's root proof and returns the existing full certificate. Public runtime APIs are unchanged.

## Nested callable outputs retain the common physical history (2026-10-14)

`29b42221` connects actual compound output collection to the common physical session. `e744359f` moves the existing constructor-call sequence onto this connection and the complete program certificate.

The unchanged nine operations return a constructor containing a new closure, an earlier closure, a named function and a builtin in that order. Subsequent calls return `20`, export a factory closure capturing `30`, return `10` from the earlier capture and convert `37`. Selection preserves the actual output handle order, repeated handles, captured environments and reached Source heap. Every selected handle receives the same physical authority used by later execution.

The original Source, checker budget and ten outcome declarations are unchanged. One certificate covers the actual two-row cache and direct table, including the constructor's complete substitution range and original payload children. Reflection starts from the actual completed invocation. Preservation starts from accepted public input and independent Source execution, and covers all sufficiently large execution and output budgets.

Validation: 107 affected modules checked together, full build (7,199 jobs), registered tests (14,228 build jobs and final pass marker), kernel policy and 546 endpoint audits pass. Eight constructor-admission cases cover original children, complete substitution ranges, missing nodes and exhausted traversal. Earlier issuance, failure/reuse, method-evidence, coercion and relay sequences still pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The next obligation is to obtain static body support from actual accepted compiler actions. Successful finite certification is still an additional condition; compiler-wide coverage and preservation across every actual pass remain unfinished.

`RecursiveNamedPublicPhysicalSessionDirectOutputCollection.SelectedAt` records the actual invocation, related Source/native payload, output budget and selected entries. `State.collect` connects common direct reflection to the existing nested collector. `RecursiveNamedPublicPhysicalSessionDirectOutputForward.forward_call` supplies the corresponding sufficient-fuel guarantee and retained physical history. Public runtime APIs are unchanged.

## Issued named and builtin handles share physical histories (2026-10-14)

`287c4b29` connects actual named and builtin issuance to the common physical session. `ea787a6a` migrates the existing direct-issued sequence to those producers and the complete program certificate.

The original five operations create a closure capturing `10`, issue the named `read` function, call it with the old closure, issue the builtin integer conversion, and call that builtin with `37`. Results remain `10` and `37`. The named factory's complete captured environment follows its actual global-slot reads and cached cells. Both issuers append the exact handle while retaining the earlier captures, Source heap, native store and registry.

One certificate covers the original two-row cache and its two-row direct table. The automatic catalog issuer is exercised on that same certificate. Source code, the original checker budget of `1000`, all five operations and four outcome definitions are unchanged. Both direct-call forward guarantees retain every output-fuel budget of at least `1`.

Validation: 1,030 affected modules checked together, full build (7,195 jobs), registered tests (14,222 build jobs and final pass marker), kernel policy and 521 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The earlier nine-event failure/reuse, seven-call method-evidence and coercion, and six-call relay sequences still pass.

Independent Source well-formedness and successful finite certification remain explicit. Wider compiler alternatives, complete static coverage from compiler success and preservation across every actual pass remain unfinished.

`CallableIndexedOwnedNamedPhysicalCaptures.of_read` constructs complete captures from an actual native read; `of_cached` keeps its original interface. `RecursiveNamedPublicPhysicalFactoryValues` derives named and builtin representations from genuine issuer receipts. `RecursiveNamedPublicPhysicalSessionIssuance.State.remember_named` and `remember_builtin` return exact Source/handle types, an appended entry and the same Source heap. `RecursiveNamedPublicPhysicalSessionDirectWordForward.forward_call` preserves the existing output-fuel lower bound of one, using an accepted start and independent Source trace. Public runtime APIs are unchanged.

## Direct invocation and failure retain the common physical session (2026-10-14)

`82517c33` extracts the exact checked-method receipt. `7546d7ad` adds common public adapters for actual input registry extensions, direct packed calls and failures. `c40caab7` connects the existing recursive-index sequence to those adapters and the complete program certificate.

The original nine events create captures for `10` and `20`, select and invoke the first through a mapping, create a third capture for `30`, select and invoke the second, fail on a missing key, and invoke the oldest capture again. All nine independent Source traces and sufficient-fuel public endpoints remain. The failed call retains its original diagnostic and the reached heap, and the final call reads `10` from the original capture.

The program certificate covers all four actual cached rows. Its automatic catalog issuer is checked on that same certificate. Source code, the original checker budget of `1000`, the call sequence and the outcome definitions are unchanged. No caller supplies a body execution law. The index scanner validates the original base and key nodes and their scalar-key type.

Validation: 2,057 affected modules checked together, full build (7,185 jobs), registered tests (14,202 build jobs and final pass marker), kernel policy and 493 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The earlier seven-call method-evidence and coercion sequences and six-call direct relay still pass.

Independent Source well-formedness and successful finite certification remain explicit. Nonempty implementation methods still require their exact checked-method coherence receipt when the original checker budget differs. Full syntax coverage, further public input/output boundaries and meaning preservation across every actual compiler pass remain unfinished.

New proof APIs use the `RecursiveNamedPublicPhysical` prefix. The `SessionRegistry` module adds `SessionState.State.at_named_request`, which derives the actual encoder extension. `SessionRegistry{Scalar,Function,Failure}{Step,Forward}` provide `*_at_input_registry` endpoints. `DirectCallableApplicationBounds` dispatches authentic packed calls; `SessionDirectScalarStep`, `SessionDirectSuccessStep` and `SessionDirectScalarForward` connect them to retained public state. `SessionExportForward` and `SessionInitialExportForward` retain both the old history entries and the exact public output reimport receipt.

`CallableMethodBodyCoherence.Checked` records the complete original implementation-method body check. `ProgramAdmission.Certificate.issue_without_methods` and `issue_for_without_methods` derive that receipt from actual checker success at any budget when the retained method list is empty. The `*_with_methods` variants take the genuine method-check receipt explicitly. The existing `issue` and `issue_for_checked` signatures and finite `certify` computation are unchanged. Public runtime APIs are unchanged.

## Scoped evidence-bearing programs through public execution (2026-10-14)

`a6c0c881` extends the finite program certificate to scoped bodies, generic method evidence and ordinary closures. `32717957` connects the existing seven-call method-origin sequence to the common physical session theorems.

The scanner retains original Source nodes and metadata. It handles monomorphic lets, blocks, Unit branches, loops and equal assignment, together with unary and binary expressions. Actual Source typing supplies lexical contexts. Generic implementation formation checks parameter coverage and uniqueness; genuine cached selection supplies the selected method, substitutions and complete resolver dictionary. No caller supplies a method or closure execution law.

One actual certificate covers all 12 cached rows, including two generic methods. Its ten ordinary rows feed the existing header order, and the automatic catalog issuer is also checked on the same certificate. All seven independent Source traces and sufficient execution/output-fuel endpoints pass. Results remain `33 / true / 33 / 55`, with three retained closures and exact store lengths `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. The earlier seven-call coercion sequence and six-call direct relay still pass.

Validation: 74 affected modules checked together, full build (7,163 jobs), registered tests (14,162 build jobs and final pass marker), kernel policy and 410 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The certificate chooses either the existing closed coercion catalog with primitive methods, or the generic origin catalog with scoped methods. Ordinary closures work in both branches; coerced closure bodies currently require the closed branch. Independent Source well-formedness and successful finite certification remain explicit. Complete syntax coverage, broader input/output/failure connections and preservation across all actual compiler passes are still unfinished.

`ScopedSourceBodyAdmission` supplies the shared bounded statement certificate. `OriginsMethodAdmission` certifies the actual generic origin catalog; `ScopedMethodAdmission` derives physical method support from authentic selected Source. `ClosureAdmission` supports original ordinary and constrained closure bodies. `ProgramAdmission.Certificate.issue` and `issue_for_checked` retain their existing public signatures and derive one `PhysicalProgramSupport.Support`.

## Whole-program static admission through public execution (2026-10-14)

`4d7992ae` adds finite certification of the actual final cache and original Source nodes. `f232b62a` uses that certificate for the existing seven-call retained-closure sequence.

`ProgramAdmission.certify` checks every cached row, original lambda body, selected method source and coercion catalog. The ordinary direct-call table remains a conservative subset, but it cannot silently stand in for whole-cache coverage. Actual cached selection and original declaration/method provenance discharge the excluded-row cases. Original coercions, ordered requirements and captured environments remain intact.

`Certificate.issue` obtains selection identity from actual public checker success, builds the authentic ordinary catalog, closes table alignment, and constructs one common `PhysicalProgramSupport.Support`. No caller supplies named, closure or method coverage callbacks or an execution law. Source well-formedness, successful certification, recipe preparation and authentic initial receiver/entry receipts remain explicit premises.

The active seven-call regression now obtains one certificate from the actual program. Its existing three-header order uses `issue_for_checked` with finite raw-row alignment. The automatic full-catalog issuer is also exercised on that same certificate. All seven Source traces and sufficient execution/output-fuel guarantees remain, with scalar results `41 / 7 / 41 / 7`, three authentic exported closures and store lengths `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`.

Validation: 12 affected modules checked together, full build (7,158 jobs), registered tests (14,170 build jobs and final pass marker), kernel policy and 362 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Successful certification is additional admission for the supported fragment. It is not implied by compilation success. This version admits the current named let/return and factory bodies, terminal constrained direct calls with output coercions in closures, primitive terminal methods and closed coercion catalogs. Complete syntax coverage, checker-derived Source well-formedness, broader public inputs/results/failures and preservation across all actual compiler passes remain unfinished.

The new modules use the `CallableIndexedOwnedPrepared` prefix: `ClosedCoercionAdmission`, `PrimitiveSourceAdmission`, `PrimitiveMethodAdmission`, `CoercedClosureAdmission` and `ProgramAdmission`. Their executable checks retain original data; proof-only issuers construct authentic compiler packets and the shared support package. `Certificate.issue_for_checked` accepts a chosen inventory and raw-table alignment. `Certificate.issue` constructs the catalog and alignment internally. The public runtime API is unchanged.

## Common public session meaning from static program support (2026-10-13)

`4c919424` connects the existing physical body family to common production theorems for initial and later public calls. `bb4ad577` moves the existing seven-call retained-closure sequence onto those theorems.

A single `PhysicalProgramSupport.Support` supplies actual named, closure and method packets, original Source well-formedness and authentic registry diagnostics. It contains no body execution law. The shared numeric family derives preservation and reflection at the actual receiving registry. The public session theorems then derive argument and heap correspondence, exact scalar results or authenticated function exports, and the next retained session/history.

The forward direction takes an accepted public start and independent Source execution. It does not require an earlier successful public execution. It establishes separate execution and output-fuel bounds for all larger budgets; function returns append the handle actually exported by each resume. Initial input/heap conditions come from the genuine fresh bootstrap and its finite resume history.

All seven existing Source/public checkpoints and sufficient-fuel guarantees pass. Results remain `41 / 7 / 41 / 7`, with three distinct retained handles and store lengths `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`. The outer sequence theorem declarations remain unchanged.

Validation: coherent checks for 25 affected modules, the full build (7,152 jobs), registered tests (14,174 build jobs and final pass marker), kernel policy and 337 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This is a common theorem for the current supported families. Constructing the static support package still requires authentic coverage; compilation success alone does not provide it. Initial arguments use the existing data/simple-input boundary. Later calls require input encoding to retain the current receiving registry. These endpoints cover successful Word, Bool and function results; broader inputs/results, prescribed failures, all Source syntax and composition across every actual pass remain unfinished.

- `PhysicalProgramSupport.Support` stores static coverage; `preserves_bodies` and `reflects_bodies` derive semantic body ports at a genuine reached receiver.
- `PhysicalSessionState.StartedCall` contains only a checkpoint and successful startup. `Call` adds actual public completion; `FunctionCall` adds its returned handle. Forward theorems use `StartedCall`.
- `PhysicalSessionState.State` retains the exact public/indexed session, Source/native heaps, receiving registry and positive function history.
- `PhysicalSessionInitial.first_function` constructs the first returned history from real bootstrap and input admission. `PhysicalSessionInitialForward.first_function` gives uniform public fuel bounds from Source success.
- `PhysicalSessionScalarStep.State.finished_call` and `PhysicalSessionFunctionStep.State.make_typed_handle` reflect actual public success. Their forward counterparts preserve Source success and produce the next retained state.

Names above abbreviate the `CallableIndexedOwnedPrepared` or `RecursiveNamedPublic` module prefixes. The executable compiler/runtime API is unchanged.

## Generated factory formation through retained public closures (2026-10-13)

`15231c91` adds `NamedFactoryAdmission`, which checks a returned lambda in the actual cached Source. `82441690` replaces the existing factory's hand-written formation conditions with that certificate.

The check retains the original lambda node, its parameters and result type, the inner return and its complete expression. Only the lambda's own metadata is checked for the formation profile. The inner call keeps its original coercion and ordered evidence. Exact cached/Header identity and accepted terminal compilation construct the formation receipt and expression occurrence internally; independent Source typing remains authoritative.

All seven existing public calls, original Source traces, captured environments, retained histories and sufficient-fuel endpoints still pass. Results remain `41 / 7 / 41 / 7`; store lengths remain `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`.

Validation: coherent checks for 8 affected modules, the full build (7,143 jobs), registered tests (14,156 build jobs and final pass marker), kernel policy and 311 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The certificate covers an outer terminal return of a lambda with one inner value return. It certifies formation; the retained closure body and selected conversion method still use their existing authentic support producers. Certification completeness, wider syntax and preservation across all actual passes remain unfinished.

`scanSource` returns `SourceCertificate` from original finite Source data. `certifyCachedFactory` chooses the actual cached body roots. `at_header` transports the certificate using full cached identity. `of_actual` constructs accepted terminal compilation and the exact expression occurrence, then issues the existing physical formation support.

## Generated direct-call certificates through public execution (2026-10-13)

`a0cabf84` derives evidence-aware scoped support from executable certificates on the original cached Source. `cd13d9d5` connects it to the existing `relay(value) { let local = identity(value); return local; }` public proof.

The actual three-row cache supplies the nonempty direct-call table. Complete ordinary inventory coverage identifies each physical row and derives table alignment internally. Authentic Header transport preserves the complete cached function, original Source, ordered statement roots and result type. Independent Header typing supplies lexical contexts; accepted compilation supplies the body receipt. No caller supplies a child execution law.

The existing sequence `make10 / make20 / A10 / make30 / B20 / A11` retains all six Source/public meaning and sufficient-fuel endpoints. The checker success is observed before any classical Header selection.

Validation: coherent checks for 23 affected modules, the full build (7,142 jobs), registered tests (14,154 build jobs and final pass marker), kernel policy and 307 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Certification remains an additional static condition, with the current let/return and expression grammar. This connection uses the existing complete ordinary inventory; it does not establish that every compilation is certifiable. Factory formation, retained coerced bodies, broader syntax and preservation across all actual passes remain unfinished.

`NamedSourceAdmissionTransport.cached_named`, `header_data` and `source_at_header` recover exact cached/Header identity. `table_aligned_of_complete` derives scanned-row membership from the actual cache slots. `NamedEvidenceAdmission.certifySource` combines source admission with a check of the original requirements on every expression. `receipt` and `of_receipt` issue the accepted body receipt and existing evidence-scoped support.

## Executable named Source admission in public proofs (2026-10-13)

Commits `c76aef63` and `edab7dac` add static certification without changing the public runtime API.

- `NamedSyntaxAdmission.expression?` and `metadata?` return proofs from original finite Source data. Full direct instantiation metadata is retained.
- `NamedScopedAdmission.admitSource` checks the original body and returns `SourceAdmission`. `of_actual` uses real Header typing and accepted compilation to produce body support.
- `OrdinarySyntaxTable.collect` computes an ordinary raw-row table from the actual cache. `type?` and `range?` retain original Source nominal membership, arity and all raw replacements. `Table.aligned` connects these data to any authentic semantic catalog.
- `NamedCatalogAdmission.certifySource` builds the table and source certificate together. `of_actual` closes table alignment internally; `of_empty_actual` handles the empty direct-call table for any retained inventory. Neither executable scanner takes classically chosen Inputs or Headers.

Both ordinary `keep` and `use` in the existing retained-closure coercion sequence now obtain body support from the actual Source checker. All seven original Source and sufficient-fuel public endpoints still pass, with results `41 / 7 / 41 / 7` and store lengths `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`.

Validation: all 30 affected modules pass coherent checks. The full build (7,140 jobs), registered tests (14,150 build jobs and the final pass marker), kernel policy and 289 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The checker currently supports initialized monomorphic lets and value returns, with read, literal, group, direct-call and indirect-call expressions under the existing ordinary metadata conditions. Its fuel bounds static traversal. Successful certification is an additional condition; completeness from compiler acceptance is not proved. Factory formation, retained coerced closure bodies and method support still use their existing authentic producers. Wider syntax and preservation across all actual passes remain unfinished.

## Final ordinary catalogs and selected public starts (2026-10-13)

The public runtime API is unchanged. `760f1a28` adds the following proof entry points; `7a8a2de8` connects them to the existing public sequence.

- `OrdinaryCachedInputs.of_cached` derives a genuine Input at the exact cached position from original ordinary origin, complete Source replacement range and ordinary stage flags. Target and slot are derived internally.
- `OrdinaryCatalog.of_compiled` returns `Nonempty (Catalog compiled)`. The catalog preserves physical indices, contains every eligible ordinary row and issues genuine Headers through the existing inventory constructor.
- `OrdinaryCatalog.eligible_of_admissible` and `eligible_of_entry` recover ordinary origin and the complete raw range from actual cached selection and independent Source admission.
- `OrdinaryCatalog.covers_direct` combines original declaration admission with the actual compiled target and global lookup to obtain Header membership, slot and signature.
- `OrdinaryCatalog.recover_start_entry` constructs the catalog and returns the actual `Started` receipt with its complete cached-row `Matches`. It requires the real target equation, independent `ProgramEntryValid`, ordinary stage flags and successful public start. The catalog-specific variant is also available.
- `RecursiveNamedPublicPhysicalFrontdoor.recover_start_at` uses only the selected root; `recover_start_at_with` retains additional static admission at its actual Header. The existing `recover_start_covered` signature is unchanged.

The existing seven-call retained-closure sequence still has Source meaning and sufficient execution/output-fuel bounds, with scalar results `41 / 7 / 41 / 7` and store lengths `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`. A second regression recovers both Word and Bool identity rows added during method preparation and confirms that they were absent from the initial validation plan.

Validation: all 141 affected modules pass coherent checks. The full build (7,135 jobs), registered tests (14,140 build jobs and the final pass marker), kernel policy and 270 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. Existing work remains unchanged.

This constructs a finite semantic inventory by classical existence; it is not an executable classifier of every cached row. Source well-formedness, independent input admission and ordinary stage flags remain required. The start receipt identifies the selected function; argument values, dictionaries and heap representation still use their existing semantic relations. Automatic body syntax/metadata certification and complete preservation across all compiler passes remain unfinished.

## Output coercions through retained public closures (2026-10-13)

`d82a65a9` extends the proof API; `c48ec7bf` adds the closed public connection. The public Artifact, Value, Session, Outcome and Checkpoint APIs are unchanged.

- `Staging.Recursive.RawForm`, `CoercionStep` and `CoercionPath`, with their sized counterparts, describe evaluation of the original raw expression and its ordered conversion suffix. The new expression constructors require nonempty coercion metadata. Existing uncoerced constructors retain their APIs.
- `RawDirectAuthority.PortWithEvidence` is indexed by the actual coerced-direct compiler receipt. It retains the selected ordinary callee, original requirement/coercion partition and complete dictionary agreement. Existing uncoerced direct-call metadata keeps its empty-coercion condition.
- `CoercionAuthority`, `CoercionIssuance` and `CoercionChainIssuance` derive actual selected-method and emitted-chain receipts. `CoercionPathBounds` and `CoercedDirectExpressionBounds` compose the native executions with independent Source traces and the actual reached physical state.
- `PhysicalMixedRootStaticSupport.RootChoice` selects existing ordinary support or `CoercedDirectRoot`. `OrdinaryCoercedDirectRoots` and `OrdinaryCoercedTerminalSupport` issue the retained-closure support from authentic compiler actions and the original Source view. The existing `PhysicalMixedCallerFamily.preserves_with_methods` and `reflects_with_methods` close the internal callbacks.

Closed endpoints are `Tests.SourceCoreCoercionPublic.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The registered runner is `Tests.SourceCoreCoercionPublic.runForward`, imported through `SourceCoreCoercionPublicSequenceForward`. Handle inputs use the actual encoder registry; all sufficient factory outputs append the returned Entry to the history used by later calls.

The public sequence creates `A` from `make(true)`, creates `B` from `make(false)`, calls `use(A)`, creates `C` from `make(false)`, then calls `use(B)`, `use(A)` and `use(C)`. The four scalar results are `41 / 7 / 41 / 7`; native store lengths are `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficiently fueled factory completion appends its actual exported handle to the reusable history.

Validation: all 2,693 affected modules pass coherent checks. The full build (7,128 jobs), all registered tests (14,126 build jobs and the final pass marker), kernel policy and 235 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The seven public calls produce the stated results, and the existing work remains intact.

The connected coercion branch covers original direct-call expressions with nonempty output coercions, argument roots supported by the existing uncoerced grammar, and terminal conversion bodies. Its conversion catalog requires implementations without type parameters and with empty method assumptions. It does not yet cover coercions at every expression position or every conversion-body shape. Compilation success still does not supply all required static support or establish completeness of the finite selection/evidence checks. Remaining expression and control forms, generalized local functions and composition across all actual compiler passes remain incomplete.

The next general entry point should accept actual compilation and input-admission receipts, build the final ordinary inventory and static certificates internally, and invoke these existing public adapters. It must not ask a public caller to supply the body preservation laws that the family is intended to prove. Completeness of this certification step from compiler acceptance remains pending.

## Nested method evidence through public execution (2026-10-13)

`RecursiveMethodOriginIdentity.RootsProduced.functional` identifies complete primary and ordered method roots from the original requirement IDs. `same_from_origins` combines authentic body identity with coherence of actual caller/root entries to prove full ordered dictionary equality.

`CallableMethodOriginCoherence.validate` compares full raw trees at the selected assumptions. `CallableMethodSelectedRoots` recovers the exact primary and method roots from the real selector action. `CallableMethodOriginTable.validate` traverses the actual final specialization table and retains materializer/resolver agreement, caller coverage and origin coherence.

`OriginsMethodSelection.Catalog` contains original method formation and the validated table. `MethodSelectionIssuer.Catalog.origins` routes it through existing `_with_catalog` support APIs. `OperatorMethodIssuance.of_actual_with_origins` derives independent Source equality internally; the two earlier issuer APIs are unchanged.

Closed endpoints are `Tests.SourceCoreMethodOriginEvidence.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The public runtime API and Source evaluation rules are unchanged.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 106 affected modules pass coherent checks. The full build (7,082 jobs), all registered tests (14,034 build jobs and the final pass marker), kernel policy and 144 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected catalog supports evidence with premises and no longer requires a premise-free rule or global uniqueness of every valid evidence tree. It checks complete trees reachable from the actual caller and selected requirements. The finite materializer/resolver, caller-coverage and origin checks can still reject compiler-accepted selections outside their supported conditions. Their completeness from compilation success, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Methods with their own evidence through public execution (2026-10-13)

`CallableMethodResolverEvidence.Materialized` relates the complete ordered materialized method dictionary to the actual fresh resolver result. `CallableMethodResolverTable.validate` checks the finite final plan and produces `Ready`; its operator receipt includes actual caller coverage.

`RecursiveMethodDictionaryIdentity.same_coherent` derives complete Source dictionary equality. `LeafTraitEvidenceCoherence` derives coherence from an original premise-free implementation rule, while `CachedMethodEvidenceCoherence` transfers it through authentic cached method identity.

`EvidenceMethodSelection.Catalog` combines method formation, the validated actual table and cached coherence. `MethodSelectionIssuer` dispatches the generic and evidence catalogs through common support producers. `OperatorMethodAuthority.Port.resolved` retains the selected method resolver receipt; `MethodCallerResolvedEvidence` carries it through real parameter and lexical contexts. Existing generic and closed producer types remain unchanged.

Closed endpoints are `Tests.SourceCoreMethodOwnEvidence.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The public runtime API and Source evaluation rules are unchanged.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 160 affected modules pass coherent checks. The full build (7,050 jobs), all registered tests (13,970 build jobs and the final pass marker), kernel policy and 196 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected method catalog now supports nonempty method assumptions. It validates the complete ordered materialized dictionary against the actual caller resolver, and derives Source dictionary equality from the original leaf Mark rule. This finite static check can reject compiler-accepted selections outside its supported conditions. Coherence for evidence with premises, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Generic implementation substitutions through public execution (2026-10-13)

`MethodPathTyping.parent_typed` recovers original parent typing along actual method-call certificate paths. `MethodSelectionGoal.admissible` identifies the primary typed requirement with the actual selected goal. `MethodSelectionRanges.of_selected` derives the complete raw replacement range from original implementation formation, head matching and accepted specialization.

`GenericMethodSelection.Catalog` retains formation and empty method assumptions while allowing implementation parameters. `selection_support` constructs the method authority from the genuine caller ledger and parent typing. Existing closed catalogs embed through `Catalog.of_closed`; the named, ordinary-closure and method support producers expose additive `_generic` entry points. The seventeen existing producer types are unchanged.

Closed endpoints are `Tests.SourceCoreMethodGenericSubstitution.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The physical recursive family and public runtime API are unchanged.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 87 affected modules pass coherent checks. The full build (7,015 jobs), all registered tests (13,900 build jobs and the final pass marker), kernel policy and 161 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Method selection now retains arbitrary actual implementation substitutions. Its complete replacement range follows from the original well-formed implementation head, actual typed selection goal and accepted concrete specialization. The connected method catalog still requires empty method assumptions. Methods with their own dictionaries, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing calls inside implementation methods (2026-10-13)

`DirectCallAuthority.ResolvedCaller` retains the exact resolver output and complete semantic dictionary. `authenticated_evidence_of_resolved` serves both ordinary and method callers; the existing ordinary API delegates to it. `MethodCallerEvidence.of_selected` retains the selected method and reached lexical ledger. `MethodEvidenceScopedRoots.of_actual` derives direct-call roots from original Source metadata, accepted method compilation and the actual ordinary callee inventory.

`RecursiveNamedPreparedFinalPlanOrigins.final_member` derives final-plan membership from the actual cached row. `of_cached_origin` combines that row with genuine Source specialization provenance and derives its complete resolver dictionary from the accepted final preparation pass. It also applies to ordinary helpers discovered after the initial worklist.

Closed endpoints are `Tests.SourceCoreMethodDirectEvidence.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The existing physical recursive family and public runtime API are unchanged.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 728 affected modules pass coherent checks. The full build (6,985 jobs), all registered tests (13,840 build jobs and the final pass marker), kernel policy and 128 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers direct declaration calls from scoped implementation methods whose own assumption lists are empty. The callees retain nonempty trait dictionaries. The current method catalog still requires closed implementations without type parameters. Broader method selection and dictionaries, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Scoped implementation methods through public execution (2026-10-13)

`MethodScopedStaticSupport` retains the genuine selected principal, SourceAt, accepted flow and footer. `MethodScopedCollectors` uses native typing from the actual cached method and collects original child syntax at each reached lexical context. `MethodScopedRoots` issues read and Boolean child roots from the actual Source nodes.

`MethodBodies.Packet` selects terminal or scoped support with the same SourceAt. `MethodScopedBounds` and `MethodBodyBounds` connect actual parameter allocation to the existing imperative preservation and reflection proofs. `PhysicalMixedCallerFamily.preserves_with_methods` and `reflects_with_methods`, plus the named family ports, use those packets in the existing recursive proof. Earlier method APIs embed terminal packets.

Closed endpoints are `Tests.SourceCoreMethodImplementationScoped.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The public runtime API is unchanged.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `11 / 29 / 47 / 93 / 111 / 157 / 203 / 239`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 45 affected modules pass coherent checks. The full build (6,956 jobs), all registered tests (13,782 build jobs and the final pass marker), kernel policy and 140 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers actual implementation method bodies with local allocation, plain assignment and finite loops, using read and Boolean child receipts from the original method nodes. The generic scoped body proof accepts mixed expression roots; deriving such roots for calls and evidence inside methods is the next connection. Broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Scoped named calls through retained closures (2026-10-13)

`NamedPhysicalMixedScopedRoots` and `NamedPhysicalMixedScopedCollectors` derive child support from actual named compiler receipts, full caller evidence and per-site Header coverage. `PhysicalMixedNamedScopedStaticSupport` retains the collected statement tree and catalog sites.

`PhysicalMixedNamedScopedBounds` uses actual parameter entry and the existing imperative engine. `PhysicalNamedBodySupport.Support` is indexed by `NamedBodies.Body`; its terminal, formation and scoped cases feed `PhysicalMixedCallerFamily.preserves_with_bodies` and `reflects_with_bodies`. The corresponding named family ports and `PhysicalBodyPublicInvocationBounds` expose the same result and heap relations. The old terminal adapters delegate through `NamedBodies.of_terminal`.

Closed endpoints are `Tests.SourceCoreMethodNamedScoped.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The public runtime API is unchanged.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `11 / 29 / 47 / 72 / 90 / 115 / 140 / 162`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 54 affected modules pass coherent checks. The full build (6,924 jobs), all registered tests (13,718 build jobs and the final pass marker), kernel policy and 121 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers the existing scoped named-body grammar inside the same physical callable family as direct calls, selected methods and retained closures. The selected implementation methods in the closed fixture still have terminal bodies. Scoped implementation method bodies, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Selected methods through scoped closure mutation (2026-10-13)

`PhysicalBranchingClosureStaticSupport` retains the original branching compiler packet and a collected tree of physical mixed roots at every reached lexical context. `OrdinaryMethodScopedSupport` derives that support from the actual caller evidence and compiler action. `PhysicalClosureStaticSupport.PacketFor` and `SupportFor` distinguish terminal and scoped bodies while retaining their original association and stage.

`PhysicalBranchingLambdaBodyBounds` and `PhysicalBranchingLambdaApplicationBounds` reuse existing parameter entry, imperative flow and restoration. `PhysicalClosureApplicationBounds` selects the matching body case. `PhysicalNamedFormationCollectors.of_branching` produces the formation support from the original Source body.

Closed endpoints are `Tests.SourceCoreMethodScoped.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The public runtime API is unchanged.

The four scalar results are `11 / false / 33 / 55`; native store lengths are `9 / 27 / 45 / 61 / 79 / 95 / 108 / 121`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 47 affected modules pass coherent checks. The full build (6,893 jobs), all registered tests (13,656 build jobs and the final pass marker), kernel policy and 106 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers the existing scoped closure grammar with genuine method calls in local initialization, captured assignment and return. The closed fixture uses identity implementations of Word and Bool bit-not with no implementation parameters or method assumptions. Method-bearing scoped named bodies in the same physical family, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Selected methods inside retained closures (2026-10-13)

`PhysicalClosureAssociation` and `PhysicalNamedAssociation` retain the original callable identity and actual captured physical slots. `PhysicalCellOrigins` carries these facts through recursive payloads and heaps. The shared indirect prefixes accept this receiving representation; conversion to the older contextual representation is used only to classify callees.

`OrdinaryMethodPolicy`, `MethodBodyViewTransport` and `OrdinaryMethodScopedRoots` authenticate the original method-bearing closure expression. `PhysicalMixedCallerFamily` closes direct, selected method and indirect calls; `PhysicalMixedNamedFamilyPorts` supplies public body meaning. `InitializedPhysicalClosureArguments` and `RecursiveNamedPublicPhysicalClosureHistory` derive initial arguments and retain every returned capture.

Closed endpoints are `Tests.SourceCoreMethodClosure.closed_sequence_meaning` and `closed_sequence_forward_meaning`. They cover seven linked public calls, including original Source `f()` invocation, three distinct exported closures and all seven original-checkpoint fuel bounds. The public execution API is unchanged.

Validation: all 761 affected modules pass coherent checks. The full build (6,865 jobs), all registered tests (13,600 build jobs and the final pass marker), kernel policy and 210 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers ordinary retained closures with terminal expressions that call selected methods, and original Source indirect calls that invoke them. The physical family also retains named and builtin handle branches. The closed fixture uses identity implementations of Word and Bool bit-not with no implementation parameters or method assumptions. Combining this family with scoped closure mutation, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Selected operator methods through public execution (2026-10-13)

`OperatorMethodCertificates`, `OperatorMethodAuthority` and `OperatorMethodIssuance.of_actual` retain actual lowering, the selected implementation and the complete Source dictionary. `ClosedMethodSelection.Catalog` derives Source selection support from the original well-formed program and actual compilation plan.

`PhysicalGlobals.Authority` records every installed cache cell; `PhysicalGlobals.Slots` records every signature reference in the reached environment. `PhysicalCanonicalState` preserves both through parameter entry, allocation and restoration. `PhysicalCallerFamily` closes ordinary direct calls and method calls using shared recursive expression bounds. `PhysicalNamedTerminalSupport`, `InitializedPhysicalArguments` and `RecursiveNamedPublicPhysicalHistory` connect that family to the actual bootstrap and public sessions. The ordinary Header inventory need not cover method slots.

Closed endpoints are `Tests.SourceCoreEvidenceMethod.closed_sequence_meaning` and `closed_sequence_forward_meaning`. The public execution API is unchanged.

Validation: all 1,016 affected modules pass coherent checks. The full build (6,803 jobs), all registered tests (13,476 build jobs and the final pass marker), kernel policy and 199 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected fragment uses selected implementations with no implementation parameters or method assumptions, ordinary terminal callers and methods whose bodies return their argument. The shared proof covers both unary and binary method heads; the closed public fixture exercises unary dispatch. Combining these method paths with retained closures and scoped bodies, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing retained closure calls (2026-10-13)

`OrdinaryCallerReceipts.CallerAt` retains actual `Prepared`, `HeaderAt`, runtime context fields and the complete evidence dictionary. Ordinary formation and `OrdinaryAt` carry it through recapture. The existing named and nested formation producers derive it internally from their accepted compiler receipts.

`OrdinaryEvidencePolicy`, `EvidenceBodyViewTransport` and `OrdinaryEvidenceScopedRoots` recover the actual evidence-aware compiler policy and preserve reached Source/view nodes. `OrdinaryEvidenceCallsReady` and `OrdinaryEvidenceScopedSupport.of_actual` feed the existing canonical body and public history machinery. The original general body-view transport wrappers retain their signatures.

Validation: all 1,007 affected modules pass coherent checks. The full build (6,741 jobs), all registered tests (13,352 build jobs and the final pass marker), kernel policy and 73 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers evidence-bearing direct declaration calls in ordinary retained closure bodies, using the existing supported scoped grammar and actual named formation. It preserves the full closed replacement range and captured environment. Trait method dispatch, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing calls in scoped named bodies (2026-10-13)

`NamedEvidenceScopedCallerFrames.of_selected` derives the full caller frame from Prepared, HeaderAt, selected Source scope and RuntimeContextFields. It has no terminal-body restriction. `NamedEvidenceScopedRoots.of_policy_sites` authenticates every direct-call action using that actual frame and inventory; `of_accepted_sites` extracts the same root from real child acceptance.

`NamedEvidenceScopedCollectors.of_actual` passes these roots into the existing `NamedCanonicalScopedCollectors.of_imperative_compiler`. The actual statement tree supplies each local context, expression typing and native child proof. The resulting canonical branching support uses the existing numeric and public theorem family.

Validation: all 23 affected modules pass coherent checks. The full build (6,716 jobs), all registered tests (13,302 build jobs and the final pass marker), kernel policy and 65 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers supported direct declaration calls in the existing named scoped grammar, including local allocation, plain assignment and finite loops. It retains the full closed replacement range and excludes coercions and generalized local functions. Evidence-bearing formation and retained closure bodies, method paths, remaining expression/control forms and composition across every compiler pass remain incomplete.

## Nested closure formation through retained public handles (2026-10-13)

`PolicyRecipe` retains the actual type projector and source-cell allocator. `OrdinarySamePolicyLambdaProducer.of_expression` constructs the inner producer from the retained Code and its real reached child. `OrdinarySamePolicyLambdaFormation.of_expression` derives the Source frame and body-view receipts at that lexical context. `ReturnLambdaBodySupport.of_return_view` retains the individual original and prepared-view lookup facts required by the generated body.

`OrdinaryMixedScopedSupport.of_actual` issues canonical or formation certificates from the genuine collector. `MixedBodyStaticSupport.NestedBranchingSupport` and `SupportFor` retain the actual ordinary association. The nested body/application bounds use authentic parameter entry and captured-frame packets in both semantic directions. `OrdinaryAt.globals` is retained from actual formation.

Validation: all 1,448 affected modules pass coherent checks. The full build (6,695 jobs), all registered tests (13,260 build jobs and the final pass marker), kernel policy and 59 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers ordinary closure formation in retained scoped bodies. The inner closure retains its own local capture and may call a named function. Formation under further expression forms, evidence-aware scoped callers, method and coercion paths, remaining control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing generic calls through public execution (2026-10-13)

`DirectCallCertificates.Supported` retains the closed replacement range and original Source ordering. `Receipt` records actual target selection and accepts genuine evidence-lowering receipts. `DirectCallAuthority.EvidenceAt` records independent production and identification of the complete dictionary; `PortWithEvidence` carries this fact into the shared numeric proof.

`GeneralCallerEvidenceProfiles` extracts each direct action from its actual compiler policy. `NamedEvidenceCallerFrames.of_selected` obtains caller evidence and ledger conditions from the prepared named function and selected Source scope. `NamedEvidenceTerminalSupport.of_actual` composes these with the genuine finite inventory and original Source typing. Existing ordinary entry points remain available.

Validation: all 1,591 affected modules pass coherent checks. The full build (6,668 jobs), all registered tests (13,206 build jobs and the final pass marker), kernel policy and 117 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers direct declaration calls with a closed full replacement range, real requirement lists and no coercions. Formation inside retained closure bodies and under other expression forms, broader specialization and method paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Generic direct calls through actual specialization (2026-10-13)

`DirectCallCertificates.Ordinary` retains empty predicates, the full closed replacement range and the original Source parameter order for the actual plan. `Monomorphic.ordinary` preserves the existing empty-substitution route. `DirectCallAuthority.of_inventory` uses ordered issued Headers, and `DirectArgumentRows.callee_receipt` derives full Source validity from the reached context.

The generic fixture connects distinct specializations through the same public session and independent Source relation.

Validation: all 555 affected modules pass coherent checks. The full build (6,649 jobs), all registered tests (13,168 build jobs and the final pass marker), kernel policy and 52 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Calls carrying declaration evidence, further closure formation and expression forms, and composition across every compiler pass remain incomplete. This connection covers ordinary direct calls with empty predicates and a closed full replacement range.

## Recursive tuple formation and collected closure handles (2026-10-13)

`CanonicalScopedStaticSupport.Certificate.group` and `.tuple` retain genuine child code, ordered compiler rows and static Source validity. `CanonicalNamedBranchingSupport.preserves_children` and `reflects_children` recurse structurally through them. `NamedCanonicalMixedCollectors.of_actual` extracts the tree using the original root policy; `NamedCanonicalScopedRoots.of_policy` constructs general leaves without reselecting a callback.

`PreparedNamedSamePolicyLambdaProducer.of_expression` and `PreparedNamedSamePolicyLambdaFormation.of_expression` retain the actual lambda Site, compiler policy, body recipe, lexical scope and read diagnostics. Public endpoints are `Tests.SourceCoreRecursiveFormation.closed_sequence_meaning` and `closed_forward_meaning`.

Validation: all 400 affected modules pass coherent checks. The full build (6,633 jobs), all registered tests (13,136 build jobs and the final pass marker), kernel policy and 37 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Formation inside retained closure bodies and below other expression forms, wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Direct-call initialization and retained closure formation (2026-10-13)

`CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.Syntax` admits a general recursive expression or an ordinary return-lambda shape. `of_actual` uses the actual compiler action and original per-context Source typing to construct either a canonical root or the existing lexical formation receipt. The latter derives runtime context and evidence validity from the same real Header.

The public endpoints are `Tests.SourceCoreCanonicalFormation.closed_sequence_meaning` and `closed_forward_meaning`. The static packet combines the actual three-row named inventory and the ordinary canonical closure-body family; no execution law is a packet field.

Validation: all 21 affected modules pass coherent checks. The full build (6,612 jobs), all registered tests (13,094 build jobs and the final pass marker), kernel policy and 21 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Formation below recursive expression nodes and inside retained closure bodies, wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Canonical calls through scoped bodies and capture mutation (2026-10-13)

`CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport` provides additive named and ordinary scoped packets. `CanonicalNamedBranchingSupport` and `CanonicalBranchingLambdaBodyBounds` use the existing scoped imperative engine with strict canonical child bounds. `CanonicalBranchingLambdaApplicationBounds` retains the actual parameter binding spine and caller post.

`PreparedNamedCanonicalScopedCollectors.of_actual` and `OrdinaryCanonicalScopedSupport.of_actual` construct the packets from genuine compiler trees. `NamedCanonicalScopedRoots` and `OrdinaryCanonicalScopedRoots` preserve original typing, ledger, evidence, reached scope and diagnostic authority at each expression child. `NamedBodies.Compilation.canonicalBranching` and `MixedBodyStaticSupport.Packet.canonicalBranching` select these paths.

The public endpoints are `Tests.SourceCoreCanonicalScoped.closed_sequence_meaning` and `closed_forward_meaning`. `forward_word` constructs the actual Word/Bool/Bool packed input relation and retains the exact mutated Source heap.

Validation: all 422 affected modules pass coherent checks. The full build (6,593 jobs), all registered tests (13,056 build jobs and the final pass marker), kernel policy and 35 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The next connection combines a direct-call local initializer with closure formation in the same named body. Formation below recursive expression nodes, wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Recursive mapping operands and retained failures (2026-10-13)

`Staging.Recursive.IndexOutcome` records the independent terminal index behavior. `CallableIndexedOwnedPreparedStagedIndexSourceInversion` and `IndexHeadBounds` connect strict base/key children to the actual lookup suffix. `IndexDiagnosticAuthority.Port.missing` uses the actual receiving registry and diagnostics; named and ordinary producers derive `IndexReady` from the original compiler receipt and reached Source occurrence.

`CanonicalRecursiveCallerBounds` consumes that authority inside the common numeric family. The older recursive interfaces retain explicit `NoIndexes` restrictions, derived by their existing producers.

The public endpoints are `Tests.SourceCoreRecursiveIndex.closed_sequence_meaning` and `closed_forward_meaning`. `RetainedState.select_failure` keeps the exact failed returned session and history. `forward_failure` derives a sufficient execution fuel while quantifying over every output fuel. `ObservedFailure.exportsReady` derives the next-call authority from the original failed native receipt.

Validation: all 760 affected modules pass coherent checks. The full build (6,565 jobs), all registered tests (13,000 build jobs and the final pass marker), kernel policy and 91 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The next connection is canonical direct and index expressions inside named and ordinary scoped bodies, including local allocation, assignment and finite loops. Wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Direct calls inside retained closure bodies (2026-10-13)

`CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds` retains the actual parameter binding spine. `CanonicalTerminalLambdaBodyBounds` and `CanonicalTerminalLambdaApplicationBounds` use the reached capture, globals and caller restoration. `MixedBodyStaticSupport.Packet.canonicalTerminal` connects these bodies to the shared recursive family.

`CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport.of_actual` derives the actual terminal packet and each canonical root. `GeneralBodyViewTransport` preserves the real compiler action, including direct and builtin validation of their synthetic callee nodes. `SourceCoreElaboration.validateBuiltinFunctionCall_congr` compares exact node lookups and owner metadata.

The public endpoints are `Tests.SourceCoreClosureDirect.closed_sequence_meaning` and `closed_forward_meaning`. The latter combines `SequenceWitness.forward` for all three factory executions with `SequenceWitness.invocations_forward` for all three closure invocations. `runForward` checks the actual accepted source and six consecutive calls.

Validation: all 3,026 affected modules pass coherent checks. The full build (6,539 jobs), all registered tests (12,948 build jobs and the final pass marker), kernel policy and 76 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The next connection is recursive mapping index children, including callable payloads and the current receiving registry for missing-default diagnostics. Wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Direct builtin calls through public sessions (2026-10-13)

`CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt` records the authentic builtin compiler action. `CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds.preserves` and `reflects` compose ordered child execution with the selected builtin and retain the reached heap and full result. The four recursive caller folds consume this receipt.

`CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual_native` and `of_terminal_native` use `NativeMetadataFor`, including the actual integer-literal evidence. Existing ordinary metadata wrappers remain available.

The closed public endpoints are `Tests.SourceCoreBuiltinCalls.closed_sequence_meaning` and `closed_forward_meaning`. `SequenceWitness.forward` supplies sufficient public fuel at the three actual relay checkpoints. `runForward` is registered alongside the existing builtin runtime test.

Validation: all 710 affected modules pass coherent checks. The full build (6,512 jobs), all registered tests (12,894 build jobs and the final pass marker), kernel policy and 52 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The runtime and Core representation are unchanged. The next connection is direct declaration calls inside retained closure bodies. Wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Named direct calls and retained closure captures (2026-10-13)

`CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt` records the authentic direct compiler action. `DirectCallAuthority.Port` identifies its header from the complete initialized inventory. `DirectHeadBounds.preserves` and `reflects` compose ordered argument evaluation, real parameter entry and the selected body at the current owned pool. These shortened module names share the `CallableIndexedOwnedPreparedStaged` prefix.

`CanonicalRecursiveCallerBounds` derives both child directions from the generated certificate. `MixedRecursiveBodyBounds` constructs the ordinary and canonical body families in one numeric induction. `NamedCanonicalTerminalSupport.of_actual` obtains original Source and canonical scope authority from the real named compiler hook. Ordinary public callers derive both families internally.

The closed test endpoints are `Tests.SourceCoreDirectCalls.closed_sequence_meaning` and `closed_forward_meaning`. `SequenceWitness` retains all six Source traces, exact reached heaps and histories. `SequenceWitness.forward` gives sufficient public fuel for the three relay calls. `Tests.SourceCoreDirectCalls.runForward` is registered in the test runner.

Validation: all 696 affected modules pass coherent checks. The full build (6,494 jobs), all registered tests (12,858 build jobs and the final pass marker), kernel policy and 72 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected direct declaration fragment uses empty instantiation substitutions and predicates, and empty caller assumptions at direct sites. Wider specialization and evidence paths, other compiler alternatives and composition across every pass remain incomplete. Runtime unification is complete; the full meaning-preservation theorem is still in progress.

## Recursive constructor children and public handle reuse (2026-10-13)

`624b8d0e` adds independent staged Source traces for constructor payloads, including ordered child execution and failure propagation. `5bf2f084` connects the actual compiler receipts to preservation and reflection through the recursive caller family. The original constructor metadata and every payload value remain represented. Validity uses the actual closed substitution range, including unused entries; a native type projection alone does not establish this condition.

`9c7b952e` connects construction, export, nested handle collection and later calls through the exact returned public sessions. The example builds `Hold(factory(20), prior, factory, builtin)`, where `prior` captures `10`. The child call creates a separate closure capturing `20`. The collected closure returns `20`; an intervening factory call creates a capture of `30`; the older closure then returns `10`, and the retained builtin converts `37`. Each step retains its independent Source trace, reached heap and complete reusable handle history. Source success also gives sufficient execution and output fuel for constructor export and any requested selection from that output.

Validation: all 2,102 affected modules pass coherent checks. The full build (6,467 jobs), all registered tests (12,804 build jobs and the final pass marker), kernel policy and 34 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The Core representation and runtime are unchanged. Direct declaration calls are the next public connection under development. Broader compiler alternatives and composition across every pass remain incomplete.

The constructor head endpoints are `CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_preserves` and `constructor_reflects`. Static extraction retains `Syntax.constructor`, its raw closed substitution range and the ordered child certificates. The public endpoint is `Tests.SourceCoreConstructorCalls.closed_sequence_meaning`; `SequenceWitness.forward_collection` derives sufficient fuel and collected histories from the same Source construction trace. `Tests.SourceCoreConstructorCalls.runForward` is registered in the test runner.

## For headers, finite loops and retained captures (2026-10-13)

`fd2b9008` adds independent staged Source traces for `for` initialization, finite iterations and post-header items. `181fa159` connects them through genuine compiler receipts to both directions of the public execution proof. Header items include monomorphic declarations, discarded expressions and plain assignment. Normal body completion executes the post header; return and failure preserve the reached heap and bypass it. Leaving the loop restores the outer lexical scope. This fragment does not yet include `break` or `continue`.

The named `update` example executes one iteration and then zero iterations across successive sessions, returning `12 / 22`. `bb21dcc0` checks separate closures capturing `10` and `20`, an intervening `make(30)`, and one, zero and one loop iterations. Its direct results are `10 / 20 / 11`; the last result observes the first closure's previous update. Each public proof derives independent Source execution, exact heaps, retained histories and sufficient execution/output fuel at the original checkpoint.

Validation: the coherent affected graph covers 656 modules (268 authenticated cached results and 388 fresh checks). Full build (6450 jobs), all registered tests (12770 build jobs and the final pass marker), kernel policy and 82 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The Core representation and runtime are unchanged. Recursive constructor payloads, including calls that produce new closures, are the next public connection under development. Broader compiler alternatives and final composition across every pass remain incomplete.

`Staging.Recursive.ForItems` and `ForLoop`, with their measured counterparts, retain the actual ordered header and body effects. `PreparedNativeBranchingHeaderCollectors.tree` authenticates `lowerForItems` and its continuation. `AdmittedStagedImperativePositions` joins statement and initializer positions while preserving the existing scoped `reflects_at` and `preserves_at` interfaces. The closed endpoints are `Tests.SourceCoreNamedFor.closed_sequence_meaning` and `Tests.SourceCoreCapturedFor.closed_sequence_forward_meaning`; both examples are registered in the test runner.

## Match bodies and retained capture updates (2026-10-13)

`d36b6b1a` adds staged Source match traces, measured children, ordinary erasure and failure-state preservation. `d64b1b5a` connects them to actual compiler output and both directions of the public proof family. Compiler receipts retain the selected pattern bindings, hidden cells, catalog, allocator and typed literals. Leaving an arm restores the outer lexical context while retaining its heap effects.

The named `update` example returns `12 / 23` through successive real sessions. `106e24d6` adds six linked calls with separate closures capturing `10` and `20`, an intervening `make(30)`, and match arms that update captured cells. Direct calls return `10 / 20 / 11`, proving that the final call sees the earlier update. Independent Source traces, exact reached heaps, retained histories and sufficient execution/output fuel connect at the original public checkpoints.

Validation: full build (6408 jobs), all registered tests (12686 build jobs and the final pass marker), kernel policy and 56 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. Finite `for` initialization, body and post-header execution are the next connection under development; remaining compiler alternatives and final composition across every pass are incomplete.

`PreparedNativeBranchingCollectors.collected` derives `PreparedBranchingCatalogSites.Collected` from the accepted compiler result. Its tree and reachable catalog-site witnesses feed `AdmittedStagedMatchTreeHeads.preserves` / `reflects` and the scoped imperative folds. `CompatibleMatchTypedLiteralSites.Certificate.sites` derives literal support from actual pattern instruction typing. These module names share the `CallableIndexedOwned` prefix except `CompatibleMatchTypedLiteralSites`.

Closed endpoints are `Tests.SourceCoreNamedMatch.closed_sequence_meaning` and `Tests.SourceCoreCapturedMatch.closed_sequence_forward_meaning`. Their registered runners exercise actual checker acceptance, compilation, initialization and successive public calls.

## Recursive operators and retained function calls (2026-10-13)

`5f17535e` connects unary, binary and conditional expressions through the recursive caller family. Child proofs use the actual selected Source nodes, compiler receipts and reached states. Short-circuit operators and conditional expressions evaluate only the selected children. Numeric literals retain the actual checked evidence. The closed `drain(n)` example executes subtraction in a while body and returns `0 / 0` from successive calls with `3 / 0`.

`f68d6763` connects the same expression family to retained named function handles. The closed example obtains an `identity` handle and uses it inside both branches of `!flag ? f(value) + value : f(value) - value`. Successive calls return `22 / 0` through the preceding actual sessions. Both examples derive independent Source traces, exact reached heaps, retained histories and sufficient public execution/output fuel at their original checkpoints.

Validation: full build (6375 jobs), all registered tests (12620 build jobs and the final pass marker), kernel policy and thirty endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The `match` connection is under development; remaining compiler alternatives and final composition across every pass are incomplete.

`PreparedStagedOperatorBounds.preserves_at` / `reflects_at` supply the operator cases of the recursive family. `PreparedStagedNamedLexicalOperatorRoots.of_accepted` supplies an actual compiler producer for the call-free arithmetic fixture; the generic recursive operator certificates also admit indirect calls. Closed endpoints are `Tests.SourceCoreNamedOperators.closed_sequence_meaning` and `Tests.SourceCoreOperatorCalls.closed_sequence_meaning`.

## Scoped blocks connected to public execution (2026-10-13)

`ea7ac706` adds recursive staged block traces, measured children, ordinary Source erasure and failure-state preservation. `18c4e95f` connects those traces through the actual compiler, scoped lexical and imperative body proofs, and public sessions. A block restores the outer lexical context after its body while keeping the reached heap. Return and failure bypass the suffix; a compiler-confirmed terminal block requires no suffix execution premise.

The closed `update(value, next)` example allocates a block-local copy of `next`, writes it to the outer `value` cell and returns that value after leaving the block. Its successive calls return `12 / 23`. Both Source traces, reached heaps and retained histories come from actual initialization and the preceding returned session. Independent Source success supplies sufficient execution and output fuel at both original checkpoints.

Validation: full build (6346 jobs), all registered tests and kernel policy pass. Twenty-four audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Recursive primitive and conditional expressions are the next public connection under verification. Remaining control flow, broader compiler alternatives and final composition across every compiler pass remain incomplete.

`AdmittedStagedBlockSequences.preserves` / `reflects` compose the actual inner and suffix children. `PreparedStagedScopedBlockSourceInversion.block_and_tail` retains each child grade and intermediate heap. `PreparedNativeBranchingCollectors` derives the accepted block tree, including terminal blocks, and both scoped lexical/imperative folds consume it. The closed endpoint is `Tests.SourceCoreNamedBlock.closed_sequence_meaning`; its `run` is registered in the test runner.

## Named while bodies from actual call entries (2026-10-13)

Checkpoint `04a8a508` connects named bodies with plain assignment and finite while loops to the same public proof family. The actual argument bundle, global slots and retained frame determine the compiler's native input prefix. The proof restricts the canonical view to those used slots while preserving the complete runtime environment, heap and owned pool. Existing input metadata extension receipts supply the required registry condition throughout public dispatch.

The closed `choose(flag, value, stop)` example executes one iteration on the first call and none on the following call, returning `11 / 22`. Both independent Source traces, exact reached heaps and reusable histories come from actual initialization and the successive returned sessions. Source success provides sufficient execution and output fuel at both original checkpoints. Static support is extracted from genuine compiler acceptance, including its assignment policy and native typing; no body execution law is supplied by the fixture.

Validation: full build (6331 jobs), all registered tests and kernel policy pass. Twenty-two audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Scoped blocks are the next connection under verification. Broader expression/control-flow coverage and final composition across every compiler pass remain incomplete.

`PreparedNamedBranchingCollectors.of_imperative_compiler` derives the named imperative tree; the existing lexical `of_compiler` remains a wrapper. `PreparedStagedNamedBranchingEntryPrefix.entry_prefix` and `packet_take` derive the used prefix from authentic call observations. `PreparedStagedNamedBranchingSupport.preserves` / `reflects` retain the full caller postcondition. The registered closed endpoint is `Tests.SourceCoreNamedWhile.closed_sequence_meaning`, executed by `run`.

## Finite while bodies and retained closure captures (2026-10-13)

`494ac11a` adds finite staged while traces, their numeric grades, ordinary Source erasure and fault-heap preservation. `b658957a` connects them through authentic compiler receipts, closure application and public sessions. Each iteration restores its outer lexical bindings and retains its actual reached heap. The proof handles finite iteration counts, early return, condition failure and body failure; this fragment does not yet include `break` or `continue`.

The closed six-call example creates separate closures capturing `10` and `20`, invokes the first, performs an intervening `make(30)`, then invokes the second and the first again. Direct results are `11 / 20 / 12`, with one, zero and one loop iterations respectively. Every Source trace uses the preceding actual session and heap. Source success derives sufficient execution and output fuel at each original direct-call checkpoint. The initial diagnostic receiver is constructed from its registry.

Validation: full build (6318 jobs), all registered tests and kernel policy pass. Twenty-one audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Named while bodies are the next public connection under verification. Wider control flow, expression coverage and composition across every compiler pass remain incomplete.

`Staging.Recursive.While` and `Size.While` retain the original condition/body selections and iteration heaps. `PreparedStagedBranchingTree.Shape.whileLoop` and `PreparedNativeBranchingCollectors.tree` authenticate the accepted loop code. `AdmittedStagedWhileHeads` and `AdmittedStagedWhileSequences` feed the scoped imperative body proofs. The closed endpoint is `Tests.SourceCoreCapturedWhile.closed_sequence_forward_meaning`; `runForward` is registered in the test runner.

## Named conditional calls at their actual checkpoints (2026-10-13)

Checkpoint `00067020` connects named conditional bodies to actual initialization, the first call and a following call on its returned session. The closed `choose` example takes both branches and proves Source results `11 / 22`, exact successive heaps and reusable histories. The first branch allocates a local copy. Independent Source success also supplies sufficient execution and output fuel for every resume above the bounds at each original checkpoint.

Static support comes from the genuine named Header and accepted compiler flow. The diagnostic receiver is constructed from its registry, without an additional execution. Full build (6299 jobs), all registered tests and kernel policy pass; twelve audited endpoints use only the standard three axioms. Finite staged loops are the next connection being verified. Wider compiler coverage and final all-pass composition remain incomplete.

`PreparedStagedNamedBodies.Compilation.branching` stores the genuine named flow receipt. `PreparedNamedBranchingCollectors.of_compiler` derives its static support, and `PreparedStagedNamedBranchingSupport.preserves` / `reflects` supply the existing public family. The closed endpoint is `Tests.SourceCoreNamedBranch.closed_sequence_meaning`; `run` observes the actual checker, compiler, bootstrap and both calls.

## Conditional closure bodies connected to public execution (2026-10-13)

Checkpoint `b5b60f45` connects conditional statements through the actual compiler, recursive Source semantics, closure application and public sessions. Branch arms execute in scoped mode. Falling through restores the surrounding lexical context while retaining the reached heap; returning or failing stops the suffix. Compiler receipts retain the actual accepted flow, selected branch code and native typing.

The closed six-call example creates two distinct closures capturing `10` and `20`. The first call takes an assignment branch and returns `11`. After an intervening `make(30)`, the second closure takes a branch with a local copy and returns `20`; another call to the first returns its retained `11`. All calls use the preceding actual session and heap. The proof also derives sufficient public execution and output fuel from independent Source success for each of the three direct calls.

Validation: full build (6284 jobs), all registered tests and kernel policy pass. Twenty-seven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The actual named conditional-body example is being connected next. Loops, match, wider compiler alternatives and final composition across every compiler pass remain incomplete.

The new production route uses `PreparedStagedBranchingTree.Shape`, `PreparedStagedBranchingLambdaCompilerReceipts`, `PreparedBranchingLambdaBodySupport.of_branching` and `PreparedStagedBranchingLambdaApplicationBounds.application_preserves` / `application_reflects`. `PreparedStagedMixedBodyStaticSupport.Packet.branching` selects it in the existing recursive family. Scoped statement ports use `Staging.Recursive.StatementsIn`; the existing `Statements` interface remains the function-body mode.

The registered endpoint is `Tests.SourceCoreCapturedBranch.sequence_forward_meaning`; `runForward` constructs and checks its actual compiler and execution receipts. Core instructions and the public runtime API are unchanged.

## Named export-error continuations (2026-10-13)

At `e32c742b`, `InitializedExportErrors.public_run_export_error_seeds` creates the first History from actual bootstrap and a completed named call whose output export fails. `ActualRegistryNamedExportErrors.public_run_export_error_retains` extends a following named call at the actual receiving registry. Both expose independent Source success and retain the exact returned session/heap; failed export adds no new handle.

`SourceCoreCapturedMappingNamedExportErrors` registers a closed four-call sequence: initial export error, successful closure export, following export error, then reuse of that closure returning Word `10`. Full build (6247 jobs), all registered tests and kernel policy pass. Six audited endpoints use only the standard three axioms. Staged conditional bodies and final all-pass composition remain under development.

## Execution continuations and nested output collection (2026-10-13)

Checkpoint `a0c2197f` adds proof interfaces without changing Core instructions or runtime behavior. Full build (6244 jobs), all registered tests and kernel policy pass; twenty audited endpoints for these additions use only the standard three axioms.

| Module | Entry point | Connection |
| --- | --- | --- |
| `SourceCoreExecution` / `SourceCoreIndexedSession` | `Checkpoint.ResumeAt.then_resume`, `Checkpoint.ResumeChain.collapse` | Finite actual resumptions to the original checkpoint at summed execution fuel and terminal output budget. |
| `SourceCoreIndexedSession` | `Checkpoint.ExportErrorResultAt`, `Checkpoint.ResumeAt.export_error` | Successful native completion, failed public export and the exact returned session. |
| `RecursiveNamedPublicActualRegistryExportErrors` | `public_resume_export_error`, `public_invoke_export_error` | Direct export failure to independent Source success and retained History at the reached heap. |
| `RecursiveNamedPublicActualRegistryOutputCollection` | `public_invoke_succeeded_collects` | Actual nested output selection to ordered retained function entries. |
| `RecursiveNamedPublicActualRegistryOutputCollectionPreservation` | `public_resume_has_sufficient_fuel` | Source success to sufficient public fuel and History for selected actual output handles. |
| `RecursiveNamedPublicActualRegistryNamedReflection` | `public_run_succeeded_retains`, `public_run_failed_retains` | Following named calls at the actual receiving registry. |
| `RecursiveNamedPublicActualRegistryNamedOutputPreservation` | `public_resume_has_sufficient_fuel`, `public_resume_fault_has_sufficient_fuel` | Following named Source value/fault to public completion and retained History. |

`ResumeChain` records genuine intermediate exhaustion; it does not reset the heap or add intermediate output budgets. An export error retains older handles and successful Source effects, but creates no new output entry. Initial/following named export-error interfaces are still under development at this checkpoint.

`RecursiveNamedPublicNestedOutputSelections.Selection` traverses supported function, product, constructor-payload and explicit ordered mapping rows. It preserves duplicate keys and repeated handles. `SourceCoreCapturedNestedCollectionForward` registers a closed seven-call example that collects `A, B, A` from a real mapping output and proves captured results `10 / 20 / 10` across another allocation. Mapping defaults and additional annotated selection forms remain outside this selection grammar.

## Actual input registries and general public output (2026-10-13)

`8f1fdfb2` connects current History to the registry produced by the actual input encoder. A proof-only receiver is constructed at that exact context, and genuine compiler diagnostics retain their token meanings along the forward extension. This removes the need to obtain a receiver from a separate execution or assume a reverse metadata extension. Captured environments, ordered entries and the reached Source heap stay intact.

Independent successful Source execution now supplies execution and output fuel bounds for all represented output shapes, including constructors, mappings, proxies and function leaves. The codec proof retains mapping order and duplicate rows, follows the genuine handle registry, and reuses an existing metadata ID even when the registry budget is full. The bound is uniform over execution fuel and export generations.

`2f941db0` connects the same general output proof to the first named call. Actual bootstrap, its export authority and the input encoder derive the initial heap, arguments and receiving context. The returned session starts a reusable History. The closed mapping-input example checks the original factory checkpoint and two direct calls with ordered mapping rows; both return the captured Word `10`. Its proofs cover reflection and sufficient public fuel from Source success. The mapping metadata already exists in the static registry; this example does not assert strict registry growth.

Validation: full build (6205 jobs), all registered tests and kernel policy pass. The ten actual-registry production endpoints, eight mapping endpoints and two initial-output endpoints audited for these units use only `propext`, `Classical.choice` and `Quot.sound`.

Next connections are collection of handles inside constructor/mapping outputs, following named calls at the actual registry, and direct Source failures with authenticated argument arity. Broader control flow, suspended/export-error continuations and final composition across every compiler pass remain incomplete. Earlier dated sections describe their own checkpoints.

The main new proof entry points are:

| Module | Entry point | Connection |
| --- | --- | --- |
| `CallableIndexedOwnedPublicFaultReceivers` | `Receiver.at_context` | Authentic diagnostic receiver without a completed execution. |
| `RecursiveNamedPublicActualRegistryStart` | `packed_input` | Actual encoded input, current captures and exact metadata context. |
| `RecursiveNamedPublicActualRegistryReflection` | `public_resume_succeeded`, `public_invoke_succeeded` | Public completion to independent Source execution and returned History. |
| `RecursiveNamedPublicActualRegistryOutputPreservation` | `public_resume_has_sufficient_fuel` | Direct Source success to sufficient public fuel for general output. |
| `CallableIndexedOwnedPreparedStagedInitializedOutputPreservation` | `public_resume_has_sufficient_fuel` | Fresh initialization and first Source success to public output and initial History. |

These endpoints retain the fixed function model, authentic static body support and structural public inputs. Returning a nested function value and adding that function to the retained history are distinct proof steps; nested collection is the next integration unit.

## Captured-cell assignment proof support (2026-10-13)

At `b1e23802`, the static mixed-body packet also supports imperative closure bodies containing bare plain assignment. `CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerReceipts` and `CallableIndexedOwnedPreparedStagedImperativeLambdaReadRoots.of_reads` retain actual compiler and reachable-read receipts. `CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds.application_preserves` and `application_reflects` feed the existing recursive public family. The public runtime API is unchanged.

`Tests.SourceCoreCapturedAssignment.sequence_meaning` proves the six-call factory/direct-invocation sequence with captured results `10 / 20 / 11`, including an intervening factory allocation and repeated mutation of the first capture. Full build (6182 jobs), all registered tests and kernel policy pass; eight audited endpoints use only the standard three axioms. These endpoints do not yet establish arbitrary imperative bodies or general metadata-bearing public output export.

## Public function export from Source success (2026-10-13)

Checkpoint `f7cbbfd8` passes the full build (6152 jobs), all registered tests and kernel policy. The ten preceding production/Source endpoint audits and two new initial-function endpoint audits use only `propext`, `Classical.choice` and `Quot.sound`.

`5edd2500` proves sufficient public fuel for function results of direct named, builtin and closure applications. Successful independent Source execution implies actual function export for every sufficient execution budget and output budget at least `1`. The returned function joins the exact reached History. `Session.ExportsReady` records genuine issuer and registry integrity; actual initialization creates it and real session transitions preserve it. The proof does not assume that native execution or export succeeds. The existing runtime entry points and History type remain available.

`f7cbbfd8` closes the corresponding initial named-call route. Its public theorem derives starting arguments, heap and caller from actual fresh initialization and startup, then constructs the first remembered function at the Source after-heap. The registered example proves both initial and later direct export at their original checkpoints while retaining the actual `10 / 20 / 10` capture sequence.

`c0a118be` extends the same staged Source relation with bare plain assignment, RHS failure and target lookup failure. Target resolution precedes the RHS; a successful write uses the RHS's actual final heap. Both erasures, numeric grades, fault preservation and existing dependent proofs have been checked. The authentic compiler/body/public connection for these new assignment rules is still in progress. General output decoding, wider imperative control flow, suspended/export-error continuations and all-pass composition remain open.

The new proof endpoints are `RecursiveNamedPublicDirectCallableFunctionPreservation.public_resume_has_sufficient_fuel` and `CallableIndexedOwnedPreparedStagedInitializedFunctionPreservation.public_resume_has_sufficient_fuel`. Rich bootstrap receipts retain the issuer created by the actual operation; they mint once. Whole-function export preserves the requested raw type, while semantic entries retain their original Source type using runtime compatibility.

## Lexical closures, callable preservation and failure continuation (2026-10-13)

The latest verified implementation checkpoint is `b9c241f9`. The full build (6147 jobs), all registered tests and kernel policy pass. The endpoint audits for these additions use only `propext`, `Classical.choice` and `Quot.sound`.

- `3341275f` connects lexical closure bodies through genuine compiler receipts, both semantic directions and the existing recursive public family. Static packets retain the actual allocator, accepted flow and expression children at their reached contexts; they do not assume a body execution law.
- `fc167824` derives sufficient public execution fuel for successful Word results from named, builtin and closure applications. With output fuel at least `1`, the actual checkpoint returns the same Word and a History at the Source after-heap. The closed named/builtin example proves captured Word `10` and builtin Word `37` at its original checkpoints.
- `b9b55505` closes six actual calls for a factory returning `lam() { let copy = seed; return copy; }`. Separate handles retain captures `10` and `20`, including after an intervening factory allocation. Direct results are `10 / 20 / 10`; every step uses its predecessor's actual session and heap.
- `354a2345` connects an initial uninitialized-local failure to a later successful identity call. The proof identifies the absent allocated cell, exact Source failure, subsequent Word `37` allocation and both returned Histories.
- `b9c241f9` proves sufficient public fuel for that initial Source failure, with any output budget. Actual bootstrap and input receipts derive the starting conditions; the result retains the same Source after-heap and a reusable failed History. The closed example includes output fuel `0`.

Next work connects forward function-handle export using registry integrity derived from actual initialization, and captured-cell assignment through the same staged Source relation and public proof family. General imperative control flow, constructor/mapping output selection, suspended/export-error continuations, receiving-model changes and final composition across all compiler passes remain open. Historical percentages are unchanged; the completed connections above describe this checkpoint. Earlier dated sections retain their original scope.

The new public endpoints are `DirectCallableWordPreservation.public_resume_has_sufficient_fuel` and `InitializedFailurePreservation.public_resume_has_sufficient_fuel`. The existing closure-specific Word endpoint remains available. `OrdinarySequenceFor.compiled` accepts an authentic static mixed-body packet, allowing lexical closure support to enter the full recursive public family. Operational runtime behavior and Core instructions are unchanged at this checkpoint.

## Lexical body support and captured-local public execution (2026-10-13)

`CallableIndexedOwnedPreparedStagedNamedBodies.Body` is the static named-body input to the public semantic endpoints. It keeps the actual prepared header, layout and either a terminal or lexical compiler receipt. Existing terminal consumers use `Body.of_terminal`. The endpoint argument name `namedTerminals` is retained for compatibility, but its type is now `Body`; `namedSupport` uses `NamedBodiesSupport.Support` for either branch.

`PreparedNamedLexicalCollectors.of_compiler` builds lexical support from the accepted compiler action, original Source typing and children at their actual contexts. `PreparedNamedLexicalLambdaFormation.of_expression` supports lambda formation after local declarations. Body preservation and reflection retain an arbitrary final Source context while restoring the native caller scope. `SingleReadSequence.sequence_on` and reached-only metadata conditions admit a captured read without constraining unrelated source nodes.

`InitializedHistoryFailures.public_run_failed_seeds` connects actual initialization, input encoding and an initial failed public call to a reusable empty-entry History at the returned failure session. Final heap typing follows from the reflected Source fault trace.

`Tests.SourceCoreCapturedLocal.sequence_meaning` closes the real compiler and public API route for `let local = seed; return lam() { return local; };`, followed by two direct invocations. It includes the allocated capture cell containing Word `10`, exact Source outcomes and successive returned histories. Production changes are `8537c3c2` and `a0cd0dba`; the fixture is `a20e0891`.

Full build (6108 jobs), registered tests and kernel policy pass. The twelve production and three fixture endpoints audited at this checkpoint use only the standard three axioms. Closure-body lexical support, a closed failure continuation, general forward result export, broader statements and final compiler composition remain in progress. Earlier dated sections describe their own checkpoints.

## Direct output collection and forward public Word execution (2026-10-13)

Commit `af456bf5` connects direct-call outputs to subsequent calls. The actual fixture creates a closure capturing `10`, issues the named `make` handle, directly invokes it with `20`, remembers that newly exported closure, then invokes the original, new and original closures. The Source results are exactly `10 / 20 / 10`; the two closure handles are distinct, and every step retains all entries at the actual returned session and heap.

`History.collect_packed_success` and `DirectCallableOutputHistory.public_invoke_succeeded_collects_function_tree` append selected function leaves from the real output codec and full Source result. Selection currently supports whole functions and product leaves. The actual requested raw result type is kept separately from its Source type; runtime compatibility suffices, including erased annotations. Earlier entries remain in order.

The forward direction is now public for successful Word-returning closure applications. `DirectWordPreservation.public_resume_has_sufficient_fuel` starts with the independent Source trace, current History, structural input and genuine packed startup. It derives a native execution threshold. Every actual public resume above that threshold, with output validation fuel at least `1`, succeeds with the same Word and a retained History at the exact Source after-heap. It assumes neither native completion nor export success. Successful Source allocation derives actual arity; raw handle result annotations may differ after runtime normalization.

The registered packed fixture now also proves this universal forward statement for its two original public checkpoints (arguments `99` and `123`, captured result `10`). It reuses the same actual calls and derives its Source traces through the independent reflection theorem.

Validation: strict Lean, full build (6072 jobs), all registered tests, kernel policy and independent reviews pass. Ten audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. General forward callable/output coverage, constructor/mapping output selection, lexical and imperative body coverage, suspended/export-error continuations, receiving-model changes and all-pass composition remain open. Work estimates are unchanged.

## Direct named/builtin calls and failed histories (2026-10-13)

Commit `cb736645` connects direct public invocation for named functions, builtins and closures through the same current History. The registered `SourceCoreDirectIssuedPublicExecution` fixture creates a capture of Word `10`, issues the named `read` handle, directly calls it with the captured closure, issues `wordFromInteger`, and directly calls it with integer `37`. The independent Source results are Word `10` and `37`, with exact singleton argument vectors and histories for all three retained functions at the actual returned sessions.

Actual callable identity selects the relevant application proof. The named branch uses its original compiler payload, Source declaration and supported recursive children; the builtin branch uses the actual primitive identity. Genuine issuance derives each handle's exact raw type. Both use the real packed encoder and complete result/heap/caller postconditions.

The failed direct-call endpoint also returns a reusable History for its actual failure session. Source fault preservation derives final heap typing from the current History, input typing and reflected fault trace. Existing captures retain effects performed before the failure. This generic failure endpoint is checked, but the new closed fixture exercises successful calls only.

Validation: strict Lean, full build (6065 jobs), all registered tests, kernel policy and independent reviews pass. Twelve audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Direct output collection, forward public execution/export fuel, wider static body coverage, suspended/export-error continuations, receiving-model changes and final all-pass composition remain open. Estimates remain unchanged.

The new interfaces are `DirectCallableApplicationBounds.reflects_packed`, `DirectCallableHistory.completed_reflects`, and `DirectCallablePublicHistory.public_invoke_succeeded_function_tree` / `public_resume_succeeded`. They consume every supported callable kind without a closure-shape premise. `DirectCallableFailures.public_invoke_failed_function_tree` / `public_resume_failed` preserve histories on actual failure. `History.after_packed_failure` transports earlier entries using the original failed-result receipt. The existing closure API retains its explicit arity result and native sufficient-fuel direction.

## Packed direct closure input and returned History (2026-10-13)

Commit `ac3a55b3` adds the semantic packed-input route without changing runtime API behavior.

- `DirectPackedInputMeaning.actual_start_compatible` derives the actual selected raw parameter/result, packed encoder and checkpoint state from startup and the current handle import. Runtime compatibility with the Source signature is proved by resolution; exact raw equality is not required.
- `DirectClosureApplicationBounds.reflects_packed` and `preserves_packed` use actual closure arity to unpack the Source argument vector, with complete result and caller/heap postconditions.
- `DirectPackedHistory.completed_reflects` and `has_sufficient_fuel` obtain callable and input meaning from current History and the original encoder. The latter concludes native completion for sufficient fuel at that exact checkpoint.
- `DirectPackedPublicHistory.public_invoke_succeeded_function_tree` derives input metadata identity for scalar/handle/product trees and returns the real public completion, Source trace and reusable History. `public_resume_succeeded` also accepts metadata-bearing inputs with their actual registry extension.
- `NamedReturnLambdaFormation.of_terminal_parameters` constructs genuine nonempty lambda parameter contexts. The old nullary wrapper remains available.

The registered `SourceCoreCapturedPackedPublicExecution.sequence_meaning` proves actual `make(10)`, direct invocation with `99`, and reuse with `123`: exact Source argument lists, captured results `10 / 10`, and both returned histories. Static compiler support is constructed inside the fixture.

Validation: strict Lean, full build (6054 jobs), all registered tests, kernel policy, independent review and eleven standard-axiom audits pass. These public semantic wrappers currently select closures. Direct named/builtin semantic dispatch, failed direct histories, output collection and the forward public export/fuel connection remain unfinished.

## Direct retained-closure invocation (2026-10-13)

Commit `dbfcaf47` adds proof receipts to direct public invocation. `invokePacked` retains its existing result and performs one startup and one resume. `invokePackedWithReceipt` additionally returns `Session.InvokeAt`, tying that same execution to its startup and completion.

- `Checkpoint.HandleStart` and `Session.HandleSelectionAt` expose the actual callable selection, descriptor gate, packed encoder, initial native state and raw requested signature.
- `InitialRegistryFrom` supports preservation of earlier authenticated handles through success and failure. `SucceededResultAt.function_source_type` derives an exported handle's exact raw type from the actual exporter.
- `RecursiveNamedPublicDirectHandleMeaning.public_invoke_succeeded_reflects_unit` reflects one successful public call of a zero-parameter closure to Source application and the complete returned caller/heap postcondition. Recursive body laws are constructed internally.
- `History.after_packed_success` retains the existing ordered entries at that actual returned session and heap.

The registered `SourceCoreCapturedDirectPublicExecution.sequence_meaning` joins three factory executions and three direct invocations, including distinct captures and an intervening allocation. Source Word results are exactly `10`, `20` and `10`. It supplies no callable representation or body execution premise.

Validation: strict Lean, full build (6042 jobs), all registered tests, kernel policy and independent reviews pass. All eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The semantic public endpoint currently requires zero Source parameters and packed Unit. Generic frontend receipts cover other signatures, but direct semantic arguments, failure continuations, output collection and the forward public fuel connection are still being implemented.

## Named terminal scope conditions (2026-10-13)

`CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual` no longer takes `NoLambda` or specialization-key uniqueness arguments. `CallableIndexedActualNamedSourceReceipts.hook_sidecar` recovers the genuine canonical sidecar. `RecursiveNamedPreparedScopeCoherence.selected_frame` derives guard-frame equality from the actual preparation and Source well-formedness, for named or anonymous registry selections. It preserves the selected scope and substitution; it does not identify distinct sidecars or keys.

`RecursiveNamedLambdaFreeSelectedScopes` has been removed. The captured-reuse fixture no longer checks owner-key uniqueness. `OrdinarySequenceCallerBounds.sequence_coverage` is public for application consumers that reuse the same supported body family. Full build (6035 jobs), registered tests, kernel policy and four standard-axiom endpoint checks pass. Runtime API behavior is unchanged.

## Public continuation for actual captured closures (2026-10-13)

Commit `c187ce09` adds the registered `SourceCoreCapturedReusePublicExecution` test, which connects six actual public calls to Source execution and returned histories: `make(10)`, `make(20)`, `read(first)`, `make(30)`, `read(second)`, `read(first)`. The three read outcomes are proved to be Word `10`, `20` and `10`. Distinct exported handles and every earlier history entry remain attached to the real returned sessions.

The runtime API is unchanged. The following proof interfaces close this concrete continuation:

- `RecursiveNamedPublicHistoryFrontdoor.recover_start` is now public. It derives the selected startup and Source function from the accepted public start and current native state. Direct continuation consumers can then provide an exact Source argument list.
- `StartAt.function_registry` derives metadata identity for an actual singleton function-handle input. `StartAt.returned_registry` retains the input encoding's registry in the actual successful returned session.
- `RecursiveNamedPublicWordResultMeaning.result_word` identifies the Source Word outcome using the same full invocation result and genuine public result decoding.
- `NamedRecursiveTerminalSupport` constructs the named indirect-read support from the accepted terminal compiler action, actual source nodes and selected sidecar. The current `RecursiveNamedPreparedScopeCoherence` adapter derives guard-frame agreement from authentic preparation and Source typing; the earlier lambda-free restriction has been removed.

The fixture's `RetainedState` carries the real indexed/public session correspondence, current caller/heap/store, metadata identity and History. Its make/read steps produce the next state from the previous one. `sequence_meaning` constructs static support internally and preserves all six state transitions. It accepts no replacement argument representation, Source execution or body meaning hypothesis.

Validation: strict Lean, the actual six-call runtime fixture, full build (6035 jobs), all registered tests and kernel policy pass. Independent review found no issues in the exact input, session, heap and history connections. All eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The formal returned-closure read is now covered for this program; generic compiler/body coverage and the final all-pass theorem remain incomplete. Estimates are unchanged.

## Captured-read factory and retained static provenance (2026-10-13)

Commit `4c2dbe39` leaves the public runtime API unchanged. `SourceCoreCapturedLambdaPublicExecution.public_factory_meaning` now instantiates the public seed theorem for the actual compiled `make(seed: Word)` factory, called with Word `10`, whose result is `lam() { return seed; }`. It returns an independent Source application and singleton History for the actual exported handle and returned session. The fixture derives Source typing, body support, inventory, family and metadata premises internally.

The proof adapters retain the following facts at the same compiler Code:

| Interface | Retained or derived fact |
| --- | --- |
| `LambdaPolicyRecipes.Retained` | The original body and full policy recipe, with its outer root fuel independent of a nested Code's fuel. |
| `BodyView` | Exact original metadata at expressions reachable from the closure body. |
| `BodyReasons` | Ordinary body tokens from the actual compiled diagnostic issuer. |
| Ordinary provenance and prepared adapters | Source lexical declarations for the original captured scope and context. |
| `NamedLambdaProducer` / `NamedReturnLambdaFormation` | The actual terminal compiler Site, exact view/reason provenance and same-Code return body. |
| `SingleReadSequence.sequence` | The captured-reference sequence family, constructed from original nodes and authentic provenance. |
| `StartAt.simple_registry` | Metadata identity for accepted simple inputs, including the actual Word argument. |

Concrete compiler producers derive these facts. Generic APIs accepting arbitrary Sites require authentic static receipts; they cannot infer original source schemes or diagnostic identity from native typing. Existing empty-body, terminal and discard adapters forward the added provenance.

The fixture's later `invokePacked` call checks Word `10` at runtime. The public Source theorem currently covers creation, capture, export and History; the later public read through that history is covered by the six-call proof above. Direct `invokePacked` reflection is still being connected. The receiving diagnostic table is issued by a separate genuine indexed execution of the same artifact. Progress estimates are unchanged.

Validation: strict Lean, full build (6019 jobs), all registered tests, kernel policy, the concrete public fixture and the six-endpoint axiom audit pass. The audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

## Closed compiler-to-public lambda factory (2026-10-12)

Commit `6b22e7b5` adds `SourceCoreClosedLambdaPublicExecution`, a registered test of `function make() returns (function() returns ()) { return lam() {}; }`. Its actual checker, compiler, initialization, input encoder and public execution receipts instantiate `public_run_succeeded_remembers`. The theorem concludes an independent Source application and a singleton History for the same handle and returned public session. Source typing, complete nonempty inventory, compiler body support, the closure family and initial metadata relation are constructed inside the fixture.

`OrdinarySequenceFor.empty` admits genuine empty unit bodies. The static producer derives the emitted footer from the same retained compiler callback. Its execution bounds use the heap and store after actual parameter allocation and retain caller restoration. `NamedEmptyLambdaFormation.of_terminal` derives the native child type from the accepted terminal compiler receipt and constructs the original empty-body certificate. `StartAt.empty_registry` derives metadata identity for an actual empty input vector.

This concrete case proves first formation, export and History construction. It does not yet call the returned closure or capture a variable. The diagnostic receiver comes from a separate genuine indexed execution of the same artifact, with its receiving metadata extension proved from actual initialization. The mutable assignment/match regression remains runtime coverage beyond the admitted static body grammar. Captured-body fixtures, broader body coverage, suspended/export-error continuations and final all-pass composition remain open.

Validation: strict Lean, full build (6008 jobs), all registered tests, kernel policy and independent review pass. Eleven checked endpoints, including the closed public theorem, use only `propext`, `Classical.choice` and `Quot.sound`. The work estimates remain unchanged.

## Histories after failed public calls (2026-10-12)

Commit `aba75ce5` connects a supported failed public call to a reusable history at its actual failure heap. `CallableIndexedOwnedPreparedStagedHistoryPublicFailures.public_run_failed_retains` derives the initial Source runtime, callable type and packed argument typing from the existing history, real input encoding and selected declaration frame. `RecursiveNamedPublicHistoryFrontdoor.public_run_failed_retains` also recovers startup and Source selection from the accepted public start. Neither endpoint requires a separate assumption that the final heap is well typed.

`Staging.Recursive.FaultPreservation` proves heap typing and type-identity preservation for the existing recursive staged trace grammar. The proof follows faulting children and retains the effects of successful prefixes and real binder allocations. It covers both semantic and staging faults without identifying their failure tags. The public consumer uses this result immediately to construct `History.after_failure`.

The actual failed-session receipt preserves each earlier handle's full native payload through registry extension. The Source result preserves its raw type, code, captured references and meaning at the returned heap. A later supported call may reuse any retained entry, and no new export is fabricated on failure.

The runtime regression mutates the first of two retained product-output closures from `21` to `30`, then fails on an uninitialized local. An intervening recursive call returns `31`; the original handles then return `31` and `112`. This checks retention of the mutation and independence of the second capture. As before, these mutable regression bodies exceed the current static body grammar, so this runtime test is not a closed instance of the semantic endpoint.

Validation: strict Lean, full build (6003 jobs), all registered tests and the kernel policy pass. Independent review found no issue in the failed-session, history or public adapters. The twelve checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The preceding startup/product/lambda unit is `82944a4e`, documented in `4bea6081`. Suspended/export-error continuations, an initial history from a first failed call, full body coverage, non-product output collection, model/registry changes and all-pass composition remain open.

## Earlier proof interface checkpoint (2026-10-12)

The current connection derives actual public startup and Source selection for history-based successful calls, collects selected function leaves from product outputs, and supports ordinary lambda formation at a named terminal expression. Earlier issuance, restoration and nested-input interfaces remain available. Validation: strict Lean, full build (5997 jobs), all registered tests and kernel policy pass. Independent reviews found no issues in output collection, public startup recovery or the lambda state connection. The twenty-one checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The empty-body certificate helper also passes the full build and axiom audit. Exact raw types, metadata extensions and supported static body certificates remain explicit. The mutable assignment/match regression is runtime coverage; the closed empty unit-lambda factory now instantiates the public theorem as described above. Captured-body fixtures and returned-closure invocation remain open.

Applied source and runtime materialization is committed in `f0f6a910`: four modules, 84 new declarations and sixteen interfaces. All 18449 preceding declarations remain exact.

Applied ancestry and ordinary sequence readiness is committed in `55fe02aa`: two modules, 5 new declarations and five interfaces. All 18444 preceding declarations remain exact.

Ordinary annotation call readiness is committed in `0d7c0a62`: three modules, 11 new declarations and eight interfaces. All 18433 preceding declarations remain exact.

Prepared ordinary call provenance is committed in `5b8c8727`: seven modules, 98 new declarations and 24 interfaces. All 18335 preceding declarations remain exact.

Ordinary specialization coherence and selected-scope calls are committed in `4f01d1fb`: three modules, 565 new declaration names and twelve interfaces. All 17770 preceding declarations remain exact.

Specialization and source-instance foundations are committed in `74b762a7`: nine selected modules, 118 new declaration names and 21 interfaces. All 17652 expanded baseline declarations remain exact.

Recursive discard-sequence exits are committed in `552dfdfd`: one module, 19 selected declarations and four public interfaces. All 16993 preceding scoped declarations remain exact.

Canonical call readiness and ordinary body exits are committed in `3059a7f5`: three modules, 19 new declarations and nine interfaces. All 16974 preceding scoped declarations remain exact.

Prepared policy, original call typing and canonical call contracts are committed in `23ac1a6c`: five modules, 256 selected declarations and 31 new interfaces. All 16727 preceding scoped declarations remain exact.

Contextual compiler policy retention is committed in `806e809c`: three modules expose eleven new interfaces, with literal private/normal agreement for 133 owned declarations. All 16679 preceding scoped declarations remain exact. The earlier retained-recipe factories and source typing lemmas are in `96a60f2f` (32 interfaces, 139 new declarations); sequence body/application changes are in `a0778ccc` (27 interfaces, 169 owned declarations).

- `SelectedBodyCompilerRoots` issues original Source certificates from authentic accepted compiler actions. `SelectedBodySupportFactories` and `SelectedCompilerTerminalCallerBounds` construct exact static support and consume the supported recursive caller proof; their original unit was verified in `d5d5e123` and `02006e66`. The constructive replacement `db1ab3d2` preserves its 25 public interface types.
- `SelectedBodyCompilerCallbacks`, `SelectedNamedCompilerRecipes` and the selected closure/named factories retain the same contextual compiler site, actual body, callback, chosen packet and raw parameter authority. They derive support for those genuine occurrences; an arbitrary earlier Association or unrelated compiler site is not upgraded.
- `DiscardSourceBodyInversion`, the discard compiler receipts and the flow/body bounds retain the original discard/return forms, actual child compiler actions, raw typing, intermediate state and literal emitted footer. Source and native grades remain independent.
- `MixedBodyStaticSupport` retains terminal/discard/sequence packets and original roots at the same Code and parameter context. `MixedBodyCompilerSupport` constructs the discard support from its actual compiler receipt. The mixed flow, body, lambda application, contextual application and parent bounds preserve the actual caller restoration for ordinary and principal Associations.
- The mixed user/indirect dispatch and call-head bounds feed `MixedRecursiveCallerBounds` and `MixedRecursiveBodyBounds`. The final body endpoints construct both execution directions internally, retaining the original Root contracts and exact caller post. They require static support for actual Associations and terminal named bodies.
- `MixedRecursiveCallerCompilerBounds.preserves_compiled` and `reflects_compiled` issue the original certificate from accepted expression compilation and supply the supported recursive body family internally.
- `MixedClosureCompilerFactories` constructs static support from the actual produced closure and accepted discard/terminal body action. `packet_for` and `support_for` cover that same ordinary Association. Coverage of arbitrary and principal Associations remains open.
- `DiscardSequenceCompilerReceipts` extracts each ordered child and literal tail action from accepted compilation. `MixedDiscardSequenceFlowBounds` proves both execution directions using original child Roots, with actual intermediate state and fault prefixes.
- `DiscardSequenceSourceBodyTyping` derives each used child's original stored node and raw type from full body typing. `DiscardSequenceCompilerSupport.raw_result` proves the terminal raw result matches the declaration. Its `Static.certificate`, `Static.root` and `issued_tree` construct exact child authority and the typed tree from actual compilation, with `Ready` tied to the issued certificates.
- `MixedCoveredCallerCompilerBounds` accepts propositional packet/support coverage and invokes the existing compiler bounds with one theorem-local dependent choice. Coverage is still a static obligation. The sequence body/application ports below consume the same packet and support.

These ports keep genuine compiler policy/read conditions, original typing and call readiness explicit. Complete formation factories, wider Source grammar and the final public all-pass theorem remain incomplete. The seven static witness replacements at `87b08905` expose 47 checked interfaces. Seed and Inventory indices are intentional proof-interface changes; profile constructors return proposition-valued existence. Complete private/normal TYPE/AXIOMS and API logs agree, and registered tests and the repository policy checker pass with zero findings. The full public semantics theorem remains incomplete.

## Actual public startup and returned product functions (2026-10-12)

| Interface | Role |
| --- | --- |
| `RecursiveNamedPublicHistoryFrontdoor.Started` | Retains the actual indexed checkpoint, root, Header, native arguments, encoded metadata, `StartAt`, `RootSelection` and exact `NamedSourceAt`. |
| `RecursiveNamedPublicHistoryFrontdoor.public_run_succeeded_retains` / `public_run_succeeded_remembers` / `public_run_succeeded_collects` | Derive that packet from actual public startup, complete inventory and current history, then return full Source/native meaning and reusable history. |
| `RecursiveNamedPublicOutputSelections.Selection` / `Selected` | Describe selected output positions and their exact Source/native shapes and recursive fuel, without representation or execution premises. |
| `Session.RawEncodedAt.reimports_function` | Reimports an actually encoded function leaf with its full raw Source type and that leaf's validation fuel. |
| `RecursiveNamedPublicFunctionHistory.first_collected` / `History.collect_success` | Derive selected entry meaning from the actual successful export and full `ResultAt`, then seed or extend history. |
| `CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects` / `CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_collects` | Connect product-output selection to initialized public execution or the next successful history step. |

The frontdoor replaces caller-supplied `started`, `selected`, `atCheckpoint` and `sourceAt` with authentic public start/session/recipe correspondence and complete inventory. `inputsFor`, `metadataFor` and `descriptors` describe the recovered request's structural inputs, actual metadata extension and static descriptor. `outputSelections` chooses positions in the observed output for that request. Conclusions retain the exact recovered packet; the semantic trace uses its Source function and original argument vector. No argument or closure representation is supplied at this boundary.

Output selection has `skip`, `function` and `product` constructors. Product children keep their own original raw types and one-less recursive codec fuel. `added.map Entry.handle = selection.handles` retains order and repeated handles. The next history contains `entries ++ added`, so earlier exports remain usable at the real returned heap. This does not yet select inside constructor, mapping or raw comptime-wrapped product outputs.

## Named terminal lambda support (2026-10-12)

`CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers keys bodyRegistry header stages terminal semanticFaults` replaces the public adapters' former `NamedSupport` parameter. `.recursive oldSupport` preserves that existing branch. `.formation static` supports the exact terminal ordinary lambda.

`Formation.of_actual` consumes its original compiler Site/body receipt, complete headers, zero capture prefixes and `ProgramWellFormed`. It derives runtime validity and evidence coverage from Header typing. `CallableIndexedOwnedPreparedStagedNamedChildBounds` uses the nested state constructed by the genuine named parameter receipt. `CallableIndexedOwnedPreparedStagedLambdaFormationHeads` derives native formation, Source closure meaning and the unchanged body heap at that current state. Both directions retain full caller restoration and postconditions.

Complete inventory, authentic compiler/body certificates, exact raw structural inputs, the actual encoder-to-receiving metadata extension and one fixed function model and registries remain explicit. The new lambda branch requires an ordinary terminal lambda and zero capture prefixes. Output collection currently traverses products; constructor, mapping and raw comptime-wrapped product outputs remain separate work. Reusable failed continuations, suspended snapshots, model/registry changes, full statement grammar and all-pass composition remain open.

The mutable runtime fixture still uses assignment and match outside the admitted body grammar; its results do not instantiate these public semantic theorems. The closed empty unit-lambda fixture is now complete through first export and History construction; captured bodies and returned-closure invocation remain open. Estimates stay at 100% for runtime unification, about 70% for meaning preservation and about 85% overall.

The following dated interface sections retain the scope and validation of their earlier checkpoints.

## Issuance and restoration in retained histories (2026-10-12)

`RecursiveNamedPublicHistoryIssuance.named_remembered` and `builtin_remembered` consume actual public issuance receipts and return the indexed completion plus an extended history. `History.remember_named` derives the exact Source global, full instantiation/dictionary and native capture from an accepted inventory packet and the current owned pool. `History.remember_builtin` derives the builtin's closed callable. Earlier exported closures keep their entries and current captured state. The existing `Input.retained` leaf can select the added entries inside arbitrary finite argument lists and containers; no separate representation or Source-typing premise is added.

The public and indexed `Session.snapshotWithReceipt` operations return a snapshot with `Session.SnapshotAt`. Existing `snapshot` delegates to this operation and discards the proof receipt. Indexed `Session.RestoredAt` records the genuine ready capture and actual restoration equation. Its `same_runtime` and `encodes_function` theorems preserve the captured store, world, authority, metadata and earlier function payloads while allowing heap observation to append handle slots.

Public `Session.SnapshotAt.restored_indexed` identifies the actual restored indexed session. `RecursiveNamedPublicRestoredHistory.restored_history` consumes that connection and the saved branch's history; `restore_snapshot_history` also accepts the ownership-checked `Session.restoreSnapshot` result. `CallableIndexedOwnedPreparedStagedRestoredHistoryPublicBounds` exposes `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. They invoke the existing history endpoints with the produced history, retaining full Source applications, native results/stores, public sessions and caller `ResultAt`.

Restoration resumes the captured ready branch. It does not carry later allocations, mutations or later-issued handles from another branch into that saved history. This proof does not cover suspended snapshots or automatically add handles first exposed by heap observation. Direct function outputs can be remembered by the existing continuation adapters; collecting functions nested in output containers remains open.

`SourceCoreUnifiedPreparationCertificates.compiled_planPrepared` recovers the executable-plan preparation equation from the compiled object's original records. History bounds, successful continuations, the initialized seed and restored bounds use it internally, so their callers no longer supply `acceptedPlan`.

The fixed function model, body/receiving registries, exact structural inputs and `Extends encodedValues.registry receiving` remain required. So do `OrdinarySequenceFor`, named `Terminal` and `NamedSupport` certificates. Assignment and match statements in the mutable regression are outside the current supported body grammar; that fixture does not instantiate these semantic endpoints.

Focused verification passes the strict public regression and its complete runtime fixture. The combined issued/retained input returns integer `233`, then `47`/`117`; ready restoration returns `39`/`110` from saved captures `38`/`109`, despite the original branch reaching `47`. Incorrect nested handles are rejected. Duplicate-row swaps leave the `176` and `233` aggregates unchanged; the differing follow-ups (`38`/`109` versus `39`/`108`, and `47`/`117` versus `48`/`116`) detect row order. Strict Lean, full build (5991 jobs), all registered tests and kernel policy pass. Independent snapshot review found no issues. The eighteen checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Estimates are unchanged.

## Retained functions across successful calls (2026-10-12)

Code commits: `1bf7248d` and `b5be3856`.

Validation: strict Lean, full build (5986 jobs), all registered tests, kernel policy and independent review passed. The fourteen checked handle-transport, history, argument, public-continuation and initialization endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

`RecursiveNamedPublicFunctionHistory.Entry` retains an exported handle, its exact raw Source type, independent Source value, complete native payload, native type and original export-validation budget. `History` ties a finite list of these entries to one actual current session, caller, map, world, Source heap and native store.

`CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers` constructs the first history from actual fresh bootstrap/resumption, selected startup and existing nested data/named/builtin input receipts. It consumes the observed successful function-handle result and invokes initialized public reflection. Its conclusion retains the Source application, full `ResultAt`, explicit reached caller and caller relation, actual returned public/indexed session, and singleton history with the exact raw output type, Source/native payload and original output-validation budget. The first selected Header anchors the history's Source context.

Each execution step retains its original `StartAt`, selected root and full native and semantic result receipts. The raw signature and ordered native arguments belong to that same selected call. A successful step can keep the existing entries when the result is data, or remember the actual new function export. Optional `IssuanceChain` steps transport earlier handles through genuine named/builtin issuance. These issuance steps preserve runtime state; execution steps use their real returned state and heap changes.

`History.current` derives each entry's current `EncodesAt`, `ValueRep` and `Dynamic.ValueHasType`, along with the session's store/world, heap representation, deep heap typing and stable caller rows. Old native closure payloads retain their captured references. Their representation and typing move to the actual reached map, world and heap, so captured cell contents may change during intervening calls.

`RecursiveNamedPublicFunctionHistoryInputs.Input.retained entry member` selects a literal retained history entry. The `data`, `product`, `constructed`, `mapping` and `comptime` cases preserve raw Source descriptions. `Inputs` and `Entries` retain ordered argument/payload vectors and mapping rows. The certificate supplies no native representation or body execution law.

`RecursiveNamedPublicFunctionHistoryEncoding.Input.meaning` compares each actual encoded function with that entry's current authenticated payload and follows the original container encoding. `RecursiveNamedPublicFunctionHistoryArgumentsReceiving.StartAt.history_arguments_receiving` combines those facts with the selected Header's exact raw parameters and native arity. It constructs the complete `Arguments` and `ValuesHaveTypes` judgments, preserving repeated aliases, distinct handles, all list positions and mapping defaults.

`CallableIndexedOwnedPreparedStagedHistoryPublicBounds` provides `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. Each consumes history-derived dynamic premises and retains the full staged Source application, native result/store, actual public result/session and complete caller `ResultAt`. `CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains` also returns a history for that actual returned session with all earlier entries. `public_run_succeeded_remembers` additionally appends a function returned directly as the result. The seed and continuation adapters do not yet collect functions nested inside an output container. The returned history can be consumed by the next supported call, including through nested inputs.

The function model, body registry and receiving registry remain fixed across the chain. Callers retain exact structural input descriptions, genuine history/startup receipts, valid constructor metadata, supported static body facts and `Extends encodedValues.registry receiving`. A registry shared ancestor does not establish that last condition. Reusable histories after failure, snapshot restoration, directly adding newly issued named/builtin input leaves, changes of receiving model/registry and complete compiler composition remain open.

The runtime continuation test invokes two independently captured closures from one product/mapping input after data-returning mutation calls and further factory issuance. The older closure appears twice; duplicate mapping keys retain first-entry behavior. It checks Word `176`, then captures `38` and `109`. This test uses the retained exported handles as function inputs; the newly issued factory handle is only an intervening issuance. Static body and history premises remain necessary to instantiate the semantic theorems.

Progress estimates are unchanged. The interface records below retain their original scope and validation.

## Returned closure inputs (2026-10-12)

Code commits: `62001b99` and `f950c96c`.

The connection consumes the preceding public success's `SucceededResultAt` and full `CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt`. The earlier public success endpoint returns both receipts for the same native result and store. Use its Source invocation context as that Header's `function.context`; `header_context_supports first first` derives the required body-to-declaration support. The previous raw request is retained through `Checkpoint.ResultTypeAt`, obtainable from the original `StartAt.original.result_type_at` and `RecursiveNamedPublicRootSourceSignature.inputs_and_result`.

The receipts are consumed in this order:

1. `SucceededResultAt.reimports_payload` recovers the complete exported native payload at the exact raw result type. `reimports_function_after` carries it through an actual `Session.IssuanceChain`, independently of the next input-validation budget.
2. `RecursiveNamedPublicReturnedValues.returned_value` obtains the corresponding Source value, value/heap representation, actual returned caller, caller relation, stable histories and deep Source typing. Captured environments come from this semantic result.
3. `header_context_supports` derives transport into the next Header's Source context. `StartAt.after_succeeded` fixes the next startup's store/world to the returned native state. The location map and Source heap remain the previous result's values.
4. `RecursiveNamedPublicReturnedInputs.Inputs` describes the new ordered public arguments. Its `returned` leaf reuses the exact prior public/Source value; `data` keeps independent raw typing and interpretation. Products, constructor vectors, ordered mappings and comptime wrappers recurse over those leaves.
5. `RecursiveNamedPublicReturnedEncoding.Input.meaning` and `StartAt.returned_arguments_receiving` follow the actual encoder and construct the whole argument relation and Source typing at the current heap. No arbitrary leaf-meaning callback is required by the final producer.

`CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds` exposes `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. Its input certificate has the form `∀ source, previousOutcome = .value source → Inputs ... (arguments source)`: the argument description may place the actual returned Source closure at several positions without choosing a different capture. Each conclusion retains that same argument list, the relation from the prior caller, and the complete next `ResultAt`. Successful and failed public runs retain their real returned public sessions. Word preservation retains independent input/output budgets and a sufficient native fuel bound.

Both executions currently use the same function model, body registry and receiving registry. The next startup's `Extends encodedValues.registry receiving` remains explicit. The previous full semantic result, actual success, exact raw request/input certificates, valid constructor metadata and supported body family are required. The current continuation accepts one returned function identity, reused alongside data, with optional actual issuance steps before startup. Several independently exported old functions, mixing with additional issued function inputs, arbitrary intervening execution, restored sessions and changes of receiving model/registry remain open.

The runtime regression is broader: it checks old and independently allocated closures together with named/builtin handles after intervening mutation. Results `81`, `29` and `101` check shared capture, returned mutation, duplicate-key selection and independent allocation. These runtime checks do not prove the still-open multi-handle continuation case.

Validation: Strict Lean, full build (5978 jobs), all registered tests, kernel policy and independent review passed. The twelve checked proof endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

## Nested function inputs (2026-10-12)

Code commits: `9181cd2b` and `708e3f8b`.

`RecursiveNamedPublicNestedInputs.Input` extends the mixed leaf certificate with products, constructed payloads, mappings and comptime wrappers. Its mutually defined `Inputs` and `Entries` retain ordered payloads and key/value rows. A leaf carries independent raw data typing and interpretation, or an actual named/builtin issuance receipt and continuation to the receiving session. Named leaves also require the exact issued inventory packet and `Inventory.HasRow`. No input certificate contains a native representation or execution law.

`RecursiveNamedPublicNestedRawInputs.StartAt.raw_input` recovers the selected argument's original encoding, starting registry, projected type and extension to the final encoded registry. `RecursiveNamedPublicNestedEncoding.Input.represents` follows that encoding structurally, including empty/singleton/list constructor packing and ordered mapping keys and values. Child registry extensions are composed in the actual encoding order.

The generic fold exposes a leaf-meaning port. `RecursiveNamedPublicNestedLeafMeaning.leaf_meaning` fills it from genuine data or function issuance receipts, accepted preparation and the initialized owned state. The named case keeps the retained Source instantiation, complete dictionary and actual captured closure; the builtin case keeps its exact closed callable. `RecursiveNamedPublicNestedArgumentReceipts.StartAt.nested_argument_represents` combines this leaf producer with the original startup encoding to derive the selected native payload's representation and deep Source typing.

`RecursiveNamedPublicNestedArgumentsReceiving.StartAt.nested_arguments_receiving` constructs the complete `CallableIndexedParameterMeaning.Arguments` and `Dynamic.ValuesHaveTypes` judgments. It aligns the selected Header's exact raw parameter list with the public values, Source values and original native argument vector. Exact lengths prevent dropped suffixes; repeated handles retain their original positions.

`CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds` exposes `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. These derive the initial owned caller, stable rows, globals, heap conditions and complete argument relation from actual fresh bootstrap completion, finite resumption and state-preserving issuance. Their conclusions retain the same full staged Source result, native value/store, caller relation and actual public returned session as the mixed-input endpoints.

Callers still provide structural input certificates at the exact raw signature, genuine named inventory membership, actual preparation/issuance/startup receipts, valid constructor metadata, supported static body facts and `Extends encodedValues.registry receiving`. Comptime erasure and proxy projection do not replace raw typing. The receiving registry must preserve IDs from the actual encoder; a shared registry ancestor is insufficient.

The runtime regression checks result `71` for a product containing constructor and mapping payloads with repeated earlier named and later builtin handles and duplicate mapping keys. It checks incompatible nested handle rejection in both mapping and constructor payloads.

Validation: Strict Lean, full build (5971 jobs), the focused public runtime regression, all registered tests, kernel policy and independent review passed.

Axiom checks: The eleven checked encoding, leaf, argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

Closure inputs, restored or previously executed sessions, complete static/compiler coverage and the final all-pass theorem remain open. Progress estimates are unchanged. The dated interface entries below retain their original scope and validation.

## Mixed function and data inputs (2026-10-12)

Code commits: `91a42c32` and `8964ff88`.

`SourceCoreIndexedSession.Session.IssuanceChain` records a finite sequence of actual successful named/builtin issuances. Its `same_runtime` theorem retains the initialized native state; `encodes_function` separately preserves an earlier handle's exact native callable through slot reuse and append. `SameRuntime` alone does not establish this authentication transport.

`Checkpoint.RootStart.data_input` and `RecursiveNamedPublicMixedDataArgumentReceipts.StartAt.data_argument_represents` recover a data value at its actual index in a mixed startup. The other positions may contain handles. The result retains the actual encoded payload, native type projection and metadata, and supplies Source representation and typing from `PublicDataTyped` and its independent data interpretation.

`RecursiveNamedPublicMixedArgumentReceipts.Input` has three constructors:

- `data` retains structural raw data typing and its independent Source interpretation. Constructors, proxies, products and mappings may be nested, provided they contain no handles.
- `named` retains the exact issued inventory packet, `Inventory.HasRow`, actual named issuance, the returned handle, and its issuance chain to the receiving session. Its Source value retains the imported specialization and dictionary.
- `builtin` retains the actual builtin issuance, returned handle and issuance chain to the receiving session. Its Source value is that exact builtin.

`Inputs` aligns those certificates with the selected Header's raw parameter types, public values and Source values as ordered lists. `StartAt.mixed_arguments_receiving` folds them into `CallableIndexedParameterMeaning.Arguments` and `Dynamic.ValuesHaveTypes`. There is no singleton restriction; positions and repeated values are retained. The producer uses the actual startup argument vector and derives each represented payload at the corresponding index.

`CallableIndexedOwnedPreparedStagedInitializedMixedPublicBounds` exposes `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. These endpoints derive the initial owned caller, globals, heap and argument conditions from the actual fresh bootstrap, finite resumption and state-preserving issuance. Results retain the staged Source outcome, native value and store, actual public returned session and complete caller relation.

Callers still provide exact raw input certificates, genuine named inventory membership, actual preparation/issuance/startup receipts, supported static body facts, and `Extends encodedValues.registry receiving`. This last condition preserves the IDs allocated by the actual encoder. Two registries extending a common ancestor do not establish it. Runtime type projection also does not establish every raw data annotation.

Handles nested inside carriers, closure inputs, restored or previously executed sessions, complete static/compiler coverage and the final all-pass theorem remain open. Validation: Strict Lean, full build (5962 jobs), the focused public runtime regression, all registered tests, kernel policy and independent review passed. Axiom checks: the ten checked issuance, data, mixed argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The dated interface entries below retain their original scope and validation; this section supersedes their singleton input boundary.

## Initialized public entry (2026-10-12)

`SourceCompiler.Artifact.bootstrapWithReceipt` returns the original public bootstrap with `Bootstrap.FreshAt`. Existing `bootstrap` delegates to it. `Bootstrap.ready_indexed` uses an actual ready equation to retain the original indexed fresh checkpoint and exact returned session.

`CallableIndexedOwnedPublicBootstrapInitialization.at_started` identifies the same session in bootstrap and startup, returning the actual native completion and exact initialized store/world. `CallableIndexedOwnedPreparedBootstrapRootState.of_completed` consumes this completion and genuine finite inventory to construct the owned caller, stable rows, global references and empty Source heap correspondence.

`RecursiveNamedPublicSimpleArgumentReceipts.simple_arguments_receiving` obtains Source arguments, their interpretation, raw typing and native representation from the original successful scalar/product encoder. It works directly at the receiving body's registry. `simple_arguments_at_receiving` matches the independently interpreted arguments of a supplied Source trace.

`CallableIndexedOwnedPreparedStagedInitializedPublicBounds` consumes these producers in `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. Their inputs no longer include an initial caller, stable rows, global reference, heap representation/typing or argument representation/typing. Reflection recovers its Source arguments existentially. Exact startup/checkpoint/bootstrap receipts and static compiler/body support remain inputs; full staged results and returned state remain conclusions.

The original scalar entry was committed in `9b6cb2c7` and `6976ab8c`. `1ebb4c6a` generalizes its bootstrap premise to `Bootstrap.ReadyAt`: `.single ready` records completion and `.suspend exhausted continued` adds an actual suspended step. `ReadyAt.indexed` recovers the exact native initial completion at the sum of the budgets and the same returned session.

`b6c24d8f` adds `RecursiveNamedPublicDataArgumentReceipts` and `CallableIndexedOwnedPreparedStagedInitializedDataPublicBounds`. The three public endpoints also accept metadata-bearing data under `PublicDataTypes` at the selected raw Source signature and an actual `Extends encodedValues.registry receiving` relation. The latter preserves the encoded tag IDs. It cannot be replaced by two independent extensions of the static registry. Singleton builtin and named handles have the additional connections below; closure handles require further Source provenance. Restored or previously executed sessions and complete compiler coverage remain open.

## Issued function inputs (2026-10-12)

`Session.namedWithReceipt` and `builtinWithReceipt` return the original completion plus `NamedIssuedAt` or `BuiltinIssuedAt`. The existing methods delegate to them once. `Completion.IndexedAt` retains the exact native completion. The receipt's `same_runtime` theorem preserves native memory, authority, metadata and Source prefix; it makes no equality claim about physical handle slots.

Initialized public endpoints now accept `ready : bootstrap.ReadyAt fuel bootstrapSession` and `sameRuntime : bootstrapSession.SameRuntime publicSession`. Use `.refl` when no handle was issued, or compose actual issuance receipts with `.trans`. Initial state is still derived from the original bootstrap completion.

`RecursiveNamedPublicIssuedFunctionInputs.StartAt.named_argument` and `builtin_argument` recover the actual issued callable at its startup argument position. `Recipe.BuiltinCallableAt.prepared` additionally derives the exact closed builtin code, raw type, descriptor and identity from accepted preparation. `RecursiveNamedPublicBuiltinArgumentReceipts.StartAt.builtin_arguments_receiving` constructs complete argument representation and typing for a singleton builtin input at the Header's exact raw parameter type.

`CallableIndexedOwnedPreparedStagedInitializedBuiltinPublicBounds` consumes that result in `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. These endpoints retain the same static body support and full staged result/state as the scalar and data endpoints. The user-supplied conditions describe actual preparation, issuance, startup and raw parameter agreement; no Source function representation or argument typing is assumed.

Committed in `54bc83a5` and `83bf7430`. The named input connection below extends this boundary. Closure Source input interpretation, mixed lists and nested handle carriers remain open.

## Singleton named input semantics (2026-10-12)

Committed in `be545d01` and `f7c07bf1`.

`SourceCoreIndexedSession.Recipe.NamedCallableAt.prepared` recovers the actual signature, specialization, global slot, closure, nonwrapping identity and contract descriptor from accepted preparation. `Recipe.native_global_location` fixes the selected cache entry's physical location. Comparison with the bootstrap store and owned capture identifies the complete closure payload.

`RecursiveNamedPublicNamedArgumentReceipts.StartAt.named_argument_represents` combines the issuance and startup receipts with an actual `Inventory.HasRow` packet. It constructs the receiving function representation and deep Source typing for that packet's retained global function, including its full ordered instantiation and resolved dictionary. `StartAt.named_arguments_receiving` constructs the complete argument relation for a singleton input whose raw parameter type equals the imported specialization's function type.

`CallableIndexedOwnedPreparedStagedInitializedNamedPublicBounds` exposes `public_run_succeeded_reflects`, `public_run_failed_reflects` and `public_word_preserved`. These consumers derive the initial owned caller, stable rows, globals, heap relations and named argument conditions from actual fresh bootstrap completion, allowing finite resumption and state-preserving issuance. Their conclusions retain staged outcomes, native results and stores, the actual public returned session and full caller relation.

The imported packet and its inventory membership, exact singleton raw type and supported static body family remain explicit. Closure inputs, mixed lists, nested carriers, restored or previously executed sessions, broader grammar and full compiler composition remain open.

Validation passes: strict Lean, full build (5959 jobs), all registered tests, kernel policy and independent review. The seven checked named factory, input and public endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Public execution receipts and semantic consumers (2026-10-12)

`SourceCompiler` exports `Compiled.openWithReceipt`, `Session.runWithReceipt` and `Checkpoint.resumeWithReceipt`. Their subtype results retain erased proofs about the original action. Existing `open`, `run` and `resume` delegate to those operations and return their values. They do not replay execution or mint a second artifact authority.

`Artifact.CompiledAt`/`IndexedAt`, `Session.IndexedAt` and `Checkpoint.IndexedAt` retain exact facade/indexed correspondence. `Session.start_indexed` derives the indexed startup from accepted public startup. `Session.RunAt` and `Checkpoint.ResumeAt` describe the actual returned outcomes; success and failure retain the exact returned indexed session.

`RecursiveNamedPublicExecutionMeaning.actual_start` combines successful public compilation, opening and startup to recover the actual recipe preparation, original checked Source program and `StartAt` receipt. Its named evidence endpoints also carry the existing Source program outcome and heap relations through public success/failure and Word export.

In `CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds`:

- `preserves_root` and `reflects_root` connect the existing mixed recursive body proof to the literal cached named root.
- `public_run_succeeded_reflects` and `public_run_failed_reflects` retain the same staged Source application, native result/store, complete returned caller relation and actual public export session.
- `public_word_preserved` gives successful public Word export at sufficient execution fuel and a positive output budget.

The staged endpoints construct body execution proofs internally. They require exact startup, actual root selection, initialized owned state, represented arguments/heaps and authentic static family support. They preserve staged failures without converting rejection to a Dynamic semantic fault. Public export metadata and the receiving body's metadata retain separate receipts. Complete initialization and compiler-grammar coverage remain integration obligations.

Strict Lean checks, full build, registered tests, kernel policy and independent review pass. The checked semantic endpoints use only the standard three axioms. Committed in `6199f27d` and `a3d8877f`.

## Connected ordinary sequence callers (2026-10-12)

Committed in `80a41cf5`. `CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_compiled` and `reflects_compiled` now connect actual preparation and retained compiler recipes to the existing recursive caller/body proof.

For ordinary closure Associations, the consumer obtains its scope from the actual Code, constructs the sequence packet with `choose_for`, and derives call readiness for each used child. It also derives readiness for the accepted caller's exact expression certificate. Both directions use the combined named/anonymous stage registry, including its named branch. The resulting packets and readiness are consumed by `MixedCoveredCallerCompilerBounds`.

Principal Associations retain their original dependent packet/support pair, so method owners are not incorrectly treated as ordinary function owners. Named support, supported sequence grammar, original typing and metadata, retained compiler policy, diagnostic interpretation, and heap/admission conditions remain explicit. This closes a supported caller connection; it does not establish all-program coverage.

The cached-root and public outcome connection is recorded above. Further work prioritizes initialization and compiler coverage for that same family. Generalized-cell drafts remain deferred until a concrete consumer needs them. New helper counts are not used to increase the progress estimate.

Validation: strict Lean compilation, full build, registered tests, repository kernel policy, and independent review pass. Both final theorem axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`.

## Applied source and runtime materialization

`CallableAppliedDynamicSourceMaterialization` tracks authenticated source ancestry and derives the selected applied source and lambda header while retaining captured variables and supplied evidence.

`CallableClosedSchemeSubstitutionAgreement` connects actual closed-scheme matching to runtime instantiation. `CallableFlexibleSubstitutionAgreement` lifts equality of variable lookups to whole typed sources, contexts and instantiated closures.

`CallableAppliedRuntimeMaterialization.materialize` combines these results for the substitution and produced-plus-caller evidence used by the actual runtime instantiation. It retains explicit matching scheme/raw type, live source ancestry, captured environment and occurrence uniqueness.

Verified in `f0f6a910`: strict, full declaration/API, build and registered test checks pass. Generalized allocation/read witness production, body execution and the final public theorem remain unfinished.

## Applied ancestry and ordinary sequence readiness

`CallableAppliedCodeScopeProvenance` recovers the full lexical owner from an actual sealed applied read and code history. It identifies the complete sidecar, selected guard frame and principal caller specialization.

`CallableIndexedOwnedPreparedStagedOrdinaryDiscardSequenceReadiness.ready_of_preparation` derives call ports for each exact child certificate issued by the retained discard-sequence packet. It uses original child typing and ordinary public preparation; its conditions do not assume call readiness.

Verified in `55fe02aa`: strict, full declaration/API, build and registered test checks pass. The owner result requires actual code ancestry; general method readiness and generalized-local allocation/read semantics remain unfinished.

## Ordinary annotation call readiness

`SourceBodyResultAnnotation` obtains the stored result annotation from original body typing. The result across equal rigid source instances follows without constructing a second substituted typing derivation.

`CallableOrdinaryAnnotationCoherence` combines genuine ordinary origins, original program typing and concrete replacements. It proves equality of the full rigid source, inferred result, stage analysis and selected guard frame.

`CallableOrdinaryPreparedScopeAnnotationCallsReady` obtains the ordinary row origins from actual public preparation, derives the selected frame and transfers the exact canonical call ports. This endpoint removes the `RangesAt` premise from the earlier ordinary prepared-scope result. Original typing, source metadata, compiler policy and the exact certificate remain explicit.

Verified in `0d7c0a62`: build 5941, strict checks, full declaration/API comparisons, registered tests and repository policy pass. General implementation methods and live generalized-local materialization are outside this result.

## Prepared ordinary call provenance

`CallablePreparedOrdinaryRequestOrigins` follows real worklist execution and canonical replay. `CallablePreparedFinalCatalogOrigins` follows public evidence preparation through coercion and operator scanning, retaining an ordinary origin or the actual checked method selector for every final row.

`CallableOrdinaryMethodCatalogSeparation` uses signature catalog disjointness to rule out a method row at an ordinary function owner. This identifies the ordinary branch without treating an implementation owner as an individual method identity.

`CallableSelectedCanonicalSourceErasure` derives canonical source correspondence from authentic paired ancestry. `CallableOrdinarySpecializationErasedStageCoherence` uses the original ordinary function's requirement profiles to recover equality of the two canonical contextual sources. `CallableOrdinaryPreparedScopeCallsReady` combines these results with actual preparation to derive the selected frame and its exact call ports.

`CallableIndexedOwnedReachedNamedConcreteRangeReceipts` combines genuine admissible declaration metadata, exact compiler selection and accepted concrete replacements. It establishes raw range formation for the matched reached callee, including retained unused replacements.

Verified in `5b8c8727`: build 5938, strict checks, full declaration/API comparisons, registered tests and repository policy pass. The ordinary scope theorem still requires `RangesAt` for that owner's retained rows and the original source/compiler receipts. Erasure alone does not establish execution equivalence for a rewritten applied source.

## Ordinary specialization coherence and selected-scope calls

`SourceAnnotationSummaryUniqueness` proves that the same unique stored statements determine their type, value and return summaries across independent typing derivations. Its body-facts theorem compares actual annotations; the declaration-result theorem extracts the required annotation equations from original declaration typing.

`CallableOrdinarySpecializationStageCoherence` derives specialized body typing and annotations from original checked-program typing, genuine ordinary origins and complete raw range formation. Equal complete sources after local substitution determine the rigid bodies, results and stage analyses. Equal preparation plans then determine the complete ledger frame.

`CallableIndexedOwnedPreparedStagedOrdinaryScopeCallsReady` combines two genuine preparation/source receipts with that coherence theorem. It transports the exact canonical call ports to the selected ordinary scope, preserving original typing, occurrence uniqueness and the actual compiler certificate.

Verified in `4f01d1fb`: build 5931, strict checks, full declaration/API comparisons, registered tests and repository policy pass. These interfaces still require their stated origins, range formation and full source receipts; applied views and general method histories need further correspondence proofs.

## Specialization and source-instance foundations

`SourceSpecializationAcceptance` exposes concreteness and absence of flexible variables for actual accepted canonical replacements. `CorrelatedParameterInstances` and `CorrelatedTypedSourceInstances` recover rigid instances from equal local instances of the same original type or complete source. These statements preserve ordered metadata and do not assume general substitution injectivity.

`CallablePreparedSpecializationOrigins` and `CallablePreparedFinalSpecializationOrigins` follow the actual requests, worklist, method, operator and coercion preparation paths. The final preparation endpoints construct specialization receipts internally. `CallablePreparedFinalSpecializationRanges` obtains concrete replacement properties from those receipts.

`CallableOrdinarySpecializationIdentity` uses genuine ordinary catalog membership and declaration uniqueness to identify a shared original checked function. `SourceStageAnalysisCongruence` compares successful analyses from equal declaration, source and effective return inputs; correspondence of those inputs must still be established.

Verified in `74b762a7`: build 5928, all affected modules, strict checks, complete scoped declaration comparisons, registered tests and repository policy pass. These interfaces do not infer nominal type formation from concreteness or complete the public semantics theorem.

## Recursive discard-sequence exits

`CallableIndexedOwnedPreparedStagedDiscardSequenceBodyExitBounds.ExitReceipt` distinguishes returned values, semantic faults and exact stage rejection. The first two retain ordinary `ReachedExit`; the third retains the original staged statement trace.

`exit_receipt_of_trace` constructs that receipt from the actual selected closure, environment and metadata extensions. `preserves_body_with_exit` and `reflects_body_with_exit` construct their strict recursive child laws internally and retain the existing result representation, heap/map/world extensions, administrative state and reached admission.

Verified in `552dfdfd`: build 5920, strict checks, full declaration/API comparisons, registered tests and repository policy pass. The four APIs keep genuine static compiler/support premises; complete production coverage and the final public all-pass theorem remain open.

## Canonical call readiness and ordinary body exits

`CallableIndexedOwnedPreparedStagedCanonicalCallsReady` reconstructs supported syntax from an authentic certificate and follows its exact call paths. `canonical_calls_ready` combines that syntax, original typing and retained policy at the sidecar selected from the same Code. Argument order and duplicate occurrences are retained.

`Staging.Recursive.Statements.returned_plain`, `fallthrough_plain` and `semanticFault_plain`, exported by `Staging.RecursiveBodyErasure`, project staged execution to ordinary execution with the same final context and heap. They do not project stage rejection to an ordinary outcome.

`CallableIndexedOwnedPreparedStagedBodyExitReceipts` builds `lexical_unchanged` from actual map/world and heap-metadata extensions. `reached_returned` and `reached_semanticFault` combine it with genuine selected-source provenance and the original staged trace.

Verified in `3059a7f5`: build 5919, all three strict checks, literal declaration comparisons, registered tests and repository policy pass. Other selected guard frames and the final theorem across all compiler passes remain open.

## Prepared policy and canonical call contracts

`RecursiveCallerPolicyProfiles.MetadataFor` states the original metadata conditions for the supported expression grammar. Its `retained_policy_for`, `retained_paired_policy_for` and `retained_selected_policy_for` derive actual callback behavior from the retained policy recipe. They do not infer global metadata conditions from compiler success alone.

`ContextualLambdaPolicyFormationReceipts` carries policy retention through ordinary and principal formation and recapture. `PreparedContextualLambdaPolicySupport` attaches the same receipt to prepared support and qualification, keeping the actual compilation, capture embedding and principal dictionary.

`RecursiveCallerRawTyping.parent_typed` follows the issued call certificate to recover its original parent type. `CanonicalScopeCallPorts.canonical_scope_port` constructs the call contract at the canonical invocation of the same Code; ordinary and principal ports preserve that provenance.

Verified in `23ac1a6c`: build 5916, all five strict checks, literal declaration comparisons, registered tests and repository policy pass. Complete call readiness and correspondence with every other selected invocation frame remain separate obligations.

## Contextual compiler policy retention

`CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe` records the actual read and special-expression callbacks for one generated Code. `Retained` keeps that policy with its named compilation and body recipe inside a proposition. The special callback keeps the original initializer, evidence and local-read choices and the `min budget code.fuel` bound; compatible reads keep the prepared compilation's fuel.

`CallableIndexedLambdaGeneration.contextual_certificate_with_policy_recipe` and `of_contextual_with_policy_recipe` construct this witness at the actual generation site. The producer's `ProducedWithPolicy` retains the same Produced value and Site. Existing projections retain their interface types.

Verified in `806e809c`: 753 affected modules, three empty normal strict checks, build 5911, registered tests and repository policy pass. Global metadata profiles and complete formation/call coverage remain separate obligations.

## Retained-recipe factories and original typing

`MixedBodyRecipeCompilerFactories` and `DiscardSequenceRecipeCompilerFactories` recover real statement receipts from the body recipe of the same Code. Their `choose` ports construct packets; `static` and `support` attach original typing and exact child authority. The `choose_for`, `packet_for` and `support_for` ports retain the ordinary or principal Association's actual named compilation.

`LambdaScopeDeclarations.parameters_declared`, `at_parameters` and `at_selected_scope` derive the parameter portion of the original declaration context. Captured declarations remain an input. `LambdaOriginalConditions.at_selected_scope` constructs the original per-scope conditions from the closure frame and body typing, retaining genuine coercion, program-validity and read-fault requirements.

Verified in `96a60f2f`: four strict Source checks, 139 declarations, 32 interfaces, build 5910, registered tests and repository policy pass. Global compiler-policy profiles, broader grammar and exact call readiness remain separate obligations.

## Sequence body and application interfaces

`MixedBodyStaticSupport.Sequence` stores the real ordered sequence receipt at the same Code. `SequenceSupport` retains its original closure frame and a propositional child Root for each used expression at every actual selected Source scope.

`DiscardSequenceCompilerBodyBounds.issued_tree` derives the typed sequence tree. Its `preserves_body` and `reflects_body` assemble the accepted footer and preserve original result typing, state and faults. `DiscardSequenceLambdaBodyBounds` connects actual parameter entry to these body proofs; `DiscardSequenceLambdaApplicationBounds` supplies both application directions. `MixedClosureApplicationBounds` handles the sequence alternative for both ordinary and principal Associations while retaining the existing public types.

Verified in `a0778ccc`: build 5906, registered tests, strict checks and repository policy pass. Complete compiler coverage and broader body grammar remain separate obligations.

## Production recipe interfaces

`CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe` records the literal equation for the same Code's body lowerer. `Retained` keeps the actual diagnostics, named code and compilation inside a proposition. `OrdinaryAt.body_recipe` and `PrincipalAt.body_recipe` project that witness from genuine provenance.

Formation constructors retain this additional static authority. Producers, recapture and prepared projections forward the same recipe. Original selected-child syntax, paired compiler policies, scope/coercion authority and certificate-indexed call readiness remain explicit. Arbitrary Association packet coverage is still incomplete.

The changes in `1bc5d609` pass private and normal strict checks, full literal comparison, build 5903, registered tests and repository policy. Public runtime entry points are unchanged.

## Public entry points

`Solcore.Frontend.SourceCompiler` reexports the types and functions of `SourceCoreExecution`. It has no separate backend, compiler representation, or session implementation.

| Role of the old API | Current entry point |
| --- | --- |
| Backend preference and fallback | Removed. All entries prepare the same Core artifact. |
| A single `main` | `compileEntry raw options` / `compileEntryChecked program moduleId options` |
| Multiple roots specified by name and type arguments | `compile raw seeds options` / `compileChecked program seeds options` |
| StaticWord selector discovery | `compileStaticWord raw options` / `compileStaticWordChecked program moduleId options` |
| Creating execution state | `compiled.open` → `artifact.bootstrap` → `Bootstrap.resume fuel` |
| Running a root | `session.run key arguments runOptions` |
| Calling a returned function again | `session.invokePacked handle packedArgument runOptions` |
| Named functions and builtins as arguments | Use Completion.value from `session.named key` / `session.builtin builtinId`. |
| Continuing after fuel exhaustion | `Outcome.outOfFuel checkpoint` → `checkpoint.resume fuel outputValidationFuel` |
| Observing the heap and restoring execution | `session.snapshot` / `checkpoint.snapshot` → `snapshot.restore` |
| Reusing the original initial heap | `snapshot.prefix` → `artifact.bootstrapFromPrefix` |
| Using the entire source heap as a new session's initial heap | `snapshot.exportPrefix` → `artifact.bootstrapFromPrefix` |
| Ordinary initial heap | A list of `SourceCoreHeapInput.Cell` containing common Value data → `artifact.preparePrefix` |
| Importing historical raw state | Explicitly import `SourceCoreLegacyHeapImport` and use its `preparePrefix`. |

`Frontend/SourceCompilerSession.lean` has been removed. The test module `Test/SourceCompilerSession.lean` tests the common API; it does not provide another implementation of the old session.

## Values and ownership

Execution uses one Value representation for Unit, Bool, Word, Integer, products, nominal constructors, ordered mappings, proxies, and function handles. Public Value exposes no source closure, source body, or native cell reference.

A Handle belongs to an artifact, session, export generation, and slot. An existing session's issuer is private, so callers cannot manufacture arbitrary handles with the same ownership. Mixing artifacts or sessions, supplying an unknown handle, or supplying a value of the wrong type produces a boundary error before execution.

Packed arguments use `.unit` for 0 arguments, the value itself for 1 argument, and the existing right-associated product layout for multiple arguments. Direct handle calls preserve the callee's staged parameter/result constraints.

## Outcomes and budgets

`RunOptions` separates `inputValidationFuel`, `executionFuel`, and `outputValidationFuel`. These are independent of the checking, specialization, and compilation budgets in `Options`. Core execution uses a different number of steps from the old direct evaluator.

`Session.run` / `invokePacked` returns `IO (Except SourceCoreIndexedSession.Error (Outcome artifact))`. `Checkpoint.resume` returns `IO (Outcome artifact)`.

- Outer error: rejection at the argument, ownership, or call boundary.
- `succeeded`: a common Value and the updated session. `Completion.typed` guarantees value authentication within the same ownership domain.
- `failed`: a source-language failure and the session at that point. Obtain a source diagnostic with `session.diagnostic key reason` or `handleDiagnostic`.
- `outOfFuel`: a typed checkpoint. Resumption continues from the saved Core continuation.
- `exportError`: a failure of output boundary validation, an insufficient observation budget, or a similar export error, together with the session.

## Snapshots and prefixes

A Snapshot retains the typed native store, world, registry, and, when needed, execution continuation from the time it was taken. `restore` also preserves the ready/suspended classification. `session.restoreSnapshot snapshot` requires ownership by the same session.

`Snapshot.cells` follows source-location order and excludes Core administrative cells. `Snapshot.heapSize` and `PrefixSnapshot.heapSize` count source cells; `Snapshot.nativeHeapSize` counts native-store cells. `Session.heapSize` and `Checkpoint.heapSize` also count native-store cells. Observe an allocation in progress through `pendingAllocation`.

A monomorphic callable is observed as a handle that can be authenticated by the registry at the snapshot's restoration destination. The same callable reuses its existing handle when already registered. Newly observed handles are not implicitly added to the registry from which the snapshot was taken.

A generic principal is a readonly observation of its scheme, type, captures, and evidence; it is not a closed callable handle. Source bodies and native references remain private. The original prefix is an inert, readonly observation.

`snapshot.prefix` is the **prefix originally supplied as input**. `exportPrefix` restores that prefix and every recorded source cell, passes them through the deep validator, and produces a separate sealed prefix. A new session keeps that prefix inert, and source locations for new allocations start at its length. Original handles and native continuations do not transfer to the new session. Prefix migration to a different artifact is not provided.

## Initial input

`artifact.preparePrefix cells validationFuel conversionFuel` converts common Value data and uninitialized cells, then applies the existing deep heap validation. It preserves nominal metadata, duplicate mapping keys, and entry order. Payloads that do not match their types are rejected.

A callable handle alone cannot be placed in an initial cell. Use `snapshot.exportPrefix`, which carries evidence of actual captures and allocations. A historical raw initial heap containing closures is validated by the explicit migration module with its existing acceptance conditions and budgets. This process does not execute source expressions or statements.

An artifact with an empty root set accepts only an empty heap and rejects all calls. A nonempty initial heap supplied to an empty root set is rejected rather than silently discarded.

## Implementation examples

- Compilation, roots, sessions, and ownership: [SourceCoreExecution](../../Solcore/Test/SourceCoreExecution.lean)
- Public snapshots, initial data, full prefixes, principals, failures, and continuations: [SourceCoreExecutionSnapshots](../../Solcore/Test/SourceCoreExecutionSnapshots.lean)
- Export of deep raw metadata, generic/read views, and caller/lexical profiles: [SourceCoreActiveHeapPrefix](../../Solcore/Test/SourceCoreActiveHeapPrefix.lean)
- Auditing public execution and internal evidence for the same artifact: [SourceCompilerFeatureSupport](../../Solcore/Test/SourceCompilerFeatureSupport.lean)
- Definitional identity of the public facade and common API: [SourceCoreUnifiedImportBoundary](../../Solcore/Test/SourceCoreUnifiedImportBoundary.lean)

## Selected literal proof interfaces

These internal proof modules connect the actual accepted compiler to a selected Word literal, singleton return body, invocation and successful public program result for the retained fixture. The final theorem for the complete public compiler remains unfinished.

| Module | Available connection |
| --- | --- |
| `CallableIndexedOwnedSingletonReturnCompilerReceipts` | `Receipt`, `of_return`, `functions_child` and `at_root` retain the original accepted child, emitted finish and actual compiler callback budget. |
| `CallableIndexedOwnedChosenWordLiteralExpressionBounds` | `WordNodeFacts` and `certificate_at_support` connect actual numeric evidence to the same selected Support. `preserves_at_support` and `reflects_at_support` prove admitted literal execution semantics. |
| `CallableIndexedOwnedLiteralLambdaBodyContinuations` | `support_flow_preserves` and `support_flow_reflects` derive the return child from actual coverage. `source_at_entry` / `native_at_entry` and `source_continuation` / `native_continuation` use genuine parameter admission and the original finish. |
| `SourceCoreChosenOrdinaryAcceptedLiteralSupport` | The accepted fixture derives its current-context domain, local absence of indirect calls, recaptured factories and expression tree internally. |
| `SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts` | The same fixture derives Word facts and original compiler receipts, then exposes preservation and reflection at its selected Support. |
| `CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission` | `source_value_typed`, `post_admission` and `callee_post` derive admission and the callee value relation from the actual initialized Source cell and occurrence typing. |
| `CallableIndexedOwnedLiteralLambdaInvocationBounds` | Invocation and application preservation/reflection derive body continuations internally and retain actual marked parameters, the reached pool and saved caller restoration. |
| `SourceCoreChosenOrdinaryAcceptedArgumentAdmission` | Actual numeric Source evaluations construct the physical pair, exclude argument faults and derive raw argument typing and admission at the same reached heap. |
| `SourceCoreChosenOrdinaryAcceptedLiteralInvocation` | The accepted fixture derives its body context, Word facts and compiler receipts internally, then instantiates invocation and application bounds. |
| `SourceCoreChosenOrdinaryAcceptedLiteralCallGuard` | Derives runtime parameter shape, Source stage acceptance, physical arity and the selected dispatch row's complete acceptance from genuine compiler and contract receipts. |
| `SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts` | Retains original parent acceptance, callee and argument compiler receipts, Prepared callsite and chosen root under the same policy, Header and body lowerer. |
| `SourceCoreChosenOrdinaryAcceptedPairArgumentBounds` | Derives the pair argument tree from parent acceptance and closes preservation/reflection using actual literal and tuple producers, with admission and all rows. |
| `SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication` | Derives final Source heap admission from actual call allocation and return; reflects the original fourth bind into a real parent Source outcome, retaining genuine dispatch, captures and complete prefix witnesses. |
| `CallableIndexedOwnedChosenOrdinaryArgumentBundles` | `native_type`, `compiler_parameters`, `compiler_parameter_pack` and `arguments_at_compiler` derive native signature and argument alignment from the known chosen carrier and actual callee value relation. |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts` | `Receipt` and `at_chosen_parent` retain the original sidecar, lambda origin, codebook rows, dispatch and selection at the same actual Prepared callsite. |
| `CallableIndexedOwnedStoredIndirectPurePrefixBounds` | `reflects_arguments` and `reflects_parent` extract the actual ordered argument post and full successful runtime prefix from Core completion, keeping the measured application child. |
| `SourceCoreChosenOrdinaryAcceptedParentEntryReceipts` | `fixture_compilation` / `fixture_root` transport only the genuine Header named index. `pair_at_chosen_parent`, `parent_declarations` and `callee_at_parent` derive the closed pair and initialized read producers from the original accepted parent. |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport` | Transports the actual sidecar, lambda origin, dispatch and selected rows along genuine Source equality while retaining the same chosen compiler root. |
| `SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes` | `values_at`, `noFault` and `evaluates` retain the actual singleton pair arguments and unchanged heap from independent Source traces. |
| `SourceCoreChosenOrdinaryAcceptedParentPreservationBounds` | `preserves_parent_at_initialized` derives whole Core parent evaluation and the full admitted result from the actual Source parent outcome. |
| `SourceCoreChosenOrdinaryAcceptedParentReflectionBounds` | `reflects_parent_at_initialized` derives the independent Source parent outcome and full admitted result from whole Core completion. |
| `SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts` | `of_body`, `emitted_at_header` and `at_original_root` retain actual initializer, Allocation/Annotated and flow/finish compiler receipts at the same root. |
| `SourceCoreChosenOrdinaryAcceptedInitializerAdmission` | `receipt_value_has_type`, `receipt_outcome_at` and `receipt_post_admission` derive the same selected closure's raw typing, pure Source outcome and unchanged-state admission from genuine coverage and captures. |
| `CallableIndexedOwnedChosenOrdinaryInitializedAllocationState` | `allocate_initialized` runs the original stateful allocator once and returns its full reached tuple, admission and positive chosen stored member. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyBounds` | `whole_from_parent_value` / `whole_from_parent_fault` compose actual native children. `parent_at_whole_completion` extracts the genuine strict child; `source_parent_at_body` inverts the independent Source body. |
| `SourceCoreChosenOrdinaryAcceptedHeaderEvidence` | `header_exists_with_evidence` and `header_fixture_with_evidence` retain `HeaderAt` and empty evidence from the same authentic Header constructor. |
| `SourceCoreChosenOrdinaryAcceptedInitializedEntry` | `initialized_entry` runs one original formation and one stateful initialized allocation, retaining the actual reached tuple, original history and positive stored member. |
| `SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction` | `body_from_parent_value` / `body_from_parent_fault` and `body_trace_at_header` construct the original two-statement Source body. `post_admission_at_runtime` transports raw typing to Γ0 at the same reached state and rows. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds` | `preserves_body` and `reflects_body` derive complete accepted-body correspondence and `BodyResultAt`, including cumulative effects, the actual restored caller and successful raw admission. |
| `SourceCoreChosenOrdinaryAcceptedBodyStatePorts` | Derives empty Source entry, actual captures, global references, native store typing, readiness and admission from the same real named parameter Receipt. |
| `SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission` | Derives deep typing after the genuine empty-parameter allocation and every stable row after the actual singleton hook installation and parameter effects. |
| `SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence` | Retains global count and empty evidence from the same authentic Header constructor. |
| `SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence` | `preserves_at_receipt` / `reflects_at_receipt` derive admitted whole-body correspondence at the actual reached pool. `source_body_at` / `native_body_at` implement the existing body interfaces. |
| `RecursiveNamedCatalogPreparedInitializationReceipts` | `stored_capture` and `entry_with_constructor` construct the actual initialization authority and retain its prescribed live capture, exact initialized store and empty Source heap relation. |
| `SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt` | `PublicRecipeReceipt`, `CompletedBootstrap` and `completed_store` retain one original preparation and one machine completion. `accepted_public_fixture` provides the positive executable receipt. |
| `SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence` | `BootstrapEvidence`, `header_exists_with_bootstrap` and `header_fixture_with_bootstrap` retain the same authentic Header, runtime evidence, layouts and empty Source captures. |
| `SourceCoreChosenOrdinaryAcceptedPublicParameterEntry` | `catalog_complete`, `catalog_ledger`, `initial_at_completed` and `parameter_entry` derive the actual initial state and named parameter Receipt. `ParameterAgreement` retains its original prefix/body ContinuationAgreement. |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence` | `at_completed` constructs the same actual parameter Receipt and `BodyAtReceipt`, including admitted body preservation/reflection and SourceBodyAt/NativeBodyAt. |
| `SourceCoreChosenOrdinaryAcceptedPublicInvocation` | `source_continuation_at_initial` / `native_continuation_at_initial`, `preserves_at_initial` / `reflects_at_initial` and `at_completed` derive original named invocation at the actual initial store. The low result keeps restoration and cumulative effects. |
| `SourceCoreIndexedSession` | `RecipeAt`, `InitialAt`, `NativeDone`, `NativeAt` and `BootstrappedFrom` retain original construction. `resumeWithReceipt` and `ResumeAt` share the actual resume action; `succeeded` / `failed` retain its real completion. `SucceededResultAt.source_type` / `word_value` and `ResumeAt.word_succeeded` use authentic request/export acceptance. Legacy operational signatures remain unchanged. |
| `SourceCoreChosenOrdinaryAcceptedPublicSessionEntry` | `accepted_public_session_fixture` retains the original public IO chain. `completed_at_ready`, `body_at_session` and `invocation_at_session` connect its actual ready Session to the same initialized store, world and static registry. Normal full/API checks and the positive ready runner pass. |
| `SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission` | `originalCatalog`, `program_well_formed` and `program_has_stages` derive genuine original Source admission from full finite catalog equality, original checker typing and actual stage analysis. |
| `SourceCoreChosenOrdinaryAcceptedPublicRootStart` | `at_session`, `preserves_root` and `reflects_root` connect actual successful Session.start and the original invocation to the same checkpoint and initialization store. |
| `SourceCoreChosenOrdinaryAcceptedPublicResultObservation` | `observe`, `Observation.word_iff` and `Observation.fault_iff` retain identical Words or the genuine fault relation from the complete low invocation result. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome` | `at_started`, `native_completed_reflects_program`, `program_has_sufficient_native_fuel`, `public_succeeded_reflects_program` and `program_word_preserved` connect independent admitted ProgramOutcome to actual native completion and successful Word export. `accepted_public_program_run` retains one original public action chain. |
| `CallableIndexedOwnedNamedProgramAdmission` | `after_program_outcome` derives successful raw value/deep heap typing and all returned stable rows from genuine ProgramOutcome and the final administrative frame. `after_program_transition` keeps the original transition's same returned witness. |
| `CallableIndexedOwnedBodyRestorationAdmission` | `restore_rows`, `restore_fault_post` and `restore_post` retain the actual restored pool. `restore_return_with_post` uses the original restore action once and keeps its complete tuple plus successful post admission under genuine TypeContextSupports. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission` | `ResultAt` retains the original six effects, same returned State, Relates and PostAdmission. `ResultAt.at_value` exposes raw value typing and deep heap admission. The program/export P/R ports and `public_run_succeeded_reflects_program` consume their original proof producers once. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit` | `BodyResultWithExit` joins the original body result with genuine ReachedExit at the same final indices. `preserves_body_with_exit` / `reflects_body_with_exit` retain the actual binder, Source control and full supplied administrative environment. |
| `SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts` | `source_preserves_at_receipt` / `native_reflects_at_receipt` supply the existing strong PreparedNamedParameterReceipts contracts at the same actual Receipt. `source_bodies_for` / `native_bodies_for` quantify genuine strict body children without low erasure. |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts` | `BodyAtReceiptWithExit` and `at_completed` retain one actual public parameter entry, the same initial state/Receipt/agreement and both strong body contracts for every independent grade. |
| `NamedInvocationFaultPostContracts` | `BodyExtra`, `TrivialExtra` and `ReturnedAtWithExtra` retain the same actual entry, parameter/body states, Source trace and restore receipt. `ReturnedAtWithExtra.forget` projects the original post-only receipt from those same witnesses. |
| `CallableIndexedOwnedInvocationBounds` | `SourceBodyAtWithExtra` / `NativeBodyAtWithExtra`, their continuation interfaces and `invocation_preserves_bounded_at_with_extra` / `invocation_reflects_bounded_at_with_extra` carry the supplied body fact and actual restored frame through the original core. Legacy post-only signatures remain unchanged. |
| `CallableIndexedOwnedPreparedNamedInvocationAdmission` | `source_body_with_extra_at_receipt` / `native_body_with_extra_at_receipt` and the actual continuation adapters retain strong Receipt exit/post at the same body state. `invocation_preserves_bounded_at_with_admission` / `invocation_reflects_bounded_at_with_admission` add caller post through pure restoration with genuine context support and saved rows. |
| `SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission` | `ResultAtWithExit`, `to_post`, `preserves_at_initial` / `reflects_at_initial` and `at_completed` retain the same causal body exit and restored caller post in the actual accepted initial/completed pair. |
| `CallableIndexedOwnedContextualStoredClosureAssociationReceipts` | `Member` retains genuine ordinary/principal formation authority. `selection`, `represents`, `association` and `extend` project or transport the same member. `formation_member` / `principal_formation_member` retain one original formation receipt. `Member.to_static` forwards it to the typed receipt at `350e4336`. |
| `CallableIndexedOwnedContextualInitializedClosureReceipts` | `StoredAt`, `allocate_initialized`, `read_member` and `callee_post` retain the positive member, real initialized cell reads and same reached state. `extend_with_reads` requires genuine future reads. `source_value_typed` / `post_admission` use actual Source admission. `TypedStoredAt` and `StoredAt.to_static` retain the same physical cells/reads with a typed StaticMember at `350e4336`. |
| `CallableIndexedOwnedContextualStoredMemberCallBounds` | `member_stage_origin`, `member_origin_at_caller`, `dispatch_at_member` and `callee_at_stored` derive the original gate and same-state callee post from a positive ordinary/principal member. `argument_rows`, `preserves_at_stored` and `reflects_at_stored` retain genuine ordered arguments, strict continuations and actual returned states. |
| `CallableIndexedOwnedContextualPrincipalStoredCallReceipts` | `member_from_selection`, `stored_from_selection` and `stage_origin_from_selection` retain method-principal authority and real current reads. `formation_member_from_selection` uses the original contextual principal formation once. |
| `CallableIndexedOwnedContextualStoredExpressionHeads` | `suffix_of_source` derives the original measured SourceSuffix; `Receipt`, `Head`, `LiveAt` and `LiveFor` bind real compiler and current-cell evidence. `preserves_at` / `reflects_at` supply admitted head contracts under genuine LiveFor and strict child continuations. |
| `CallableIndexedOwnedContextualStoredClosureWriteReceipts` | `written_member` performs one actual initialized write and retains the positive member at that cell. `preserves_other` requires genuine Source/native writes and map injectivity to preserve another cell. |
| `CallableIndexedOwnedContextualCellOrigins` (typed migration validated at `350e4336`) | `FunctionOrigins`, `PayloadOrigins` and `CellOrigins` retain typed StaticMember closure leaves through the existing payload/heap model. `payload_static_member` attaches genuine typed authority; the legacy `payload_member` forwards its receipt. `functions_include_general` forgets forward. Actual allocate/write ports and `stored_at` retain live cell evidence; `PostWithOrigins`, `post_at_same_state` and `at_value` bind admission and strong result at the same reached state. |
| `CallableIndexedOwnedContextualCellOriginFormationReceipts` (validated at `53095e76`) | `ordinary_formation` / `principal_formation` each retain one original formation and its receiving-model representation, same positive Member, unchanged strong heap, attached PayloadOrigins and result representation. |
| `CallableIndexedOwnedContextualCellOriginAllocationReceipts` (validated at `67d5c9af`) | `AdmissionWithOrigins`, `allocate_initialized_from_post` and `write_initialized_from_post` retain raw admission and positive cells inside the same actual reached witness. Allocation retains its full original tuple; a real mapped write preserves the actual records and stable rows. |
| `CallableIndexedOwnedStoredIndirectCallForModelReflection` (validated at `31b073bf`) | `application_reflects_of_bundles` derives the genuine receiving-model application leaf. `reflects_selected` reconstructs the whole finite Source call and retains its independent grade, represented result, heap and raw post at the same returned caller. Ordered bundles, Association and strict children remain genuine inputs. |
| `CallableIndexedOwnedContextualCalleeOriginReadReceipts` (typed migration validated at `350e4336`) | `InitializedReadAt` / `initialized_read_at` preserve the actual raw cell type and real reads. `CalleeAt` / `callable_at` and the closure/global/builtin projections retain positive origins through compatible wrappers; closure projections return the actual StaticMember; no selected-code or generalized-cell receipt is inferred. |
| `CallableIndexedOwnedContextualStoredCallOriginPosts` (validated at `1ec31128`) | `ResultAt`, `of_result_at`, `preserves_selected` and `reflects_selected` retain positive cells and raw admission inside the original same-state returned caller. `ResultAt.at_value` and `forget` observe or project that witness. Actual Association, ordered bundles, callee traces, SourceSuffix and strict children remain explicit. |
| `CallableIndexedOwnedContextualCellOriginExpressionPosts` (validated at `7e39da09`) | `model`, `PreservesAt` / `ReflectsAt`, `preserves_at` / `reflects_at` and both `forget` ports retain the original child witness with positive cells, result and admission. |
| `CallableIndexedOwnedContextualCellOriginReadPosts` (validated at `9308e009`) | `Reads`, `preserves_reads_at` / `reflects_reads_at`, `initialized_at_binding` / `initialized_at_local` and `callee_at_post` cover actual read branches and classify the same returned positive payload. |
| `CallableIndexedOwnedContextualTypedClosureReceipts` (validated at `df034b25`) | `Association` and `StaticMember` retain the actual ordinary/principal Code/body/Syntax. Compiler shape, native typing, stage origin, selection and forward representation ports retain that authority. `preserves_at` / `reflects_at` use genuine strict typed FlowBelow and the original invocation/restoration at the same Association. |
| `CallableIndexedOwnedContextualTypedClosureFormationReceipts` (validated at `1d279cc7`) | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` retain the same generated StaticMember, positive result/cells and Source admission. Each uses one original factory. Body and receiving registries remain separate; legacy `ResultAt.forget` requires their equality. |
| `CallableIndexedOwnedContextualStoredCallTypeReceipts` (validated at `7e85f0bb`) | `TypedCallAt`, `at_typed_callee` and `at_callee_post` derive ordered Source/native aggregate equalities from original raw typing, argument Tree, compiler callable policy and retained StaticMember. Admission and positive cells stay at the callee post; physical arity and stage verdicts remain separate. |
| `CallableIndexedOwnedContextualCalleeStageReceipts` (validated at `7e85f0bb`) | Origin and `boundary_at_*` ports retain the actual prepared user Dispatch or builtin row. `BuiltinAt.parameter_count`, `first_gate` and `resolve_prefix` retain the physical builtin count, native `.inRight .word .unit` first-gate result and unchanged original suffix/state/strict grade. Whole call/body composition remains separate. |
| `CallableIndexedOwnedPreparedOrdinaryBodyProjection` (validated at `0451cd62`) | `bodyWith`, `plain`, `Receipt` and `StaticMember` retain the same prepared JointBody. Flow ports use its real table and reached interpretations; `forget` and `extend` preserve the retained authority. |
| `CallableIndexedOwnedPreparedPrincipalLambdaSupport` (validated at `0451cd62`) | `Support`, `PreparedAt`, `source_receipt` and `Receipt` retain the selected Principal Site, implementation, dictionary and cached compilation. Same-body flow and forward plain/provenance ports keep those indices. |
| `CallableIndexedOwnedPreparedPrincipalFormationReceipts` (validated at `0451cd62`) | `formation_member` and `formation_post` retain one original principal formation, its prepared receipt and the same reached positive post. |
| `CallableIndexedOwnedPreparedContextualCellOrigins` (validated at `0451cd62`) | `Association`, `StaticMember`, `PayloadOrigins`, `CellOrigins` and `StoredAt` keep actual preparation through growth, allocation, writes and reads. `PostWithOrigins` retains that authority and Source admission at the same reached state. |
| `CallableIndexedOwnedPreparedContextualFormationReceipts` (validated at `0451cd62`) | Ordinary/principal `formation_member` and `formation_post` use the real factory once and retain the prepared member, positive cells and Source admission without equating body and receiving registries. |
| `CallableIndexedOwnedPreparedContextualFunctionViews` (validated at `0451cd62`) | `functions_include_general`, `observations`, `runtime_views`, `payload_general` and `cells_general` expose the forward General views. |
| `CallableIndexedOwnedPreparedContextualFormationBounds` (validated at `0451cd62`) | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` retain value/fault alternatives, prepared cells and admission at the returned state with independent Source/native grades. |
| `CallableIndexedOwnedPreparedCompilerChildCollector` (validated at `e27c3ccb`) | `Collected`, `factories`, `caller`, `prepared`, `cover_for` and `cover` retain actual ordinary compiler children and derive their coverage. |
| `CallableIndexedOwnedPreparedContextualQualification` (validated at `e27c3ccb`) | `Facet`, qualified Association/StaticMember and function/payload/cell origins retain one concrete preparation qualification through forward extension. |
| `CallableIndexedOwnedPreparedPrincipalCompilerChildren` (validated at `e27c3ccb`) | Accepted children, `SiteShell`, `extraction`, `collected` and `root_of_accepted` retain the selected method/dictionary and invoke the original joint-body producer once at the same Site. |
| `CallableIndexedOwnedPreparedCompiledQualification` (validated at `e27c3ccb`) | Positive `Ordinary`/`Principal` constructors, `facet` and association producers install the actual collected compiler packet at the same Code and Support. |
| `SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission` (validated at `6bbea5e`) | `RootAtInitialWithExit`, `forget`, `invocation_at_session`, `at_session`, `preserves_root` and `reflects_root` retain the same causal exit/admission witness at actual root completion, including the measured native invocation child and independent Source grade. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramOutcomeWithExit` (validated at `6bbea5e`) | `ProgramAtWithExit`, `forget`, `at_started` and the `*_with_exit` program/export ports join that same result to genuine ProgramOutcome and successful Word export through the original receipts. |

The literal invocation derives its body ledger and runtime validity from the same selected Support. Source and native grades remain independent. The approved body child is literal occurrence 3; the outer indirect parent at occurrence 5 remains in the Source. Whole parent preservation and reflection now derive the callee post, pair arguments, fault exclusion, dispatch and native argument bundle internally. Both retain the actual returned caller and cumulative heap, mapping, world and administrative effects. Genuine initial heap, stored-cell authority, captures, history, environment correspondence, native typing and input admission remain explicit in the parent ports. The accepted outer body now forms its initializer and allocates its local cell once, then runs the proved parent at that actual admitted post. Reflection reconstructs whole native execution and uses determinism to align its final value and store. The returned result retains cumulative effects, the actual restored pool, every ordered row and successful raw value/deep heap typing at Γ0. The BodyState adapter derives these inputs from the same actual named parameter Receipt and runs each whole-body port once. Its returned result retains the same actual pool and successful raw PostAdmission. The existing low SourceBodyAt and NativeBodyAt interfaces remain available. The new BodyStateExitReceipts companion also populates PreparedNamedParameterReceipts.PreservesAt/ReflectsAt with genuine ReachedExit, successful PostAdmission and the same returned state.

The latest committed and normally verified code commit is `2caef32a`. The typed contextual receipt unit was introduced at `df034b25`, and the positive-cell backend migrated at `350e4336`. `CallableIndexedOwnedContextualTypedClosureReceipts` retains actual ordinary and method-principal lambda formation through a typed `Association` and a propositional `StaticMember`.

The receipt keeps the original Code, owner, ordered history, captures, parameter bindings, static body and independent Source syntax. Its forward representation and selection ports preserve that authority. Finite application preservation and reflection consume real argument typing, initial stable rows and strict typed `FlowBelow` for the same retained Code. Each uses the original parameter/body invocation and saved caller restoration once, retaining the actual returned pool and independent Source/native grades. The typed finish derives exclusion of escaping break/continue from the Source body receipt; it requires no unconditional escaped-control diagnostic at internal Word zero.

Normal verification at `df034b25` passes 5635 registered build jobs, one empty strict Source log, all 56 complete module-owned declarations and 24 API checks. Every private/normal TYPE/AXIOMS block and the complete API logs match literally, using only the standard three axioms. The measured cumulative census is 16605 from 16549: 56 additions, no prior overlaps or removals. The 5567-row pre-install snapshot, actual 2094-module import environment, one existing `CoreLowering` object delta, three-module dependency cone/rebuild and all 4985 protected artifacts pass. Three proof-port name corrections preceded the final empty strict log. This unit adds one proof Source and one umbrella import.

The positive-cell proof backend migrated to these receipts at `350e4336`. Four strict Source logs are empty on their first attempts. Normal validation passes all 92 complete private/normal literal TYPE/AXIOMS blocks and 22 byte-exact API checks. The original/current ownership census changes 88 → 92: 80 same-name literal matches, eight explicitly reviewed TYPE changes, four additions and no removals. Seven changes replace the legacy `Member` with `StaticMember`; one replaces `StoredAt` with `TypedStoredAt`. The measured cumulative declaration census is 16609 from 16605. Build 5635, the 5568-row pre-install snapshot, actual 2110-module import environment, 11 existing object deltas covered by the 15-module dependency cone/rebuild, and all 4985 protected artifacts pass. Shared registration roots and imports remain exact.

Typed closure formation now preserves and reflects ordinary and method-principal heads at `1d279cc7`. `CallableIndexedOwnedContextualTypedClosureFormationReceipts` keeps the generated `StaticMember`, positive cells and raw Source admission inside the same returned state witness. Each direction uses its original formation factory once. Reflection uses native determinism and independently sizes the Source trace. The main results keep the body registry and receiving registry separate; the two legacy `ResultAt.forget` ports explicitly require their equality because their targets use one registry.

Normal verification passes 5636 registered build jobs, one empty strict Source log, all 10 complete module-owned declarations and eight API checks. Private/normal TYPE/AXIOMS blocks and complete API logs match literally. The cumulative census is 16619 from 16609: ten additions, no overlaps or removals. The 5568-row pre-install snapshot, actual 2110-module environment, one existing umbrella object delta, three-module dependency cone/rebuild and all 4985 protected artifacts pass. The unit adds one proof Source and one umbrella import. Mixed expression/body closure and all-pass composition remain incomplete.

Typed stored-call and selected stage-boundary receipts now pass normal verification at `7e85f0bb`. `CallableIndexedOwnedContextualStoredCallTypeReceipts` derives ordered Source/native aggregate equalities from the original compiler receipt, raw Source typing, argument Tree and the positive callee's retained StaticMember. `at_callee_post` keeps Source admission and positive cells at that same reached state. Body and receiving registries remain separate. Physical binder arity and stage decisions require their own receipts.

`CallableIndexedOwnedContextualCalleeStageReceipts` uses the retained origin and actual caller preparation to construct a user Dispatch or authentic builtin row. `BuiltinAt.parameter_count` retains the builtin's physical parameter-list length. Its absent guard proves the original first-gate result `.inRight .word .unit`; `resolve_prefix` preserves the original argument/application suffix, unchanged gate store and strict suffix grade. User rejection, second-gate arity/application and whole indirect body composition remain separate.

Normal verification passes 5638 registered build jobs, two empty final strict Source logs, all 47 complete module-owned declarations (22 typed-call / 25 stage-boundary) and 17 API checks. Private/normal TYPE/AXIOMS blocks and complete API logs match literally. The cumulative census is 16666 from 16619: 47 additions, no overlaps or removals. The 5569-row pre-install snapshot, actual 2126-module environment, one existing umbrella object delta, four-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds two proof Sources and two umbrella imports.

Prepared closure receipts and cell origins now pass normal verification at `0451cd62`. Ordinary and selected-principal support retain the actual compiler preparation, one JointBody, the same Code and typed body, and Source provenance. Principal support also retains the selected implementation, dictionary and cached named compilation. These receipts project forward to the existing typed model; an existing plain leaf cannot be upgraded to prepared authority.

The prepared Association, payload and cell model preserve that authority through map/world growth and actual allocation, writes and reads. Formation uses its original ordinary or principal factory once and retains the prepared member, represented result, positive cells and Source admission at the same reached state. Graded preservation and reflection retain the Source value/fault alternatives and independent Source/native grades. The body's static registry and receiving registry remain separate; function observations and runtime views project forward to the General model.

Normal verification passes one registered build with 5645 jobs, seven empty final strict Source logs, all 274 module-owned declarations and 79 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 16666 to 16940: 274 additions, no overlaps or removals. The 5571-row pre-install snapshot, actual 2172-module environment, one existing umbrella object delta, nine-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds seven proof Sources and seven umbrella imports.

Compiler child collectors and prepared function qualification now pass normal verification at `e27c3ccb`. The ordinary collector derives child coverage from the actual retained compiler inventory. The selected-principal collector keeps the actual method, dictionary, cached compilation and same Site; its original joint-body producer runs once. Concrete ordinary/principal qualification travels with the same Code and Support through function values, payloads and cells, including forward map/world extension. These static receipts retain compiler authority for the subsequent semantic proof.

Normal verification passes one registered build with 5649 jobs, four empty final strict Source logs, all 159 module-owned declarations and 36 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 16940 to 17099: 159 additions, no overlaps or removals. The 5578-row pre-install snapshot, actual 2187-module environment, 1 existing umbrella object delta, 6-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds four proof Sources and four umbrella imports.

Canonical parameter protocols and qualified closure flow now pass normal verification at `0338a276`. Ordinary and selected-principal packet producers retain the original parameter entry, canonical bindings, globals and base pool. Typed continuations consume the body flow under that same caller protocol and keep the original Source body receipt. Qualified formation retains compiler authority with the represented closure, positive cells and Source admission. The canonical flow producer uses one retained JointBody and transports the actual returned pool through its protocol bridge. Source and native grades remain independent.

Normal verification passes one registered build with 5655 jobs, six empty strict Source logs, all 128 module-owned declarations and 29 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 17099 to 17227: 128 additions, no overlaps or removals. The 5582-row pre-install snapshot, actual 2192-module environment, one existing umbrella object delta, eight-module dependency cone/rebuild and all 4985 protected artifacts pass. Six proof Sources and six umbrella imports are added.

Protocol-specific finish, ordinary/principal parameter packets, qualified formation and canonical flow are integrated. The shared expression/body family still needs actual compiler occurrence typing, canonical capture and selected method-prefix alignment, reached diagnostic interpretations, and a concrete common induction over expressions and function bodies. The canonical flow producer requires genuine diagnostic table readiness and both reached error interpretations; registry extension alone supplies neither. Named and indirect dispatch, mixed bodies and the final public theorem across specialization, evidence and comptime remain unfinished.

Reached read and index diagnostics are integrated at `ef85a057`. The proof uses the actual local-cell read or raw missing-index witness, the selected compiler issuer and the receiving public decoder. The ordered Source prefix, diagnostic reason, returned state and independent grades remain attached to that occurrence. Normal verification passes build 5673, seven empty strict logs, 76 declarations and 24 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17536.

Direct prepared closure origins and ordinary/principal formation are integrated at `6dbfa243`. The actual Code, History, Support, Source origin, captures and positive cells remain together in the returned state. The stage-scope receipts recover the original owner and source scope from authentic sidecars. Receiving and body registries remain independent. Normal verification passes build 5677, four empty strict logs, 139 declarations and 47 API checks with complete literal private/normal agreement; the cumulative census is 17675. Invocation adapters and the shared expression/body family still need normal integration and complete compiler occurrence factories.

Paired compiler typing and constructive call packets are integrated at `2caef32a`. One compiler traversal retains independent actual-context and fixed-prefix typing for each used child, while keeping the original body Tree, plan and diagnostic issuer. Accepted closure and named branches construct their argument packets from genuine Source types, physical arity and the selected owner or dictionary. Eligible ordinary and principal lambda flow uses the same retained compiler receipt and receiving state. Normal verification passes build 5742, 20 empty strict logs, 273 declarations and 75 API checks with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 18887 (+273, no overlaps or removals). The numeric expression/body induction and complete public compiler coverage remain unfinished.

The shared expression/body family remains incomplete. Static factories must construct the same retained body's compiler Tree at every genuine occurrence context, scope and read budget. Source typing alone does not justify globally empty evidence or coercions, or exclude generalized local cells. Actual compiler alternatives require their own coverage. Ordinary execution also needs authentic guard acceptance at each reached indirect call; separate staged judgments preserve guard rejection before arguments. The final recursive staging proof must cover the remaining Source forms.

Next: close one receiving-model expression/body family across closure, named/global, builtin and method calls, with positive cells and genuine physical arity, Source stage gates and public diagnostic inclusion. Then compose the actual specialization, evidence and comptime transformations through the public compilation and input boundary. Generalized/scheme cells, compound assignment, general failure/export-error correspondence and the final all-pass theorem remain incomplete. The first objective remains 100%; the second stays about 70%, and the equally weighted overall estimate stays about 85%. These are estimates of completed work, not declaration counts or remaining time.

The actual public Recipe and completed bootstrap populate the named parameter Receipt and its ContinuationAgreement for the unchanged accepted fixture. `PublicBodyCorrespondence.at_completed` supplies admitted body preservation/reflection and SourceBodyAt/NativeBodyAt. `PublicInvocation.at_completed` supplies original named invocation at the same initialization store, deriving its actual parameter child internally and retaining caller restoration and cumulative effects. That low ResultAt remains available. The accepted public program companion adds successful raw PostAdmission at the same returned caller using genuine ProgramOutcome, saved stable rows and the final administrative frame.

The Session consumer retains one real `openWithReceipt` / `bootstrapFreshWithReceipt` / `resume` chain and the actual `.ready` equation. The program collector derives StaticReceipt on that same fixture, performs its selected root start once and calls `resumeWithReceipt` once. Its successful public result has the identical Source Word and genuine original ProgramOutcome. The post-admission companion now retains successful raw value/deep heap typing and all returned stable rows at that result's same caller state. Faults retain stable rows only. Source and native budgets remain independent; Source Word export requires a positive boundary budget. The finite accepted body retains genuine ReachedExit/LexicalResult through the strong parameter Receipt contract. The generic invocation factor now carries a supplied body fact inside the same causal witness through one original caller restoration. The adapter now supplies that fact from genuine strong Receipt contracts and adds caller admission at the same causal witness using pure restoration and genuine context support. Its accepted initial/completed pair retains both directions without replaying bootstrap or parameters. At `06f2635c`, normal verification passes build 5618, full 27 / API 20, two empty strict logs and every private/normal TYPE/AXIOMS block literally; cumulative 16297 adds 27 names with no overlaps or removals. The 5549-row snapshot, 2295-module environment, two existing object deltas, four-module cone/rebuild and 4985 protected artifacts pass. The public root/program exit companions now retain the same causal exit/admission result at actual root completion and successful positive Word export. They use the original start/resume receipts, retain the measured native invocation child and independent Source grade, and project low observations by pure forgetting. At `6bbea5e`, normal verification passes build 5620, full 31 / API 14 and two empty strict logs; all 31 private/normal TYPE/AXIOMS blocks match literally with only the standard three axioms. Cumulative 16328 adds 31 names to 16297 with no overlaps or removals. The 5551-row snapshot, 2297-module environment, one existing `Tests.Main` object delta, three-module cone/rebuild and 4985 protected artifacts pass. The proof umbrella is unchanged and no IO is added. The scope is the finite accepted fixture. Contextual ordinary/principal members now pass through initialized allocation/read to Association and the same-state callee post at `d51edb70`. The common stored-call ports at `45a38df8` connect that producer to the original selected-call preservation/reflection. The admitted whole-expression head now derives its SourceSuffix internally; universal LiveFor and mixed-family closure remain separate. General public failure/export-error correspondence, mixed bodies and all-pass correctness remain unfinished. At `8d2289c5`, normal verification passed 5616 build jobs, two empty strict Source logs, all 62 private/normal literal TYPE/AXIOMS blocks and 36 signatures. The measured cumulative count is 16270 (net +10); 50 original same-name blocks match literally and two generated helpers have reviewed moves. This factor adds no runner or IO. The public Word 7 and two existing regression receipts at `7b0f562f` remain historical.

The accepted initialized body now preserves and reflects genuine lexical exit and LexicalResult with the same represented result, cumulative effects, returned pool and PostAdmission. The BodyState adapter uses the actual parameter Receipt's full administrative environment; creator capture remains separate. One public parameter entry supplies the same initial state, Receipt and ContinuationAgreement and both strong body contracts at independent grades.

The three-module checkpoint is `f0274543`. Its one prior overlap is `Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captures_at_entry.congr_simp`, whose saved-before and current TYPE/AXIOMS blocks match literally. The proofs add no runtime action, runner or new public Session correspondence.

The old `SourceTypedRuntime` namespace remains in compatibility value, observation, and validation carriers. Its name does not imply that a runtime evaluator of Source expressions and statements remains.

Moving the comptime evaluator to Core and adding source contract/storage/external-call connections are the agreed next phase. Meaning preservation for comptime transformations actually performed by the current compiler is part of the second goal.

## Canonical parameter and closure proof interfaces (`0338a276`)

These interfaces retain static proof authority for the existing public execution API.

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedTypedLambdaProtocolContinuations` | `Packets`, `FlowPreserves`, `FlowReflects`, `source_continuation`, `native_continuation` |
| `CallableIndexedOwnedPreparedLambdaProtocolPackets` | `Ordinary.packets`, `Principal.packets` |
| `CallableIndexedOwnedPreparedQualifiedExpressionOutputs` | `payload_static_member`, `closure_member`, `Post` |
| `CallableIndexedOwnedPreparedQualifiedFormationReceipts` | Ordinary/principal `formation_member` and `formation_post` |
| `CallableIndexedOwnedPreparedQualifiedFormationBounds` | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` |
| `CallableIndexedOwnedPreparedCanonicalFlowBounds` | `Origin`, its protocol/bridge/transport/bindings/producer/acquire ports, `preserves_flow`, `reflects_flow` |

Protocol-specific finish, ordinary/principal parameter packets, qualified formation and canonical flow are integrated. The shared expression/body family still needs actual compiler occurrence typing, canonical capture and selected method-prefix alignment, reached diagnostic interpretations, and a concrete common induction over expressions and function bodies. The canonical flow producer requires genuine diagnostic table readiness and both reached error interpretations; registry extension alone supplies neither. Named and indirect dispatch, mixed bodies and the final public theorem across specialization, evidence and comptime remain unfinished.

## Native compiler occurrence proof interfaces (`e0edb2ec`)

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedPreparedCanonicalCaptureReceipts` | Prefix/capture agreement and ordinary/principal captured parameter packets and admission |
| `CallableIndexedOwnedPreparedPrincipalRootPrefixTyping` | `body_native_at_prefix` |
| `CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping` | Snapshot result normalization and `certificate_native` |
| `CallableIndexedOwnedPreparedNativeLexicalCollectors` | `tree_of_typed_flow_with_residual` |
| `CallableIndexedOwnedPreparedNativeMatchCollectors` | Native expression/body extraction and `finite_typed_of_lower` |
| `CallableIndexedOwnedPreparedNativeAssignmentChildren` | Raw typing, packed children, present RHS and ordered key extraction |
| `CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors` | `Head.of_lower_with_raw_occurrences` |
| `CallableIndexedOwnedPreparedNativeForHeaderCollectors` | `extraction_of_lowerForItems_with_coupled` |
| `CallableIndexedOwnedPreparedNativeImperativeCollectors` | `extraction_of_typed_position_with_catalog_coupled` |

These interfaces derive local child typing from the same emitted Core expression. Authentic Source facts and the actual compiler Site remain independent inputs. The shared expression/body induction and full public compiler theorem remain incomplete. Normal verification passes build 5664, nine empty strict logs, 134 declarations and 28 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17361.

## Static compiler authority proof interfaces (`27abbb6f`)

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedLocalIdentityFreshness` | `lambda_parameter_not_input`, `lambda_parameter_kind`, `lowered_parameter_kinds`, `match_hidden_fresh` |
| `CallableIndexedOwnedPreparedNativeSitePolicies` | Same-Site match context, binder/read/reference-slot/allocator policies and actual issued assignment/unary policies |

These interfaces derive static facts from genuine Source ownership and one actual Named Compilation and Site. They retain the root policy, scope/ledger and actual issued diagnostic identities. Runtime validity alone does not establish ownership, and these interfaces do not assume or prove the shared body execution family. Normal verification passes build 5666, two empty strict logs, 99 declarations and 16 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17460. The complete compiler theorem remains in progress.

## Reached diagnostic proof interfaces (`ef85a057`)

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedPublicDecodedAssignmentFaults` | `ErrorView`, `faults`, `of_decoded`, `reached_interpretation` |
| `CallableIndexedOwnedSelectedDiagnosticIssuerReceipts` | `lowered`, `selected_collected`, `SelectedReceipt`, `at_selected`, `at_principal`, `SelectedReceipt.principal`, `SelectedReceipt.principal_source` |
| `CallableIndexedOwnedReachedExpressionDiagnosticBounds` | `preserves_with_literals`, `reflects_with_literals` |
| `CallableIndexedOwnedReachedDataHeadBounds` | `Head.preserves_at`, `Head.reflects_raw_at` |
| `CallableIndexedOwnedReachedAdmittedDataHeadBounds` | `preserves_at`, `reflects_at` |
| `CallableIndexedOwnedReachedAdmittedExpressionCallsHeads` | `preserves_at_with_calls`, `reflects_at_with_calls` |
| `CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies` | `reasonAt`, `reason_eq`, `own_found`, `reads`, `missing` |

These interfaces keep actual reached read/index witnesses and the selected receiving diagnostic issuer. They construct decoder error views from real runtime facts and retain the original Source prefix, state and grades. Header reason alignment, compiler branch factories, strict expression/body induction and the full public compilation theorem remain open. Normal verification passes build 5673, seven empty strict logs, 76 declarations and 24 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17536.

## Direct prepared closure proof interfaces (`6dbfa243`)

| Module | Main interfaces |
| --- | --- |
| `CallableIndexedOwnedPreparedNativeDirectCellOrigins` | `Association`, `StaticMember`, `FunctionOrigins`, `PayloadOrigins`, `CellOrigins`, `Post`, forward representation and runtime views |
| `CallableIndexedOwnedPreparedDirectFormationReceipts` | Ordinary/principal `history_at`, `formation_member` and `formation_post` |
| `CallableIndexedOwnedPreparedDirectFormationBounds` | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` |
| `CallableIndexedOwnedPreparedDirectStageScopeReceipts` | `sidecar_owner`, `code_scope`, `scope_at` and `original_scope` |

These interfaces retain the actual prepared source, captures and returned state. They recover the original stage scope without assuming its guard result. Body and receiving registries are independent. Normal verification passes build 5677, four empty strict logs, 139 declarations and 47 API checks with complete literal private/normal agreement; the cumulative census is 17675. The strict mixed expression/body family, full compiler alternatives and the final public theorem remain unfinished.

## Selected named static proof interfaces (`ee27dc50`)

| Module | Main interfaces |
| --- | --- |
| `CallableIndexedOwnedSelectedNamedHeaderReceipts` | `diagnostic_typed`, `reissued`, `reissued_view`, `reason_at`, `canonical_at_prepared`, `retained_at_prepared` |
| `CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts` | `selected_evidence_empty`, `SourceReceiptCover`, `SourceReceiptCover.selected_empty` |
| `CallableIndexedOwnedPreparedNamedSourceFactoryFacts` | `source_types`, `selected_validity` |
| `CallableIndexedOwnedNamedPhysicalArityReceipts` | `bound_parameters`, `dispatch_parameter_count`, `named_parameter_count`, `before_application` |

These factories retain the same actual selected row, diagnostic issuer, complete ordered Source metadata and resolved dictionary. Ordinary selected dictionary emptiness and physical arity follow from authentic receipts. Arity does not establish acceptance of the separate staging guard. The finite Source receipt cover remains an input; constructing that inventory, closing the shared expression/body induction and covering all public compiler branches remain unfinished.

## Prepared named inventory and bootstrap interfaces (`ae3d5594`)

| Module | Main interfaces |
| --- | --- |
| `CallableIndexedOwnedPreparedFiniteNamedInventories` | `Input.of_selected`, `issue`, `headers`, `globals`, `source_receipts`, `ordered`, `reached_coverage` |
| `CallableIndexedOwnedPreparedNamedDiagnosticSources` | `prepared`, `source`, `issuer`, `assignments`, `operand`, `unary`, `projection`, `missing`, `factory` |
| `CallableIndexedOwnedPreparedDirectNamedProfileExtraction` | `Children`, `Receipt`, `extract_at`, `Receipt.profile` |
| `CallableIndexedOwnedPreparedCatalogNamedProfiles` | `Profile.nested`, `Profile.receiving`, `Profile.factory`, `Profile.prepared_eliminator` |
| `CallableIndexedOwnedPreparedCatalogNamedBodyContinuations` | `body_protocol`, `bridge`, `source_continuation`, `native_continuation` |
| `CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds` | `invocation_preserves_bounded`, `invocation_reflects_bounded`, `application_preserves_at`, `application_reflects_at`, `source_certificate`, `arguments_at_global` |
| `CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles` | `of_collected`, `extract_at` |
| `CallableIndexedOwnedNamedBootstrapReceipts` | `of_recipe`, `Bootstrap`, `NamedOwner`, `NamedOwner.capture_zero`, `NamedOwner.globals`, `NamedOwner.named_capture` |
| `CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts` | `slots`, `empty_locals`, `cache`, `ledger`, `of_recipe` |
| `CallableIndexedOwnedReachedNamedRangeReceipts` | `range_of_valid_match`, `range_of_selected`, `range_at_catalog`, `catalog_range_of_selected` |

Direct and nested typed named-body adapters retain the same actual parameter-entry protocol. A bootstrap owner is produced from initialization and transported forward through a complete key embedding. An arbitrary existing named capture cannot be upgraded to that provenance. Profiles, genuine child typing, receiving diagnostics and the common graded expression/body induction must still be supplied by their actual compiler producers.

## Shared positive function and native call proof interfaces (`922ac60f`)

The following modules are registered through `CoreLowering`. Their interfaces retain the actual owner, compiler association, Source dictionary and occurrence context.

| Module suffix | Main interfaces |
| --- | --- |
| `PreparedPositiveFunctionOrigins` | `Owner`, `OwnerCover`, `ClosureAssociation`, `NamedAssociation`, `PayloadOrigins`, `CellOrigins`, `closure_member`, `global_member`, `bootstrap_owner_cover` |
| `PreparedFunctionModelFormationBounds` | Ordinary and principal `preserves_at` / `reflects_at` |
| `PreparedSelectedNativeFamilyQualification` | `facet`, `ordinary_family`, `principal_family`, `ordinary_prepared`, `principal_prepared` |
| `PreparedNativeTaggedLambdaCompilerReceipts` | `of_certificate_with_shell_property` |
| `PreparedReachedNativeExpressionTreeBounds` | `RuntimeTree`, `preserves_at`, `reflects_at` |
| `PreparedCatalogTypedNamedCallBounds` | `preserves_at`, `reflects_at`, `CallerEvidence`, `preserves_calls`, `reflects_calls` |
| `PreparedCatalogIndirectInvocationDispatcher` | `Receipt`, `preserves`, `reflects` |
| `PreparedCatalogIndirectArgumentReceipts` | `closure`, `named` |
| `PreparedCatalogIndirectApplicationBounds` | `ArgumentPackets`, `preserves`, `reflects` |
| `PreparedNamedProfileFamilies` | `profiles`, `source_continuation`, `native_continuation` |

These are conditional proof interfaces. A concrete packet producer must establish accepted physical argument count, retained Source typing and the selected callee association at the actual argument post. The shared expression/body induction must then supply the strict body continuations. These interfaces do not yet constitute the final theorem for all compiler passes.


## Paired compiler typing and accepted call interfaces (`2caef32a`)

These interfaces retain the same compiler occurrence, issuer and reached caller.

| Module suffix | Main interfaces |
| --- | --- |
| `IndirectSourceTypeRows` / `AcceptedIndirectPhysicalArity` | `original_rows`, `selected_count`, `closure_count`, `named_count` |
| `PreparedAcceptedClosureArgumentPackets` | `packets` |
| `PreparedAcceptedNamedArgumentPackets` | `StaticBodies`, `at_arguments`, `packets` |
| `PreparedPositiveNamedValueReceipts` | `association`, `of_read`, `at_arguments` |
| `PreparedPairedReachedNativeExpressionTreeBounds` | `NativeAt`, `WithBoth`, `native_head`, `RuntimeTree`, `preserves_at`, `reflects_at` |
| `PreparedPairedNativeLexicalCollectors` / `PreparedPairedNativeMatchCollectors` / `PreparedPairedNativeImperativeCollectors` | Single extraction with both actual and fixed native child witnesses |
| `PreparedPairedNamedProfileExtraction` | `Children`, `body_native_at_prefix`, `extract_at` |
| `PreparedEligibleSelectedNativeFamilyFlowStep` / `PreparedEligibleSelectedAssociationFlowBounds` | Ordinary/principal receiving flow and strict bounds at eligible roots |
| `PreparedSelectedPositiveLambdaPackets` / `PreparedEligibleSelectedLambdaCallBounds` | `of_compiler`, `Point`, ordinary/principal preservation and reflection |
| `PreparedPositiveCalleeBoundaryReceipts` | `function_origin`, `payload_origin`, `boundary_at_payload` |

The argument factories discharge concrete packet and arity obligations at accepted call branches. The eligible body ports still require the numeric expression/body induction. Reached stage rejection remains an independent Source staging outcome before argument evaluation; a boundary receipt does not establish complete recursive staging coverage.

## Accepted indirect parent and eligible function interfaces (`22a68060`)

Accepted-call proofs construct the builtin or user argument packet at the actual argument post, then invoke the original application and restore the saved caller. The following modules are registered through `CoreLowering`.

| Module suffix | Main interfaces |
| --- | --- |
| `PreparedOriginGlobalsCarriers` | `carrier`, `forget_slots` |
| `PreparedPairedCatalogNamedProfileFamilies` | `profiles` at the actual body entry with both native typings |
| `PreparedHeaderRootPolicyReceipts` | `header_action`, `at_successor`, `at_accepted` |
| `PreparedAcceptedBuiltinArgumentPackets` | `builtin_member`, `at_arguments`, `packets` |
| `PreparedAcceptedBuiltinIndirectParentBounds` | `preserves`, `reflects` |
| `PreparedAcceptedUserIndirectParentBounds` | `UserCallee`, closure/global constructors, `user_packets`, `preserves`, `reflects` |
| `PreparedIndirectCalleeReflection` | `reflects_value`, `reflects_fault` |
| `PreparedPairedOriginNamedCallBounds` | `preserves_calls`, `reflects_calls` |
| `PreparedEligiblePairedExpressionFamilies` | Pointwise and budgeted `ExpressionPreserves` / `ExpressionReflects`, `preserves_at_prefix`, `reflects_at_prefix` |
| `PreparedEligibleSelectedLambdaRecipes` | `RawLambda`, ordinary/principal `CompilerInputs`, `Recipes`, `preserves_at`, `reflects_at` |

Builtin application closes through the original primitive proof. User application retains strict closure or named body hypotheses. The eligible expression interfaces describe the needed induction hypotheses; they do not close the numeric expression/body induction. Actual first- and second-stage acceptance remain explicit. A rejected first-stage guard retains its separate Source staging judgment before arguments. Second-stage rejection occurs after argument evaluation and remains a separate pending branch. Complete scoped rejection and compiler occurrence coverage remain unfinished.

## Staged indirect call runtime proof interfaces (`d9f2a0c4`; 2026-10-10)

The ten proof Sources below are registered through CoreLowering at `d9f2a0c4`. Normal validation checked all 234 owned declarations and 71 selected APIs with literal private/normal TYPE/AXIOMS and complete API agreement. Build 5762 passed and the cumulative census grew from 19016 to 19250. Each Source had two nonauthor reviews. The common public execution API and Core AST/runtime definitions retain their existing behavior.

Except for `Staging.RecursiveTraceSize`, module names below are suffixes under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `Staging.RecursiveTraceSize` | `Size.stepSize`, `stepSize_positive`, `child_lt_stepSize`; `Expression`, `Expressions`, `Applies`, `Statements`: each `sound`, `of_trace` (11) | Grades the 46 original supported recursive staging rules; preserves actual scope, heap and failure tag. |
| `PreparedPairedSelectedAssociationFlowBounds` | `preserves_at_most`, `preserves_below`, `reflects_below` (3) | Same retained Association and literal fixed-prefix specialization; numeric eligible E and receiving contracts remain inputs. |
| `PreparedNamedEligibleExpressionFlowBounds` | `Certificate`, `certificates`, `Static`, `children`, `of_collected`, `preserves_children`, `reflects_children`, `preserves_flow`, `reflects_flow` (9) | Same finite Issued packet, actual Header root and independent actual/fixed typing; requires strict eligible E and static/receiving receipts. |
| `PreparedFunctionModelStageReflection` | `reflects_rejected` (1) | Actual rejected first gate before arguments, at the genuine callee post and full receiving function model; retains supplied genuine callee trace. |
| `AdmittedStagedExpressionBounds` | `PostAdmission`, `PostAdmission.at_value`, `PostAdmission.rows`, `PostAdmission.at_fault_type`, `after_expression_sized`, `after_related_expression_sized`, `PreservesAt`, `ReflectsAt`, `PreservesAtMost`, `PreservesBelow`, `ReflectsBelow` (11) | Actual reached caller state, relation and administrative frame; deep Source admission follows successful values, and stage failure retains stable rows. |
| `PreparedStagedIndirectCalleeFaultBounds` | `ResultAt`, `preserves_callee_fault`, `reflects_callee_fault` (3) | Propagates the exact semantic or nested stage failure from a strict callee child, preserving reached heap/store and caller relation. |
| `PreparedScopedCallBoundaryReceipts` | `CallView`, `CallView.argument_count`, `substituted_indirect_origin`, `indirect_origin`, `boundary_at_original`, `boundary_at_source_view` (6) | Forward original-call transport from the same SourceView and Prepared row; original codebook metadata stays distinct from actual substituted metadata. |
| `PreparedSecondCallGateRejection` | `rejected_row`, `rejected_gate`, `closure_gate`, `named_gate`, `builtin_gate`, `values_count`, `closure_source`, `named_source`, `builtin_source`, `user_native_preserves`, `user_native_completion`, `builtin_native_preserves`, `builtin_native_completion`, `arityFaults`, `stagedArityFaults`, `public_diagnostic`, `public_argument_post`, `public_staged_argument_post` (18) | Actual selected physical arity and codebook row yield semantic arity failure after evaluated arguments; retains reached argument state and explicit receiving transport. |
| `AdmittedStagedExpressionSequence` | `PostAdmission`, `PostAdmission.at_values`, `preserves_values`, `preserves_fault`, `reflects` (5) | Constructive ordered argument fold from genuine Tree, unique/typing rows and strict staged child E; success-only admission, exact failures and cumulative effects. |
| `PreparedStagedIndirectNativePrefix` | `CalleePost`, `FaultPrefix`, `ValuePrefix`, `reflects_prefix` (4) | Actual whole-parent first-bind inversion yields strict callee completion, its Source trace and reached post, then fault propagation or the original gate suffix. |

These are conditional semantic ports. The budgeted expression interfaces still need the numeric induction that constructs them. The first gate rejects before arguments with `Failure.stage`; second-gate arity rejects after arguments with `Failure.semantic`. A stage fault cannot be projected to an ordinary Dynamic fault. Both directions retain independently measured Source and Core grades and the same actual reached state.

Staged builtin application, terminal statements, receiving diagnostic adapters, the whole argument-prefix draft and later body drafts remain outside this package. Complete staged body recursion, call classification, scoped diagnostic composition, static compiler coverage, remaining recursive Source forms and the final all-pass public theorem are unfinished. Estimates remain 100% / about 70% / about 85%.

## Staged call diagnostics and terminal body interfaces (`1507404b`; 2026-10-11)

The twelve Sources below are registered through CoreLowering at `1507404b`. Normal validation checked all 184 owned declarations and 66 selected interfaces with literal private/normal TYPE/AXIOMS and complete API agreement. Build 5774 passed and the cumulative census grew from 19250 to 19434. Each Source had two independent nonauthor reviews. Module suffixes are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. These proof interfaces retain the existing public execution definitions.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `ReceivingPreparedShapeInterpretations` | `decoded_token_below`, `receiver_lookup`, `reached_interpretation` (3) | Actual accepted preparation bounds decoded tokens and preserves earlier receiving lookups through the sealed callable allocation; authentic receiver identity remains required. |
| `PreparedReceivingCallRejectionDiagnostics` | `reason_at_lower_bound`, `receiver_lookup`, `original_diagnostic`, `receiving_diagnostic` (4) | Same original selected call row and Site.reasonAt reach the actual receiving completion table; original metadata and selected issuer remain attached. |
| `PublicDecodedCallFaults` | `ErrorView`, `faults`, `stagedSemanticFaults`, `of_decoded`, `of_assignment`, `of_arity`, `of_staged_arity`, `arity_result`, `staged_arity_result` (9) | Concrete assignment and semantic arity views use the literal diagnostic table and physical counts; generic result forwarding retains the existing value model. |
| `PreparedReceivingCallRejectionPosts` | `selected_row`, `receiving_argument_post`, `receiving_staged_argument_post`, `row_at_source_view` (4) | Original BoundaryAt selects the row while CallView retains substituted metadata; physical mismatch yields a post at the actual argument heap/store and caller relation. |
| `PreparedReceivingFirstCallGateRejection` | `StageErrorView`, `stagedFaults`, `original_diagnostic`, `receiving_diagnostic`, `receiving_staged_post` (5) | StageErrorView keeps the actual invocation, failing scope, guard frame, SourceView, original Selected and GuardRejects; stage rejection keeps the actual callee post. |
| `AdmittedStagedTerminalStatements` | `Head`, `control`, `Head.trace`, `ResultRepresents`, `preserves`, `reflects` (6) | Four terminal value/fault rules are constructed from the actual Head and strict staged child hypotheses; return/tail controls retain exact tags and reached state. |
| `AdmittedStagedTerminalBody` | `code`, `code_rename`, `terminal_evaluates`, `flow_prefix`, `body_result`, `preserves`, `reflects` (7) | Actual terminal and footer binds produce original BodyResult for code.rename; strict child hypotheses retain independent grades, effects and reached admission. |
| `PreparedTerminalBodyCompilerReceipts` | `Terminal`, `Receipt`, `of_accepted`, `Receipt.head`, `Receipt.native_child`, `certificate` (6) | Accepted returnSome or singleton tail supplies the actual child action, predecessor fuel, result type and emitted footer; authentic child certificate remains explicit. |
| `PreparedTerminalStatementOrigins` | `substituted_contains`, `substituted_returning_iff`, `substituted_tail_iff`, `returning_origin`, `tail_origin`, `returning_head`, `tail_head` (7) | Forward SourceView transport recovers the original statement occurrence and form under substitution; node type equality remains separate. |
| `PreparedStagedTerminalBodyMeaning` | `fallback`, `source_head`, `emitted`, `preserves`, `reflects` (5) | Same accepted terminal receipt and SourceView construct Head and the actual emitted code.rename meaning using strict child E; original Source typing and compiler certificate remain cuts. |
| `PreparedStagedBuiltinApplicationBounds` | `source_value`, `preserves`, `reflects`, `argument_post` (4) | Represented ordered scalar arguments exclude builtin arity/type failures; original primitive P/R preserves the same argument state and independently grades the Source rule. |
| `PreparedStagedIndirectArgumentPrefix` | `source_rows`, `scoped_boundary`, `StageRejectedPrefix`, `ArgumentFaultPrefix`, `ApplicationPrefix`, `reflects_arguments` (6) | Actual parent inversion, original Source rows, scoped first gate and concrete ordered-argument reflection retain exact callee/argument posts and the strict application suffix. |

The first gate carries Failure.stage before arguments, with the exact failing scope and token. Physical arity mismatch at the second gate carries Failure.semantic after arguments. Both retain the concrete reached caller state and Source/Core effects. Numeric staged E hypotheses, authentic static certificate producers, whole application/body dispatch and complete Source/compiler coverage remain unfinished. Work estimates stay 100% / about 70% / about 85%.

Normal verification passed one registered build with 5774 jobs, twelve empty strict Source checks, and literal private/normal TYPE/AXIOMS agreement for all 184 complete owned declarations and complete API agreement for 66 selected interfaces, using only the standard three axioms. The cumulative census grew from 19250 to 19434 (+184), with no overlap or removals. The normal pre-install snapshot contained 5695 module rows; the current snapshot contains 5707. The independent BEFORE environment measured 2195 project modules and the compiled environment measured 2207. The existing CoreLowering object changed for registration; all fourteen modules in the reverse dependency cone were rebuilt, and all 4985 protected artifacts passed. All sixteen original normal receipts closed with exit code 0.

The independent BEFORE capture closed at `95d226` (`5e30b5`, session 27207); private full/API audit at `e7c58a` (`c4bffc`, session 59109); packet freeze at `ffc386` (`36c4ae`, session 8576); registered build at `335796` (`dc06e6`, session 62711); and normal validation at `8d3298` (`b29544`, session 57723). Code commit `1507404b20264fc300b656e9971205f3ecbf90a8` closed at `07591c`. The saved `staged-call-diagnostics-terminal-bodies-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `f3558384cf298fe7fd4d535eaafe4cd535435adef662b8e24db3b3cf80e013ba`. The checkpoint uses the original sixteen closed validation receipts; metadata finalization does not repeat their kernel runs.

## Staged call dispatch and terminal closure interfaces (2026-10-11; `6c165e33`)

`staged-call-dispatch-and-terminal-closures` is committed and normally verified at `6c165e33`. The twelve proof Sources contribute 106 complete module-owned declarations and 42 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19434 to 19540: 106 additions, no overlaps and no removals.

The registered build passes 5786 jobs. The independent selected dependency BEFORE contains 2250 modules; the compiled native environment contains 2262. The complete normal module snapshot changes from 5707 to 5719 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint uses these original sixteen closed receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `0799ac`; code commit `6c165e334b61a044e480e96ea9da7d414894817c` closed at `215010`. The saved `staged-call-dispatch-and-terminal-closures-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `dc631c0c098aee0e8a9fec163b3141d0142c3cb429aa78878f272d15a57c1ee3`. The corrected summary distinguishes the selected BEFORE environment of 2250 modules from the complete pre-install snapshot of 5707 module rows.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. All 42 interfaces below match the complete native and normal API logs. The 106 complete module-owned declarations also have literal private/normal TYPE/AXIOMS agreement.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `PublicDecodedStagedCallFaults` | `faults`, `of_semantic`, `of_first_gate`, `of_assignment`, `of_arity`, `decoded`, `semantic_result`, `first_gate_result`, `arity_result` | Literal receiving table keeps semantic and stage tags separate; exact call/scope/token result forwarding. |
| `PreparedStagedIndirectFirstGateBounds` | `result_at_rejected`, `preserves_rejected`, `reflects_rejected_prefix` | Strict callee preservation or authentic rejected-prefix reflection produces the same reached first-gate stage post. |
| `PreparedStagedIndirectSecondGateBounds` | `NamedOrigin`, `source_at_boundary`, `rejected_suffix`, `classify_application_prefix` | Original selected physical count produces semantic arity failure after arguments; authentic named provenance remains a static input. |
| `PreparedStagedIndirectArgumentFaultBounds` | `first_gate`, `preserves_argument_fault`, `reflects_argument_fault_prefix` | Strict callee and concrete ordered-argument fold produce the actual argument-fault post; prefix reflection retains that same fault. |
| `PreparedStagedIndirectApplicationSuffix` | `application_to_payload`, `application_from_payload`, `accepted_gate`, `reflects_suffix`, `preserves_suffix` | Literal payload normalization and accepted second gate retain the argument store and strict native application child. |
| `PreparedSelectedTerminalLambdaCompilerReceipts` | `of_receipt` | Retained NativeLambda recipe/body compilation constructs an accepted terminal compiler receipt before execution. |
| `PreparedStagedTerminalSourceBodyInversion` | `child_of_body`, `result_of_control` | Actual whole supported Source body yields the used child, strict Source grade and exact BodyResult/control. |
| `PreparedStagedBodyRestorationAdmission` | `restore_post` | Saved physical caller restoration transports the actual body admission for value, semantic fault or stage fault. |
| `PreparedStagedTerminalBodyTraceBounds` | `preserves_body` | Whole supported Source body supplies its child internally; strict expression preservation proves the emitted code.rename and full post. |
| `PreparedStagedClosureInvocationPostBounds` | `SourceBodyAt`, `ResultAt`, `invocation_preserves`, `NativeBodyAt`, `invocation_reflects`, `application_preserves`, `application_reflects` | Actual parameter/body prefixes and strict body hypotheses restore full caller admission; Source/Core grades remain independent. |
| `PreparedStagedIndirectFaultDispatch` | `FaultResult`, `reflects_fault_or_application` | Actual native parent returns callee/first-gate/argument fault meaning or preserves the right application prefix. |
| `PreparedStagedBuiltinArgumentRows` | `builtin_member`, `Rows`, `at_arguments`, `at_callee_post` | Authentic BuiltinAt/equal count plus original callee typing recover literal signatures and ordered scalar values at the argument post. |

The fault relation retains the actual receiving table and same result model/map/world. Stage rejection stays at the callee post; argument failure and second-gate arity stay at the reached argument post. PostAdmission carries deep Source admission for successful values and stable rows for faults. Complete body hypotheses and Scope/source provenance are not manufactured by decoding a diagnostic token.

Retained-callee argument prefixes (258), builtin whole-parent reflection/preservation (134/154), terminal body typing (96), metadata-body bounds (131), parameter-admission and concrete body-join drafts, and retained-callee fault/builtin dispatch drafts (127/216) are outside this twelve-Source checkpoint.

The numeric staged expression/argument/application/body induction, authentic static factories for complete compiler alternatives, general call/body dispatch and remaining recursive Source grammar remain unfinished. Specialization, evidence and comptime composition, general failure/export-error correspondence and the final public all-pass theorem are open. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure semantic completion.

## Staged parent and terminal lambda interfaces (2026-10-11; normally verified at `6844f7b0`)

`staged-parent-and-terminal-lambda-producers` is committed and normally verified at `6844f7b0`. The twelve proof Sources contribute 74 complete module-owned declarations and 26 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19540 to 19614: 74 additions, no overlaps and no removals. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews.

The registered build passes 5798 jobs. The independent selected dependency BEFORE contains 2218 modules; the compiled native environment contains 2230. The complete normal module snapshot changes from 5719 to 5731 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint will use those original sixteen receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `cc2cfe`; code commit `6844f7b0f788069d858f42a29343c7c5900829ba` closed at `5cea3d`. The saved `staged-parent-and-terminal-lambda-producers-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `bf9f5a5635e9876005265366485f4f31bad0d297b3478785aa453b778561c456`. The selected BEFORE environment of 2218 modules is separate from the complete pre-install snapshot of 5719 module rows.

The strict child hypotheses are induction assumptions for the actual executed child: its Source trace grade is smaller for preservation, or its native evaluation grade is smaller for reflection. The shared numeric induction must still construct these hypotheses; the static compiler receipts do not contain a completed execution law.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. All 26 selected interfaces match the complete native and normal API logs. The 74 complete module-owned declarations also have literal private/normal TYPE/AXIOMS agreement.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `PreparedStagedIndirectRetainedCalleeArgumentPrefix` | `ApplicationPrefix`, `ApplicationPrefix.to_original`, `reflects_arguments` | Retains callee PostAdmission and raw typing through the actual argument fold; projects to the original application prefix. |
| `PreparedStagedBuiltinParentBounds` | `reflects_suffix` | Accepted builtin suffix constructs the original whole Source parent and full reached caller post. |
| `PreparedStagedBuiltinParentPreservation` | `preserves_parent` | The actual primitive and original binds construct the whole native builtin parent and caller post. |
| `PreparedStagedTerminalBodyTyping` | `child_typed`, `at_parameters` | Original body typing selects the genuine terminal child and declared result at parameter entry. |
| `PreparedStagedTerminalMetadataBodyBounds` | `source_head`, `preserves_body`, `reflects_body` | Actual metadata identifies the Source head; terminal body preservation/reflection retain the real used child and full post. |
| `PreparedLambdaParameterAdmission` | `install_rows`, `after_parameters`, `at_parameters` | Real parameter allocation and row histories construct entry admission without a supplied support law. |
| `PreparedStagedIndirectRetainedCalleeFaultDispatch` | `reflects_fault_or_application` | Whole-parent reflection returns the exact fault post or application prefix with retained callee typing. |
| `PreparedStagedIndirectBuiltinApplicationDispatch` | `UserApplicationPrefix`, `UserApplicationPrefix.to_retained`, `ParentResult`, `reflects_builtin_or_user` | Reflection constructs the accepted builtin result or arity fault, preserving the real user application prefix. |
| `PreparedStagedIndirectValuesPrefix` | `ValuesPrefix`, `preserves_values` | Strict callee P and the concrete ordered fold retain represented values at the actual argument post. |
| `PreparedStagedSuccessfulArgumentTyping` | `values_at`, `closure_at` | Successful Source arguments produce raw ordered typing, heap extension and the actual closure frame. |
| `PreparedStagedTerminalLambdaBodyBounds` | `source_body_at`, `native_body_at` | Code/registry derive child scope and parameter entry facts internally before strict terminal body preservation/reflection. |
| `PreparedStagedTerminalLambdaApplicationBounds` | `application_preserves`, `application_reflects` | Constructs the terminal body port at actual entry, then uses original closure application and caller restore once. |

The dependent caller post, callee typing, ordered argument heap and restored pool refer to the same actual execution. Builtin application has no function-body child. Terminal closure application still uses a strict expression hypothesis for its genuine compiled child. Physical gates retain their actual codebook count and rejected tag; Source and native grades are independent.

The shared numeric induction for expressions and function bodies, general user and named application dispatch, full statement grammar and authentic compiler occurrence coverage remain open. Specialization, evidence and comptime composition, general failures/export errors and the final public all-pass theorem are unfinished. Finite proofs for literals and grouping, the separate closure argument-typing producer and the whole builtin preservation dispatcher are outside this checkpoint. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.

## Staged call parent dispatch interfaces (2026-10-11; normally verified at `910e3e1d`)

`staged-call-parent-dispatch-bounds` is committed and normally verified at `910e3e1d`. Its seven proof Sources have 117 complete module-owned declarations and 19 selected interfaces. Every native and normal strict Source log is empty. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete 19-interface API logs are byte-identical. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews; the tooling has independent Root and Entry reviews.

The cumulative census is 19730 from 19614: 116 additions, one prior overlap and no removals. The overlapping generated helper, `ContextualCellOrigins.functions.congr_simp`, is literally unchanged. Build 5805 passes. The selected dependency BEFORE contains 2228 modules and the compiled native environment 2235; the complete normal snapshot changes from 5731 to 5738 rows. Seven new Source/olean/ilean triples are installed. Only the existing `CoreLowering` object pair changes, within the nine-module dependency cone and nine actual rebuilds. All 4985 protected artifacts remain unchanged.

The eleven original normal validation receipts are closed with exit code zero. Normal validation closed at `ce446f`; code commit `910e3e1d9f18c1fde867b7d56ef3321b5a0dd943` closed at `83f21b`. The saved `staged-call-parent-dispatch-bounds-checks.json` has SHA-256 `9360372c1f3e5abb9ab873e023f542f20bcfd58b301b46851ee5d9e7a108df4c`. Metadata finalization reuses the original eleven closed validation receipts without repeating their kernel checks.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. These are exactly the 19 selected interfaces of this seven-Source unit.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedClosureArgumentRows` | `source_arity`, `at_arguments` | Derives original physical Source arity and contextual closure argument/binder rows at the actual argument post. |
| `PreparedStagedTerminalClosureParentBounds` | `Terminal`, `TerminalFor`, `ReflectsBelowFor`, `application_reflects`, `reflects_suffix` | Reflects the selected terminal closure application and suffix, retaining the actual body result and full caller post. |
| `PreparedStagedTerminalClosureUserDispatch` | `GlobalApplicationPrefix`, `reflects_closure_or_global` | Reflects a closure, including its receiving arity fault, or retains the literal global application prefix. |
| `PreparedStagedTerminalClosureParentPreservation` | `PreservesBelowFor`, `application_preserves`, `preserves_parent` | Preserves the actual Source-selected terminal body/application and restores the saved caller once. |
| `PreparedStagedIndirectBuiltinPreservationDispatch` | `ParentAt`, `preserves_builtin_or_user` | Constructs the builtin parent or retains the actual user prefix, with physical mismatch handled at the real argument state. |
| `PreparedStagedIndirectSourcePrefixDispatch` | `NativeResultAt`, `ApplicationAt`, `preserves_fault_or_application` | Constructs real Source prefix failure parents or the successful application packet from actual strict children. |
| `PreparedStagedTerminalClosureUserPreservationDispatch` | `GlobalAppliedPrefix`, `preserves_closure_or_global` | Preserves the closure branch or retains the literal global applied prefix, including its Source parent grade and actual argument post. |

The strict child hypotheses describe the actual executed child: preservation uses a smaller Source trace grade, and reflection uses a smaller native evaluation grade. The shared numeric induction must still construct these hypotheses. Source and native grades are independent, and static compiler receipts retain authority rather than a completed execution law.

Completed parent results retain the full caller post for the same callee/argument execution. A retained global application prefix keeps reached Admission before its whole application is composed. Actual physical count and receiving row identify arity failures; tokens alone do not identify Source scope. Stage and semantic result interpretations remain separate.

The whole indirect parent reflection and preservation dispatch proofs, and terminal named invocation reflection, have saved author passes and genuine peer reviews in W. They are outside the seven registration targets, and their normal integration remains open. The whole parent proofs retain the actual named/global application prefix for further composition. Named invocation constructs the real parameter receipt, reflects the supported terminal body at its selected scope, and restores the caller; joining original raw global arguments, named physical arity, the outer indirect parent and the preservation direction remain separate obligations.

The shared numeric expression/function-body induction, general named application, full statement grammar and authentic compiler occurrence coverage remain open. Specialization, evidence and comptime composition, general failures/export errors and the final public theorem across all passes are unfinished. Finite literal, group and product-tree proofs remain a separate reviewed W unit. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.


## Finite staged expression and named call interfaces (2026-10-11; normally verified in two code commits)

`staged-finite-expressions-and-named-call-parents` is committed and normally verified in two logical code groups. The finite expression commit `5a5bdeffec4008cb4d6e972224b90b8a2df048db` contains four proof Sources, 102 module-owned declarations and 32 selected interfaces. The whole-call and named-call commit `ef75b2c3b86a2e2bc140ea274ae9ff55d86c99d2` contains seven Sources, 89 declarations and 18 interfaces. Together they add eleven Sources with 191 complete owned declarations and 50 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native strict logs and all eleven normal strict logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 191 declarations. The complete 50-interface API logs are byte-identical: 112327 bytes, SHA-256 `df758c72f09c97d7e7f17fee86fd94d67595c6adf117e6103b2bd158aa7f4058`. The independent selected BEFORE contains 2240 modules and the compiled native environment 2251.

The cumulative census grows from 19730 to 19921: 191 additions, no prior overlaps and no removals. Build 5816 passes. The complete normal snapshot grows from 5738 to 5749 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The original package tooling has independent Root and Entry reviews. The separate snapshot-copy successor was authored by Root and independently reviewed by Entry and Formal. Both code commits closed with exit code zero at actual receipt `0cb4aa`; normal validation records fifteen original CLOSED0 receipts. Its complete checks have SHA-256 `d48582c7b3291b9093a30b010b37f4805312f1b812e93c272b08ec96ed21d8cc`. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. The table lists exactly the 50 selected interfaces of this normally verified eleven-Source unit.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedGroupBounds` | `Group`, `Group.actual`, `of_literal_sites`, `group_preserves`, `group_reflects` | Retains the actual group child; Source preservation is strict, while native reflection recurses structurally at the same grade. |
| `PreparedStagedLiteralGroupBounds` | `Tree`, `Tree.literal`, `Tree.group`, `Tree.literal_sites`, `Tree.of_functions_literal`, `literal_preserves`, `literal_reflects`, `preserves`, `reflects` | Constructs the finite literal/group fold from actual literal receipts and grouped children. |
| `PreparedStagedPairBounds` | `Pair`, `Pair.actual`, `ProductValues`, `pair_preserves`, `pair_reflects` | Constructs ordered pair meaning at the actual intermediate state using strict evaluated bind children. |
| `PreparedStagedProductTreeBounds` | `Syntax`, `Syntax.literal`, `Syntax.group`, `Syntax.pair`, `Syntax.to_canonical`, `Tree`, `Tree.literal`, `Tree.group`, `Tree.pair`, `Tree.of_literal_sites`, `Tree.of_functions`, `preserves`, `reflects` | Extracts the supported finite syntax from actual LiteralSites and constructs the literal/group/pair fold. |
| `PreparedStagedIndirectTerminalReflectionDispatch` | `reflects_parent_or_global` | Reflects completed failure, builtin and terminal closure parents, or retains the literal global prefix. |
| `PreparedStagedIndirectTerminalPreservationDispatch` | `GlobalAt`, `preserves_parent_or_global` | Preserves completed failure, builtin and terminal closure parents, or retains the literal global applied prefix. |
| `PreparedStagedNamedPayloadReceipts` | `global_representation`, `named_payload` | Retains positive named payload authority, original source identity and dictionary. |
| `PreparedStagedNamedSourceScopeReceipts` | `global_view`, `record`, `selected`, `applies`, `arity_failure` | Derives the original Header record, selected row, staged Source scope and Source arity failure. |
| `PreparedStagedTerminalNamedBodyBounds` | `compiler_receipt`, `preserves_body`, `reflects_body` | Constructs the actual terminal compiler receipt and body preservation/reflection from strict child hypotheses. |
| `PreparedStagedNamedEntryBounds` | `Prefix`, `native_prefix` | Recovers the real named parameter/body prefix at the same reached pool and dictionary. |
| `PreparedStagedTerminalNamedInvocationBounds` | `parameter_receipt`, `ResultAt`, `reflects_invocation` | Constructs parameter authority and reflects the supported named invocation with exact saved-caller restoration. |

The finite expression fold constructs preservation and reflection for literals, transparent grouping and ordered two-element products from the actual compiler Tree and LiteralSites receipts. It retains original Source typing, the represented result, both staged and semantic failure interpretations, and the reached heap, store and caller post. Preservation descends on the independent Source trace grade. Reflection descends structurally through a transparent group at the same native evaluation grade; only children of actual evaluated pair binds require a strictly smaller native grade. The finite fold constructs its child meanings internally.

The whole indirect parent dispatch composes real callee, first-gate, ordered argument and physical-arity failure branches with accepted builtin and supported terminal closure application. Completed cases keep the exact restored caller PostAdmission at the returned pool. The named/global alternative retains the literal application prefix and reached Admission for an independent named consumer. First-gate stage failure and after-arguments semantic arity failure retain their distinct Source rules, tags and scopes.

The five named-call proofs retain the positive payload, original Header, selected record, Source scope, dictionary and actual parameter/body state. Supported terminal body preservation and reflection use the genuine compiled child with a separate strict child hypothesis. Invocation reflection constructs the parameter receipt, reflects the supported body once, and restores the saved caller in the actual returned pool. Its complete caller post refers to that same execution.

The shared numeric expression/function-body induction still has to provide strict hypotheses for the actual executed children; Source and native grades remain independent. Joining the original raw global argument list to the Header, connecting the independent named physical-arity receipt, composing the outer indirect parent and proving named invocation preservation remain open. General bodies, the full expression/statement grammar and authentic compiler occurrence and receiving-diagnostic coverage are unfinished. Specialization, evidence and comptime composition, general failures/export errors and the final public theorem across all passes remain open.

The separate real-cell read proof and finite compiler-factory proof remain reviewed work in the private proof area, outside these eleven registration targets. The first objective remains 100%; the second stays about 70%, and the equally weighted overall estimate stays about 85%. These estimates describe completed work, not declaration counts or remaining time.

## Finite read and named body interfaces (2026-10-11; normally verified in two code commits)

`staged-finite-reads-and-named-body-composition` is committed and normally verified in two logical code groups. The finite read/body commit `6d4fcbd855b387845dba4ca511ea66d6dde0c020` contains six proof Sources, 64 module-owned declarations and fourteen selected interfaces. The closure/named commit `ed30cd3be8a2f9b11e5ff21387a19f8fcfdbde99` contains five Sources, 56 declarations and twenty-two interfaces. Together they add eleven Sources with 120 complete owned declarations and 36 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native and eleven normal strict Source logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 120 declarations. The complete 36-interface API logs are byte-identical: 108225 bytes, SHA-256 `79a0c159998685d6e97f3c1c1302f389d6ffcba81df469023faf1e62582b2e2c`. The independent selected BEFORE contains 2274 modules and the compiled native environment 2285.

The cumulative census grows from 19921 to 20041: 120 additions, no prior overlaps and no removals. Build 5827 passes. The complete normal snapshot grows from 5749 to 5760 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The selected tooling has independent Root and Entry reviews; the inherited snapshot-copy change retains its genuine Entry and Formal reviews. Both code commits and all fifteen original normal validation receipts are closed with exit code zero. The complete checks have SHA-256 `ce9c5751d088be73b668e9f76a8f64ce7f2c126d873dc8ae03102f7ccf498ed6`. Metadata finalization reuses the original fifteen closed normal validation receipts without repeating their kernel checks.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. This table lists the exact 36 selected interfaces, not a native declaration census.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedReadBounds` | `preserves`, `reflects` | Proves actual real-cell read preservation/reflection, including authentic uninitialized reads and lazy mapping writes. |
| `PreparedStagedNamedReadDiagnostics` | `decoded_read`, `uninitialized`, `staged_uninitialized` | Produces the certified read diagnostic and uninitialized interpretation in the recursively staged semantics from the same issuer and receiver. |
| `PreparedStagedContextualProductReceipts` | `of_contextual` | Extracts an actual contextual Tree.WithLiterals using the genuine literal producer. |
| `PreparedStagedNamedTerminalChildReceipts` | `source_child`, `finite_child` | Derives the original typed terminal child and its finite compiler certificate from the Header. |
| `PreparedStagedReadProductTreeBounds` | `Certificate`, `of_functions`, `preserves`, `reflects` | Constructs the accepted read/literal/group/pair fold with internally discharged child meaning. |
| `PreparedStagedFiniteNamedBodyBounds` | `preserves_body`, `reflects_body` | Constructs finite named body preservation/reflection without an external child expression law. |
| `PreparedTerminalClosureFactories` | `of_actual_body_exact`, `of_actual_body`, `TerminalShapeFor`, `ReadPolicyFor`, `HasBodyCertificate`, `HasBodyChild`, `terminal_for_exact`, `terminal_for`, `at_prepared_registry`, `at_prepared_registry_exact` | Retains authentic terminal shape, read policy and the exact accepted body child at the selected scope. |
| `PreparedTerminalClosureFactoryBounds` | `ReflectsActualBodyBelow`, `PreservesActualBodyBelow`, `application_reflects`, `application_preserves` | Consumes actual selected-child semantic hypotheses to construct complete closure application results. |
| `PreparedStagedTerminalNamedInvocationPreservation` | `body_prefix`, `preserves_invocation` | Inverts the actual Source body prefix and constructs named invocation preservation with saved-caller restoration. |
| `PreparedStagedNamedArgumentRows` | `caller_supports`, `accepted_rows`, `at_successful_arguments` | Derives caller support and typed ordered rows at the original selected node/metadata and actual argument post. |
| `PreparedStagedTerminalNamedApplicationBounds` | `carrier`, `application_preserves`, `application_reflects` | Constructs the literal named carrier and both application directions using the generic invocation producers. |

Named read diagnostics come from the actual prepared Header, diagnostic receipt and receiving issuer. The uninitialized-read interpretation is indexed by the certified read occurrence, including its binder, span and reason token; decoding does not manufacture a Source fault. The Header and accepted terminal receipt supply the real child typing and finite compiler tree. The finite named body producer calls this fold directly in both directions, removing its external child-expression meaning and arbitrary certificate callback. It keeps the actual parameter entry and selected body scope, and carries the returned heap, store, map, world, relation and PostAdmission.

The closure factories retain an exact accepted body child and its authentic static support. Their application consumers still require meaning for the actual selected child. Named invocation preservation constructs the real parameter allocation, uses the selected terminal body, and restores the caller at the returned pool. Named argument rows retain the original selected node and metadata, the Source argument types and the independent physical-count receipt. The literal named carrier supports both application directions at those exact endpoints. These generic invocation/application proofs still consume strict child hypotheses; they do not yet instantiate the new finite body producer.

The next finite named invocation/application proof will retain the substantive parameter-entry and restoration proofs and replace their body call with the finite named body producer. It must preserve the actual Source-selected child in preservation and the authenticated Header/descriptor scope in reflection, with real ledger, runtime, coverage, ordinary-metadata and finite-syntax premises. The shared numeric expression/function-body family, outer named/global joins, full compiler and Source grammar, general bodies and complete receiving-diagnostic coverage remain open. Specialization, evidence and comptime composition, general failure/export-error correspondence and the public theorem across all passes are unfinished. Estimates remain 100% for runtime unification, about 70% for the second objective and about 85% overall.

## Finite call body and global join interfaces (2026-10-11; normal verification complete)

The selected `staged-finite-call-bodies-and-global-joins` work contains nine proof Sources and 37 selected interfaces. The three generic parent/global joins expose seven interfaces; the two static closure-child producers expose twelve; the four finite call/body proofs expose eighteen. Each selected Source has an isolated author pass and two genuine nonauthor Source reviews. Normal verification passes for all nine Sources, 177 module-owned declarations and 37 selected interfaces. The generic joins contribute 68 declarations, the static closure-child producers 27, and the finite call/body proofs 82. The three code commits are `c37620a6`, `b568df64` and `ef72f57e`.

| Validation item | Completed result |
| --- | --- |
| Selected proof scope | Nine Sources / 37 interfaces, with isolated author passes and two genuine nonauthor Source reviews each. |
| Native and normal strict checks; full literal TYPE/AXIOMS/API audits | All nine strict Source logs are empty. All 177 complete module-owned TYPE/AXIOMS blocks agree literally; the 37-interface API logs are byte-identical (195517 bytes, SHA-256 `a601df8af4153992798319bc93f9f0d4870323bf5cebf5f4a30114070d61d9ec`). |
| Independent selected BEFORE and compiled environment | 2312 modules before the selection; 2321 in the actual compiled environment. |
| Registered build and normal snapshot | Build 5836 passes; the full normal snapshot grows from 5760 to 5769 rows. All thirteen original normal validation receipts close with exit code zero. |
| Cumulative additions, overlaps, removals and current census | 20041 → 20218: 177 additions, no prior overlap and no removals. |
| Existing object changes, dependency cone, rebuilds and protected artifacts | Only the existing `CoreLowering` object changes. The reverse dependency cone and actual rebuild each contain eleven modules; all 4985 protected artifacts remain unchanged. |
| Code commits | Generic named joins: `c37620a6` (three Sources / seven interfaces / 68 declarations); static closure children: `b568df64` (two / twelve / 27); finite call bodies: `ef72f57e` (four / eighteen / 82). |

Metadata finalization reuses the original thirteen closed validation receipts without repeating their kernel checks.

Preservation constructs native execution from an actual Source derivation. Reflection reconstructs a Source derivation from native completion with an independent Source grade. Both retain the actual reached heap, store, map, world, relation and returned pool. Completed application and parent results retain full caller PostAdmission, including the original tag and scope of nested stage failures.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. The table lists the exact 37 selected interfaces; it is not a native declaration census.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedTerminalNamedParentBounds` | `preserves_parent`, `reflects_suffix` | Constructs the generic named parent or reflects its accepted suffix at the authentic ordered argument post; strict child hypotheses remain explicit. |
| `PreparedStagedTerminalNamedGlobalDispatch` | `Terminal`, `reflects_global`, `preserves_global` | Runs the generic named parent at the selected equal count, or retains the actual Source arity failure and receiving diagnostic. |
| `PreparedStagedIndirectTerminalCallBounds` | `reflects_parent`, `preserves_parent` | Connects the actual whole indirect completion or Source trace to generic closure, builtin and named-global branches; child hypotheses remain explicit. |
| `PreparedTerminalClosureCanonicalChildFactories` | `canonical_child`, `HasCanonicalBodyChild`, `canonical_for`, `terminal_for_both`, `at_prepared_registry_both` | Retains the exact original-Source child and corresponding compiler child from the same accepted BodyWith without metadata typing assumptions. |
| `PreparedTerminalClosureUsedChildBounds` | `Point`, `narrow`, `narrowFor`, `ReflectsUsedChildBelow`, `PreservesUsedChildBelow`, `application_reflects`, `application_preserves` | Narrows the certificate to the actual used child and supplies both application directions from strict selected-child hypotheses. |
| `PreparedStagedFiniteNamedInvocationBounds` | `carrier`, `preserves_invocation`, `reflects_invocation`, `application_preserves`, `application_reflects` | Constructs finite named invocation/application directly from the finite body at the real parameter entry and restores the saved caller. |
| `PreparedStagedFiniteNamedParentBounds` | `preserves_parent`, `reflects_suffix` | Constructs the finite named parent and reflects its accepted suffix from authentic Source/native argument rows and the finite application. |
| `PreparedStagedFiniteNamedGlobalDispatch` | `Terminal`, `reflects_global`, `preserves_global` | Recovers the actual positive Header and constructs finite global dispatch, including its receiving semantic arity fault. |
| `PreparedStagedFiniteClosureBodyBounds` | `Family`, `FiniteBody`, `canonical_child`, `raw_child`, `child_preserves`, `child_reflects`, `application_preserves`, `application_reflects` | Extracts the canonical typed child from a fixed finite BodyWith and constructs finite closure child/application meaning internally. |

Finite named invocation and application now call the finite named body producer directly at the actual parameter entry. Preservation retains every actual Source-selected body scope; reflection retains the authenticated Header/descriptor-selected scope. The proof runs the original parameter installation and body prefix once, uses the finite read/literal/group/pair body once, and restores the saved caller at the actual returned pool. It no longer takes an external child-expression meaning hypothesis or arbitrary certificate callback.

The finite named parent derives typed Source arguments and represented native parameters from the authentic ordered rows and independent physical-count receipt. Its accepted suffix uses that same finite application once. The finite global dispatcher recovers the real Header, dictionary, capture and Source frame from the positive named payload. It either runs the finite parent at the selected equal count or proves the actual Source semantic arity failure with the exact receiving diagnostic at the reached argument post. First-gate `Failure.stage` and second-gate semantic arity failure remain separate.

The finite closure body proof retains a fixed accepted BodyWith with both compiler-view and original-Source trees. Authentic frame typing and the selected Source scope provide the raw child type; the exact original child certificate feeds the finite evaluator. Its application proofs construct read/literal/group/pair child meaning internally and retain the restored caller post. Genuine finite-family compiler transport, terminal/read policy, certified read-fault interpretation, registry extension and runtime premises remain explicit.

The generic named parent/global joins and whole terminal indirect-call proof connect actual callee and ordered-argument prefixes to the original payload application and native suffix. They keep transient effects and the complete restored caller post. These generic ports still require authentic terminal factories and strict child induction hypotheses: those hypotheses assert child execution only below the enclosing numeric budget.

The static closure-child producers retain the exact accepted child in both original and compiler Sources, then restrict a requested child certificate to that literal occurrence. They do not infer raw typing from a metadata view or turn an arbitrary static certificate family into finite semantics.

The shared numeric expression/function-body family and general callee/argument recursion remain open. The finite named and closure application proofs do not yet instantiate every generic whole-call child hypothesis. Constructing the fixed finite closure support from every actual compiler path still needs genuine reachable certificate transport. Wider expression/statement grammar, general bodies, complete receiving-diagnostic coverage, specialization/evidence/comptime composition and the final public theorem across all passes are unfinished. Runtime unification remains 100%; the second objective remains about 70%, with an equally weighted overall estimate of about 85%. These are estimates of completed work, not declaration counts or remaining time.

## Finite closure dispatch and arbitrary tuple proof interfaces (2026-10-11)

`staged-finite-call-dispatch-and-tuple-folds` is normally verified in three code commits: `fb42f8c2` adds the finite closure parent, static transport and terminal packet (three modules, thirteen interfaces); `280557de` adds the arbitrary tuple fold and compiler issuer (two modules, six interfaces); `a48286e4` connects the whole-call and user dispatch branches (six modules, eight interfaces). The eleven modules expose 27 selected interfaces and 156 owned declarations. Each Source has two genuine nonauthor Source reviews.

All eleven fresh private and normal strict Source checks closed with empty output. Complete TYPE/AXIOMS and API audits passed, and the private and normal API logs are byte-identical (142486 bytes). The native import closure grew from 2319 to 2330 modules. The registered build completed 5847 jobs; normal Source/BOTH rows grew from 5769 to 5780. The only changed existing object was `CoreLowering`; all eleven new modules have regular objects, all thirteen modules in the reverse dependency cone were rebuilt, and 4985 protected artifacts stayed unchanged. The cumulative census grew from 20218 to 20374, with 156 additions, no overlap and no removals. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

| Module in `Solcore.SourceSemantics.CoreLowering` | Selected interfaces | Proof boundary |
| --- | --- | --- |
| `CallableIndexedOwnedPreparedStagedFiniteNamedIndirectCallBounds` | `reflects_parent`, `preserves_parent` | Connects the finite named branch to whole-call preservation/reflection; genuine caller and closure child hypotheses remain explicit. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds` | `FiniteTerminal`, `FiniteFor`, `application_preserves`, `application_reflects`, `reflects_suffix`, `preserves_parent` | Constructs finite closure application and joins its literal suffix to the full restored caller post. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport` | `finite_syntax`, `literal_sites`, `certificate`, `syntax_original`, `certificate_original`, `of_tree` | Transports finite syntax and literal/read certificates at authentic reachable unedited occurrences, then constructs the same finite body. |
| `CallableIndexedOwnedPreparedStagedTupleTreeBounds` | `Certificate`, `preserves`, `reflects` | Constructs ordered arbitrary-tuple preservation/reflection internally, including same-grade singleton reflection. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureTerminalPackets` | `of_tree` | Constructs the exact finite terminal packet from the accepted body tree and selected Source scope. |
| `CallableIndexedOwnedPreparedStagedTupleCompilerReceipts` | `Syntax`, `PolicyFor`, `of_functions` | Extracts a positive tuple certificate from genuine accepted compiler actions and raw child typing. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureUserDispatch` | `reflects_closure_or_global` | Reflects a closure, including its receiving semantic arity fault, or retains the actual global application prefix. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureUserPreservationDispatch` | `preserves_closure_or_global` | Preserves the actual closure application or retains the literal global Source suffix at the reached argument state. |
| `CallableIndexedOwnedPreparedStagedIndirectFiniteClosureReflectionDispatch` | `reflects_parent_or_global` | Reflects failure, builtin and finite closure parent branches; retains global dispatch and strict caller child hypotheses. |
| `CallableIndexedOwnedPreparedStagedIndirectFiniteClosurePreservationDispatch` | `preserves_parent_or_global` | Preserves failure, builtin and finite closure parent branches; retains global dispatch and strict caller child hypotheses. |
| `CallableIndexedOwnedPreparedStagedFiniteIndirectCallBounds` | `reflects_parent`, `preserves_parent` | Combines finite named and closure application; strict caller callee/argument hypotheses remain explicit. |

The arbitrary tuple fold supports nested finite tuples of any arity, including repeated child identifiers, in their original order. It internally constructs the read/literal/group/pair leaves and evaluates each next child at the actual intermediate caller state. Preservation uses the actual Source grades, including the legacy two-element pair rules. Reflection uses structural child descent when a singleton's native packer erases the tuple wrapper and keeps the same grade. The compiler issuer extracts this certificate from the actual accepted action and ordered child vector, with original raw typing and static policy inputs; no leaf execution law is supplied.

The next substantive cut is a recursive static caller certificate whose read/literal/group/tuple/call fold constructs those child hypotheses internally. The current tuple issuer admits groups only inside its older leaf grammar, not groups around a new arbitrary tuple or call. Finite closure transport and terminal bodies still use the narrower read/literal/group/binary-pair grammar. Authentic compiler policy, raw typing, selected Header or Association, registry/receiving diagnostics, runtime ledger and coverage remain inputs. Shared numeric expression/application/body induction, general recursive bodies, broader expression and statement grammar, and the final public all-pass theorem remain unfinished. Runtime unification stays 100%; the second objective stays about 70%, and the equally weighted overall estimate stays about 85%.

## Recursive caller certificates and compiler composition (2026-10-11)

The selected `staged-recursive-callers-and-static-receipts` unit is normally verified in `e8607d82` and `abe72325`: six proof Sources, 198 owned declarations and 37 selected interfaces. Each Source has an isolated strict author pass and two independent nonauthor Source reviews.

All six native and normal strict Source checks have empty logs. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete API logs are byte-identical (89589 bytes, SHA-256 `05cacd2519262ad3ad8a8762e6110fde41596f12f27aa90b3638ffdfdfe4eafb`). The selected native environment grows from 2324 to 2330 modules. Build 5853 passes; the normal Source/BOTH snapshot grows from 5780 to 5786 rows. The cumulative census grows from 20374 to 20572: 198 additions, no overlap and no removals. All 8 modules in the affected dependency cone are rebuilt and all 4985 protected artifacts remain unchanged.

Metadata finalization reuses the original ten closed validation receipts without repeating their kernel checks.

| Module suffix under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStaged` | Selected interfaces | Role |
| --- | --- | --- |
| `RecursiveCallerSourceReceipts` | 4 | Derives original call-node alignment, raw child typing and actual callable preparation. |
| `TupleHeadBounds` | 2 | Assembles ordered tuple preservation/reflection from the structural child hypotheses at the actual intermediate states. |
| `FiniteCallHeadBounds` | 4 | Retains the authentic call port and joins one finite whole-call result to expression preservation/reflection. |
| `RecursiveCallerCertificates` | 21 | Defines supported syntax, policy, recursive certificates and reachable call receipts, then issues the root from an accepted compiler action. |
| `RecursiveCallerBounds` | 4 | Builds caller child preservation/reflection internally by structural induction. |
| `RecursiveCallerCompilerBounds` | 2 | Connects the actual accepted compiler action and generated root to the preservation/reflection fold. |

The Source receipt APIs are `original_read_metadata`, `source_parent`, `original_child_types` and `prepared`. Tuple heads expose `tuple_preserves` and `tuple_reflects`; call heads expose `Point`, `Port`, `preserves` and `reflects`.

The certificate module exposes `Syntax`, `PolicyFor`, `Certificate`, `Calls` and `of_functions`, together with their sixteen selected constructors or fields. The fold exposes `Point`, `CallsReady`, `preserves` and `reflects`. The compiler wrapper exposes `preserves_compiled` and `reflects_compiled`; both construct the root certificate from the actual accepted compiler action.

The compiler issuer starts from the actual accepted lowering action and original Source typing. It recovers the original indirect-call node, raw callee type and ordered argument types before building the child certificate. The certificate retains groups, tuples and indirect calls recursively, including groups around new tuple or call nodes. Argument entries keep their original order and repeated identifiers.

Structural induction on that certificate proves both preservation and reflection at every actual reached state. Child execution hypotheses are constructed internally. Group reflection and erased singleton tuple packing can use the same native grade; induction follows the child certificate rather than assuming a smaller execution grade. An indirect call uses the actual callee entry and ordered argument tree, then the existing finite whole-call proof once. Results retain the reached heap, store, map and world, exact staged fault scope, returned pool, caller relation and PostAdmission. Source and native grades remain independent.

The compiler-facing wrapper constructs its root certificate internally. Its `CallsReady` premise refers only to call receipts reachable from that exact generated root. Actual preparation, Source view, sidecar, guard frame, selected Header or Association, receiver, registry extension, diagnostic interpretation, ledger and coverage remain static or runtime premises. Called bodies still use the existing finite read/literal/group/binary-pair family. No public child execution or arbitrary body meaning callback is supplied.

General recursive called bodies, the shared numeric expression/application/body family, other expression and statement forms, and specialization/evidence/comptime composition remain unfinished. The final public theorem across all compiler passes is incomplete. Estimates remain 100% for runtime unification, about 70% for meaning preservation and about 85% overall.

The static Source/compiler receipt group (`e8607d82`) contains two Sources, 125 declarations and 25 selected interfaces. The semantic head/fold/compiler composition group (`abe72325`) contains four Sources, 73 declarations and twelve interfaces. Interface and declaration counts do not measure proof completion.

## Selected caller and recursive terminal body interfaces (2026-10-11; normal verification complete)

The selected `staged-selected-callers-and-recursive-body-bounds` unit is normally verified in `7db7dd2c`, `dda78f9c`, `31549a17`: sixteen proof Sources, 376 owned declarations and 53 selected interfaces. Each Source has an isolated strict author pass and two independent nonauthor Source reviews, excluding contributing repair authors.

All sixteen native and normal strict Source checks have empty logs. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete API logs are byte-identical (215570 bytes, SHA-256 `40020d9c5a18129f8d398856d30533f3fbbb94a7d853a9d9bc783fc51eb820e9`). The selected native environment grows from 2317 to 2333 modules. Build 5869 passes; the normal Source/BOTH snapshot grows from 5786 to 5802 rows. The cumulative census grows from 20572 to 20948: 376 additions, no overlap and no removals. All 18 modules in the affected dependency cone are rebuilt and all 4985 protected artifacts remain unchanged.

Metadata finalization reuses the original twenty closed validation receipts without repeating their kernel checks.

| Module suffix under `CallableIndexedOwnedPreparedStaged` | Selected interfaces | Role |
| --- | --- | --- |
| `SelectedTerminalCertificates` | 4 | Narrows the certificate to the actual chosen terminal child. |
| `SelectedTerminalClosureParentBounds` | 1 | Reflects the selected closure application and original parent. |
| `SelectedTerminalClosureParentPreservation` | 1 | Preserves the selected closure application and original parent. |
| `SelectedTerminalNamedGlobalDispatch` | 2 | Connects the actual selected named Header and global application. |
| `SelectedTerminalClosureUserDispatch` | 1 | Reflects user arity and accepted selected closure dispatch. |
| `SelectedTerminalClosureUserPreservationDispatch` | 1 | Preserves user arity and accepted selected closure dispatch. |
| `SelectedIndirectTerminalReflectionDispatch` | 1 | Reflects actual callee and ordered argument prefixes. |
| `SelectedIndirectTerminalPreservationDispatch` | 1 | Preserves actual callee and ordered argument prefixes. |
| `SelectedIndirectTerminalCallBounds` | 2 | Joins selected closure and named whole-call branches. |
| `SelectedGeneralCallHeadBounds` | 4 | Connects one authentic whole-call result to expression meaning. |
| `SelectedRecursiveCallerBounds` | 4 | Builds caller child meaning by structural certificate induction. |
| `SelectedBodyStaticSupport` | 9 | Retains original Root/RootAt and named/Association static authority. |
| `SelectedRecursiveBodyBounds` | 10 | Constructs selected terminal body meaning by numeric induction. |
| `SelectedCallerFromRecursiveBodies` | 2 | Uses the constructed body family in the caller fold. |
| `SelectedBodyCompilerSupport` | 2 | Issues original Source roots from actual accepted compiler actions. |
| `RecursiveBodyViewTransport` | 8 | Transports accepted compiler-view lowering to the original Source. |

The call chain selects one authentic terminal packet for the actual named Header or contextual closure Association. Its certificate is narrowed to that packet's original expression, scope and lowered child. Closure and named dispatch retain the real argument order, physical arity, staged rejection and selected scope. The accepted application keeps its actual returned pool and restores the saved caller, including caller relation and PostAdmission.

The selected caller fold constructs callee and argument preservation/reflection internally from the actual recursive certificate. Group reflection and erased singleton tuple packing may keep the same native grade; their induction follows the child certificate. Ordered argument entries retain repeated identifiers and use the actual intermediate state. Numeric strong induction then constructs meaning for supported selected terminal bodies at strictly smaller semantic budgets. The caller-from-bodies adapter consumes that constructed body family. These endpoints require no external child execution or body meaning callback. Source and native grades remain independent.

Static body support retains the original Source root, raw context, actual Header or Association body context and every genuinely selected child scope. The compiler support issues a certificate from the actual accepted original action and indexes call readiness by that exact proof. The compiler-view transport proves accepted lowering on the original Source from paired policies, reached unedited metadata and the real compiler action. Compiler callbacks, reason functions, original typing/declarations, receiver, registry extension, diagnostics, runtime ledger and coverage remain explicit authority inputs.

This closes the supported selected terminal body/caller recursion. Constructing these authentic roots and authority packets for every compiler path remains unfinished. Wider expression and statement grammar, unrestricted function bodies, complete receiving-diagnostic coverage, specialization/evidence/comptime composition and the final public theorem across all passes are still open. Runtime unification remains 100%; meaning preservation remains about 70%, with an equally weighted overall estimate of about 85%. These estimates describe completed work, not interface counts or remaining time.
