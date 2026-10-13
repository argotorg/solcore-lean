# Core unification: T0 audit of features, semantics, and proof boundaries

Initial audit: 2026-09-30. Last updated: 2026-10-13.

This document preserves the initial audit for the [implementation design](core-runtime-unification.md) and subsequent dated investigations. Sections 1–9 record the state on 2026-09-30; later sections record the state on their respective dates. References to the "current" implementation, "unfinished" work, "next steps," or old API names describe that historical state.

Runtime Core unification was completed in `a3168382`. See the [API migration record](core-runtime-unification-api.md) for the current public entry points. The [implementation record](core-runtime-unification-progress.md) and the latest dated audit section describe the latest commits, validation, and uncommitted work.

Compilation preparation has been separated into `SourceCompilationPlan`. The historical investigations below refer to definition names at the time rather than line numbers.

## Final ordinary catalogs and selected public starts (2026-10-13)

Commits `760f1a28` and `7a8a2de8` connect actual final preparation to the ordinary inventory and selected public start. The review checked these boundaries:

- Exact specialization and unique physical slot come from accepted preparation of the complete cached record. An erased native type or a detached key does not establish row identity.
- Original ordinary provenance is distinguished from selected implementation-method provenance using the well-formed program's declaration identities. Method-discovered ordinary helpers remain eligible.
- The catalog filters finite actual cache positions by independent Source conditions. It does not require unused or staged rows to satisfy ordinary admission, and it does not renumber the physical cache.
- Full raw replacement ranges follow Source declaration/entry admission and actual specialization, including replacements absent from native signatures.
- Public selection follows the actual first matching root, its authentic factory and current session state. `Matches` authenticates the selected function metadata; it does not establish argument, dictionary or heap representation.
- The existing public proof retains all seven Source/forward endpoints and original histories while replacing hand-built Inputs and whole-root coverage.

The existing seven-call retained-closure sequence still has Source meaning and sufficient execution/output-fuel bounds, with scalar results `41 / 7 / 41 / 7` and store lengths `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`. A second regression recovers both Word and Bool identity rows added during method preparation and confirms that they were absent from the initial validation plan.

Validation: all 141 affected modules pass coherent checks. The full build (7,135 jobs), registered tests (14,140 build jobs and the final pass marker), kernel policy and 270 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. Existing work remains unchanged.

This constructs a finite semantic inventory by classical existence; it is not an executable classifier of every cached row. Source well-formedness, independent input admission and ordinary stage flags remain required. The start receipt identifies the selected function; argument values, dictionaries and heap representation still use their existing semantic relations. Automatic body syntax/metadata certification and complete preservation across all compiler passes remain unfinished.

## Output coercions through retained public closures (2026-10-13)

Commits `d82a65a9` and `c48ec7bf` connect a constrained direct call followed by output coercion inside a retained closure. The fixture has four physical cache slots, three ordinary Headers and two public roots. Its selected conversion method has no implementation parameters or method assumptions and returns a conditional Word result from its Bool input.

The audit checked the following boundaries:

- The raw call and conversion path retain the original Source node, complete requirement partition and coercion list. No sanitized Source body is substituted for the original staged scope.
- Actual accepted lowering, selector actions, full retained metadata and dictionaries identify the ordinary callee and conversion method. The method remains a physical cached method with genuine Source typing and parameter entry.
- Sized raw and path traces provide strict recursive child bounds. The existing shared family derives the internal body callbacks; no public execution or dictionary-equality premise is added.
- Native suffix composition uses the actual intermediate heap, pool and physical authority. Failure skips only the remaining work and retains effects already performed. Restoration returns to the original caller frame while retaining the resulting heap, pool and stage-fault identity.
- Public reflection follows all seven original calls. Source-derived forward bounds apply at every original checkpoint, and every sufficiently fueled factory result appends its actual new handle to a reusable history.

The public sequence creates `A` from `make(true)`, creates `B` from `make(false)`, calls `use(A)`, creates `C` from `make(false)`, then calls `use(B)`, `use(A)` and `use(C)`. The four scalar results are `41 / 7 / 41 / 7`; native store lengths are `5 / 8 / 11 / 20 / 23 / 32 / 41 / 50`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficiently fueled factory completion appends its actual exported handle to the reusable history.

Validation: all 2,693 affected modules pass coherent checks. The full build (7,128 jobs), all registered tests (14,126 build jobs and the final pass marker), kernel policy and 235 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The seven public calls produce the stated results, and the existing work remains intact.

The coherent graph includes compatibility repairs for exhaustive consumers of the extended Source relation. Reused validation records were accepted only when their source and transitive dependency identities matched; the affected-module count is not a claim that every module was rebuilt in the final append.

The connected coercion branch covers original direct-call expressions with nonempty output coercions, argument roots supported by the existing uncoerced grammar, and terminal conversion bodies. Its conversion catalog requires implementations without type parameters and with empty method assumptions. It does not yet cover coercions at every expression position or every conversion-body shape. Compilation success still does not supply all required static support or establish completeness of the finite selection/evidence checks. Remaining expression and control forms, generalized local functions and composition across all actual compiler passes remain incomplete.

The largest remaining generality gap is the connection from compiler success to static certification. `CallablePreparedFinalCatalogOrigins.of_preparation` already identifies all final rows as genuine ordinary or method origins. The next producer should use those receipts to construct the ordinary inventory and public/direct slot coverage, then derive supported body syntax and metadata before invoking existing collectors. General closure support must follow actual formation origins, and method support must follow actual Principal/SourceAt receipts. The final theorem still needs justified input admission, complete replacement ranges and certification completeness; finite fixture coverage supplies none of those universally.

## Nested method evidence through public execution (2026-10-13)

Commits `749acda1` and `d671b4e3` remove the leaf-rule restriction from the connected method evidence proof. The fixture has three original implementation declarations, twelve physical cache slots, ten ordinary Headers and four public roots. Each selected Word/Bool BitNot body retains a Mark tree with its actual Seed premise.

The proof fixes primary and method roots using independent Source requirement production and original requirement-ID uniqueness. It compares complete reachable raw trees; evidence order and repeated assumptions are retained in Source assembly. The finite validator deliberately rejects conflicting actual origins. The negative regression uses actual checked/worklist data, and its whole program is also rejected by the existing compiler. It is not a counterexample for the compile-success theorem.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 106 affected modules pass coherent checks. The full build (7,082 jobs), all registered tests (14,034 build jobs and the final pass marker), kernel policy and 144 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected catalog supports evidence with premises and no longer requires a premise-free rule or global uniqueness of every valid evidence tree. It checks complete trees reachable from the actual caller and selected requirements. The finite materializer/resolver, caller-coverage and origin checks can still reject compiler-accepted selections outside their supported conditions. Their completeness from compilation success, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Methods with their own evidence through public execution (2026-10-13)

Commits `92b3848c` and `890ebedc` connect a selected method with its own nonempty dictionary through seven public executions. The fixture retains twelve physical cache slots, ten ordinary Headers and four public roots. The actual Word and Bool method rows each retain one type replacement and one Mark dictionary entry. Their original eighteen-node bodies retain all three constrained direct calls.

The executable static validator compares complete ordered raw evidence trees and checks actual caller coverage. Source identity follows original body selection and coherence of each reached assumption. The method port retains the real complete resolver receipt, which is reused by direct calls at the reached lexical scopes. No method execution law or dictionary equality is added to the public caller assumptions.

An investigation found distinct default and ordinary evidence origins in a checker-accepted program; existing compilation validation rejects that case. It is not a counterexample for the compile-success theorem. No Source selection rule was changed. The general connection between accepted compilation and evidence-origin coherence remains work to do.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 160 affected modules pass coherent checks. The full build (7,050 jobs), all registered tests (13,970 build jobs and the final pass marker), kernel policy and 196 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected method catalog now supports nonempty method assumptions. It validates the complete ordered materialized dictionary against the actual caller resolver, and derives Source dictionary equality from the original leaf Mark rule. This finite static check can reject compiler-accepted selections outside its supported conditions. Coherence for evidence with premises, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Generic implementation substitutions through public execution (2026-10-13)

Commits `e31d23c5` and `191f8355` connect actual generic implementation substitutions through seven public executions. The fixture retains twelve physical cache slots, ten ordinary Headers and four public roots. A single original generic implementation method produces the actual Word and Bool method rows, each with one retained type replacement. Its eighteen-node source has three direct calls with real Mark requirements.

The range proof follows actual parameter occurrences in the checked implementation head and preserves nominal catalog membership and arity. Concrete checks come from successful specialization, not from a scalar-only observation. The method body receipt compares complete cached specializations and uses the actual selected synthetic signature; it does not replace the method with an ordinary declaration Header or erase its substitution. Independent Source typing and actual accepted method compilation remain the semantic authority.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 87 affected modules pass coherent checks. The full build (7,015 jobs), all registered tests (13,900 build jobs and the final pass marker), kernel policy and 161 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Method selection now retains arbitrary actual implementation substitutions. Its complete replacement range follows from the original well-formed implementation head, actual typed selection goal and accepted concrete specialization. The connected method catalog still requires empty method assumptions. Methods with their own dictionaries, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing calls inside implementation methods (2026-10-13)

Commits `8401d7ee` and `358575d6` connect actual method-to-function evidence calls through seven public executions. The fixture retains twelve physical cache slots, ten ordinary Headers and four public roots. Each original implementation body has eighteen nodes and three direct calls with genuine solved Mark requirements. Independent Source typing covers the entire original body and its lexical changes.

The caller resolver and dictionary are compared in full. Source evidence production is authenticated by the actual accepted call and selected callee; coverage alone does not establish dictionary equality. Newly discovered ordinary callees retain their actual final cache slots and complete successful Source specialization requests. Their preparation does not require membership in the earlier validation plan.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `13 / 31 / 49 / 122 / 140 / 213 / 286 / 340`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 728 affected modules pass coherent checks. The full build (6,985 jobs), all registered tests (13,840 build jobs and the final pass marker), kernel policy and 128 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers direct declaration calls from scoped implementation methods whose own assumption lists are empty. The callees retain nonempty trait dictionaries. The current method catalog still requires closed implementations without type parameters. Broader method selection and dictionaries, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Scoped implementation methods through public execution (2026-10-13)

Commits `6a1b2416` and `1cc4ad92` connect scoped implementation methods through seven successive public executions. The artifact retains ten physical cache slots, eight ordinary Headers and four public roots. Original Source typing covers both selected implementation bodies, including local freshness, writable assignment targets and the loop context.

The exact method instantiation and its actual closed implementation establish the empty structural substitution used by this fixture. SourceAt retains the complete selected dictionary and accepted compiler body. Native prefix agreement follows from the actual parameter type, physical slots and frame reference. The proof preserves the same Source heap, callable representation and returned pool, without a supplied method execution law.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `11 / 29 / 47 / 93 / 111 / 157 / 203 / 239`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 45 affected modules pass coherent checks. The full build (6,956 jobs), all registered tests (13,782 build jobs and the final pass marker), kernel policy and 140 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers actual implementation method bodies with local allocation, plain assignment and finite loops, using read and Boolean child receipts from the original method nodes. The generic scoped body proof accepts mixed expression roots; deriving such roots for calls and evidence inside methods is the next connection. Broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Scoped named calls through retained closures (2026-10-13)

Commits `71c40c0c` and `f24bbeb7` connect scoped named relays through retained closure captures and seven successive public sessions. The artifact contains ten physical cache slots, eight ordinary Headers and four public roots. Each closure retains its own value, next value and loop flag; the actual input registry authenticates the handle used by the Source indirect caller.

The named entry derives its native prefix from the actual frame packet and captured physical slots. The scoped proof retains the same positive callable representation, Source heap, full pool and physical authority. Static support stores actual compiler and Source typing receipts; no called-body execution law is supplied by the closed fixture. Both directions use the same strong induction and strict child grades.

The four scalar results are `33 / true / 33 / 55`; native store lengths are `11 / 29 / 47 / 72 / 90 / 115 / 140 / 162`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 54 affected modules pass coherent checks. The full build (6,924 jobs), all registered tests (13,718 build jobs and the final pass marker), kernel policy and 121 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers the existing scoped named-body grammar inside the same physical callable family as direct calls, selected methods and retained closures. The selected implementation methods in the closed fixture still have terminal bodies. Scoped implementation method bodies, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Selected methods through scoped closure mutation (2026-10-13)

Commits `20b48ab6` and `9639ca05` connect scoped closure mutation and selected methods through original Source indirect calls and seven successive public sessions. The artifact retains eight physical cache slots, six ordinary Headers and four public roots. The first closure is called both before and after an intervening factory call and another closure invocation. Its second result observes the retained value update and its loop flag remains false.

The static packet retains real accepted compiler actions and the full caller dictionary at the reached contexts. The dynamic proof retains physical authority and all captured slots through parameter entry, local allocation, assignment and restoration. It uses the existing imperative flow proof and introduces no Core or operational Source rule. Public entry follows actual initialization and authenticated handle reimport. The closed fixture supplies no body execution law.

The four scalar results are `11 / false / 33 / 55`; native store lengths are `9 / 27 / 45 / 61 / 79 / 95 / 108 / 121`. All seven original checkpoints have independent Source meaning and sufficient execution/output-fuel bounds. Every sufficient factory completion appends its actual exported handle to the reusable history.

Validation: all 47 affected modules pass coherent checks. The full build (6,893 jobs), all registered tests (13,656 build jobs and the final pass marker), kernel policy and 106 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers the existing scoped closure grammar with genuine method calls in local initialization, captured assignment and return. The closed fixture uses identity implementations of Word and Bool bit-not with no implementation parameters or method assumptions. Method-bearing scoped named bodies in the same physical family, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Selected methods inside retained closures (2026-10-13)

Commits `81da9984`, `ef0cd998` and `8a082cea` connect selected methods inside retained closure bodies through actual Source indirect calls and seven successive public sessions. The artifact has eight physical cache slots and six ordinary Headers. Method cells remain covered by physical authority without being treated as ordinary declarations.

A named handle now retains the exact captured environment and embedding. Code identity and cache typing alone cannot identify that capture. At a later call, retained capture facts and current physical authority reconstruct the same installed function. Closure and named origins remain present throughout argument execution and heap restoration; there is no conversion from an erased heap back into the stronger representation.

The public regression derives function-input registry equality from actual handle reimport. Its three factory calls append genuine handles, and all seven calls use their preceding returned session and Source heap. The four scalar results are `11 / false / 11 / 33`. Each original checkpoint has a Source-derived sufficient-fuel result, including an appended history for every sufficient factory completion. No called-body execution or initialized-heap relation is supplied by the fixture.

Validation: all 761 affected modules pass coherent checks. The full build (6,865 jobs), all registered tests (13,600 build jobs and the final pass marker), kernel policy and 210 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers ordinary retained closures with terminal expressions that call selected methods, and original Source indirect calls that invoke them. The physical family also retains named and builtin handle branches. The closed fixture uses identity implementations of Word and Bool bit-not with no implementation parameters or method assumptions. Combining this family with scoped closure mutation, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Selected operator methods through public execution (2026-10-13)

Commits `0883d66d`, `aebd8640` and `e963a2a9` connect selected operator methods through genuine Source typing, actual compiler receipts and four successive public calls. A single strong induction supplies called-body meaning; the closed endpoints introduce no assumed method execution or initialized heap relation.

The identity implementation of Word bit-not returns its input, so the regression distinguishes selected method dispatch from primitive bit-not. Its artifact contains six physical slots and four ordinary Headers. Actual physical authority covers both method cells, while the ordinary inventory remains exact for declarations. Selection retains full caller evidence, even though the selected method dictionary is empty in this fragment.

Validation: all 1,016 affected modules pass coherent checks. The full build (6,803 jobs), all registered tests (13,476 build jobs and the final pass marker), kernel policy and 199 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected fragment uses selected implementations with no implementation parameters or method assumptions, ordinary terminal callers and methods whose bodies return their argument. The shared proof covers both unary and binary method heads; the closed public fixture exercises unary dispatch. Combining these method paths with retained closures and scoped bodies, broader method selection, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing retained closure calls (2026-10-13)

Commits `fd39e383` and `a19eac55` close the retained ordinary closure dictionary connection. Full dictionary equality is retained at genuine formation; it is never inferred from dictionary coverage or capture typing alone. Both original Source well-formedness and actual selected compiler evidence are retained in the closed public regression.

The regression has six actual selected named rows, three distinct exported closures and seven linked public calls. The three creation steps append actual handles; later calls preserve all older entries. Both Word and Bool outputs follow from Source/native result representation and the actual public encoder. Each of the seven original starts has an independent Source-derived sufficient-fuel theorem.

Validation: all 1,007 affected modules pass coherent checks. The full build (6,741 jobs), all registered tests (13,352 build jobs and the final pass marker), kernel policy and 73 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers evidence-bearing direct declaration calls in ordinary retained closure bodies, using the existing supported scoped grammar and actual named formation. It preserves the full closed replacement range and captured environment. Trait method dispatch, coercions, remaining expression and control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing calls in scoped named bodies (2026-10-13)

Commits `8a433c18` and `55db5d43` extend genuine declaration evidence beyond terminal bodies. Every direct-call occurrence is reconstructed from the selected compiler policy. The independently produced Source dictionary agrees with the actual compiler dictionary through the original ledger, including after local allocation and inside the loop.

The four-call regression retains all six cached rows and their distinct specializations. The initial state comes from actual initialization, later states from the preceding returned sessions, and every call has reflection plus a sufficient-fuel result at its original checkpoint. No assumed called-body execution or initialized heap relation is introduced.

Validation: all 23 affected modules pass coherent checks. The full build (6,716 jobs), all registered tests (13,302 build jobs and the final pass marker), kernel policy and 65 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers supported direct declaration calls in the existing named scoped grammar, including local allocation, plain assignment and finite loops. It retains the full closed replacement range and excludes coercions and generalized local functions. Evidence-bearing formation and retained closure bodies, method paths, remaining expression/control forms and composition across every compiler pass remain incomplete.

## Nested closure formation through retained public handles (2026-10-13)

Commits `0de590b2` and `df6f8314` connect inner closure generation to the same Source/public proof family used for later handle invocation. No supplied body execution law or initialized heap relation replaces the compiler receipts. Original Source typing, precise reached metadata, retained policy fields and actual global-slot provenance construct the static support.

The closed regression covers all seven linked calls and four distinct function handles. It proves exact successive Source heaps, histories that retain every previous handle, and sufficient execution/output fuel at each original start. Both factory exports and both inner-formation exports append their actual handles to the reusable history.

Validation: all 1,448 affected modules pass coherent checks. The full build (6,695 jobs), all registered tests (13,260 build jobs and the final pass marker), kernel policy and 59 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers ordinary closure formation in retained scoped bodies. The inner closure retains its own local capture and may call a named function. Formation under further expression forms, evidence-aware scoped callers, method and coercion paths, remaining control forms, generalized local functions and composition across every compiler pass remain incomplete.

## Evidence-bearing generic calls through public execution (2026-10-13)

Commits `8439d72a` and `d5614a9b` connect full direct-call evidence through actual compilation and four successive public executions. Requirement-bearing Source traces preserve their original lists. The actual selected target, complete specialization metadata and physical slot determine the callee; the prepared caller identifies its inherited dictionary. Ledger uniqueness identifies independently produced Source evidence with the actual callee dictionary.

The regression exercises both an implementation-selected root and a generic caller that uses an assumption. It retains all six cached rows, exact successor sessions and Source heaps. The public proofs introduce no assumed called-body execution, dictionary equality or initialized-heap relation.

Validation: all 1,591 affected modules pass coherent checks. The full build (6,668 jobs), all registered tests (13,206 build jobs and the final pass marker), kernel policy and 117 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

This connection covers direct declaration calls with a closed full replacement range, real requirement lists and no coercions. Formation inside retained closure bodies and under other expression forms, broader specialization and method paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Generic direct calls through actual specialization (2026-10-13)

Commits `62158ce7` and `a4e52efd` connect ordinary generic calls through actual compiler selection and public execution. Source and compiler substitution lists have opposite orders. Equality is proved using the successful full matcher and the original domain order; specialization keys and projected types are insufficient. Every raw replacement retains its closedness check, and original Source admissibility provides the corresponding well-formedness at entry.

The regression keeps two concrete specializations and their distinct native slots in one compiled artifact. All four linked calls have Source traces and public completion bounds, without a called-body execution premise.

Validation: all 555 affected modules pass coherent checks. The full build (6,649 jobs), all registered tests (13,168 build jobs and the final pass marker), kernel policy and 52 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Calls carrying declaration evidence, further closure formation and expression forms, and composition across every compiler pass remain incomplete. This connection covers ordinary direct calls with empty predicates and a closed full replacement range.

## Recursive tuple formation and collected closure handles (2026-10-13)

Commits `ed24ea28` and `72744c3f` connect recursively generated tuple closures through real nested output collection and subsequent calls. The root compiler policy is selected once. Child acceptance, original typing, native packed-child typing and lambda metadata determine each formation receipt; the original root policy fuel remains distinct from the child compilation fuel.

Structural certificate induction preserves the actual nested caller packet. Group reflection and singleton tuples may keep the native grade; Source preservation uses the strict child grades supplied by the independent Source rules. Output collection derives both ordered Source leaves and their exact encoder budgets from the actual full result and successful export. All six public checkpoints have sufficient-fuel bounds.

Validation: all 400 affected modules pass coherent checks. The full build (6,633 jobs), all registered tests (13,136 build jobs and the final pass marker), kernel policy and 37 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Formation inside retained closure bodies and below other expression forms, wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Direct-call initialization and retained closure formation (2026-10-13)

Commits `fac267b5` and `3e578bd2` connect a direct initializer followed by closure formation at its actual extended lexical scope. The collector retains the selected Source node, absence of generalized local lowering, original return shape, native child typing and original evidence/ledger context. It invokes the existing lexical formation producer on that same accepted child.

The public sequence creates distinct closures over newly allocated `saved` cells, invokes A, creates C, invokes B and reuses A. Every call uses its preceding returned session and reached Source heap. All six Source traces and sufficient-fuel bounds are proved; whole-body meaning and runtime captures are not static assumptions.

Validation: all 21 affected modules pass coherent checks. The full build (6,612 jobs), all registered tests (13,094 build jobs and the final pass marker), kernel policy and 21 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

Formation below recursive expression nodes and inside retained closure bodies, wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Canonical calls through scoped bodies and capture mutation (2026-10-13)

Commits `37591075` and `59fdf839` connect direct/index children inside actual scoped bodies to public sessions. Named entry derives its canonical packet from the genuine parameter prefix and complete Header inventory. Ordinary entry derives its global slots from the retained capture and actual parameter binding spine.

Both paths reuse the existing scoped flow induction. The marked allocator, administrative transport and lexical restoration preserve the original canonical slots alongside the reached owned pool. The footer restores the exact returned pool and Source postcondition. Actual compiler collectors derive the child support; no whole-body meaning is a static packet field or public premise.

The six-session fixture executes a direct call in a named local initializer, direct calls before and inside closure while loops, and a direct return call. Its final reuse observes the earlier captured-cell update after an intervening closure creation and a call of another handle. All six independent Source traces connect to their original public checkpoints at sufficient execution and output fuel.

Validation: all 422 affected modules pass coherent checks. The full build (6,593 jobs), all registered tests (13,056 build jobs and the final pass marker), kernel policy and 35 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The next connection combines a direct-call local initializer with closure formation in the same named body. Formation below recursive expression nodes, wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Recursive mapping operands and retained failures (2026-10-13)

Commits `6a73f02f`, `544751f6` and `f517e1cd` connect independent recursive indexing to actual public execution. The base runs before the key; each strict child uses its actual reached heap and current owned pool. Lookup suffix allocations restore the same physical caller while retaining the complete ordered record history.

The fault proof obtains authority from the actual named or ordinary compiler occurrence. It carries the genuine issuer into the current receiving registry, without assuming diagnostic token injectivity. The failure adapter identifies the token through the original native result decode and retains the actual returned session.

The fixture checks all nine real events and all nine forward bounds. After the missing-key failure, the older closure is invoked from that returned session. No expected output or body execution law is a public premise.

Validation: all 760 affected modules pass coherent checks. The full build (6,565 jobs), all registered tests (13,000 build jobs and the final pass marker), kernel policy and 91 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The next connection is canonical direct and index expressions inside named and ordinary scoped bodies, including local allocation, assignment and finite loops. Wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Direct calls inside retained closure bodies (2026-10-13)

Commits `2b9fbd92` and `8d5bb1e6` connect retained closure captures, canonical body roots, the shared recursive proof and the actual public sequence. The body producer derives its packet, original Source typing, ledger coverage, read diagnostics and complete direct-call authority from the retained compiler record. The parameter-entry spine identifies the actual frame after installation; the proof retains the exact reached caller and its full record lists when restoring the outer call.

The fixture uses two actual named compiler rows, `identity` and `make`. Its closure body contains the original direct `identity(seed)` call. Reflection follows all six public sessions and Source heaps. Forward theorems quantify every sufficient execution and output fuel at the six original checkpoints. Separate handles keep their respective captures through the intervening factory call and later reuse.

Validation: all 3,026 affected modules pass coherent checks. The full build (6,539 jobs), all registered tests (12,948 build jobs and the final pass marker), kernel policy and 76 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The next connection is recursive mapping index children, including callable payloads and the current receiving registry for missing-default diagnostics. Wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Direct builtin calls through public sessions (2026-10-13)

Commits `23740f15`, `cab7e4b0` and `4aeff59b` connect staged builtin evaluation, the accepted compiler action and public retained sessions. The Source rule evaluates the argument vector and applies the selected builtin. Its synthetic callee is authenticated statically. Compiler validation, original raw parameter types and physical native arguments agree before the actual contracted wrapper executes.

The public test retains `wordFromInteger(0)` in the original Source and the genuine builtin compiler certificate. Its literal carries the actual solved evidence. An alternative with a runtime Integer intermediate was rejected by the existing compilation plan; the connected example obeys that policy. No staging restriction was weakened. Argument failures and successful calls retain the actual reached heap and admission.

Validation: all 710 affected modules pass coherent checks. The full build (6,512 jobs), all registered tests (12,894 build jobs and the final pass marker), kernel policy and 52 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The runtime and Core representation are unchanged. The next connection is direct declaration calls inside retained closure bodies. Wider specialization and evidence paths, remaining expression and control forms, and composition across every compiler pass remain incomplete.

## Named direct calls and retained closure captures (2026-10-13)

The direct-call connection is committed in `25b9a92a`, `8626c646` and `bc453668`. Source evaluation follows the actual argument vector and selected global application. It introduces neither a runtime evaluation of the synthetic declaration reference nor an indirect-call gate. Ordinary erasure retains the actual invocation dictionary, and failure preservation composes the argument and invocation heap extensions.

Compiler authority includes the exact specialization and physical row, not just the declaration key. The original raw Source types determine parameter typing before native packing. Complete inventory and authentic canonical caller bindings determine the global slot; the current pool determines the capture after argument effects. The simultaneous ordinary/canonical induction closes named child meaning with strictly smaller budgets. Legacy finite callers derive their direct-call exclusion from their actual supported syntax.

The actual three-function fixture executes six linked public calls and retains distinct captures across an intervening allocation. Its forward result derives export fuel, the returned handle type, payload encoding and the exact Source heap from Source success. A final kernel-policy check corrected one prohibited keyword in a comment; theorem declarations were unchanged.

Validation: all 696 affected modules pass coherent checks. The full build (6,494 jobs), all registered tests (12,858 build jobs and the final pass marker), kernel policy and 72 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The connected direct declaration fragment uses empty instantiation substitutions and predicates, and empty caller assumptions at direct sites. Wider specialization and evidence paths, other compiler alternatives and composition across every pass remain incomplete. Runtime unification is complete; the full meaning-preservation theorem is still in progress.

## Recursive constructor children and public handle reuse (2026-10-13)

`624b8d0e` adds independent staged Source traces for constructor payloads, including ordered child execution and failure propagation. `5bf2f084` connects the actual compiler receipts to preservation and reflection through the recursive caller family. The original constructor metadata and every payload value remain represented. Validity uses the actual closed substitution range, including unused entries; a native type projection alone does not establish this condition.

`9c7b952e` connects construction, export, nested handle collection and later calls through the exact returned public sessions. The example builds `Hold(factory(20), prior, factory, builtin)`, where `prior` captures `10`. The child call creates a separate closure capturing `20`. The collected closure returns `20`; an intervening factory call creates a capture of `30`; the older closure then returns `10`, and the retained builtin converts `37`. Each step retains its independent Source trace, reached heap and complete reusable handle history. Source success also gives sufficient execution and output fuel for constructor export and any requested selection from that output.

Validation: all 2,102 affected modules pass coherent checks. The full build (6,467 jobs), all registered tests (12,804 build jobs and the final pass marker), kernel policy and 34 endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The Core representation and runtime are unchanged. Direct declaration calls are the next public connection under development. Broader compiler alternatives and composition across every pass remain incomplete.

## For headers, finite loops and retained captures (2026-10-13)

`fd2b9008` adds independent staged Source traces for `for` initialization, finite iterations and post-header items. `181fa159` connects them through genuine compiler receipts to both directions of the public execution proof. Header items include monomorphic declarations, discarded expressions and plain assignment. Normal body completion executes the post header; return and failure preserve the reached heap and bypass it. Leaving the loop restores the outer lexical scope. This fragment does not yet include `break` or `continue`.

The named `update` example executes one iteration and then zero iterations across successive sessions, returning `12 / 22`. `bb21dcc0` checks separate closures capturing `10` and `20`, an intervening `make(30)`, and one, zero and one loop iterations. Its direct results are `10 / 20 / 11`; the last result observes the first closure's previous update. Each public proof derives independent Source execution, exact heaps, retained histories and sufficient execution/output fuel at the original checkpoint.

Validation: the coherent affected graph covers 656 modules (268 authenticated cached results and 388 fresh checks). Full build (6450 jobs), all registered tests (12770 build jobs and the final pass marker), kernel policy and 82 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The Core representation and runtime are unchanged. Recursive constructor payloads, including calls that produce new closures, are the next public connection under development. Broader compiler alternatives and final composition across every pass remain incomplete.

## Match bodies and retained capture updates (2026-10-13)

`d36b6b1a` adds staged Source match traces, measured children, ordinary erasure and failure-state preservation. `d64b1b5a` connects them to actual compiler output and both directions of the public proof family. Compiler receipts retain the selected pattern bindings, hidden cells, catalog, allocator and typed literals. Leaving an arm restores the outer lexical context while retaining its heap effects.

The named `update` example returns `12 / 23` through successive real sessions. `106e24d6` adds six linked calls with separate closures capturing `10` and `20`, an intervening `make(30)`, and match arms that update captured cells. Direct calls return `10 / 20 / 11`, proving that the final call sees the earlier update. Independent Source traces, exact reached heaps, retained histories and sufficient execution/output fuel connect at the original public checkpoints.

Validation: full build (6408 jobs), all registered tests (12686 build jobs and the final pass marker), kernel policy and 56 endpoint audits pass. Audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. Finite `for` initialization, body and post-header execution are the next connection under development; remaining compiler alternatives and final composition across every pass are incomplete.

## Recursive operators and retained function calls (2026-10-13)

`5f17535e` connects unary, binary and conditional expressions through the recursive caller family. Child proofs use the actual selected Source nodes, compiler receipts and reached states. Short-circuit operators and conditional expressions evaluate only the selected children. Numeric literals retain the actual checked evidence. The closed `drain(n)` example executes subtraction in a while body and returns `0 / 0` from successive calls with `3 / 0`.

`f68d6763` connects the same expression family to retained named function handles. The closed example obtains an `identity` handle and uses it inside both branches of `!flag ? f(value) + value : f(value) - value`. Successive calls return `22 / 0` through the preceding actual sessions. Both examples derive independent Source traces, exact reached heaps, retained histories and sufficient public execution/output fuel at their original checkpoints.

Validation: full build (6375 jobs), all registered tests (12620 build jobs and the final pass marker), kernel policy and thirty endpoint audits pass. The audited proofs use only `propext`, `Classical.choice` and `Quot.sound`. The `match` connection is under development; remaining compiler alternatives and final composition across every pass are incomplete.

## Scoped blocks connected to public execution (2026-10-13)

`ea7ac706` adds recursive staged block traces, measured children, ordinary Source erasure and failure-state preservation. `18c4e95f` connects those traces through the actual compiler, scoped lexical and imperative body proofs, and public sessions. A block restores the outer lexical context after its body while keeping the reached heap. Return and failure bypass the suffix; a compiler-confirmed terminal block requires no suffix execution premise.

The closed `update(value, next)` example allocates a block-local copy of `next`, writes it to the outer `value` cell and returns that value after leaving the block. Its successive calls return `12 / 23`. Both Source traces, reached heaps and retained histories come from actual initialization and the preceding returned session. Independent Source success supplies sufficient execution and output fuel at both original checkpoints.

Validation: full build (6346 jobs), all registered tests and kernel policy pass. Twenty-four audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Recursive primitive and conditional expressions are the next public connection under verification. Remaining control flow, broader compiler alternatives and final composition across every compiler pass remain incomplete.

## Named while bodies from actual call entries (2026-10-13)

Checkpoint `04a8a508` connects named bodies with plain assignment and finite while loops to the same public proof family. The actual argument bundle, global slots and retained frame determine the compiler's native input prefix. The proof restricts the canonical view to those used slots while preserving the complete runtime environment, heap and owned pool. Existing input metadata extension receipts supply the required registry condition throughout public dispatch.

The closed `choose(flag, value, stop)` example executes one iteration on the first call and none on the following call, returning `11 / 22`. Both independent Source traces, exact reached heaps and reusable histories come from actual initialization and the successive returned sessions. Source success provides sufficient execution and output fuel at both original checkpoints. Static support is extracted from genuine compiler acceptance, including its assignment policy and native typing; no body execution law is supplied by the fixture.

Validation: full build (6331 jobs), all registered tests and kernel policy pass. Twenty-two audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Scoped blocks are the next connection under verification. Broader expression/control-flow coverage and final composition across every compiler pass remain incomplete.

## Finite while bodies and retained closure captures (2026-10-13)

`494ac11a` adds finite staged while traces, their numeric grades, ordinary Source erasure and fault-heap preservation. `b658957a` connects them through authentic compiler receipts, closure application and public sessions. Each iteration restores its outer lexical bindings and retains its actual reached heap. The proof handles finite iteration counts, early return, condition failure and body failure; this fragment does not yet include `break` or `continue`.

The closed six-call example creates separate closures capturing `10` and `20`, invokes the first, performs an intervening `make(30)`, then invokes the second and the first again. Direct results are `11 / 20 / 12`, with one, zero and one loop iterations respectively. Every Source trace uses the preceding actual session and heap. Source success derives sufficient execution and output fuel at each original direct-call checkpoint. The initial diagnostic receiver is constructed from its registry.

Validation: full build (6318 jobs), all registered tests and kernel policy pass. Twenty-one audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Named while bodies are the next public connection under verification. Wider control flow, expression coverage and composition across every compiler pass remain incomplete.

## Named conditional calls at their actual checkpoints (2026-10-13)

Checkpoint `00067020` connects named conditional bodies to actual initialization, the first call and a following call on its returned session. The closed `choose` example takes both branches and proves Source results `11 / 22`, exact successive heaps and reusable histories. The first branch allocates a local copy. Independent Source success also supplies sufficient execution and output fuel for every resume above the bounds at each original checkpoint.

Static support comes from the genuine named Header and accepted compiler flow. The diagnostic receiver is constructed from its registry, without an additional execution. Full build (6299 jobs), all registered tests and kernel policy pass; twelve audited endpoints use only the standard three axioms. Finite staged loops are the next connection being verified. Wider compiler coverage and final all-pass composition remain incomplete.

## Conditional closure bodies connected to public execution (2026-10-13)

Checkpoint `b5b60f45` connects conditional statements through the actual compiler, recursive Source semantics, closure application and public sessions. Branch arms execute in scoped mode. Falling through restores the surrounding lexical context while retaining the reached heap; returning or failing stops the suffix. Compiler receipts retain the actual accepted flow, selected branch code and native typing.

The closed six-call example creates two distinct closures capturing `10` and `20`. The first call takes an assignment branch and returns `11`. After an intervening `make(30)`, the second closure takes a branch with a local copy and returns `20`; another call to the first returns its retained `11`. All calls use the preceding actual session and heap. The proof also derives sufficient public execution and output fuel from independent Source success for each of the three direct calls.

Validation: full build (6284 jobs), all registered tests and kernel policy pass. Twenty-seven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The actual named conditional-body example is being connected next. Loops, match, wider compiler alternatives and final composition across every compiler pass remain incomplete.

## Initial and following named export errors (2026-10-13)

Checkpoint `e32c742b` connects successful Source execution to the state returned when a named call's output cannot be exported. Actual bootstrap derives the first empty-entry History; following calls retain earlier handles at the actual encoded registry. Both routes derive final heap typing from the full result and preserve authentic encodings and export authority.

The closed four-call example begins with an export error, successfully exports a closure on the next call, encounters another named export error and invokes the retained closure. Its result is Word `10`. All four Source applications use the preceding actual session and reached heap. Failed exports add no handle.

Validation: full build (6247 jobs), all registered tests, kernel policy and six standard-axiom endpoint audits pass. Staged conditional bodies are the next connection in progress; the final theorem covering every compiler pass remains incomplete. Earlier dated entries retain their own scope.

## Continuations and nested selection audit (2026-10-13)

Checkpoint `a0c2197f` passes the full 6244-job build, all registered tests and kernel policy. Twenty audited endpoints for the two latest units use only `propext`, `Classical.choice` and `Quot.sound`.

`2ab1db28` proves composition of actual execution resumptions. Each intermediate receipt must be a genuine out-of-fuel outcome. Composition preserves the terminal outcome, reached store, export generation and final output budget; it sums only execution fuel. The closed example exhausts positive execution fuel twice before each of two direct completions. Its forward theorem applies to every actual finite chain meeting the total execution and terminal output bounds.

The same commit handles direct export errors. The receipt distinguishes successful native/Source execution from failure to export that result. It retains the reached session and old authenticated encodings without adding an output handle. Source heap typing follows from the full successful result. A closed call with output budget `0` continues from that exact state and reuses its older captured handle.

`a0c2197f` collects ordered mapping entries `A, B, A` from the actual public result, including repeated handles and duplicate keys. Subsequent calls use those selected output entries, not an independently supplied list of input handles. They preserve separate captures through another allocation and return `10 / 20 / 10`. The general forward collector quantifies over selections of the actual exported value; the concrete ordered three-row mapping is identified in the observed reflection theorem.

Preceding checkpoints `65a7ed23` and `990acc26` connect following named calls, nested selection and decoded arity to both semantic directions. In particular, a packed Unit value does not by itself determine whether the callable takes zero or one argument. Failure reflection uses the genuine decoded arity, and Source failure preservation uses authentic callable arity.

Initial/following named export errors and staged conditional bodies remain under development at this checkpoint. No final all-pass preservation claim follows from these units.

## Actual input registries and general public output (2026-10-13)

`8f1fdfb2` connects current History to the registry produced by the actual input encoder. A proof-only receiver is constructed at that exact context, and genuine compiler diagnostics retain their token meanings along the forward extension. This removes the need to obtain a receiver from a separate execution or assume a reverse metadata extension. Captured environments, ordered entries and the reached Source heap stay intact.

Independent successful Source execution now supplies execution and output fuel bounds for all represented output shapes, including constructors, mappings, proxies and function leaves. The codec proof retains mapping order and duplicate rows, follows the genuine handle registry, and reuses an existing metadata ID even when the registry budget is full. The bound is uniform over execution fuel and export generations.

`2f941db0` connects the same general output proof to the first named call. Actual bootstrap, its export authority and the input encoder derive the initial heap, arguments and receiving context. The returned session starts a reusable History. The closed mapping-input example checks the original factory checkpoint and two direct calls with ordered mapping rows; both return the captured Word `10`. Its proofs cover reflection and sufficient public fuel from Source success. The mapping metadata already exists in the static registry; this example does not assert strict registry growth.

Validation: full build (6205 jobs), all registered tests and kernel policy pass. The ten actual-registry production endpoints, eight mapping endpoints and two initial-output endpoints audited for these units use only `propext`, `Classical.choice` and `Quot.sound`.

Next connections are collection of handles inside constructor/mapping outputs, following named calls at the actual registry, and direct Source failures with authenticated argument arity. Broader control flow, suspended/export-error continuations and final composition across every compiler pass remain incomplete. Earlier dated sections describe their own checkpoints.

## Captured-cell assignment connection audit (2026-10-13)

Checkpoint `b1e23802` completes the compiler/body/public connection for staged bare plain assignment. Target resolution precedes RHS evaluation, the write uses the actual post-RHS heap, and failure retains preceding effects. Static packets derive compiler shape and reachable diagnostic/read conditions. `818d4435` restricts projection-read obligations to nonempty paths, preserving existing stronger adapters.

The closed public example connects six actual sessions to six independent Source applications and reached histories. The first closure changes from `10` to `11`, the second still returns `20`, and another factory allocation occurs between their direct calls. The final call through the original first handle returns `11`. Validation includes the full 6182-job build, all registered tests, independent production/fixture review and kernel policy. Eight audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The next identified gap is registry direction: a representation at an arbitrary larger receiving registry does not justify decoding at the actual checkpoint's smaller registry. The implementation in progress moves History through the actual encoder's forward extension, constructs an authentic diagnostic receiver at that exact context and derives output codec shape there. Reverse registry extension or an unrelated successful execution must not become caller assumptions. General output collection, wider control flow, suspended/export-error continuations and full compiler composition remain open.

## Public function export from Source success (2026-10-13)

Checkpoint `f7cbbfd8` passes the full build (6152 jobs), all registered tests and kernel policy. The ten preceding production/Source endpoint audits and two new initial-function endpoint audits use only `propext`, `Classical.choice` and `Quot.sound`.

`5edd2500` proves sufficient public fuel for function results of direct named, builtin and closure applications. Successful independent Source execution implies actual function export for every sufficient execution budget and output budget at least `1`. The returned function joins the exact reached History. `Session.ExportsReady` records genuine issuer and registry integrity; actual initialization creates it and real session transitions preserve it. The proof does not assume that native execution or export succeeds. The existing runtime entry points and History type remain available.

`f7cbbfd8` closes the corresponding initial named-call route. Its public theorem derives starting arguments, heap and caller from actual fresh initialization and startup, then constructs the first remembered function at the Source after-heap. The registered example proves both initial and later direct export at their original checkpoints while retaining the actual `10 / 20 / 10` capture sequence.

`c0a118be` extends the same staged Source relation with bare plain assignment, RHS failure and target lookup failure. Target resolution precedes the RHS; a successful write uses the RHS's actual final heap. Both erasures, numeric grades, fault preservation and existing dependent proofs have been checked. The authentic compiler/body/public connection for these new assignment rules is still in progress. General output decoding, wider imperative control flow, suspended/export-error continuations and all-pass composition remain open.

## Lexical closures, callable preservation and failure continuation (2026-10-13)

The latest verified implementation checkpoint is `b9c241f9`. The full build (6147 jobs), all registered tests and kernel policy pass. The endpoint audits for these additions use only `propext`, `Classical.choice` and `Quot.sound`.

- `3341275f` connects lexical closure bodies through genuine compiler receipts, both semantic directions and the existing recursive public family. Static packets retain the actual allocator, accepted flow and expression children at their reached contexts; they do not assume a body execution law.
- `fc167824` derives sufficient public execution fuel for successful Word results from named, builtin and closure applications. With output fuel at least `1`, the actual checkpoint returns the same Word and a History at the Source after-heap. The closed named/builtin example proves captured Word `10` and builtin Word `37` at its original checkpoints.
- `b9b55505` closes six actual calls for a factory returning `lam() { let copy = seed; return copy; }`. Separate handles retain captures `10` and `20`, including after an intervening factory allocation. Direct results are `10 / 20 / 10`; every step uses its predecessor's actual session and heap.
- `354a2345` connects an initial uninitialized-local failure to a later successful identity call. The proof identifies the absent allocated cell, exact Source failure, subsequent Word `37` allocation and both returned Histories.
- `b9c241f9` proves sufficient public fuel for that initial Source failure, with any output budget. Actual bootstrap and input receipts derive the starting conditions; the result retains the same Source after-heap and a reusable failed History. The closed example includes output fuel `0`.

Next work connects forward function-handle export using registry integrity derived from actual initialization, and captured-cell assignment through the same staged Source relation and public proof family. General imperative control flow, constructor/mapping output selection, suspended/export-error continuations, receiving-model changes and final composition across all compiler passes remain open. Historical percentages are unchanged; the completed connections above describe this checkpoint. Earlier dated sections retain their original scope.

## Lexical allocation and body-reachable reads (2026-10-13)

Commits `8537c3c2` and `a0cd0dba` extend the existing public proof route to lexical named bodies. Review checked genuine compiler acceptance, actual local allocation, context extension, strict recursive child bounds, native frame restoration and full returned heap/pool conditions. The static body packet contains compiler evidence; it does not assume a body execution law. Terminal callers use an explicit compatibility adapter.

Read-policy and metadata obligations are restricted to expressions reached from the actual body. Structural reachability through groups, tuples and calls comes from original metadata. This removes the earlier global single-read-table restriction while preserving diagnostic identity for actual reads.

The closed fixture in `a20e0891` checks and compiles a factory with `let local = seed`, returns a closure over that allocated local, then invokes the same handle twice through successive public sessions. The Source proof identifies the allocated location, its captured environment lookup and Word `10` in the factory's actual final heap. Both direct results are Word `10`; every returned History uses the corresponding actual session and heap.

The generic first-failure seed theorem derives the final typed heap from Source fault preservation and retains the reached failure session. Its closed failure continuation fixture is still being assembled. Lexical declarations inside closure bodies also remain separate work at this checkpoint.

Validation: full build (6108 jobs), all registered tests and kernel policy pass. Independent production reviews found no blockers. Twelve production and three fixture endpoints use only `propext`, `Classical.choice` and `Quot.sound`. This checkpoint does not establish general imperative statements, general forward public result export, suspended/export-error continuations or the all-pass theorem.

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

## Packed input and raw signature audit (2026-10-13)

Commit `ac3a55b3` closes a public captured-closure sequence with nonempty arguments: `make(10)`, `invokePacked(handle, 99)`, then `invokePacked(handle, 123)`. The theorem derives exact Source vectors `[99]` and `[123]`, results `10 / 10`, and the corresponding actual session/heap histories. Review checked genuine binder ownership, the lambda's retained lexical capture, actual arity and the original encoder/completion. No independent Source execution or callable-representation premise is supplied by the fixture.

A general equality between a remembered entry's raw Source type and its handle type would be false: decoding a product normalizes child types, so a function leaf may be registered without its inner annotations. The new startup adapter instead derives runtime compatibility from actual resolution and preserves the selected raw signature separately. Whole-function export still supports exact raw equality where it is used by the concrete Word fixture.

Packed reflection and preservation use the actual closure parameter list to distinguish zero arguments from a singleton Unit argument. Metadata-free scalar/handle/product inputs derive registry identity. Metadata-bearing inputs retain the real encoder-to-receiving extension condition. Native sufficient fuel is proved at the actual startup checkpoint; this does not yet prove sufficient public output-validation fuel.

Validation: strict Lean, full build (6054 jobs), all registered tests, kernel policy and independent reviews pass. All eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Direct named/builtin semantic dispatch, failed direct continuations, output collection and final compiler composition remain open. Estimates remain 100% / about 70% / about 85%.

## Direct public handle execution (2026-10-13)

Commit `dbfcaf47` adds the closed `SourceCoreCapturedDirect.sequence_meaning` theorem. Three genuine factory calls and three direct public invocations preserve separate captures through an intervening allocation, with Source Word results `10`, `20` and `10` and six linked actual session/heap states.

Independent review checked startup, exact selected callable and packed Unit, current captured heap, native evaluation size, recursive body support, original public completion and returned History. The frontend still performs one startup and one resume. The Source closure and raw handle type come from the actual preceding factory trace/export, not an additional semantic observation. Generic old-handle preservation covers successful and failed exports, while the new direct semantic History branch currently covers success only.

Validation: strict Lean, full build (6042 jobs), all registered tests, kernel policy and independent reviews pass. All eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

Scope remains successful direct invocation of zero-parameter closures in the admitted body family. This does not establish arbitrary packed arguments, direct semantic failure continuations, direct output collection, the forward public fuel theorem or full compiler preservation.

## Named scope generalization (2026-10-13)

The named terminal producer now obtains its canonical sidecar from the genuine hook and Source owner from the accepted ordinary specialization. The shared coherence theorem covers named and anonymous selections and differing specialization keys; its conclusion is guard-frame equality only. No Source execution law, body meaning law or replacement metadata premise has been added. Lambda-free Source and owner-key uniqueness restrictions, including the fixture's runtime uniqueness check, have been removed.

Validation: full build (6035 jobs), all registered tests and kernel policy pass. `hook_sidecar`, `selected_frame`, `NamedRecursiveTerminalSupport.of_actual` and the closed six-call `sequence_meaning` depend only on `propext`, `Classical.choice` and `Quot.sound`. Direct public `invokePacked` meaning preservation remains unfinished.

## Sequential captured-closure reuse audit (2026-10-13)

Commit `c187ce09` adds `SourceCoreCapturedReusePublicExecution.sequence_meaning`, which connects the actual six-call public sequence to six independent Source applications and reusable returned histories. Independent review checked the exact public inputs, selected functions, exported handles, Source arguments, heap transitions and final results.

The public sequence is `make(10)`, `make(20)`, `read(first)`, `make(30)`, `read(second)`, `read(first)`. Every call starts from the immediately preceding returned public session. The Source heaps are joined in the same order. Source arguments for the reads are the corresponding retained closure values, and the outcomes are exactly Word `10`, `20` and `10`. The first two handles are distinct. Histories retain both original entries, append the third export once, and preserve all three through the final reads.

The read result follows from the same full `ResultAt` used to construct the returned History, together with actual successful decoding and the selected raw Word result type. The proof does not infer closure meaning from handle authentication. Entry membership supplies the retained Source value; the existing history derives its representation and typing at the current heap. The actual input encoder and successful completion derive the registry equalities needed by the next call.

Static support is constructed from the genuine two-header inventory and complete source tables. Actual cached-slot selection identifies a closure's source. The no-lambda read row cannot supply a lambda origin; the make row supplies the captured-reference body. The original terminal compiler action and real named sidecar provide indirect-read support. The receiving diagnostic table comes from a genuine indexed execution of the same compiled artifact. No dynamic representation, child execution or arbitrary body law is introduced as a fixture premise.

Validation: strict Lean, the actual six-call runtime fixture, full build (6035 jobs), all registered tests and kernel policy pass. Independent review found no issues in the exact input, session, heap and history connections. All eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

This closes the earlier gap between exported captured functions and a subsequent supported public call. It does not extend the static body grammar to the separate mutable assignment/match regression or prove all compiler alternatives. The fixed model/registry boundary, other output containers, suspended/export-error continuation and all-pass composition remain open. Estimates remain 100% / about 70% / about 85%.

## Captured-reference factory audit (2026-10-13)

Commit `4c2dbe39` adds the closed `SourceCoreCapturedLambdaPublicExecution` fixture, which proves Source factory execution and exported-handle History for an actual checked/compiled `make(seed: Word)` call with Word `10`. The body returns `lam() { return seed; }`. Its theorem constructs the Source program proof, nonempty inventory, body support, closure family and input metadata relation from original receipts; no dynamic representation or body execution premise is supplied.

The connection exposed four static facts that the old generic Association did not retain: the full compiler policy, original metadata at reached body expressions, lexical declarations of captured variables and actual read-diagnostic issuer tokens. These are now carried through the same Code and recapture. Native type equality alone does not identify a Source binder scheme. Equality with a generic Header's reason function alone does not identify an issued diagnostic token. Concrete named producers derive both facts from the actual header/terminal receipts; arbitrary-Site adapters retain authentic static evidence.

The policy audit also distinguishes the original outer callback fuel from a nested Site's compilation fuel. A genuine nested child reuses the original policy, so its policy receipt retains that original fuel rather than asserting equality with `Code.fuel`. Compatible reads continue to use the prepared read budget.

The single-read sequence producer restricts authentic lambda bodies using the complete original node table. It derives the read certificate, unchanged reached metadata, declaration scope and receiving fault interpretation at that exact Code. The named formation uses the actual installed parameter state and preserves captured references. `StartAt.simple_registry` derives the Word-input registry identity from the real encoder.

The separate indexed run supplies a genuine receiving diagnostic table for the same artifact. The later exported-handle invocation returns Word `10` in the runtime test, but that invocation is not yet included in the closed Source theorem. The next public retained-handle read, broader body grammar and final all-pass composition remain open. Estimates remain 100% / about 70% / about 85%.

Validation: strict Lean, full build (6019 jobs), all registered tests, kernel policy, the concrete public fixture and the six-endpoint axiom audit pass. The audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The initial private validation missed part of the dependency closure after a frontend proof change and produced compiler panics with mixed objects. That attempt is not accepted as validation. A fresh canonical dependency build replaced it; the private checker now includes the frontend overlay and treats panic output as failure even when the process exits successfully.

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

## Actual startup, product outputs and terminal lambda audit (2026-10-12)

Validation: strict Lean, full build (5997 jobs), all registered tests and kernel policy pass. Independent reviews found no issues in output collection, public startup recovery or the lambda state connection. The twenty-one checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The empty-body certificate helper also passes the full build and axiom audit.

The public startup recovery follows the original accepted `Session.start`. It reconciles public/indexed artifact and session identity, recovers the exact indexed `StartAt`, and equates its world/store with `History.current.NativeAt`. Complete finite inventory determines a Header for the selected root and derives its `NamedSourceAt`. The successful consumer returns this same packet with the full trace and `ResultAt`; it does not assume a replacement source function, initial heap relation or argument representation.

Output collection was reviewed for raw types, recursive fuel, metadata, ordering and semantic assumptions. `Addition.select` stores only the actual output/type observations and a structural `Selected` receipt. `Selected` fixes each leaf's Source/native shape, native type and recursive fuel. Its uniqueness proof prevents substituting a different entry list. Entry meaning is derived from `SucceededResultAt.reimports_payload` and the independent Source `ResultAt`; function reimport uses the actual handle resolver. Product traversal follows both original child encodings, restores their full raw Source types and preserves order and duplicates. Existing entries still pass through the unchanged success transport before new entries are appended.

The terminal lambda branch was reviewed through actual parameter installation and caller restoration. `Formation.of_actual` retains one authentic compiler occurrence and its same-code static body; Header typing supplies runtime validity and evidence coverage. The named parameter receipt supplies the nested packet at the real reached state. Native formation and Source closure representation use its current environment, captures and heap. The branch returns the existing complete pool result and postcondition, while `.recursive` retains the previous body proof. There is no supplied dynamic capture or closure-representation premise.

Complete inventory, authentic compiler/body certificates, exact raw structural inputs, the actual encoder-to-receiving metadata extension and one fixed function model and registries remain explicit. The new lambda branch requires an ordinary terminal lambda and zero capture prefixes. Output collection currently traverses products; constructor, mapping and raw comptime-wrapped product outputs remain separate work. Reusable failed continuations, suspended snapshots, model/registry changes, full statement grammar and all-pass composition remain open.

The mutable runtime fixture still uses assignment and match outside the admitted body grammar; its results do not instantiate these public semantic theorems. The closed empty unit-lambda fixture is now complete through first export and History construction; captured bodies and returned-closure invocation remain open. Estimates stay at 100% for runtime unification, about 70% for meaning preservation and about 85% overall.

## Used-session issuance and ready restoration (2026-10-12)

The current connection adds named/builtin issuance and ready snapshot restoration to actual retained histories, then consumes those histories in the public success/failure and Word endpoints. The strict public regression and its complete focused runtime fixture pass. Strict Lean, full build (5991 jobs), all registered tests and kernel policy pass. Independent snapshot review found no issues. The eighteen checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The preceding history checkpoint below retains its original record.

`IssuedEntry` stores genuine issuance, raw encoding and preparation/inventory provenance. Its producer derives Source representation and typing from the current caller and actual stored callable; those semantic conclusions are not certificate premises. Named entries retain the full Source specialization/dictionary and current native capture. Builtins retain their accepted closed code. The public `named_remembered` and `builtin_remembered` adapters append the actual entry while preserving earlier handles, including when the issued operation reuses a physical slot. Existing structural inputs and public history endpoints consume the extended list.

The snapshot receipt retains the original successful heap observation and exact saved ready session. Restoration changes only its handle registry to the observed registry, whose slots are proved to extend the captured registry. Store, world, authority and raw metadata stay equal to the saved branch. Thus every previously retained handle keeps its full native payload and the same Source meaning at that saved heap. Public restoration adapters construct the new history from actual capture/restore equations, then feed it to all three public endpoints. They do not assume a replacement heap relation or callable meaning, and do not preserve changes made later on another branch.

Executable-plan preparation is now derived from the compiled object's accepted records by `compiled_planPrepared`. The current history, continuation, initialized-seed and restoration adapters consume that equation internally. This removes the separate `acceptedPlan` assumption without claiming all compiler passes or body forms are covered.

The runtime regression combines two retained closures, a repeated alias and newly issued named/builtin receipts in nested inputs. Captures `38`/`109` produce integer `233`, followed by `47`/`117`; an incompatible nested builtin is rejected. Another branch captures a snapshot at `38`/`109`, mutates the original to `47`, restores the saved heap without later allocations, and invokes the original handles to obtain `39`/`110`. Duplicate-key order is observed by subsequent captures: swapping the closure rows leaves aggregates `176`/`233` unchanged, but changes `38`/`109` to `39`/`108` and `47`/`117` to `48`/`116`.

The mutable fixture does not instantiate the current semantic endpoints. Its assignment and match statements are outside the body certificates required by `OrdinarySequenceFor`, named `Terminal` and `NamedSupport`. Exact raw inputs, genuine encoded-to-receiving metadata extension, supported body facts and one fixed model/body/receiving registry remain explicit. Reusable histories after failure, suspended snapshot histories, remembering handles newly exposed by snapshot observation, nested output collection, model/registry changes and full body/all-pass coverage remain open. Estimates are unchanged.

## Multiple retained function histories (2026-10-12)

Code commits: `1bf7248d` and `b5be3856`.

Validation: strict Lean, full build (5986 jobs), all registered tests, kernel policy and independent review passed. The fourteen checked handle-transport, history, argument, public-continuation and initialization endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The new boundary retains an arbitrary finite list of function exports through supported successful intervening executions, including calls that return data and calls that allocate or mutate captured cells. Every history execution keeps exact startup and selected-root provenance, its native success receipt and full semantic `ResultAt`. The real selected raw signature and original native argument vector tie the semantic step to that execution. Remembering a new function uses the actual public export, Source outcome and complete native payload.

The initialized seed adapter derives the first history from the actual fresh bootstrap, finite resumption, selected startup and nested data/named/builtin input receipts. It invokes initialized public success reflection and retains its complete Source trace and `ResultAt`. The observed function export determines the first entry's exact raw type, Source/native payload and output-validation budget. The reached caller and relation to the initial caller are explicit outputs, so starting the history requires no separately assumed initial representation or closure meaning.

Two obligations are tracked separately. The session proof preserves each older handle's exact registry binding through execution/export and optional issuance. The semantic proof moves its representation and Source typing to the actual returned map, world and heap using that execution's extension and heap-metadata receipts. Closure code and captured reference identity remain stable; the contents of captured cells may change. State equality from issuance does not replace this execution proof.

The history producer derives the current owned caller, stable rows, deep heap typing, heap representation and per-entry meaning. The structural input certificate chooses exact history members and preserves distinct handles, repeated aliases, constructor payload packing and ordered mapping keys/values. The actual encoder supplies each native payload at its original position. Raw annotations and genuine encoded-to-receiving metadata extensions remain explicit, and mapping defaults follow the actual encoder.

Public success/failure reflection and Word preservation consume those current-state facts and retain full results and returned state. Successful continuation adapters also return reusable histories for the actual returned public/indexed session. One keeps all earlier entries through a data result; another additionally records a function returned directly as the result. Collecting functions nested inside an output container remains open, although nested inputs are supported. Failure reflection is available, while constructing a reusable history after failure remains a separate obligation.

The runtime regression first reaches independent captures `29` and `101` through successful calls that return data. It then issues another named factory without changing capture storage. A nested product/mapping argument uses the older closure twice and the independent closure once: `31 + 37 + 108` yields Word `176`. Follow-up calls return `38` and `109`, making both mutations and distinct captures observable. A duplicate mapping row swaps the handles; choosing that row would keep the aggregate `176` but change the follow-ups to `39` and `108`. The newly issued factory is not an input leaf. The earlier mixed named/builtin test and its `81`, `29`, `101` checks remain separate runtime coverage.

All history steps use one fixed function model, body registry and receiving registry, and retain supported static body evidence. Restored sessions, histories after failed execution, direct input leaves for newly issued named/builtin handles in a used session, model/registry changes, unrestricted bodies and the final all-pass theorem remain unfinished. The percentage estimates are unchanged. Earlier dated sections preserve their original scope and validation.

## Returned closure input connection (2026-10-12)

Code commits: `62001b99` and `f950c96c`.

The public semantic connection now continues from a preceding successful call that returns a function handle. The next call can receive arbitrary finite lists of independently typed data and repeated occurrences of that same returned function. Those occurrences may appear inside products, constructor payload vectors and ordered mapping keys or values. Exact raw types, comptime wrappers, proxy annotations, payload order and duplicate mapping keys are retained.

The preceding call supplies both its actual native success receipt and full semantic `ResultAt`. `SucceededResultAt.reimports`, `reimports_payload` and `reimports_function_after` recover the original exported payload with its actual handle registry and complete captured references. `RecursiveNamedPublicReturnedValues.returned_value` extracts Source meaning, the reached owned caller, stable histories, heap typing and representation from the same returned semantic result. `header_context_supports` derives transport between the actual Source declaration contexts. `RecursiveNamedPublicReturnedSessionInputs.StartAt.after_succeeded` identifies the next startup with the preceding returned store and world.

`RecursiveNamedPublicReturnedInputs` describes the ordered arguments independently of their native representations. The argument producer combines those descriptions with the previous result and the actual nested encoder. `CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds` consumes the produced arguments in public success/failure reflection and Word preservation. The endpoints retain the reached Source heap, location map, native store, caller relation and complete resulting `ResultAt`. Initialization is not replayed. The immutable global references come from genuine finite inventory membership and the fixed prepared environment.

Both calls currently use the same function model, body registry and receiving registry. The next encoder's genuine extension to that registry remains explicit for metadata-bearing arguments. The exact prior success and semantic result, raw input certificates, valid constructor metadata and supported static body family also remain premises. Between the returned completion and the next startup, the connection permits a finite sequence of actual state-preserving named/builtin issuances.

The returned-input certificate covers one returned function identity, reused any finite number of times alongside data. It does not yet combine several independently exported old handles or mix that returned handle with additional issued function inputs. Arbitrary intervening executions, restored sessions, changes of receiving model/registry, complete static body coverage, broader compiler grammar and final all-pass composition remain unfinished. Progress estimates are unchanged.

The public runtime regression exercises broader behavior: it allocates an independent closure, mutates an older closure, then issues named and builtin handles before passing them together in nested carriers. Two occurrences of the older closure share its current captured state, and duplicate mapping keys select the first entry. The call returns `81`; subsequent calls observe the original capture at `29` and the independent capture at `101`. These are runtime checks for preserved mutation and aliasing. They do not instantiate the narrower theorem for multiple independent handles and arbitrary intervening execution.

Validation: Strict Lean, full build (5978 jobs), all registered tests, kernel policy and independent review passed.

Axiom checks: The twelve checked reimport, returned-state, argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

## Nested function input connection (2026-10-12)

Code commits: `9181cd2b` and `708e3f8b`.

The input boundary includes named and builtin handles at arbitrary finite depth inside products, constructed payload vectors and ordered mapping keys or values. The structural certificates retain the independent Source value, exact raw type, original payload order and mapping duplicates. Empty, singleton and longer constructor payload vectors follow their actual native packing. Comptime wrappers and raw proxy annotations remain distinct in Source typing.

Every function leaf retains a genuine issuance receipt and its actual issuance continuation to the receiving session. Named leaves retain the real inventory packet, full Source instantiation and resolved dictionary. The leaf producer derives the installed capture from the initialized owned state and the builtin callable from accepted preparation. The selected producer constructs leaf meaning internally from these receipts. The generic container fold then follows the original raw encoder through each child registry and composes genuine extensions to the receiving registry. Mapping defaults also follow the actual `encodeDefaultRaw` result, including both present and absent defaults.

The whole argument producer derives representation and deep Source typing at every original index and retains exact Source/native list lengths. The initialized public consumer derives caller, globals and heap conditions from the same fresh bootstrap and finite resumption chain. All three public endpoints retain actual native and staged Source outcomes, complete returned state and the public returned session. The certificates do not supply an argument representation, Source value typing judgment or body execution law.

`Extends encodedValues.registry receiving` remains explicit. Common registry ancestry is insufficient because the receiving metadata must preserve IDs allocated during the original nested encoding. Independent raw typing and valid constructor metadata remain necessary where runtime projection erases Source distinctions. The supported static body family remains an explicit prerequisite.

The runtime fixture passes an outer product containing a constructor with named/builtin payloads and a mapping whose values pair the repeated named handle with a Word. It uses the original earlier named and later builtin handles after reissuance. Duplicate mapping keys select the first row. The result is `71`: `31 + 7 + 31 + 2`. Replacing the named handle with the incompatible builtin is rejected separately in the mapping payload and constructor payload. This fixture checks runtime behavior; instantiation of the semantic endpoints still requires their static body premises.

Validation: Strict Lean, full build (5971 jobs), the focused public runtime regression, all registered tests, kernel policy and independent review passed.

Axiom checks: The eleven checked encoding, leaf, argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

Closure input provenance, restored or previously executed sessions, complete static body coverage, broader compiler grammar and the theorem across all compiler passes remain unfinished. Progress estimates are unchanged. Earlier dated audit sections retain the scope and validation of their original checkpoints.

## Mixed function and data input connection (2026-10-12)

Code commits: `91a42c32` and `8964ff88`.

The new boundary is an arbitrary-length flat argument list containing named handles, builtin handles and handle-free data. Exact raw Source parameter types and argument positions are retained. Data may contain constructors, proxies, products and ordered mappings. Repeated values and duplicate mapping keys are preserved.

The issuance proof follows actual successful named/builtin operations. It covers both reuse of an existing physical slot and append of a fresh slot, and retains the native callable of an earlier handle through later issuance. This authentication transport is separate from the unchanged native state supplied by `SameRuntime`.

The mixed data producer selects the original encoded payload at its actual startup index. It permits neighboring handle arguments and uses the encoder's real final metadata. The ordered structural `Inputs` certificate then assembles complete `Arguments` and deep Source typing. Named entries retain their actual finite inventory packet and complete captured closure; builtin entries retain the actual closed factory code. No supplied function representation, argument relation or body execution law replaces these producers.

The initialized public consumer connects those facts to success/failure reflection and Word preservation, deriving the original caller, global references and heap conditions from fresh bootstrap completion with finite resumption. The result retains actual native and Source outcomes, complete returned state and the public returned session.

The receiving registry extension remains a genuine premise from the actual encoded registry to the body's receiving registry. Raw structural typing is also required for data. Neither a common registry ancestor nor erased native type equality discharges these obligations.

The runtime regression passes an earlier named handle, Word `3`, a `mapping Word Word` with rows `(3, 7)` and `(3, 99)`, a later `wordToInteger` handle and the earlier named handle again. The expected result is `72`; incompatible function-handle order is rejected. The duplicate mapping keys and repeated handle make argument order and earlier-handle retention observable.

Before execution, the test issues the same named handle again after builtin issuance and checks that it reuses the original handle without changing the heap or increasing the handle count. The subsequent call still uses the original issued values.

Validation: Strict Lean, full build (5962 jobs), the focused public runtime regression, all registered tests, kernel policy and independent review passed. Axiom checks: the ten checked issuance, data, mixed argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The boundary remains flat for handles. Nested handles inside data carriers, closure inputs, restored or previously executed sessions, complete static body coverage, broader compiler grammar and the theorem across all compiler passes remain unfinished. The progress estimates are unchanged.

## Singleton named input connection (2026-10-12)

Committed in `be545d01` and `f7c07bf1`.

The named input proof follows the actual issued handle through startup into the initialized owned pool. Accepted factory preparation fixes the signature, specialization, identity, descriptor and cache slot. The finite inventory supplies the actual `Issued` packet and `HasRow` witness. The actual second-pass cache and bootstrap store read identify the installed code and complete captured environment.

Source typing uses that packet's retained instantiation and complete resolved dictionary in the receiving caller's context. Exact raw parameter equality remains a condition; erased native type equality cannot substitute for it. Public success/failure reflection and Word preservation construct the initial caller, heap and argument relations internally and retain the full returned state.

The added runtime regression issues the recursive `recurse` handle after two bootstrap suspensions and passes that exact handle to a singleton `namedUse` root. It checks result `31`, unchanged storage during issuance, and rejection at a root expecting a different function result type.

Validation passes: strict Lean, full build (5959 jobs), all registered tests, kernel policy and independent review. The seven checked named factory, input and public endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`.

This boundary covers a single named handle issued into the fresh initialized runtime. Closure inputs, mixed lists, nested carriers, restored or previously executed sessions, broader static grammar and the final theorem across all compiler passes remain unfinished.

## Issued function and builtin input audit (2026-10-12)

`54bc83a5` preserves the original single issuance operation and binds its cached factory to the actual startup argument index. Review checked deterministic handle resolution and exact state-preservation transport. It does not equate physical handle registries or infer Source function meaning from authentication.

`83bf7430` adds the missing Source meaning for singleton builtin inputs. Preparation supplies literal closed code with empty captures, a nonwrapping identity and the real contract descriptor. The Header supplies exact raw parameter agreement and native projection; actual startup supplies the same issued value. The proof constructs function representation, argument representation and Source typing internally before calling all three public semantic endpoints. Native and Source execution results retain their full state relations.

Strict Lean, full build (5957 jobs), all registered tests, kernel policy and independent review pass. The six selected builtin endpoints use only the standard three axioms. A public runtime regression passes the freshly issued builtin handle into a cached root after two bootstrap suspensions. At this checkpoint, named/closure Source provenance, mixed lists, nested handles and all-pass composition remained unfinished. The newer named connection is recorded above.

## Resumed initialization and data input audit (2026-10-12)

`1ebb4c6a` derives initial completion from any finite chain of genuine public bootstrap suspensions. The consumer retains the exact ready session, original authority and Source prefix, and total fuel. The public execution regression retains two suspension equations and the final ready equation. Out-of-fuel remains a suspension.

`b6c24d8f` connects raw data arguments to the initialized public success/failure and Word endpoints. Review checked the direction of the metadata extension, encoded registry to receiving registry; exact raw proxy and constructor annotations; ordered mapping rows; independent structural input typing; and full returned state. No caller-supplied argument representation or body execution law is introduced. The raw typing and registry extension conditions remain explicit. Their necessity is not discharged by native type erasure or by sharing a static registry ancestor.

The targeted strict builds, public execution regression, kernel policy and independent review pass. All nine selected resumption/data endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The older one-resume limitation below describes the earlier commits.

## Verified initialization-to-public connection (2026-10-12)

Commits `9b6cb2c7` and `6976ab8c` derive the initial conditions used by the supported public consumer. Review followed one fresh bootstrap receipt through its actual ready session and the same startup session. Native completion fixes the full store; store typing fixes the world. The genuine initialization constructor supplies the fixed singleton owner, stable empty history, installed global references and empty Source heap relation.

The original accepted scalar/product encoder supplies argument representation at the body's receiving metadata and deep Source typing, including nested comptime wrappers. Reflection obtains its Source arguments internally. Forward Word preservation matches the independently supplied arguments using the existing interpretation's functionality. No equality between encoding and receiving metadata is assumed.

The three final public endpoints consume these producers and retain staged outcomes, exact native result/store, export session and full `ResultAt`. No supplied initial State, heap law, argument typing/representation or body execution law replaces the connection. Strict Lean checks, full build (5952 jobs), registered tests, kernel policy and independent review pass; all nine checked endpoints use only the standard three axioms.

The new theorem covers a fresh initial bootstrap completed in one resume and `SimplePublic` inputs. It does not yet cover multiple bootstrap resumes, restored/used sessions, handles or metadata-bearing inputs. The latter need a raw Source typing argument beyond accepted runtime projection: retaining an actual proxy's raw inner type can differ from the expected type after comptime erasure. Static family coverage and all-pass composition also remain open. Percentage estimates are unchanged.

## Verified cached-root and public outcome connection (2026-10-12)

Commits `6199f27d` and `a3d8877f` connect real public execution receipts to cached-root proofs. The supported ordinary sequence family constructs its strict recursive body laws internally and reaches the actual named root selected by public startup. Public success/failure reflection retains the native result/store, staged Source application, complete returned heap/caller relation and exact export session. Word preservation reaches successful public export with sufficient native fuel and a positive output budget.

Review checked that each facade operation executes once, the compiled facade's existing constructor remains unchanged, receipt fields are erased, and no body execution law replaces the recursive proof. The proof keeps actual argument packing and optional-cell lookup, exact startup/checkpoint identity, separate body/export metadata receipts, and original staged rejection. The existing named Dynamic evidence path retains its Source admission prerequisites; it is distinct from the staged path.

Strict Lean checks, full build (5948 jobs), all registered tests and kernel policy pass. Independent reviews found no outstanding issue. Checked facade, root and public semantic endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`.

This closes a supported public consumer connection. Initialized owned state/global slots, represented inputs/heaps and genuine static support remain premises. Complete initialization, wider grammar, unrestricted methods/generalized-local bodies and the final theorem across all compiler passes remain open. The 70% / 85% estimates are unchanged; proof counts do not measure this integration.

## Connected ordinary sequence callers (2026-10-12)

Committed in `80a41cf5`. `CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_compiled` and `reflects_compiled` now connect actual preparation and retained compiler recipes to the existing recursive caller/body proof.

For ordinary closure Associations, the consumer obtains its scope from the actual Code, constructs the sequence packet with `choose_for`, and derives call readiness for each used child. It also derives readiness for the accepted caller's exact expression certificate. Both directions use the combined named/anonymous stage registry, including its named branch. The resulting packets and readiness are consumed by `MixedCoveredCallerCompilerBounds`.

Principal Associations retain their original dependent packet/support pair, so method owners are not incorrectly treated as ordinary function owners. Named support, supported sequence grammar, original typing and metadata, retained compiler policy, diagnostic interpretation, and heap/admission conditions remain explicit. This closes a supported caller connection; it does not establish all-program coverage.

The cached-root and public outcome connection is recorded above. Further work prioritizes initialization and compiler coverage for that same family. Generalized-cell drafts remain deferred until a concrete consumer needs them. New helper counts are not used to increase the progress estimate.

Validation: strict Lean compilation, full build, registered tests, repository kernel policy, and independent review pass. Both final theorem axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`.

## Latest verified proof additions (2026-10-12)

| Committed unit | Normal owned declarations / selected interfaces | Exact scoped census |
| --- | --- | --- |
| Compiler roots, support and caller: `d5d5e123`, `02006e66` | 219 / 36 | Newly measured 376 → 595 |
| Constructive support/caller replacement: `db1ab3d2` | 175 / 25; all public interface types retained | 595 → 597; two generated proof additions |
| Concrete compiler factories and discard bodies: `7a321ac5`, `18031d7a` | 360 / 56 | 597 → 957; no removals |
| Retained static witnesses: `87b08905` | 184 / 47 | Expanded explicit scope 1117 → 1182; 43 TYPE changes, 72 additions, seven generated removals |
| Mixed closure bodies/applications: `448ad204`, `333c5d61` | 150 / 28 | 1182 → 1332; no removals |
| Mixed dispatch and recursive caller/body: `a6cb5ab2`, `2f22789d` | 70 / 12 | 1332 → 1402; no removals |
| Accepted caller compilation and ordinary closure factory: `c2d799e7`, `46a03ca1` | 63 / 12 | 1402 → 1465; no removals |
| Ordered discard sequences and propositional coverage: `37b62b0b`, `5d708d56` | 155 / 13 | 1465 → 1620; no removals |
| Original sequence typing and compiler support: `de3c71e5` | 47 / 13 | 1620 → 1667; no removals |
| Production body recipe retention: `1bc5d609` | 325 / 26; all 21 preceding selected interfaces retained | Expanded scope 8635 → 8646; 52 TYPE changes, eleven additions, no removals |
| Sequence bodies and lambda applications: `a0778ccc` | 169 / 27; all 17 preceding selected interfaces retained | 8646 → 8723; seven generated TYPE changes, 77 additions, no removals |
| Retained-recipe factories and original typing: `96a60f2f` | 139 new / 32 | 8723 → 8862; all preceding declarations exact, no removals |
| Contextual compiler policy retention: `806e809c` | 133 / eleven new interfaces | Expanded scope 16679 → 16727; all preceding declarations exact, 48 additions, no removals |
| Prepared policy and canonical call contracts: `23ac1a6c` | 256 selected (247 new) / 31 | 16727 → 16974; all preceding declarations exact, no removals |
| Canonical call readiness and ordinary body exits: `3059a7f5` | 19 new / nine | 16974 → 16993; all preceding declarations exact, no removals |
| Recursive discard-sequence exits: `552dfdfd` | 19 new / four | 16993 → 17012; all preceding declarations exact, no removals |
| Specialization and source-instance foundations: `74b762a7` | 758 selected (118 new) / 21 | Expanded scope 17652 → 17770; all preceding declarations exact, no removals |
| Ordinary specialization coherence and calls: `4f01d1fb` | 570 selected (565 new) / 12 | Scope 17770 → 18335; all preceding declarations exact, no removals |
| Prepared ordinary call provenance: `5b8c8727` | 98 new / 24 | Scope 18335 → 18433; all preceding declarations exact, no removals |
| Ordinary annotation call readiness: `0d7c0a62` | 11 new / 8 | Scope 18433 → 18444; all preceding declarations exact, no removals |
| Applied ancestry and ordinary sequence readiness: `55fe02aa` | 5 new / 5 | Scope 18444 → 18449; all preceding declarations exact, no removals |
| Applied source and runtime materialization: `f0f6a910` | 84 new / 16 | Scope 18449 → 18533; all preceding declarations exact, no removals |

Each unit has actual strict Source checks and complete private/normal literal TYPE/AXIOMS and API comparisons. The preceding sequence typing/support build passed 5902 jobs and rebuilt all four affected modules; all 57 preceding scoped modules retained their literal declarations. The recipe retention build passes 5903 jobs and rebuilds all 355 affected modules. The sequence body/application build passes 5906 jobs and rebuilds all 24 affected modules. The retained-recipe factory build passes 5910 jobs and rebuilds all six affected modules. The policy-retention build passes 5911 jobs and rebuilds all 753 affected modules. The prepared-policy and call-contract build passes 5916 jobs and rebuilds all seven affected modules. The call-readiness and ordinary-exit build passes 5919 jobs and rebuilds all 5 affected modules. The discard-sequence exit build passes 5920 jobs and rebuilds all 3 affected modules. Registered tests and repository policy pass, and unrelated user work is preserved. Supported caller/body recursion is constructed internally. Mixed packets retain the actual ordinary/principal Association parameter context and exact returned caller state. Original full-body typing now supplies every used sequence child's raw type and fixes the terminal's declared result. The accepted child action issues its exact certificate, and readiness remains indexed by that proof. Sequence application joins are now verified for both ordinary and principal Associations. Complete compiler packet coverage and wider grammar remain unfinished; original compiler policy/read facts, raw typing and call authority stay explicit.

The last confirmed historical full census is 20948. After temporary evidence loss, that continuity is unavailable; the current scoped census starts from an authentic new measurement at 376. The seven witness replacements at `87b08905` retain exact Seed/Inventory packets and construct profile existence inside propositions. They intentionally change proof-interface types, with complete private/normal comparison and all 28 protected scoped modules unchanged. The final repository policy check passes with zero findings after the preceding nine findings. This closes the repository policy checks; it does not complete the public all-pass semantics theorem. The runtime/semantic/overall estimates remain 100% / about 70% / about 85%.

## Verified applied source and runtime materialization (2026-10-12)

The four modules in `f0f6a910` connect an actual runtime instantiation of a generalized local closure to its compiler-selected source and lambda header.

Authenticated source ancestry tracks ordinary, lambda and applied views. Closed-scheme matching determines the same substitution lookups as the actual runtime instantiation. Equal substitution lookups preserve complete typed sources, contexts and closures, including the masking of quantified variables. The combined theorem retains the actual produced evidence followed by caller evidence.

Private and normal strict checks have empty logs. The 90 selected declarations and sixteen interfaces agree between private and normal checks. Of those declarations, 84 are new; six imported generated helpers match their existing types and axiom lists exactly. All 18449 preceding declarations retain their complete types and axiom lists; the scope grows to 18533 with no removals. Build 5947 rebuilds all 6 affected modules. Registered tests and repository policy pass.

The runtime theorem still requires the descriptor's authenticated source attachment, captured environment, unique source occurrences and matching scheme and raw type. Producing those conditions at generalized allocation and reading, executing the selected body, broader grammar and the final public semantics theorem remain open.

Each source has actual strict/full/API author results and two independent complete reviews. Declaration counts do not measure semantic coverage.

## Verified applied ancestry and ordinary sequence readiness (2026-10-12)

The two modules in `55fe02aa` connect actual applied-read ancestry to its lexical code owner and construct ordinary discard-sequence call readiness from public preparation.

A sealed applied read and its original code history identify the full owner key. Successful sidecar preparation at that key gives the same guard frame and principal method specialization. The ordinary sequence theorem uses each child's actual compiler certificate and original typing to derive call readiness.

Private and normal strict checks have empty logs. The 5 declarations and five interfaces agree between private and normal checks. All 18444 preceding declarations retain their complete types and axiom lists; the scope grows to 18449 with no removals. Build 5943 rebuilds all 4 affected modules. Registered tests and repository policy pass.

Actual code history, source receipts, original typing and compiler policy remain explicit. General method call readiness, live generalized-local allocation and reading, wider grammar and the final public semantics theorem remain open.

Each source has actual strict/full/API author results and two independent complete reviews. Declaration counts do not measure semantic coverage.

## Verified ordinary annotation call readiness (2026-10-12)

The three modules in `0d7c0a62` derive ordinary call readiness directly from original source annotations. A checked body's result annotation is either unit or its stored statement annotation. Equal original rigid sources therefore recover equal result annotations across independent declarative contexts.

Actual ordinary origins identify the common original function. Accepted concrete replacements recover its rigid source, and annotation agreement gives the same stage analysis and selected guard frame. The prepared scope then inherits canonical call ports without requiring raw range formation for every retained row.

All three private and normal strict checks have empty logs. Their 11 declarations and eight interfaces agree between private and normal checks. All 18433 preceding declarations retain their complete types and axiom lists; the scope grows to 18444 with no removals. Build 5941 rebuilds all 5 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5871 to 5874.

The readiness theorem retains original function typing, actual preparation, full source receipts, exact compiler certificates and the supported compiler policy. General methods, live generalized-local cells, wider grammar and the final public semantics theorem remain open.

Each source has actual strict/full/API author results and two independent complete reviews. All eleven selected names are distinct and absent from the preceding scope. No shared-helper exception is needed. Declaration counts do not measure semantic coverage.

## Verified prepared ordinary call provenance (2026-10-12)

The seven modules in `5b8c8727` connect successful executable-plan preparation to the catalog origin of every retained specialization. Each row comes from an ordinary function request or an actual implementation-method selector. Signature catalog disjointness then identifies the ordinary rows at a function owner.

Authentic paired ancestry preserves canonical source correspondence after erasing requirement IDs. For ordinary functions, the original checked function determines the requirement profiles and recovers equality of the canonical contextual sources. This derives the selected guard frame and transfers the real canonical call ports. A separate theorem combines admissible reached-call metadata with accepted concrete replacements to establish complete catalog type formation for the matched callee.

All seven private and normal strict checks have empty logs. Their 98 declarations and 24 interfaces agree between private and normal checks. All 18335 preceding declarations retain their complete types and axiom lists; the scope grows to 18433 with 98 additions and no removals. Build 5938 rebuilds all 9 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5864 to 5871.

Ordinary call readiness still requires raw replacement formation for the selected owner's retained rows, original typing, full source receipts and genuine compiler certificates. Qualified generalized-local materialization, general method-frame correspondence, wider grammar and the final public semantics theorem remain open.

Each source has actual strict/full/API author results and two independent complete reviews. The 98 selected names are distinct and absent from the preceding scoped inventory. Two generated equation helpers in imported namespaces were also checked against the old normal environment and were absent; they receive no shared-helper exception. Declaration counts do not measure semantic coverage.

## Verified ordinary specialization coherence and calls (2026-10-12)

The three modules in `4f01d1fb` prove that original statement annotations determine body-result summaries across independent declarative contexts. For authentic ordinary specializations, equal complete sources after local substitution recover equal rigid bodies, inferred results and stage analyses. The resulting guard-frame equality transfers canonical call authority to the selected ordinary scope.

All three private and normal strict checks have empty logs. Their 570 selected declarations and twelve interfaces agree between private and normal checks. There are 565 new declaration names; five imported generated helpers match their existing types and axiom lists exactly. All 17770 preceding declarations retain their complete types and axiom lists; the scope grows to 18335 without removals. Build 5931 rebuilds all 5 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5861 to 5864.

The call theorem requires genuine program typing, ordinary specialization origins, complete raw range formation, full source receipts and the original compiler certificate. Arbitrary applied views, implementation-method histories and the final public semantics theorem remain open. Core instructions and runtime behavior are unchanged.

Each selected source has an actual strict/full/API pass and two independent complete reviews. All existing scoped declarations keep their literal types and axioms; the additional names include helpers generated by the mutual annotation proof. Five existing generated helpers are checked separately and excluded from new-name counts. Declaration counts do not measure semantic coverage.

## Verified specialization and source-instance foundations (2026-10-12)

The nine-module foundation in `74b762a7` connects successful executable-plan preparation to the actual specialization receipts for every retained row. Accepted canonical replacements are concrete and contain no flexible variables. Equal local instances of one original source recover its complete rigid instances, including ordered nodes, binders and qualified metadata. Genuine ordinary catalog origins identify the same original checked function. A separate congruence theorem transports successful stage analyses when their actual inputs agree.

All 2505 affected modules pass private strict compilation and rebuild normally. The nine selected strict logs are empty. Their 758 owned declarations and 21 selected interfaces agree between private and normal checks. Of those declarations, 640 already belonged to the existing specialization checker; 118 names are new. The expanded baseline includes that checker's existing declarations, and the scoped census grows from 17652 to 17770, with every old type and axiom list exact and no removals. Build 5928, registered tests and repository policy pass. The normal source/object inventory grows from 5853 to 5861.

Concreteness does not establish nominal catalog membership or arity validity. These foundations do not yet derive every selected stage frame or the public all-pass semantics theorem. General method identity, complete formation coverage and broader grammar remain open. Core instructions and runtime behavior are unchanged.

Each selected Source has an actual strict/full/API pass and two independent complete reviews. The literal migration audit covers the measured 772-owner scope, including the changed checker; the wider compilation cone is not a complete ownership census. Existing checker computation is retained byte-for-byte before the appended proof.

## Verified recursive discard-sequence exits (2026-10-12)

The module in `552dfdfd` connects both preservation and reflection for supported recursive discard sequences to their exact exits. Ordinary returned values and semantic faults carry the reached lexical exit. Stage rejection retains its original scope, call, reason, context and prefix heap. The strict child laws are constructed inside the proof.

Private and normal strict checks have empty logs. All 19 selected declarations and four public interfaces agree literally between private and normal checks. The scoped census grows from 16993 to 17012; every preceding declaration keeps its full type and axiom list, with no removals. Build 5920 rebuilds all 3 affected modules. Registered tests, all 38 Tests.Main declaration blocks and repository policy pass. The normal source/object inventory grows from 5852 to 5853.

The result still requires genuine compiler packets and support for the selected closure and named bodies. Broader grammar, complete formation coverage, selected-frame correspondence and the final public theorem across all compiler passes remain unfinished.

The Source has actual strict/full/API author checks and two independent complete Source reviews. Existing declaration, axiom and import checks remain in force.

## Verified canonical call readiness and ordinary body exits (2026-10-12)

The three modules in `3059a7f5` construct call readiness at the canonical invocation of the same generated Code. The proof recovers the original supported grammar from the compiler certificate, follows each actual call occurrence and combines original typing with the retained compiler policy.

The staged body projection preserves ordinary returned values, fallthrough and semantic faults with their exact stopping context and heap. Genuine map/world growth and heap metadata construct the lexical exit used by the existing body consumers. Stage rejection keeps its separate semantics.

All three private and normal strict checks have empty logs. Their 19 new declarations and 9 interfaces agree literally between private and normal checks. All 16974 preceding scoped declarations retain their complete types and axiom lists; the scope grows to 16993 without removals. Build 5919 rebuilds all 5 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5849 to 5852, and all 38 Tests.Main declaration blocks remain exact.

The call-readiness theorem still requires original metadata, source provenance, occurrence uniqueness and the actual compiler certificate. Other selected invocation frames need their own correspondence proof. Complete formation coverage, broader grammar and the final public theorem across all passes remain unfinished.

Each module has an actual strict author pass, complete owned/API audits and two independent Source reviews. Existing declaration, axiom and import checks remain in force.

## Verified prepared policy and canonical call contracts (2026-10-12)

The five modules in `23ac1a6c` derive supported compiler policies from the retained callbacks and original metadata conditions. Ordinary and principal formations carry the same policy through recapture and prepared qualification. Original root typing supplies the raw parent type at each compiler-issued nested call. The actual Code selects its canonical sidecar and call contract.

All five private and normal strict checks have empty logs. Their 256 selected declarations and 31 new interfaces agree between private and normal checks. Nine existing generated helpers appear in the selected-only audit; their complete types and axiom lists match the preceding scope. There are 247 genuinely new declaration names. All 16727 preceding scoped declarations retain their complete types and axiom lists; the scope grows to 16974 with no removals. Build 5916 rebuilds all 7 affected modules. Registered tests and repository policy pass, and the normal source/object inventory grows from 5844 to 5849. All 38 Tests.Main declaration blocks remain exact.

The call contract proof covers the canonical invocation selected from the same Code. Other selected invocation scopes still need their stage-frame correspondence. Global metadata conditions, complete formation coverage, broader grammar and the final public all-pass theorem remain unfinished.

Each module has a strict author pass, a complete owned/API audit and two independent Source reviews. The additive integration retains the existing declaration and axiom checks.

## Verified contextual compiler policy retention (2026-10-12)

The three modules in `806e809c` retain the actual contextual compiler policy together with the body recipe, named compilation and generated Code. The receipt records initializer overrides, evidence, local reads and the original fuel choices. Generation and producer projections preserve this same witness.

All 753 affected modules pass private strict compilation and rebuild normally. The three selected normal strict checks have empty logs. The selected modules own 133 declarations and expose eleven new interfaces. All 16679 preceding scoped declarations retain their complete types and axiom lists; 48 declarations are added and none are removed. All 16727 complete private/normal declaration blocks and the API logs agree. Build 5911, registered tests and repository policy pass. The normal source/object inventory grows from 5843 to 5844, and all 38 Tests.Main declaration blocks remain exact.

The wider baseline includes existing dependencies; its growth from the preceding 8862-declaration scope does not measure new semantic coverage. Policy profiles, formation coverage, original typing, supported grammar and exact call readiness still need to be composed. The final public all-pass theorem remains incomplete.

Each selected module has an actual author pass and two independent Source reviews. Both independent migration reviews check the unchanged preceding declarations and the complete added interfaces.

## Verified retained-recipe factories and original typing (2026-10-12)

The four Sources in `96a60f2f` construct discard and sequence packets from the retained production recipe of the actual Code. Both ordinary and principal Associations retain their named compilation and body context. Original closure typing supplies parameter declarations and per-scope typing conditions.

All four private and normal strict checks pass with empty logs. Their 139 new declarations and 32 interfaces agree literally; all 8723 preceding scoped declarations retain their complete types and axiom lists. The scope grows to 8862 without removals. Build 5910 rebuilds all six affected modules, and registered tests and repository policy pass with zero findings. The normal Source/BOTH snapshot grows from 5839 to 5843. Unrelated user work is preserved.

Compiler policy, captured declarations, supported grammar and readiness at the exact issued calls remain genuine static obligations. Complete production coverage and the public all-pass theorem remain unfinished.

Each Source has an actual author pass and two independent Source reviews before integration. Every declaration in the preceding 362-module scope remains exact.

## Verified sequence body/application migration (2026-10-12)

The five Sources in `a0778ccc` connect real sequence receipts to the existing closure entry, application and caller-restoration proofs. All 24 private dependent-module checks pass; the five selected private and normal strict logs are empty. Both independent Source reviews and complete migration reviews are recorded before installation.

The scope grows from 8646 to 8723 with 77 additions and no removals. Of seven changed complete TYPE blocks, three are alpha-identical and four add exactly one sequence-branch binder to generated eliminators. All common AXIOMS lists remain exact. The 17 preceding selected interfaces and all 38 Tests.Main blocks remain unchanged.

All 8723 complete TYPE/AXIOMS blocks agree between private and normal checks, and the 27-interface API logs are byte-identical. Build 5906, registered tests and repository policy pass with zero findings. The normal Source/BOTH inventory grows from 5836 to 5839. Existing user work remains unchanged. This closes sequence application composition; complete production coverage and the public all-pass theorem remain incomplete.

## Verified production recipe migration (2026-10-11)

The changes in `1bc5d609` retain actual body-lowerer identity through ordinary/principal formation and provenance. All 355 affected modules pass private strict compilation and are rebuilt normally. The nine selected Sources pass normal strict checks with empty logs; they own 325 declarations and expose 26 checked interfaces.

The expanded baseline owns 8635 declarations and the resulting scope owns 8646. Review covers all 52 intentional TYPE changes, eleven additions and zero removals. The expanded scope includes existing declarations; it does not measure additional semantic coverage. All 8646 complete TYPE/AXIOMS blocks and API logs agree between private and normal checks. The 21 preceding selected interfaces remain exact.

The audit retains zero-declaration module rows and complete multiline AXIOMS blocks. Only the exact eighteen previously measured test axiom Names are admitted under `Tests.Main`; all 38 test-owned blocks are identical across baseline, private and normal checks. Proof Sources retain the standard three-axiom policy. Build 5903, registered tests and final repository policy pass with zero findings. Production packet coverage and the public all-pass theorem remain incomplete.

## 1. Feature migration table

Coverage is measured against `ExpressionForm`, `StatementForm`, and `ForItemForm` in `SourceInference.TypedIR`, together with the old runtime's values and public boundary.
The target is the closed roots and finite plans supported by the compilation and execution boundary, rather than every source program accepted by the type checker.
Tests that pass modified carriers to `runTrusted` do not establish what the public boundary accepts.

### 1.1 Expressions and values

| Subject | Behavior to preserve | Initial Core approach | Implementation and test references |
| --- | --- | --- | --- |
| `literal` | Convert the natural number denoted by the literal to Word by modular reduction. | Existing Word constant. | `LiteralConstructs`, `WordLiteral`, `evaluate`. |
| `integerLiteral` | Construct Word or Integer according to the resolved type and Int evidence. | Word constant / Integer representation to be selected after comparison. | `ResolvedIntegerLiteralConstructs`, `validateIntegerLiteralResolutionWith`. |
| builtin boolean reference | Return a Bool value. | Bool constant. | `builtinBoolean` in `evaluate`. |
| local reference | Read a cell by stable local ID and observe subsequent updates. An uninitialized mapping can be read as empty. | Local ID → Core binder / cell correspondence. | `initialRootValue`, `testClosuresOrderProxyAndFuel`. |
| declaration reference | A first-class function with the exact generic instantiation and evidence. | Function-table reference and required dictionary values. | `testConstrainedGlobalValue`, `testPredicateReordering`. |
| builtin function reference | Retain a builtin as a first-class value. | Typed Core function value. | `applyBuiltin`, `BuiltinFunctionId`. |
| `group` | The same value and effects as the enclosed expression. | Lower the enclosed expression. | `ExpressionFormEvaluates.group`. |
| `tuple` | Evaluate left to right and construct the same product tree with `Value.pack` / `ValuesPack`. | Existing pair/unit. | `testNestedMatchingAndCalls`. |
| `unary` | Bool not, Word / Integer bit-not, or a method selected by evidence. | Core primitive or compiled method call. | `applyUnary`, `executeUnaryOperatorMethod`. |
| `binary` | Word / Integer operations and comparisons, selective equality, short-circuiting, and selected trait methods. | Core primitive / branch / method call. | `applyBinary`, `testSelectedOperatorMethods`. |
| `conditional` | Evaluate the condition, then only the selected branch. | Core if. | Conditional rule in `ExpressionFormEvaluates`. |
| `lambda` | Capture cell locations and evidence from that activation, rather than a snapshot of their values. | Core lambda / generated function with captured cell references. | `testGenericRecursiveClosure`, `testRecursiveClosureSelfCellAndEvidence`. |
| direct call | Enter the type-specialized declaration body, including recursive and mutually recursive calls. | Function-table reference and call. | `testNominalConstructionAndRecursiveCalls`. |
| builtin call | Preserve the 7 builtins below, their types, and argument order. | Primitive or small Core function. | `applyBuiltin`. |
| indirect call | Callee, arguments, argument-bundle coercion, body, then result coercion. | apply and explicit coercion calls. | `testIndirectArgumentCountMetadata`, `testIndirectEndpointMetadata`. |
| `constructor` | Nominal identity, type arguments, payload order, and payload types. | Closed source type → Core data ID; relax payload restrictions. | `testNominalConstructionAndRecursiveCalls`, `testNominalInputValidation`. |
| `member` | Return the selected payload from a base evaluated once. | Core data decomposition and projection. | `ValueAt`, `updateResolvedValue_member_*`. |
| `proxy` | Identify the retained closed type. Proxy keys of the same type match. | Type tag that does not interpret source `Ty`. | `testGenericProxyMappingKey`. |
| `index` | Evaluate the base before the key. Return an existing entry's value, or the value type's default if absent. | Entry sequence represented by Core data, with ordinary lookup/update functions. | `MappingLookup`, `DefaultValue`, `testAssignmentsMappingsAndControl`. |
| locally polymorphic lambda | Instantiate a single principal initializer at each use site. All instances share the same captured cells. | A set of monomorphic code instances with a shared environment. | `testLocalLetPolymorphism`, `testContextualLocalGenericCalls`. |
| qualified locally polymorphic lambda | Relate template requirements to concrete use-site evidence. | Instantiated code and dictionaries. | `testQualifiedLocalLetPolymorphism`, `testQualifiedLocalAliasEscape`. |
| expression output coercion | After obtaining the raw value, execute methods in the recorded order and retain their effects. | A chain of typed functions. | `executeCoercionPath`, `testStatefulCoercionMethod`. |

The builtins are `integerSub`, `wordFromInteger`, `integerAdd`, `integerEq`, `integerLt`, `integerMul`, and `wordToInteger`.
Word → Integer produces a nonnegative mathematical integer. Integer → Word reduces modulo `2^256`, including negative inputs.
Word and Integer division and remainder return 0 for a divisor of 0. Do not introduce a new division-by-zero failure.
Integer bitwise operations follow infinite two's-complement behavior. Fix their correspondence with Lean's signed division and remainder operations as well.

`valueEqual` is not a general decision procedure for equality of all values. Closures and mappings are not comparable values.
Do not replace equality for global / builtin functions, proxies, nominal payloads, and products with a comparison of outer Core type tags.

### 1.2 Statements, scope, and heap

| `StatementForm` / related feature | Behavior to preserve | Migration target and checks |
| --- | --- | --- |
| `letDecl`, without initializer | Allocate a fresh cell. Reading an uninitialized non-mapping cell fails. | Explicit uninitialized representation such as `cell (sum unit T)`. |
| `letDecl`, with initializer | Allocate a fresh cell after the initializer's effects. | Relation between `Heap.Allocates` and Core allocation. |
| generalized let | Create the principal descriptor once and instantiate it at each use site. | Do not equate a descriptor cell with a single monomorphic cell. |
| `returnStmt` | Return a value or unit; do not execute the remaining statements. | Returned branch of a typed control result. |
| `expression` | Execute effects. An expression without a semicolon at the end of a function is an implicit return. | Final-statement rule in `executeFunctionSequence`. |
| `assignValue` | Resolve the target and evaluate indices, then evaluate the RHS, then update the target. | See the evaluation-order table below. |
| compound assignment | `+= -= *= /= %= &= ^= \|=`. Distinguish the value selected during target resolution from the root at write time. | `assignmentBinary?`, `ResolvedPlace.selected`, `updateResolvedValue`. |
| `assignBitNot` | Apply bit-not to the resolved place's current value. There is no RHS. | `SourcePlaceBitNotExecutes`. |
| `ifThen` | Execute only the branch selected by the condition. The else branch is optional. | Distinguish fallthrough from return. |
| `block` | Restore lexical names. Retain allocated cells for closures that capture them. | Relate environments and heaps separately. |
| `matchWith` | Evaluate the scrutinee once; handle the hidden binding, arms in source order, pattern bindings, and default. | Constructor / tuple / binder / literal patterns. |
| `whileLoop` | Condition → body. continue returns to the condition; break exits the loop. | Generated recursive function and control result. |
| `forLoop` | Initializer → condition → body → post. continue also executes post. | Handle every let / expression / assign / bit-not form in `ForItemForm`. |
| `breakStmt` / `continueStmt` | Consumed by the innermost loop; cannot escape the function. | Loop-control typing and correspondence of runner outcomes. |
| recursive closure | Allocate the function cell first, then store a closure that captures that cell. | Core safety for self-cells and mutual sharing. |
| mapping update | Resolve the index path once, reconstruct inner values, and update the root cell. | Do not turn mappings into new shared reference objects. |

The old heap is a sequence of cells with a type and `Option Value`. Closures capture cell locations.
Mappings, nominal data, and products are value structures; do not unconditionally turn them into shared mutable objects.
New mapping entries are appended; replacing an entry preserves its original position.

## 2. Evaluation-order contract

| Construct | Order |
| --- | --- |
| tuple / constructor / argument list | Left to right in source order. A fault or fuel exhaustion returns the heap at that point. |
| direct call | Validate metadata for the synthetic declaration callee, evaluate arguments, then enter the body. The synthetic reference introduces no extra effects. |
| indirect call | Callee → arguments → pack → coercion of the argument bundle → unpack → body → expression output coercion. |
| strict binary | Left → right → primitive or selected method. |
| logical and / or | Do not evaluate the right operand if the left determines the result. |
| conditional / if | Condition → the single selected branch. |
| indexing | Base → key → lookup or default. |
| assignment | Resolve root / projection indices → RHS → reread current root → update path → write root. |
| compound assignment | Use the leaf selected after target resolution and before the RHS as the operation's left operand. Structural writeback uses the latest root after the RHS and preserves unrelated changes. Do not reevaluate resolved indices. |
| coercion path | Pass each stage's result and heap to the next. Retain method side effects. |
| match | Scrutinee → hidden binding → arm selection → binder allocation → body. |
| for continue | Move from the body to post, then back to the condition. |

Assignment proofs must not identify the heap used to resolve the place with the heap after the RHS.
Carry the `ResolvedPlace.selected` snapshot forward: the operation uses the old leaf, while reconstruction uses the new root.
Retain `assignmentOrder` from `testClosuresOrderProxyAndFuel` and the state-interaction coercion cases as regressions.

## 3. Outcome and failure classification

This classification preserves failure meaning and state, rather than requiring exact diagnostic names.
Every constructor of the runtime's `RuntimeError` at the time must map to one of these categories during migration.

| Category | Examples | Treatment at the new boundary |
| --- | --- | --- |
| Specified source failure | Uninitialized read of a non-mapping local; mapping read / projected update with no available default. | Typed trap or specified failure result. Preserve effects before failure. |
| Invalid program / plan | Missing / duplicate specialization, ownership errors, noncanonical plan, missing / duplicate call/reference edge. | Reject during compilation. Do not call a solver or worklist during Core execution. |
| Invalid typed metadata | Indirect arity / endpoint, declaration mismatch, malformed literal/pattern, result type mismatch. | Make unreachable from checked lowering; reject forged carriers at the boundary. |
| Invalid evidence | Duplicate / missing requirement, goal mismatch, selected implementation mismatch, local scheme template/actual mismatch. | Reject in compilation-plan and external function-handle validation. |
| Stage constraint | Runtime-dependent comptime argument, invalid stage of a comptime result, unsupported staged input. | Preserve the existing accepted scope and distinguish compile/input rejection from source failure. |
| Invalid external value / heap | Dangling cell, nominal payload mismatch, forged closure code/evidence, handle from a different artifact. | Reject before execution; leave the initial heap unchanged on rejection. |
| Insufficient compilation resources | Specialization / method-frontier budget, executable-plan closure fuel, comptime depth. | Compilation outcome; separate from runtime outOfFuel. |
| Insufficient input-validation budget | `inputValidationFuelExhausted` and similar errors. | Validation outcome; separate from execution fuel. |
| Insufficient execution budget | `outOfFuel`. | Preserve typed machine state and continuation. |
| Defensive internal runtime diagnostic | expectedBool / Function / Product, invalid primitive, controlEscapedFunction, deep final-state rejection. | Prove these cannot arise from valid artifacts and inputs. Revisit classification if a legal reachable example is found. |

### 3.1 Known specification gaps

`SourceSemantics.Dynamic.Fault` has positive fault derivations. Its current description alone does not establish determinism or complete failure coverage for every well-formed execution.

When a mapping entry is absent and its value type has no default, the old evaluator returns `typeMismatch valueType none`.
For expression indexing, `SemanticFault.missingMappingDefault valueType` and
`ExpressionFormFaults.indexDefaultUnavailable` were added. Successful evaluation of the base and then the key, the key's type,
`MappingAbsent`, and the absence of an independent `Defaultable` derivation produce a fault with the heap at that point.
The observation correspondence is `missingMappingDefault valueType` → the old `RuntimeError.typeMismatch valueType none`.
No restriction was added to type checking of mappings with non-defaultable value types.
`Solcore/Test/SourceMappingDefaultFault.lean` checks an empty mapping of function values, the heap after evaluation,
and matching diagnostics from the old default computation and projected update.

Independent rules were also added for place reads and updates:

- `ProjectionsFaults` in `Dynamic/Place.lean` is a pure path failure restricted to missing defaults. It explicitly records each index's type check and the successful prefix through existing entries, defaults, and members.
- `ProjectionsFaults.excludes_read` and `excludes_update` prove incompatibility with a successful read or update of the same root and path. `ProjectionsUpdate.readable` shows that a successful update implies readability of the leaf on that path.
- `SourcePlaceFaults.projectionRead` reads the current root in the heap **after evaluating all index expressions** and derives a pure path fault. It returns the post-index heap; the RHS has not yet been evaluated.
- `SourcePlaceAssignmentFaults.structuralUpdate` derives a fault from the **latest root** after successful target resolution and RHS evaluation, returning the post-RHS heap unchanged. It checks that the root type matches. Structural traversal precedes the leaf modifier, so a missing default is observed first even if the operation on the old selected leaf would fail.
- `SourcePlaceAssignmentFaults.operands` requires a latest-root read, matching type, initialized value, and successful path read. It does not skip structural traversal to derive an operand fault. In the missing-default case, the exclusion lemma prevents the read premise for the same root/path.
- BitNot has no intervening RHS. `SourcePlaceResolves.excludes_projection_fault` proves that a missing default cannot newly arise after successful target resolution in the same post-index heap. No unreachable additional fault constructor was introduced.

Regression proofs check successful index/default/member prefixes, preservation of post-index / post-RHS heaps, structural faults preceding invalid snapshot operands, and read/update exclusion.
They also check that the actual `updateResolvedValue` and `writeResolvedPlace` return the existing `typeMismatch valueType none` before calling any leaf modifier, without changing the heap. This includes prioritizing the missing default even when a modifier explicitly returns `invalidAssignmentOperands`.
The new source rules and regression proofs passed a combined Lean check in a temporary file without updating shared artifacts. Ordinary module builds are deferred to integration validation.

The following specification gaps remain separate:

- Invalid projection shapes, wrong key types, out-of-range members, post-RHS uninitialized roots, dangling locations, root-type mismatches, and failed type checks of leaf / rebuilt-root values are outside this pure path-fault relation.
- The existing success relation `ProjectionsRead` itself does not require the index key type. Adding a read premise to the operand fault does not cover the runtime's type checks for arbitrary invalid keys.
- The new rules derive faults from explicit successful prefixes. They do not collectively establish complete failure coverage, determinism, first-fault agreement, or reachability from the checker for all well-formed source programs.
- The current `ValueRuntimeType` and index key-type fault rules compare source types directly.
  Agreement with the old runtime's recursive comptime erasure is a separate obligation; the unstaged Word-key regression does not supply it.

The old `RuntimeBoundaryAccepts` is a small unit/bool/word/product residualization boundary, rather than an admission test for general source values.
Passing the new Core Integer, mapping, closure, and nominal values through it unchanged would incorrectly produce stagingViolation.

Removal criteria include regression checks of legal failures, their classification, evaluation order, and heaps up to failure, in addition to successful examples.
When source rules and the old evaluator disagree, record the difference, its language-level justification, and compatibility implications rather than defining semantics directly from old behavior.

## 4. Actual public-input scope

Inspect `runWithValidationFuel` and `runDeepCertifiedWithValidationFuel` separately.
The latter checks shallow input validation, the prepared plan, the deep initial heap, and deep arguments, then rechecks the heap/value of successful results.
The guarantee is stronger than equality of the outer `Value.type?` tag.

- `Value.validateTypeFuel` checks nominal declarations/payloads, products, mapping entries, and proxy types.
- External function arguments currently have global / builtin branches. Do not assume arbitrary lexical closures are already accepted as public arguments.
- Closures created during execution or present in the initial heap participate in deep checks of code provenance, capture cells, and evidence.
- The old `runTrusted` differs from the public boundary. Do not automatically promote trusted-only tests of forged inputs into new API feature requirements.
- New API input certificates tie the code table, nominal table, store typing, references, and evidence to the same artifact.
- Function handles must preserve the existing public-input admission scope. Accepting arbitrary external closures is not required by this migration.

Provide a theorem deriving the relation's initial conditions from successful public validation, rather than merely requiring external callers to assume them.
Conversely, do not require every hand-written Core value without source provenance to have a corresponding source value. Keep the contracts of standalone Core APIs and source-compiler APIs distinct.

## 5. comptime and retained evaluation

The following direct evaluation can remain separately from the runtime interpreter being removed:

- `SourceCoreElaboration.evaluateStagedInteger*`, `evaluateStagedWord*`, and `evaluateStagedBool*`.
- `SourceCoreElaboration.evaluateStagedValue*` and statement / binding helpers.
- `SourceCoreDirectLinking.evaluateStagedIntegerFunctionFuel` / `evaluateStagedValueFunctionFuel` and staged callbacks for selected methods and coercions.
- The unit/bool/word/product carrier of `SourceStagedValue` and its reification into Core.

`SourceStageAnalysis` is a sidecar classifying occurrence stages, rather than a residualizer with a proof of execution meaning.
The final theorem targets **admitted TypedSource before specialization and pre-evaluation**.
Required proofs cover correspondence of actual pre-evaluation with source evaluation, constant embedding, branches/short-circuiting, effects, erased staged cells, and the runtime heap.
Intermediate lemmas may assume `StagingCorrect`; the final theorem must supply that proof from success of the actual pass.

Do not retain runtime stage validation from the typed runtime, together with its runtime AST interpreter, merely by renaming it comptime.
Complete evidence resolution and helper-frontier construction for compilation plans during compilation as well.

## 6. Representation and proof contract

### 6.1 Representation relations

`Representation` includes at least type instances, Core code IDs, local lambda instances, and a correspondence between source locations and Core cells.

- Extend the relation on allocation without relocating existing locations or breaking aliases.
- Do not require a one-to-one correspondence for source descriptor cells, erased staged cells, and Core administrative cells.
- Relate nominal payloads and mapping entries structurally.
- A generalized closure may correspond to multiple monomorphic Core code instances, but they share the captured mutable cells.
- The closure relation requires registered code and its corresponding capture environment, rather than mere function-type equality.
- Initially represent monomorphic locals with explicit cells wherever possible. Consider eliminating unnecessary cells after proving the correspondence.

General Core safety is stated under code table `Δ` and store typing `Σ`.
cellRef checks its type in `Σ`; separately typing the store, including closures, under the same `Σ` supports cyclic heaps.
Type preservation does not require a definition that recursively traverses heap contents without bound.

### 6.2 Initial premises of the final theorem

```text
compile(S, entry) = Ok C
SourceAdmitted(S)
EntryValid(S, entry, sourceInputs, sourceHeap)
ProgramRel(S, C, R0)
InputRel(R0, sourceInputs, sourceHeap, coreInputs, coreStore)
```

`ProgramRel` is a separate proof result constructed from compilation success and admitted source, rather than a hole requiring the caller to assume meaning preservation.
It records definition provenance and structural correspondence of types, specialization, and code, rather than equality of final execution results themselves.
Construct the required typed-input / store conditions from successful public input validation.
Keep proofs for the entire raw parser / resolver separate from the main lowering theorem. Record remaining source-checker bridge premises as unfinished until their actual proofs exist.

### 6.3 Preservation and reflection of finite observations

For normal completion in both directions, existentially quantify an `R1` extending the same initial relation `R0`.

```text
SourceEvaluates(S, entry, sourceInputs, sourceHeap, v, H)
  → ∃ fuel, vC, HC, R1,
      Extends(R0, R1)
      ∧ CoreRun(C, coreInputs, coreStore, fuel) = Done(vC, HC)
      ∧ ValueRel(R1, v, vC) ∧ HeapRel(R1, H, HC)

CoreRun(C, coreInputs, coreStore, fuel) = Done(vC, HC)
  → ∃ v, H, R1,
      Extends(R0, R1)
      ∧ SourceEvaluates(S, entry, sourceInputs, sourceHeap, v, H)
      ∧ ValueRel(R1, v, vC) ∧ HeapRel(R1, H, HC)
```

Relate specified faults and their heaps in the same way.
Translate failure reasons containing source locations through `R1` and the diagnostic map rather than requiring raw index equality.
Prove absence of internal MachineFault for arbitrary finite fuel, type preservation of suspended states, and resumption with additional fuel in the Core layer.

This correspondence of finite observations in both directions does not require new source small-step semantics.
It prevents compilation from introducing divergence for terminating source executions or normal completions absent from the source.
It does not automatically establish equivalence of infinite traces, overall source progress, or correspondence with a source prefix leading to outOfFuel.

### 6.4 Completion checks against circular premises

- Source semantics must not define results using the old evaluator or generated Core.
- Compilation success alone must not define source validity.
- Plan replay equality must not substitute for complete dynamic reachability coverage.
- Core checker success must not substitute for meaning preservation.
- The outcome relation must not be so weak that lowering can discard an entire admitted program.
- Do not relate every scalar to the same value. Function values must constrain code and captures.
- Do not leave unproved `StagingCorrect` / `SpecializationCorrect` or caller-supplied simulation in the final theorem.
- Check success/fault exclusion, required determinism, and rules for reachable legal faults over the target scope.

## 7. Dependencies of the Core safety change (initial implementation record)

Dependencies found at the start of the audit and their state after general-cell admission was implemented:

- `CellPayload` remains as a first-order helper predicate, but was removed from the premises of `HasType.newCell/loadCell/storeCell` and the executable checker.
- `ConstructorPayload` corresponds to general `Ty.WellFormed`, allowing functions and general cells.
- The pure machine's `StateHasType` and finite `evaluation_preserves_type` use `RuntimeStoreHasTypes`. `BoundedSafety` covers world extension and typing of suspended states and completed values.
- `ReducibleValue` / `ReducibleEnvironment` and the unconditional normalization proof were removed from `Core.Safety`. Completion and sufficient-fuel APIs for closed/Program execution require finite `Evaluates` evidence.
- The sufficient-fuel API of `ContractRuntime.CheckedCoreProgram` also requires finite evaluation evidence. Guarantees for arbitrary fuel use bounded safety and resumption.
- The old `StoreHasTypes` remains in conditions for first-order input and exact-store lemmas. General heap correspondence with changing closure captures does not require literal equality of final stores.
- Full builds and tests validated the corresponding changes to host state, frontend, ContractRuntime, and existing Core Wire. Language-trap propagation and validation of the new public input format remain unfinished at this point.

Individual Lean checks of `CoreGeneralCells` proved checker acceptance of a program that constructs a self-referential closure from an empty store, a 7-step cycle, absence of finite successful evaluation, and typed suspension/resumption for all fuel.
The example uses a `Unit → Unit` cell with a placeholder initial value, so it does not resolve uninitialized cells or a general source-recursion representation.
`CoreRecursiveCells` also checks terminating self-recursion and mutual recursion, use as a function argument, a counter shared across calls, returned references and captures, exact fuel, and typed resumption.
Uninitialized cells, recursive initialization for arbitrary source types, and language traps remain; T1 is unfinished at this point.

## 8. Scope of the first proof unit

New module: `Solcore/SourceSemantics/CoreLowering/StagedValue.lean`.

The implemented small scope covers:

- Interpretation of existing `SourceStagedValue.Value` as an independent source value.
- The scalar/product source–Core representation relation, its range, and uniqueness.
- Source-value typing under arbitrary source heaps and contexts.
- The actual `toCoreExpr` returning the corresponding value without changing any Core store.
- Preservation and reflection of that declarative execution, and completion/reflection for execution with fuel.

This proves correctness of **staged-value reification**.
It does not prove that the staged evaluator computed the value correctly, or correctness of arbitrary source-expression lowering, shared heaps, recursion, or failure.
Reuse it as the first connection between independent SourceSemantics and the existing implementation.

Validation: `lake env lean Solcore/SourceSemantics/CoreLowering/StagedValue.lean` succeeded.

## 9. Actual lowering from literal trees

Added module: `Solcore/SourceSemantics/CoreLowering/Literals.lean`.
Internal proof wrappers and computation rules for unit / Bool / Word / pair were added to existing `SourceCoreElaboration`, reusing its expression traversal unchanged.
No new lowering algorithm or public source API was introduced.

`Literals.Tree` is an independent finite-tree grammar for actual source occurrences.
It includes empty tuples, builtin Booleans, compatibility Word literals within range, and recursive combinations of two-element tuples.
It requires exact type information for every node, empty requirements / coercions, and global occurrence uniqueness.
The Word premise matches existing strict lowering; agreement with the source's modulo semantics was separately proved for values within range.

The proofs establish:

- With sufficient traversal budget, the existing expression lowerer and `Resolved.Expr.lower?` actually return the corresponding Core expression.
- Core checker success for that output.
- Construction of an independent `Dynamic.ExpressionEvaluates` derivation, with the same value and final heap for every successful derivation of the same source tree.
- Correspondence in both directions between the actual generated Core expression and finite successful source results, without changing either heap/store.
- Sufficient execution fuel from finite source evaluation, and reflection of source evaluation from a completed Core execution.

Compiler success is not a grammar premise. Evidence for `ExpressionLowers` is constructed before composition theorems that assume it.
General source determinism, staged-evaluation correctness, and source-inference soundness are not used as unproved assumptions.
This scope does not cover general expressions, Integer literals, groups, arbitrary tuple arity, shared cells, failures, staging computations, or whole-function lowering.

Validation: the affected Lean files, `lake build`, `lake test`, and the kernel-policy check succeeded.
The lowering-proof umbrella is registered in `Tests/Main.lean`; the independent specification umbrella does not import the frontend.

## 2026-10-01: Grouped root-tuple observation mismatch and approved fix

At the time of this investigation, the parser/checker and explicitly selected typed-source compiler accepted the following program.

```solidity
function main(left: Word, right: Word) returns (Word) {
  match ((left, right)) {
    case ((x, y)) { return x; }
    default { return 99; }
  }
}
```

For inputs 7 and 8, the old evaluator returned 99. The validation log is
`/private/tmp/solcore-grouped-tuple-runtime-audit-2.log`.
The tuple branch of `SourceTypedRuntime.matchPattern` reads elementCount only when `pattern.source` is directly `.tuple`; it uses 0 for `.group`. Unpacking the tuple value fails and selects the default arm.

Independent SourceSemantics treats groups transparently, so this match binds x=7 and y=8 and returns 7.
On 2026-10-01, the user approved aligning the implementation with the independent semantics. The new Core lowerer recurses through groups, and the old runtime also reads tuple arity through groups. The old runtime's internal nested-pattern search bound was changed to 2 times the instruction count + 1.

At the time, `Test.SourceCoreGroupedTuple` checked multiple parentheses, nested tuples, Unit, literal arm selection, and side effects using actual checked programs in both Core and the old runtime. Registered tests now use public and internal Core paths. Repeated Core execution and resumption from a zero-fuel checkpoint were also checked. `DataPatternCertificates` and `Test.SourceCoreDataPatternProofs` prove static extraction of grouped roots, independent PatternMatches, finite execution of authenticated binder values, and reflection. The log is `/private/tmp/solcore-grouped-tuple-fixed-run-4.log`. No change to checker/staging acceptance conditions was needed.

## 2026-10-01: Additional audit of staging and public closure boundaries

`SourceCoreStageContracts` authenticates original analyzer outputs and parameter/result flags for named, lambda, and contextual-lambda functions. `SourceCoreStageCodebook` assigns a contract ID to each owned origin and preserves the existing validator's decision at each indirect callsite. The ID is independent of function identity.

The old indirect execution order is callee → stage guard → arguments/coercions → applyCallable arity check → parameter allocation → body. An effectfulStaging caller skips the stage guard but keeps the arity check. An effectful fixture accepted by the public parser/checker/forced typed compiler passes two scalar arguments to one tuple parameter and returns argumentArityMismatch 1 2 after both arguments modify the trace. No parameter cells are allocated, and heap typing is preserved. Reproduction: `/private/tmp/solcore-staged-arity-public-audit.lean`. The original applyCallable checks arity before bindValues; bindValues also checks value types before allocation.

The independent `Dynamic` indirectCall/argument fault rules at this point lack the stage guard's acceptance premise and stage-fault rules. Metadata agreement with an existing validator does not complete independent source meaning preservation.

Internal DeepSafety does not distinguish missing or renamed captures. Public `Value.validateTypeFuel`, however, rejects raw closure/instantiated-closure values even inside products, data, and mappings. Public function inputs resolve from global/builtin references. A clarification question based on inferring public-input scope from internal checks was withdrawn; no approval to reduce features was sought.

A malformed closure that passes internal DeepSafety can be placed in an unused initial-heap prefix; that prefix remains after a successful global call. A global's initial lexical environment is empty, and input allocation begins after the prefix. Public inputs provide no constructor that refers to a prefix location. The full unreachability theorem and observation preservation for opaque prefixes are next steps. Rejecting every prefix does not establish preservation of old features.

### Output metadata for generalized locals and nested lambdas

`directLambdaLetBinder?` detects only polymorphic binders. Do not add a new `.instantiated` wrapper to local reads of monomorphic lambdas.
Even when the same generalized initializer is read at the same concrete type multiple times, `ownWitnesses.actualRequirement` differs at each read occurrence.
The native code ID for `(initializer, cumulative substitution)` alone therefore cannot reconstruct the old wrapper's own substitution/witnesses.
Preserve occurrences using cached `CallableViews` and ordinary Core lambda wrappers retaining descriptor/anonymous identity.

When the body invoked through such a wrapper creates a nested lambda, the old runtime also rewrites original Source requirement IDs according to the read occurrence.
Authentication of a static parent receipt and exact native lambda template cannot by itself recover this dynamic difference.
Connect the following metadata transport separately from completion of template authentication:

- Represent callable ancestry with ordinary Core recursive nominal data. Distinguish named boundaries, ancestry at lambda creation, and local-read views.
- Give the artifact a single administrative context cell. Do not add it to the source allocation ledger.
- A local-read wrapper saves the view frame immediately before invoking the original payload, then restores the caller frame on both success and language failure. Fuel exhaustion retains it within the Core checkpoint.
- A lambda captures its lexical ancestry at creation through a pure let. Calls use that snapshot and add only the immediately preceding view frame for the same lambda.
- A named call uses its own metadata boundary. Do not apply unrelated caller local views to principal source metadata.
- Authenticate output by checking owned views/templates, exact native bodies, global slots, capture ledgers, and ancestry correspondence, rather than a word alone.

This connection is in progress at this point. Restoration of the whole source heap, including lambdas/principals, and switching public typed-source routing are not yet complete.
These changes do not add Core kernel syntax or machine instructions.

## 2026-10-01: Public source values with raw metadata

The actual `checkProgram` → forced typed compile → public `runTyped` path showed that the old public boundary accepts raw metadata equivalent under `runtimeType`. Reproduction: `/private/tmp/solcore-public-source-boundary-audit.lean`.

- A `.proxy (comptime Word)` key in `mapping(@Word => Word)` is accepted by type validation. `table[@Word]` does not match that key and returns default 0; a canonical `.proxy Word` key returns the stored value 7.
- Constructor metadata `Box<comptime Word>` is accepted as a `Box<Word>` input and remains in an echo result. A canonical `Box<Word>` pattern does not match a value with different raw metadata and selects the default arm. The number of allocated pattern binders also differs.
- An empty `mapping(Word => @Word)` with raw valueType `proxy(comptime Word)` is accepted. A missing lookup returns `.proxy (comptime Word)`. The default is built from the actual mapping header's valueType rather than the static expected type.
- Scalar globals in the plan and the builtin `wordToInteger` are accepted as function inputs. Initial-heap prefixes containing existing valid closures and uninitialized `.error` cells are also accepted and retained in the result heap.

Strict raw-metadata equality in `SourceCoreDataValues` / the owned session codec is therefore insufficient to finish the adapter for old public values. The compatibility profile retains authenticated raw-metadata Word IDs in Core carriers at canonical runtime types. Nominal matching, proxy-key equality, result restoration, and source-cell restoration use these IDs. A mapping carrier retains a raw-header ID, authenticated optional default, and ordered entry sequence; updates preserve the header/default. Missing-default diagnostics use a token that recovers the raw valueType and callsite.

A hidden match scrutinee is an actual old-source heap cell and must be exported. Keep it distinct from administrative cells for globals, loops, comparisons, and mapping helpers. Its type is the runtime type of the old runtime value; do not restore the raw expression annotation directly as the cell type.

Preserving these differences does not require Core kernel extensions. The new registry/helpers use ordinary Word, product, sum, data, and function representations. Their connection to the public runtime and typing/meaning correspondence are validated separately.


## 2026-10-10: Current status

### Execution and public boundary

The first goal was completed on 2026-10-01 in `a3168382`. `SourceCompiler` reexports `SourceCoreExecution`. Common artifacts and sessions execute cached Core code prepared by `SourceCoreCompiler → SourceCoreUnifiedCompilation`. Backend preferences, fallback, the old session implementation, and runtime typed-source expression/statement/call evaluators have been removed.

The raw metadata, grouped tuples, stage/arity evaluation order, callable views/ancestry, inert initial-heap prefix, and distinction between source allocations and administrative cells found in the initial audit have been incorporated into compatibility carriers, public ownership, snapshots/full prefixes, and regression tests. Public Value does not expose source closures or arbitrary native references; function calls authenticate owned handles. Historical raw heaps migrate through the explicit `SourceCoreLegacyHeapImport` boundary.

The `SourceTypedRuntime` namespace remains for compatibility values, observations, and validation data. The namespace and tests named after old features do not demonstrate survival of a runtime evaluator. Existing comptime direct evaluation remains in preparation as agreed. Unifying that evaluator with Core and adding source contract/storage/external-call connections belong to the next phase.

### Latest proofs and validation scope

The latest committed and normally verified code commit is `d9f2a0c4`. The typed contextual receipt unit was introduced at `df034b25`, and the positive-cell backend migrated at `350e4336`. `CallableIndexedOwnedContextualTypedClosureReceipts` retains actual ordinary and method-principal lambda formation through a typed `Association` and a propositional `StaticMember`.

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

The next closure call join and named-body adapters remain unintegrated, text-reviewed drafts. The closure join keeps the body's static registry separate from the receiving payload registry, requires explicit actual `CatalogSites` for the same retained trees, and consumes the same Association's strict flow child. The named adapter connects genuine `SourceReceipt.of_named`, actual parameter rows and the canonical body protocol to the original typed finish and invocation. Their complete admitted expression dispatcher, actual diagnostic-site construction and shared named/global/method family remain open. A registry extension preserves existing payload evidence, but each new registry's diagnostic coverage still requires its real compiler receipts.

Next: close one receiving-model expression/body family across closure, named/global, builtin and method calls, with positive cells and genuine physical arity, Source stage gates and public diagnostic inclusion. Then compose the actual specialization, evidence and comptime transformations through the public compilation and input boundary. Generalized/scheme cells, compound assignment, general failure/export-error correspondence and the final all-pass theorem remain incomplete. The first objective remains 100%; the second stays about 70%, and the equally weighted overall estimate stays about 85%. These are estimates of completed work, not declaration counts or remaining time.

| Commit | Proved scope | What this unit alone does not complete |
| --- | --- | --- |
| `618cd059` | Connects acceptance of pure `elaborateFunction` with staged Integer lets to the full original Source heap, actual Resolved/Core results, and reflection of original finite Core completion. | The full-state theorem for the public unified path. No Integer-let erasure was added to that path. |
| `85da3f04` | AuthorityPool invariants for ordered ownership keys with duplicates, shared physical frames, and retained snapshots/records. | Pool integration with function values and general call bodies; no coverage claim for all physical heap snapshots. |
| `a3e0f4ab` | Derives lambda template permission from actual prepared inventory, the same full source/table row, and compiler receipts. | Runtime catalog authority and body meaning preservation; static permission does not imply them. |
| `0bb0c9ee` | Connects additional children to the same compiler induction, preserving original policy, predecessor fuel, independent Source typing, duplicates, and order. | Mutual induction closing the execution meaning of callees, arguments, and general bodies. |

Shared registration, concrete ownership and actual lexical/imperative producers were verified at the earlier `4521c209` checkpoint. The CatalogSites fold, origin-neutral body kernel and named body family consume actual states. Named and anonymous parameter prefixes, frame installation, invocation and caller restoration retain the body's exact reached record vector. Actual ordinary/direct call heads pass ordered argument states into live Capture acquisition. A proof wrapper carries original canonical slots through lexical prepend/restore and genuine marked allocation.

Data, builtin and tuple producers now forward actual child posts through the unchanged expression Tree fold. The closed named body/caller family derives strict callee callbacks internally from authentic static profiles; its final public methods take no expression/body meaning premise. Runtime mode retains full evidence and the requirement ledger. Formal consumers exercise complete Header-based ordinary/direct calls and an ordered tuple containing a call with nonempty Source/native Boolean arguments. Selected accepted indirect lambda calls now retain the complete callee receipt and the actual argument, parameter, body and restored posts, including argument faults. Actual method invocation is connected, and builtin method bodies close internally. A concrete anonymous empty-Unit consumer also closes its body internally. Arbitrary indirect dispatch and general method/coercion bodies remain incomplete.

Original `Prepared.HeaderAt.layouts` provides full layout equality. Canonical slot receipts come from authentic Header bootstrap construction, actual input Entry globals or complete Capture coherence. Pool authority alone does not prove a canonical slot. Selected-frame `BodyAuthorizationAt` retains the original owned-id, Carries and code receipts while adding the actual physical frame equality, from which concrete allocation readiness is proved. Raw Source capture declarations and generalized storage metadata also require genuine Source validity; native type projection cannot supply them.

That earlier proof-umbrella and `Tests.Main` build passed **5173 jobs**, all registered `lake test` executions passed, and the latest strict audit checked **4100 declarations** using only the permitted standard axioms. Fresh inventories cover **219 declarations** in nine modules. All **105 original declarations** have exact raw type/axiom matches and independent original literal Expr.eqv/axiom checks; no helper was relocated. All **49 signature probes**, semantic policy and whitespace checks passed. **5019 original files** outside explicit owned changes remained unchanged. Records: `/private/tmp/solcore-owned-functions-resume-20261007/catalog-body-ready-validation.json` and its logs.

The shared measured family supports a separate protocol and dependent record type for each genuine origin. Actual lambda and method parameter continuations wrap authentic canonical slots at the exact entry. Selected indirect calls retain the actual caller protocol independently of the selected closure's captured owner/prefix. The same actual body pool is restored and wrapped at the caller's original scope and captures. Receipt-aware named and indirect caller bridges now return stronger formation packets at the same actual body post using genuine cumulative effects. The named entry factory authenticates its original Source seed from the actual Header record and carried history.

Actual named lambda views and genuine nested formation leaves are registered. They retain original frame references, bundle tags, Source captures and metadata from reached own Current receipts and real physical reads. Their static helper boundary explicitly retains capture prefix zero and caller prefix one. The packet survives genuine lexical allocation, restoration and named calls. Actual nested expression head callbacks consume the packet at real child inputs. The same original expression Tree and measured shared family now close nested named bodies and expressions without outside body/expression execution laws. Actual anonymous parameter entries retain their genuine full capture spine and expose pointwise continuations. Nested anonymous bodies now close expression and named callee meanings internally through the original kernel and closed named family. A genuine named-body formation consumer is registered. The original formation producer supplies a selected ClosureAt with exact owner, prefix one, complete captures and Source seed; arbitrary ValueRep inversion does not recover that receipt. General indirect/method branches and all static factories remain incomplete.

Complete outer Source adapters and a closed full indirect expression consumer construct actual callee reads, a Boolean argument, singleton Source allocation and the nil body internally. A selected method consumer now also derives genuine typed bootstrap capture and whole empty Source heap relation, full Source admission at the same marked allocation, and internally closed builtin Source/native invocation. Internally closed actual method coercion steps compose an ordered path through the existing folds, threading real intermediate and final states through the actual protocol relation. A fault retains the reached pool and skips subsequent steps. These consumers retain actual returned pools and independent grades. The whole outer method operator, live caller transport, nonempty initial Source prefixes and general body families remain unfinished.

Authentic method principals now retain independent TraitMethodInstantiates, the complete selector/dictionary and cached Source body. Genuine hook history authenticates the emitted method seed at actual parameter posts. The new generic origin packet requires no ordinary Header and retains the same real pool, reads and complete records. A Boolean parameter consumer derives actual Source admission and preserves strict native children and the original saved-frame write. The compiler's synthetic function does not establish top-level Source function authority. Existing lambda static support still requires an ordinary Header; method-produced lambda origins remain a separate unproved model extension.

The authentic method continuation providers now consume the exact hook history and parameter packet. Builtin method bodies and complete invocation close internally through the existing shared measured family using real marked allocation. A typed-bootstrap Boolean consumer retains the same restored pool and every ordered record observation. General method-produced lambda support and live caller transport remain separate.

Raw Source capture validity follows from genuine Source formation, typing or whole Source expression preservation. Actual parameter admission for named functions and selected methods derives the complete original Source certificate internally from genuine instantiation/selection and whole-program validity. Initial Source heap and raw argument validity remain explicit, and their extraction at the actual public boundary is unfinished. No Core type projection is used to infer Source declarations or dictionaries.

Literal indirect call selection now uses the authentic formation producer at the same caller state, retaining the exact emitted callee and its full closure receipt. A separate closed continuation specialization consumes the real argument pool through the existing named/anonymous body grammar. The Source/native parent still requires genuine pointwise input admission and already closed ordered argument meaning. New admitted expression contracts derive successful value and deep heap typing from real Source traces at the exact reached state; the two-child packing consumer passes that actual successful admission to its next child. Faults retain the actual pool and all-row stable history. No deep Source heap typing or uniform input admission is inferred from administrative metadata extension or a bare selected-row packet. The admitted ordered sequence now instantiates the same indirect call providers at the real callee post. Actual selected literal Head callbacks retain that admitted input and successful post. The complete shared mixed family remains necessary.

Authentic named, lambda and method Source parameter receipts now wrap the complete original body Entry with genuine heap typing and all-row history. Real carried hook installation and parameter effects preserve that same pool. The existing complete FunctionStatements preservation core derives successful body value and heap typing, including the implicit final expression. Faults retain stable rows without a deep heap-typing claim. These wrappers strengthen already closed producers; the general CatalogSites/kernel still require admitted child inputs. Original parent typing supplies an ordered argument/value row independently of native types. Actual absent and initialized lexical allocation now preserve the complete original allocator output while deriving deep heap typing from genuine Source allocation and raw value typing. The same reached state is admitted in its genuine next Source context. Composition, tuple and builtin Head adapters now derive raw Source operand rows from genuine parent typing and consume admitted children at actual inputs. Their shared original cores retain the real guarded builtin environment, left-to-right order, short circuits and selected branches. Source success admits the exact returned witness; faults retain stable rows. Admitted constructor/member/index providers now retain actual child states and genuine parent typing. The existing lexical Tree folds consume authentic contextual Source syntax, actual initializer/allocation posts and restoration at the same reached state. Suffix facts are requested only after genuine fallthrough, preserving accepted dead code. Named invocation now requests its body continuation at the actual parameter state. The same five-way control proof cores now consume actual readiness and authentic Source facts, retaining the real tail or selected-branch input. Named ordinary/direct Heads select invocation continuations after actual argument evaluation. Genuine Source declaration typing, argument preservation, Header certificates and actual arity derive the raw callee context and argument types. Full actual named parameter receipts now construct pointwise admitted entries. Internally closing their body callbacks and connecting assignment, loops and match through CatalogSites remain in progress.

Shared expression dispatch now consumes genuine parent typing and admitted child providers at actual inputs. Bare assignment uses the actual RHS snapshot and written or fault prefix, preserving the real seven-slot native continuation. Successful Source assignment derives admission at the actual written heap. Ordered place key providers retain every Source occurrence and use the pointwise sequence producer at the real protected root input. Source projection typing derives the independent raw key row, and genuine resolution admits the same reached getter heap. The admitted projected assignment adapter now consumes the actual whole-key and getter/RHS producers. A shape dispatcher retains the same actual bare or projected write/fault output and strict native continuation. The same while proofs now carry actual readiness at condition, body and recursive posts. High while factories now retain actual Source condition/body facts and admitted posts. Authentic same-code body Trees derive their reflection control restriction. For/match readiness and general imperative closure remain unfinished.

The admitted named adapter retains the full actual parameter BodyState, original globals, selected physical hook and carried history. Its canonical and nested entries keep the same Source receipt and rows. Body callbacks target that exact computed entry; they still need internal discharge by the shared family. A generic typed BodyEntry alone supplies neither canonical global slots nor the named Source seed. Imperative facts now retain original Source assignment legality, Boolean while conditions and complete ForItems judgments independently of compiler syntax. Suffix typing is transported only after actual fallthrough by the existing dynamic final-context proof.

A closed no-expression named receipt consumer now proves that pointwise body callbacks can be constructed internally at authentic full parameter receipts. It uses the real marked producer and existing singleton mutual family, retaining the exact original entry and body pool. Its bounded grammar does not close general mixed, indirect or method bodies. Generic while reflection retains its original control-fault restriction; an authentic same-code body compiler Tree can discharge it through the existing control-shape theorem.

The restricted admitted expression Tree now closes ordinary/direct named callees internally from authentic full parameter receipts, real marked producers and the existing singleton mutual family. Its callee grammar has no executable expression leaves; this does not establish the general mixed body family. Match admission helpers derive raw Source case/default typing and preserve deep heap typing through genuine hidden and binder allocations at actual states. The selected-prefix/body execution composition still requires the next readiness cut.

For iteration now retains the actual condition/body/post states, readiness and real recursive self-cell reads. Genuine ForItems traces establish Source heap typing at both original and static final contexts through actual Source preservation and runtime context fields. Function finish preserves the same reached flow witness and converts escaped controls to fault history without rebuilding state. A literal-false while consumer closes its Source/native completion and nil-body proof internally, retaining real physical reads. For header/post, full match readiness and general CatalogSites/body closure remain in progress.

The match cores now carry actual readiness through scrutinee, selected prefix, body and restoration. High Source admission uses real hidden and pattern allocations at a single actual selection post, without a fabricated intermediate protocol state. Genuine cases and body typing remain independent of Core representation. Faults retain actual stable rows, and restoration retains the same returned body pool. High parent adapters and the existing CatalogSites/body closure remain in progress.

High match endpoints now derive original scrutinee/cases/default typing from the actual parent Source judgment and occurrence uniqueness. Their actual selected-body callbacks retain compiler and Source receipts separately. Actual bit-not snapshot/write traces now establish reached heap admission through already proved Source preservation; no external expression execution law is assumed. These receipts still need composition into the original CatalogSites fold and general mixed body family.

For headers now retain readiness through actual initializer children, allocations, assignment and snapshot writes, and the exact tail. Genuine Source item typing selects facts only at visited contexts. Successful initializer traces identify runtime/static final contexts and retain deep Source heap typing in both contexts. Post restoration uses the actual tail state, genuine Source binder restoration and real loop progress. High for endpoints retain the original parent Source judgment and independent condition/body/post facts; the same-code compiler body Tree derives the reflection control restriction. General ready CatalogSites/body closure remains in progress, including the authentic normalized initializer receipt. No administrative metadata rule is used to derive deep Source heap typing.

Original actual parameter Source receipts now construct genuine body typing beside a separate authentic compiler syntax receipt. A closed false-for consumer with nil initializer/body/post constructs both Source and native completions internally, retaining the actual reached readiness, every ordered row and real physical self/frame reads. Its native witness is the original self-cell producer; Source preservation identifies the same store by evaluation determinism. This consumer does not establish general loop bodies or mixed dispatch. The original ready CatalogSites folds and body flow/finish compositions are integrated. Their complete original entries, actual Source facts, reached readiness and ordered pools are retained. The ready measured family and complete mixed dispatch remain in progress.

The same two CatalogSites folds now carry genuine facts through lexical, allocation, assignment, snapshot and five-way control producers. Finite while/for/match recipes retain authentic static receipts and only smaller child goals. The genuine initializer judgment follows original contexts to the nil continuation, retaining its loop facts and inclusive loop bound. The callable body composes that actual flow post with the original finish proof, retaining ReachedExit and readiness at the same returned state. Legacy APIs have exact original types. Ready origin entries retain the complete actual original Entry and pair independent Source typing with authentic compiler syntax. No extra execution or Tree induction is introduced. Closing these contracts in the measured family and deriving complete public origin factories remain unfinished.

The same measured callable family now consumes genuine Ready inputs and actual Source runtime origins. The finite Catalog and body adapters retain the full original actual entry and reached state. A closed named false-while consumer constructs Source execution internally and separately reflects the original measured native completion through that family, including real parameter/frame observations. This establishes the bounded false-while body; general call and formation dispatch remains unfinished. Verification at `5da8a5bb` passed the 5179-job normal build, all registered tests, strict kernel audit of 4241 declarations, fresh inventories of 148 declarations, all seven original literal/type/axiom checks, 39 signature probes and the kernel policy. The 5019 protected original files are unchanged.

Finished mixed body closure requires the authentic canonical or nested protocol at the same parameter entry. A base owned pool has no caller Globals or captured Source seed. Those facets must be retained from actual Header globals, complete capture spines or genuine method principal/history receipts, then projected away at the same returned pool. No administrative metadata rule supplies deep Source heap typing.

The public session keeps valid inert prefixes separately from its empty active Source bootstrap heap. Existing heap migration proves reconstruction and prefix preservation, without a whole execution correspondence. A theorem executing Source over a nonempty initial prefix therefore needs an authentic complete heap relation or a proved prefix execution relation. The existing fresh public root entry is constructible for the empty active Source heap.

Actual named parameter receipts now choose the complete static family index internally from their original profile, member, Source runtime validity and independent Syntax. The actual canonical entry supplies global slots; the original admitted expression Tree consumes strict family children for arbitrary authentic ordinary/direct named callee profiles. Runtime literal meanings come from the real requirement ledger. Actual lambda/method wrappers retain genuine captured or principal packets beside the same Source receipt and all-row history, then forward the same returned pool. These adapters reuse the existing folds and do not establish joint mixed dispatch.

Method lambda sites now retain original Source provenance, graph uniqueness, genuine carried history and emitted descriptor from the actual selected method principal. The owned lambda StaticSupport remains Header-based; a method-only principal requires an explicit support alternative before the current value model can represent it. No ordinary Header or FunctionInstantiates is inferred from synthetic compiler code.

Verification at `ed314136` passed the 5190-job normal build, all registered tests, strict kernel audit of 4375 declarations, fresh inventories of 71 declarations in six new modules, 37 signature probes and the kernel policy. No original proof module changed in this unit, and the 5019 protected original files are unchanged. General named closure, joint origin factories, mixed dispatch and the compiler/public theorem remain unfinished.

The general ordinary/direct named family now closes its own body and recursive expression obligations through the existing measured family and original admitted expression Tree. The runtime expression endpoints assume only the genuine static and Source receipts, deriving literal meanings internally. They carry no outside completed expression or body execution law. Actual lambda and method entries construct the matching dependent family index at their original parameter post; strict continuations return the identical underlying pool and full exit. Genuine method occurrence typing now proves the exact lambda closure frame without an ordinary Header.

Verification at `6d4bfd65` passed the 5195-job normal build, all registered tests, strict kernel audit of 4474 declarations, fresh inventories of 99 declarations in five new modules, 29 signature probes and the unchanged kernel policy. No original proof module changed in this unit, and the 5019 protected original files are unchanged. Joint origin factories and expression dispatch, method-generated lambda support, static public extraction and the compiler/public theorem remain unfinished.

Genuine method-principal lambda support now exists as an additive alternative to the ordinary Header-based model. It retains the same compiled Code, full captures, carried history and independent Source method origin. Original representations lift forward into the new model; erasing a new representation does not recover an ordinary Header. Authentic principal packets derive lambda formation history, the captured bundle and the real frame slot. The admitted formation leaf preserves the exact packet, Source heap and native store and reflects completion with an independently constructed Source size.

The extended joint Family reuses the existing measured closer for named, ordinary lambda, method, nested named and method-lambda origins. Actual parameter continuations select only their genuine dependent index. In particular, an ordinary lambda entry supplies the original full layout equality at that actual selection; a universal transport for arbitrary standalone static lambda indices is not assumed. The mixed expression dispatcher remains incomplete.

The public ordinary/direct named runtime connector derives layouts from the original prepared Header and uses the actual compiler bundle prefix. The closed named family supplies all body execution meanings internally. The endpoint still needs genuine interpreted static output receipts and independent Source Syntax. An arbitrary receipt's diagnostic predicate cannot be inferred from native typing or compiler acceptance; the actual producer's emitted diagnostic shape must be retained and proved.

Verification at `773d5836` passed 5200 build jobs, all registered tests, a strict audit of 4623 declarations, fresh inventories of 149 declarations and 40 signatures. Verification at `37d10587` passed 5208 jobs, all tests, 4811 strict declarations, 188 fresh declarations and 59 signatures. Verification at `ec287604` passed 5213 jobs, all tests, 4864 strict declarations, 53 fresh declarations and 25 signatures. The semantic kernel policy remains unchanged. Every final source passed parent and two independent exact-source reviews. No original proof source or runtime/fuel/Tree induction changed in these units; the 5019 protected original files remain unchanged.

Ordinary formation now reconstructs the actual capture/code/history witness from a genuine ranked static certificate. Selected ordinary and method formation keep distinct actual protocols. A selected method-lambda call retains independent raw Source argument typing, ordered argument fault/success posts, its strict dependent body continuation and the actual saved-frame restoration. Every returned packet retains the same reached pool and full ordered record vector. Method used-prefix capture projection changes no underlying heap, world, store or pool.

Concrete static method formation and selected-call heads construct their runtime receipts at each input. The existing expression support fold and actual runtime literal producer now consume these heads. No arbitrary compiler body certificate is identified with the constructed Tree. The supported expression grammar and selected literal call are narrower than complete mixed dispatch or arbitrary stored/returned callee selection.

Verification at `23d60439` passed 5216 normal build jobs, all tests, 4874 strict declarations, 10 fresh declarations and 10 signatures. Verification at `3ff3daf4` passed 5220 jobs, all tests, 5075 strict declarations, 201 fresh declarations and 37 signatures. Verification at `666f95b0` passed 5222 jobs, 5164 strict declarations, 89 fresh declarations and 16 signatures; the registered tests were unchanged by its two proof modules and passed at the preceding checkpoint. All final sources passed parent and two independent exact-hash reviews. The kernel policy remains unchanged, no runtime/fuel/Tree induction was added, and 5019 protected original files remain unchanged.

The actual for-header and statement/match static folds now retain emitted diagnostic plans and exact equations to their original predicates. The finite plan interpreter consumes genuine local Source/fault receipts and follows only the retained scoped requests. Terminal cases preserve the original unused suffix. Cached/public profile extraction uses the actual returned plan rather than an arbitrary interpreted output. This does not yet derive every public local fault token or the global prepared operand typing condition.

Verification at `145bdc6e` passed the 5229-job normal build, 5386 strict declarations, fresh inventories of 224 declarations across nine added/modified modules and 43 signature probes. The two original modules preserve all old theorem headers and unchanged source prefix/suffix. Original compatibility covers 68 raw type/axiom matches plus one relocated compiler-generated matcher checked against an independently saved original literal `Expr.eqv` and exact axioms in both private and normal objects. Both original static Syntax inductions remain unique. The unchanged registered executions passed at `3ff3daf4`; the new changes affect static proofs and certificate extraction. All three exact-source reviews, the kernel policy and whitespace checks passed. The two intentional original fold changes are excluded from the **5017 other protected original files**, which remain unchanged.

The `356a4871` checkpoint added genuine unrestricted ordinary support, exact Source-origin entries and a shared owned function relation that embeds prior method values forward. Same-model formation/selected calls retain all actual heaps, argument/body posts and caller restoration. Prepared unary/binary operators with empty output coercions retain the independently selected Source dictionary and original raw grades. Public named endpoints interpret their own actual emitted plans. Verification passed 5238 normal jobs, 5546 strict declarations, 160 fresh module-attributed declarations and 60 signatures.

The `6db08194` checkpoint connects the same-model method-lambda heads to runtime Trees and composes actual named/direct named and method-lambda calls at one genuine method caller packet. Ordinary formation uses authentic accepted Sites with unrestricted same-Code bodies and full actual capture/Source history. The compiler prefix changes only slot evidence, while the underlying pool, records, Source seed and restoration remain identical. Original expression/body folds and runtime literal producers are reused. Verification passed 5244 normal jobs, 5626 strict declarations, 81 fresh module-attributed declarations and 36 signatures. All source reviews, policy and whitespace checks passed; 5017 other protected original files remain unchanged. Registered native and interpreted tests passed at `3ff3daf4`; later units change proofs and static certificates and rebuild the test target.

At `c271f222`, actual table unary entries, for-header items and scoped statement/match children retain their owning Source sites and emitted tokens through the original static folds. Their prepared table internally supplies unary/operand interpretation; remaining place laws concern only actual assignment atoms. Verification passed 5252 normal jobs, 5782 strict declarations, 322 fresh declarations and 35 signatures. Of 187 originals, 186 raw types/axioms match exactly; one relocated matcher passes an independently saved original literal `Expr.eqv` and exact axiom check in private and normal objects. Original traversal counts and explicit headers remain unchanged.

At `b3d58921`, the same shared model retains authentic principal prefix-one globals and the leading bundle through actual formation, extension, key embedding and exact selection. Unrestricted ordinary literal calls use genuine same-Code Support, the real argument post and original strict body family. Public named runtime bounds interpret their own actual tokens internally. Verification passed 5256 normal jobs, 5858 strict declarations, 109 fresh module declarations and 46 signatures. All 27 original non-recursor model/selection types and all 33 original axiom arrays remain exact; six recursors intentionally gain a case. Every source passed three exact full-source reviews; kernel policy, whitespace and 5015 other protected original-file checks passed. Registered executions passed at `3ff3daf4`; subsequent units add proofs/static certificates and rebuild the test target.

The principal and unrestricted ordinary branches retain their actual invocation facets. Legacy prior method/ranked branches keep their original arbitrary prefixes. Assignment tables also do not justify universal missing-default/uninitialized laws over arbitrary raw types and bare roots. General stored-callee invocation, typed reachable assignment faults, full Source diagnostic typing and all-pass composition remain separate obligations. No weaker native relation or externally supplied completed body law establishes them.

At `6d74be1f`, actual public compilation retains the identical raw program diagnostic producer and exact selected specialization. Its own Header receives the corresponding assignment preparation. The unit passed 5257 normal jobs, 6028 strict declarations, 170 fresh module-attributed declarations and nine signatures; all 116 original program-fault raw types and axiom arrays remain exact.

At `08991147`, genuine ordinary lambda and principal mixed heads connect to the same original expression support fold and finite dispatcher. Actual nested captures, independent Source argument typing, parameter entry and restored pool remain intact. Runtime literals come from the actual Source ledger. Public named endpoints derive the selected assignment table internally from the retained producer. Verification passed 5263 normal jobs, 6131 strict declarations, 103 fresh declarations across six new modules and 34 signatures. All final sources passed three exact full-source reviews; policy, whitespace and 5014 other protected original-file checks passed. Runtime and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

The runtime fault audit found correct emitted categories for absent bare compound assignments, unary bit-not, nonmapping projections and compatible mapping defaults. The proof obstruction is broader quantification: the unused bare projection token is zero, while missing-default laws currently admit unrelated raw mapping headers. The next proof cut retains authentic prepared paths, actual ordered arguments and root representations at the reached key/RHS/fault states. Bare heads need only the operand law. No zero-token reinterpretation or broader fault relation is justified. Full original Source body typing and graph closure, rather than runtime validity alone, must also supply all-occurrence assignment typing.

At `5e90dffd`, full original Source body certificates and graph closure derive unary and assignment operand typing for actual ordinary and selected trait bodies. Public endpoints derive those conditions internally. Actual successful callee representation exposes complete selection; raw Source argument packing, binder-bundle equality and genuine arity recover the closure binder row at the same argument-post heap. Stored ordinary/principal payload application retains the current owner row, distinct captured history, original strict body continuation and identical restored caller pool. Verification passed 5269 normal jobs, 6218 strict declarations, 89 fresh declarations and 28 signatures.

At `d35929c6`, projected fault receipts retain the actual key/getter or RHS/live-root phase and the same terminal state, prepared path, ordered represented arguments, raw root and existing fault tree. Bare heads require only operands. Original finite cores are factored once; legacy wrappers erase receipts. Actual caller admission derives raw closure inputs internally, and map/world extension preserves the unchanged full invocation association. Verification passed 5272 normal jobs, 6250 strict declarations, 109 fresh declarations across seven new or modified modules and 29 signatures. Original compatibility covers 72 exact raw type/axiom matches plus five relocated helpers independently checked against original literal expressions in private and normal objects; all 59 explicit theorem headers remain verbatim. Three exact source/diff reviews, policy, whitespace and 5014 other protected-file checks passed. Runtime code and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

Actual public projected-fault interpretation remains open: it must associate the reached terminal metadata with the precise prepared missing-default row, including normalized raw key/value checks and reserved token range. General stored-call parent expressions still need actual argument/stage/coercion and compiler binding receipts. Bundle type equality alone does not imply Source arity. Neither native type vectors nor an arbitrary fault relation can supply these facts.

At `69e3f120`, actual Source call prefixes retain independent callee/argument typing and real heap extensions; actual codebook preparation exposes the selected generated request and count. Original stage acceptance remains an independent receipt. The missing-default producer retains authenticated emitted rows, and the original path-fault core exposes the actual terminal index and raw mapping fields. Verification passed 5278 normal jobs, 6329 strict declarations, 79 fresh declarations and 36 signatures. The original path-fault theorem retains its exact raw type and axioms against Root's independently saved actual original objects.

At `eb7851c3`, genuine equal arity and independent Source/native bundle equalities derive the original binder argument representation. The indirect parent and payload application suffixes preserve the exact native grade, body, captures, argument and stores through finite inversion. Verification passed 5280 normal jobs, 6345 strict declarations, 21 fresh declarations and 11 signatures. All source reviews, policy, whitespace and 5013 other protected-file checks pass. Actual compiler pack provenance, whole-parent composition and coherent public diagnostic lookup remain incomplete; row membership and packed type equality do not replace those obligations.

At `f3a8bc11`, actual native binder packs, accepted stored-call invocation and terminal provider provenance passed 5283 normal jobs, 6409 strict declarations, 64 fresh declarations and 31 signatures. All 16 original prepared-path raw types and axiom arrays match independently saved original normal objects exactly.

At `8d187247`, strict callee bounds construct the actual reached state and retain complete selection; callee faults close the original parent at that same state. Actual contextual lambda generation retains the genuine binder policy and Source monomorphic projections. Original diagnostic preparation supplies all range, fixed and escaped exclusion conditions for coherent raw-error lookup at a genuine MissingSite member. Verification passed 5287 normal jobs, 6628 strict declarations, 223 fresh module-attributed declarations and 17 signatures. All 59 original lambda-generation types and axioms remain exact. Three exact source/diff reviews, kernel policy, whitespace and 5011 other protected-file checks passed. Runtime and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

Terminal-to-inventory membership and catalog Source type closure remain separate static obligations. Header occurrence graph closure does not establish type closure. Successful stored-call composition currently requires genuine strong ordinary/principal provenance, same-Code body syntax, actual guard acceptance and independent raw Source bundle/count facts. It does not cover every legacy, rejected or coerced call.

At `108f6af3`, the same original registration fold retains closed Source entries, and actual factory/projection/description proves the concrete assignment gate. The genuine lambda Site identifies the native binder pack, while concrete ordinary/principal receipts build invocation association at the actual callee post. Actual route collection and Source projection typing associate the reached mapping terminal with its precise MissingSite/base and raw table error. Verification passed 5294 normal jobs, 6800 strict declarations, 186 fresh module-attributed declarations and 27 signatures. All 48 original registration-prefix raw types and axioms remain exact against independently saved original normal objects. Three exact source/diff reviews, policy, whitespace and 5010 other protected-file checks passed. Runtime and registered tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

The public adapter must still produce its authentic selected catalog factory and full Source inventory membership from actual compilation. The terminal proof now closes for a real collected prepared assignment, while Source projection typing, actual extended raw metadata and the same generated path remain genuine inputs. Stored-call raw Source bundle/count/result production, full rejection/coercion/stage coverage and all-pass composition remain unfinished.


At `0f829f4e`, actual public compilation supplies the selected catalog and complete Source inventory. Missing terminals and uninitialized projected roots retain their actual prepared paths and first table rows. Actual callable preparation supplies arity diagnostics before and after argument effects. Empty output coercions and genuine successful callee traces derive the raw Source result used by the ordinary/principal continuation adapters. The original assignment and Header static folds retain their selected preparation; admitted projected endpoints consume the actual reached diagnostic packet.

Verification passed 5314 build jobs, 7186 strict declarations, 221 fresh module-attributed declarations and 29 signatures. All seven original Header raw types and axiom lists are exact against independently saved normal objects. The preceding assignment checkpoint independently checked all eight saved literal expressions and axiom lists; seven raw types are exact, with one hygienic matcher-name difference. Source/diff reviews, policy, whitespace and 5009 protected-file checks passed. Runtime and registered tests are unchanged since their actual executions at `3ff3daf4`.

At that checkpoint, preparation still needed a structural connection to the exact assignment in the emitted Tree. Equality of diagnostic predicates or emitted code does not recover the chosen head. Actual raw table observations also require a precise interpretation into the semantic fault relation, especially the reached uninitialized location. Existing uniform profile/Catalog fault requirements remain a separate consumer obligation. Stage rejection, nonempty coercions, public Source admission and all-pass composition remain incomplete.

At `744c1c40`, the actual compiler's original Header/match Syntax traversals retain joint Tree/Plan receipts. Each assignment shares the chosen head with its real preparation and Source occurrence; the match receipts retain the actual requests, child contexts and terminal materialization. Original theorem types remain available. Public projected endpoints derive their reached diagnostics internally. First-stage rejection and callee-fault adapters retain the genuine staged outcome, same reached pool, strict child callbacks and actual full native completion bound.

At `744c1c40`, the proof umbrella and `Tests.Main` build passed **5323 jobs**. Strict `--trust=0` verification checked **7430 declarations** against the three permitted standard axioms. Fresh inventories cover **301 module-attributed declarations** across six new or modified modules, with **65 signatures**. All **88 original declarations** retain their types and axiom lists: 81 keep their names and exact raw types, six private generated helpers have explicit relocation mappings and exact raw types, and one retained matcher alias differs only in a hygienic bound name. Seven independently regenerated literal Lean-expression checks pass against saved original normal objects. Eight public generated declarations retain their names and raw types while their owning module moves to the finite adapter. Every final source passed parent and two independent reviews; both modified original modules passed complete diff review. Kernel policy, whitespace and **5009 other protected original files** pass. Runtime code and tests remain unchanged since their actual native and interpreted executions at `3ff3daf4`.

At that checkpoint, the existing ready Header/Catalog fault and reflection proofs still consumed their older uniform laws. The subsequent Header checkpoint below shares its semantic branches between derived legacy and joint recursor adapters.

At `c9078fd2`, Header fault and reflection proofs each use one common six-branch semantic core. Legacy wrappers derive their structural recursor from original error laws; coupled endpoints derive it from the genuine Tree/Plan receipt and its actual prepared assignment payload. The original successful-prefix proof is unchanged. Public assignment readiness derives the bare operand law internally and retains precise reached interpretations for projected heads.

Strict callee induction now constructs the actual stored-call post from the full native completion, closing the earlier successful-child reflection premise. Accepted first gates feed actual ordered argument evaluation. Argument failures retain genuine Source/staged outcomes, cumulative state and all-row stable history. Successful arguments retain the complete fourth-bind bound beside the application projection. Physical arity, the gate after arguments and general body invocation remain the next boundaries.

At `c9078fd2`, the proof umbrella and `Tests.Main` build passed **5330 jobs**. Strict `--trust=0` verification checked **7505 declarations** against the three permitted standard axioms. Seven new or modified modules account for **102 fresh module-attributed declarations**, with **26 signatures**. All **49 original Header declarations** preserve their types and axiom lists: 38 exact same-name raw types and 11 explicitly mapped helpers checked independently against saved original literal Lean expressions. Parent and two independent final reviews, complete original-module diff reviews, policy, whitespace and **5009 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

At `a1bb3536`, the public Header supplies actual per-context assignment providers and derives unary typing and issued tokens internally. The stored-call gate after arguments uses genuine physical arity. Rejection retains the actual argument post and true Source/staged arity failure; acceptance returns the original argument receipt and complete fourth-bind bound. The combined checkpoint with `676743ef` passed **5332 build jobs**, **7520 strict declarations**, **15 fresh declarations** and **seven signatures**. No original source module changed. Three exact full-source reviews, policy, whitespace, hashes and **5009 protected-file checks** passed.

A legacy Tree or diagnostic predicate does not yield PreparedAt. Catalog integration must retain actual initializer code, loop post-header receipts and genuine match catalog/context fields. The current coupled match receipt omits its full solved-row identity; emitted code cannot recover unused rows. Unary token interpretation, interpretation of reached table entries as semantic faults, later phases, nonempty coercions and recursive staged semantics remain separate obligations. Public Source admission and all-pass compiler closure remain incomplete.

At `31bf3d35`, genuine public Source program facts derive catalog well-formedness, and strict child induction composes the stored-call parent prefixes at one real callee post. That checkpoint passed 5334 jobs, 7532 strict declarations, 12 fresh declarations and six signatures. The accepted body continuation still needs the callee-to-argument effects retained from the same ordered argument traversal.

At `5faa387e`, the proof umbrella and `Tests.Main` build passed **5338 jobs**. Strict verification checked **7702 declarations**, with **326 fresh module-attributed declarations** across seven new or modified modules and **55 signatures**. All 156 original declarations retain their types and axiom arrays: 154 have exact same-name raw types, and two generated matchers pass independently regenerated literal Lean-expression checks against saved original normal objects. Every final source and all three modified original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5009 protected original-file checks** pass.

The Catalog common cores preserve actual initializer code and continuation and exact loop post-header receipts. The compiler extraction carries genuine Source signatures and full solved-row ledger identity through binder and selected-child contexts. Prepared endpoints consume that same static receipt internally; a bare coupled receipt still needs an explicit match-field supplier. Prepared Head/loop providers, precise diagnostics, strict general body closure and all-pass/public-entry composition remain separate obligations. No runtime code or tests changed; actual executions remain those at `3ff3daf4`.

At `4e9cd0ae`, the proof umbrella and `Tests.Main` build passed **5344 jobs**. Strict verification checked **7767 declarations**, with **89 fresh module-attributed declarations** across eight new or modified modules and **16 signatures**. All 24 original declarations have exact same-name raw types and axiom arrays against independently saved normal objects. Every final source and both modified original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5009 protected original-file checks** pass.

Public Catalog extraction now retains the exact generated flow, finish equation and chosen compiler receipt at the actual ordinary BodyState. Prepared for-header adapters keep genuine Source typing, reached readiness and the original static payloads. The same measured closer is publicly reusable without a new induction.

Accepted stored-call adapters retain the real callee-to-argument effects from one ordered argument proof and use only strict body induction. They derive genuine Source and staged outcomes and preserve the complete body pool through caller restoration. The original 15 argument declarations and nine measured-family declarations retain exact raw types and axiom arrays. The whole parent must still pass the stronger receipt to these adapters; accepted intermediates do not establish complete callee classification.

Prepared Head/loop production, public flow/finish family closure, precise diagnostics, nonempty coercion and stage routes, Source admission and all-pass compiler closure remain incomplete. Runtime code and tests are unchanged; actual native and interpreted executions remain those at `3ff3daf4`.

At `0a3ab594`, the proof umbrella and `Tests.Main` build passed **5349 jobs**. Strict verification checked **7843 declarations**, with **148 fresh module-attributed declarations** across ten new or modified modules and **55 signatures**. All 72 original declarations retain exact same-name raw types and axiom arrays against independently saved normal objects. Every final source or complete original-module diff passed parent and two independent reviews. Policy, whitespace, final source hashes and **5009 protected original-file checks** pass. This checkpoint changes proofs; the most recent actual native and interpreted executions remain those at `3ff3daf4`.

Prepared initializer/Head/loop providers now construct genuine reached header results and exact post receipts internally. Their legacy wrappers and the three post restorations share the existing finite proof bodies. Public Source-site inputs and successful Source heap typing retain the actual original body receipt. Whole stored-call reflection retains ordered argument effects and the actual callee post through accepted ordinary/principal body invocation; its provenance callback does not establish a complete classifier. All 72 original declarations have exact raw types and axiom arrays.

Next: connect the actual public flow through the existing function finish and named callbacks carrying genuine parameter receipts into the same measured family. Prove that typed Source bodies cannot let break or continue escape the function, and retain actual lambda formation provenance through stored values. Precise reached diagnostic interpretation, complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished. Semantic child callbacks must come from strict mutual induction.

### Remaining audit and proof obligations

- Preserve full captures, original named/lambda Source provenance, caller/lexical frames, and the actual AuthorityPool under the same function-value and heap model.
- Connect callees, arguments, general bodies, methods/coercions, local instances, and application views to the same mutual induction. Actual indirect continuations now select the real argument post; final mixed closure must supply them internally from strictly smaller body obligations. Retain records added during calls through restoration.
- Relate specified failures and all preceding state as well as normal results. Positive missing-default rules have been added, but whole-syntax/whole-failure coverage and the final theorem remain unfinished.
- Compose actual specialization, evidence, and pre-evaluation passes to prove preservation and finite completion reflection from independent Source before pre-evaluation to actual public Core execution. Correctness of current passes belongs to the second goal even though comptime backend unification is deferred.

The old temporary Values and Entry fragments have been replaced by committed modules. Ordered expressions, ordinary/marked allocation, lexical restoration, all assignment outcomes, finite while/for, headers, five-way control, selected match and function finish retain actual post-witnesses. The outer imperative fold and origin-neutral body kernel now carry actual states. Named body/caller expression families reuse the measured mutual fold, and actual parameter/restoration consumers use real allocator receipts. Closing general indirect/method/coercion dispatch, every static factory and the full compiler theorem remains incomplete. A generic prefix transition does not establish exact fresh snapshot membership; that claim requires the concrete allocator receipt for the same execution. See the [implementation record](core-runtime-unification-progress.md) for the current boundary and validation scope.

The language's `mapping(K => V)` in this audit is a dictionary type. `SourceStagingHeapRelation.LocationMap` and similar definitions are proof tables relating cell locations; they are a different subject. Do not count ordinary Core administrative cells, retained Source cells, and Integer cells erased by pure staging as the same set of cells.

### 2026-10-08: actual parameter and public body checkpoint

At `85983792`, the proof umbrella and `Tests.Main` build passed **5353 jobs**. Strict verification checked **7912 declarations**, including **67 declarations** in four new proof modules, and **32 signatures**. Each module passed parent and two independent source reviews. Policy, whitespace, exact final source hashes and **5009 protected original-file checks** pass. The most recent actual native and interpreted executions remain those at `3ff3daf4`.

The new parameter receipts retain actual argument typing, installed frame, captured history and full reached pool. Public body bounds use the actual compiler flow and the existing function finish, and derive successful Source admission from the genuine Source receipt. All semantic child callbacks remain strict; the complete mutual family and final public compiler theorem remain unfinished.

### 2026-10-08: Source control and prepared named family checkpoint

At `75075048`, the proof umbrella and `Tests.Main` build passed **5356 jobs**. Strict verification checked **8052 declarations**, including **224 module-attributed declarations** in six new or modified modules, and **28 signatures**. All final sources or complete original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5008 protected original-file checks** pass. The most recent actual native and interpreted executions remain those at `3ff3daf4`.

Typed Source statement summaries now retain possible fallthrough, break and continue transfers through the existing mutual preservation proof. Loops consume break and continue, and a genuinely typed function body cannot let either transfer escape. The original explicit preservation APIs remain available. Function finish uses that actual Source trace to discharge the escaped-control condition, including lambda contexts whose internal reason is zero. Nested callee faults retain their original reason and token.

`CallableIndexedOwnedPublicPreparedNamedFamilyClosure` closes prepared ordinary/direct named bodies through the existing measured family. It consumes actual parameter receipts, the same public Header and generated flow, and strict callee body callbacks. It retains genuine Source typing, administrative effects, the complete reached record pool and independent Source/native grades. Prepared read/place diagnostic interpretation and static child associations remain explicit; this does not establish the final public compiler theorem.

Compatibility checks preserve exact raw types and axiom arrays for all 42 explicitly declared original Source APIs and all 29 original function-finish declarations. Across the three modified modules, 73 same-name raw types and 105 surviving original axiom arrays match. Strengthening the Source mutual proof changes 32 compiler-generated private matcher types and removes eight generated helpers; the validation record enumerates those generated changes separately.

Next: retain actual contextual lambda formation provenance through storage and later selection. Replace uniform read/index fault premises with policies at the genuine reached Source read and mapping lookup, then connect them to the actual public diagnostic receiver. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished. Semantic child callbacks must come from strict mutual induction.

### 2026-10-08: reached diagnostics and contextual lambda provenance checkpoint

The checkpoint comprises `d1d76443`, `61ff6e28`, `7866b408` and `fd8f7c94`.

Read and mapping index fault policies now consume Source witnesses at the actual reached environment and heap. The existing four terminal proof bodies are shared with their legacy wrappers. Source preparation supplies each local read's exact canonical function, occurrence, binder, span and globally issued token. Retokening retains row identity, and actual assignment ranges and function boundary tokens establish separation in the original program table.

Contextual ordinary and principal lambda formation retains its original compiler producer, binder policy and full Source body syntax. The additive value relation and selection cases keep that packet through storage, map/world extension and later selection. Principal evidence retains its original dictionary and method receipt. The existing runtime expression heads still need to select the stronger formation endpoints and feed them into typed invocation.

Public fault observation uses the actual completion's registry, rebuilt diagnostic table, filtered callable append, failed native token/store and accepted heap export. The ordinary-read packet retains the actual read certificate. It currently retains the whole Source failure and primitive read separately: their occurrence path through the same failure must be constructed by the existing semantic joins. Read/index priority, extra-source preparation ranges and successful table rebuilding remain explicit producer obligations. These proof definitions and preparation certificates do not establish the final compiler theorem.

At `fd8f7c94`, the proof umbrella and `Tests.Main` build passed **5366 jobs**. Strict verification checked **8787 declarations**, including **913 declarations attributed to nineteen new or modified modules**, and **82 signatures**. All final sources or complete original-module diffs passed parent and two independent reviews. Policy, whitespace, final source hashes and **5002 protected original-file checks** pass. The most recent actual native and interpreted executions remain those at `3ff3daf4`.

Compatibility checks preserve exact same-name raw types for 509 of 515 original declarations and exact axiom arrays for all 515. The six changed types are the generated `rec`, `recOn` and `casesOn` eliminators of the two lambda representation/selection relations; they reflect two additional contextual lambda cases. All original declarations remain present. The normal validation record lists these changes.

Next: use the retained contextual lambda packet at actual runtime expression heads and connect typed body continuations for the exact emitted Code to the original parameter, invocation and restoration proofs. Carry actual primitive fault origins through the same existing ordered-expression, call and imperative proof joins, and derive diagnostic priority and reserved registry ranges from the actual preparation. Public Session lookup and failure completion must retain their actual table and state receipts. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished. Semantic child callbacks must come from strict mutual induction.

### 2026-10-08: actual Session receipts, typed lambda invocation and failure paths

The latest implementation checkpoint is `9e0e3da8`, following `2363f329`, `70b62780`, `6532c642`, `2766ef4c`, `a194a050` and `10fef624`.

Public Session lookup now retains the actual registry extension and the table selected by the original lookup. Failed native completion retains the actual returned Session, weakened slots, values and ownership. The failure observer uses those receipts and the original diagnostic lookup; it does not assume equality between the exported Source heap and the native store.

Typed lambda invocation uses the actual parameter installation and a genuinely typed Source body. The original invocation proof supplies allocation, the body post, restored caller frame and complete returned pool. Source control facts discharge escaped break and continue at function finish. Contextual ordinary and principal formation now supplies typed body syntax and the actual binder policy for the emitted Code. The runtime heads and the mixed body family still need to consume these stronger static and invocation receipts together.

Expression sequences and the five existing composition branches share their original preservation and reflection proofs with stronger failure posts. These posts retain the origin of an uninitialized local read or a missing default in a mapping through the actual selected child path, retaining the final Source heap and token. Primitive terminal providers still need to construct these posts from the actual Core completion and bind the mapping leaf to the emitted token base. Call, imperative and remaining expression branches must retain that path through the same existing folds.

Actual missing-diagnostic generation now retains each emitted row's Source site, registry entry, checked one-based header, runtime type views and nonwrapping token. Rebuilding a table retains the actual generated rows and fixed prefix. This proves where accepted rows came from. It does not yet prove that every required row exists or that the public decoder selects it. Preparation ranges, priority among read, fixed and callable rows, and contextual Source occurrence agreement remain separate producer obligations.

At `9e0e3da8`, the proof umbrella and `Tests.Main` build passed **5442 jobs**. Strict verification checked **10724 declarations**, including **469 declarations attributed to nine new or modified modules**, and **50 signatures**. All **213 original declarations** retain exact same-name raw types and axiom arrays against saved normal objects. Every final source or complete original-module diff passed parent and two independent reviews. Policy, whitespace, source hashes and **4997 protected original-file checks** pass.

The preceding checkpoint for typed lambda invocation and failed completion at `6532c642` passed **5437 build jobs**, **10255 strict declarations**, **1563 module-attributed declarations** and **24 signatures**; all 1491 original raw types and axiom arrays match. Session diagnostic lookup at `2363f329` passed **5366 build jobs**, **10189 strict declarations**, **1404 module-attributed declarations** and **4 signatures**; all 1393 original raw types and axiom arrays match. These checkpoints add proofs and static receipts. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

Next: derive concrete primitive failure posts from the original read/index terminal proofs and retain the actual model through their semantic joins. Strengthen the existing preparation range proof once to retain actual base acceptance, final token bounds and read/fixed separation; use those receipts with the real table rebuild and filtered callable append. Retain coupled Catalog/structural body extraction at actual contextual lambda formation, then connect the stronger runtime heads and typed invocation through strict mutual induction. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-08: primitive failure posts and actual public diagnostic priority

The latest implementation checkpoint is `7c110570`, following `9cede6ab` and `c7f6e67a`.

The original read and mapping index terminal proofs now construct primitive failure posts internally. A lifted pointwise policy retains the actual witness, then projects the original result, heap and effects alongside the concrete Source path. The same catalog and function model remain associated with that origin. The upper read/index adapters and the remaining expression, call and imperative folds still need to carry this post through their actual children.

The existing diagnostic preparation loop now retains its actual accepted base, generated rows, final token bounds and separation of original reads from fixed and reserved diagnostics. The old range theorem projects the same proof. Actual callable preparation places its checked unknown token at or above the supplied minimum; the existing filtered append preserves earlier diagnostics.

Public read and missing-default endpoints use the actual rebuilt table and callable allocation at the preparation's final token boundary. They derive decoder priority from these producer receipts. Read decoding preserves the exact binder, occurrence and span. Missing-default decoding preserves the raw error; a duplicate token keeps the first selected row's span.

Actual public preparation, selected callable identity, receiving registry and site membership remain required receipts. The compiler must supply them and relate the same Source occurrence to the issued row. Arbitrary extraSources can reuse a key and expression ID with a different form, so accepted generic preparation alone does not establish Source ownership. The next producer work retains the genuine contextual substitution and canonical occurrence facts.

At `7c110570`, the proof umbrella and `Tests.Main` build passed **5446 jobs**. Strict verification checked **10787 declarations**, including **194 declarations attributed to five new or modified modules**, and **26 signatures**. Every final source or complete original-module diff passed parent and two independent reviews. Policy, whitespace, source hashes and **4997 protected original-file checks** pass.

All 124 surviving original preparation declarations retain exact same-name raw types and axiom arrays. Seven generated proof/simplification helpers move from prepare_ranges to prepare_reserved_receipt: four retain exact raw types, and three have recorded raw binder-name differences. All 131 original axiom arrays match using those explicit relocation pairs. The normal record preserves both raw hashes; it makes no normalized-type compatibility claim and introduces no obsolete aliases. These changes add proofs and static receipts. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

Next: connect the stronger primitive posts to actual emitted read/index constructors and early child failures through the existing folds. Derive query-specific diagnostic Source ownership from the real contextual factory and canonical occurrence uniqueness, retaining provenance in the same preparation loop. Retain coupled Catalog/structural lambda body extraction and connect the stronger runtime heads and typed invocation through strict mutual induction. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-08: actual read/index ports and authentic public diagnostic factories

The latest implementation checkpoint is `f0ddfaa3`, following `834f69b6` and `61824c61`.

Actual certified local reads retain their lexical binding and current cell witness through the concrete primitive post. Scalar and general mapping index adapters evaluate the actual ordered children, including the hidden key slot, then call the original terminal proof at the emitted reasonAt id. They preserve the same Source outcome, native result, final heap, map, world and effects. Extended paths retain early base and key failures; the existing full index folds still need to carry those posts.

The real contextual factory retains full-key singleton selection, the selected original Source, its active substitution and the exact ordered extraSources passed to diagnostic preparation. The original local catalog remains separate from its later callable rewrite. Local-read and index constructors, occurrence IDs and spans survive substitution. General forms and types are not equated; canonical occurrence uniqueness remains a genuine Source receipt. The same preparation loop still needs to retain actual index issuer provenance and coverage before these views establish the public reasonAt association.

The actual compatible, automatic and sealed factories now supply optional callable allocation at the issued preparation endpoint. Sealed read and missing-default decoder endpoints derive preparation and callable priority internally. Actual receiving table identity, selected read or MissingSite, raw metadata and runtime type views remain required. Read decoding retains the exact binder, occurrence and span; missing-default decoding retains the raw error and the original first selected duplicate span.

At `f0ddfaa3`, the registered Solcore modules and `Tests.Main` build passed **5451 jobs**. Strict verification checked **10910 declarations**, including **123 declarations attributed to five new modules**, and **45 signatures**. Each exact full source passed parent and two independent semantic reviews. Policy, whitespace, source hashes, regular normal objects and **4997 protected original-file checks** pass. This checkpoint adds only new proof modules and umbrella imports; existing runtime and semantic implementation modules remain unchanged. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

Next: carry early index posts through the original scalar and general folds once. Retain unconditional actual index issuer and selector coverage in the same preparation proof, then derive query-specific ownership from the genuine contextual views. Complete joint contextual lambda Catalog/structural body extraction and connect it to typed invocation through strict mutual induction. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-08: index failure folds, actual diagnostic issuers and joint lambda static bodies

The latest implementation checkpoint is `32cbe6b1`, following `250c2d61` and `9b670b52`.

The original scalar and general index preservation/reflection proofs now retain failure posts at the actual base or key child. Key failures retain the successful base trace and its exact middle heap. Concrete terminal adapters use the emitted reasonAt id and genuine Header, key and ordered child receipts. The original semantic result, final heap, map, world, store and effects stay paired with the primitive origin. The scalar/general fragment suppliers and larger expression/body folds still need to carry this stronger post internally.

Diagnostic preparation retains literal index issuers, per-key uniqueness and coverage of the actual ordered source/node prefixes in its existing loops. This receipt accepts arbitrary extra sources. Only finite contextual queries add the real factory's Source views and canonical occurrence uniqueness; they derive no-index priority for local reads and the first selected index's canonical form and span. Substituted issuer types remain distinct from canonical types. Public reasonAt/receiver composition and the selected MissingSite's own Source association remain separate work.

Contextual lambda generation retains the actual body-lowering recipe and binder policy. Shared static transport moves prepared assignment, unary, header and match packets with their exact mapped trees. A post tree retains its chosen Plan and tokens. The real view collector runs once, yielding a canonical typed body and prepared structural elimination. Genuine local views, reachability, both syntax certificates, the actual compiler children, native body typing and the complete ledger remain inputs. Connecting this joint static receipt to typed invocation through the same measured family is the next runtime proof unit.

At `32cbe6b1`, the registered Solcore modules and `Tests.Main` build passed **5457 jobs**. Strict verification checked **11194 declarations**, including **477 declarations attributed to eleven new or modified modules**, and **71 signatures**. Every final source or complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4994 protected original-file checks** pass. This checkpoint factors five existing proof modules and adds six proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **271 original axiom arrays** match against saved actual normal source and regular objects. **259 same-name raw types** match exactly. Twelve generated helpers have explicit relocation pairs: nine raw types match exactly, and three retain enumerated raw binder-name differences. Comparisons preserve the complete literal types and axiom arrays; no normalized comparison or obsolete generated alias is used.

Next: derive the stronger scalar Members fragment from its actual literal/read producers through the five original support cores. Compose real contextual reasonAt/receiver observations, retaining MissingSite/metadata authority. Consume the joint contextual lambda prepared body in the existing strict measured family. Complete callee classification, general rejection/coercion and stage coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: scalar failure origins, prepared lambda execution and Session diagnostic observations

The latest implementation checkpoint is `52999450`, following `bd7f9250` and `7cf8c705`.

The five original scalar expression proof modules now retain primitive failure posts in their existing preservation and reflection inductions. Actual grouping, ordered products, primitive operations, conditional branches, constructor arguments and member bases carry the same failure token, reached heap, map, world, store and model association. Concrete literal and read adapters supply their stronger results internally. The scalar index fold consumes this stronger fragment and preserves the successful base prefix when a key fails. Larger general, builtin, recursive and named expression folds remain to be connected.

Contextual lambda execution now consumes the actual joint prepared body. The owning Source's real assignment and diagnostic preparations supply finite operand and projected-fault laws. Genuine Source typing and reached readiness feed the original head, loop and flow producers. The actual prepared eliminator yields bounded flow preservation and reflection; strict admitted expression children then yield typed parameter-entry and body-finish continuations with independent Source and native grades. Precise reached-table interpretation remains an input. The actual function formation, storage and selection path must still retain this stronger body receipt inside the shared mixed family.

Public and Session diagnostic observations now compose the genuine contextual factory and callable allocation bounds with the actual receiving registry and rebuilt table. Local reads retain the exact diagnostic binder, identifier and span. Missing-index observations retain the first literal index issuer and the raw missing-type error. A sealed Artifact's real compiler authority is extracted only into a proof proposition. The selected MissingSite's membership, provider base, receiving metadata and runtime views remain genuine inputs; decoding alone does not establish a Source fault origin or heap association.

At `52999450`, the registered Solcore modules and `Tests.Main` build passed **5469 jobs**. Strict verification checked **11491 declarations**, including **297 declarations attributed to seventeen new or modified modules**, and **97 signatures**. Every final new source and complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4989 protected original-file checks** pass. This checkpoint factors five existing proof modules and adds twelve proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **141 original axiom arrays** match saved actual normal source and regular objects. **131 same-name raw types** match exactly. Ten generated support matchers move to the strengthened proof cores and have genuinely changed raw types, recorded in explicit pairs. The comparison retains complete literal types and axiom arrays without normalization, renamed binders or obsolete generated aliases.

Next: retain the joint prepared lambda body through actual function formation, local storage and selected invocation, then close its strict expression children in the shared measured family. Retain the actual selected MissingSite and its Source/type-mapping issuer in the original diagnostic preparation. Connect the stronger scalar post to larger general, builtin, recursive and named folds. General callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: recursive failure posts, missing issuer ownership and prepared ordinary lambda invocation

The latest implementation checkpoint is `09e65b60`, following `e7b74177` and `554c65df`.

The original recursive expression preservation and reflection folds now retain primitive failure posts through their existing inductions. Concrete literal, read and scalar-member providers are assembled internally. Ordered child traces retain the actual intermediate Source heap and the complete native result, map, world, store and model association. General, builtin and named folds remain to be connected.

The actual missing-diagnostic preparation now retains accepted expression suffixes and place routes in the same original proof cores. Each appended missing row keeps its literal Source issuer, mapping and result type views, selected key and provider reason. Checked fresh allocations prove both index reason ownership by full specialization key and separation from place reasons. Ordered coverage supplies missing membership and provider bases internally. Genuine contextual Source views and canonical uniqueness then identify the occurrence and span of actual expanded receiving rows. Public and Session observations still need to consume these stronger receipts; decoding alone does not establish a runtime Source fault or heap association.

Prepared ordinary lambda support now survives actual formation, capture, model extension, key embedding and exact value selection. The original stronger contextual producer selects one Site with its policy and body recipe. The same owning Source and joint prepared body stay indexed by that Code through recapture. Finite formation heads construct the actual nested Header packet, global frame reference and captured history. Genuine physical arity and independent raw and native bundles align the selected parameter vector. Strict children of the same expression family supply the prepared flow and typed body finish; the original invocation and apply proofs restore the current caller's complete pool with independent Source and native grades. The new model explicitly retains prior General alternatives. Their prepared-body population, generic stored-call parent composition, principal formation and shared mixed-family closure remain unfinished. Precise reached-table interpretation and outer stage/coercion routes remain genuine inputs.

At `09e65b60`, the registered Solcore modules and `Tests.Main` build passed **5476 jobs**. Strict verification checked **11783 declarations**, including **427 declarations attributed to nine new or modified modules**, and **75 signatures**. Every final new source and complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4988 protected original-file checks** pass. This checkpoint factors two existing proof modules and adds seven proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **175 original axiom arrays** match saved actual normal source and regular objects. **145 same-name raw types** and **four relocated raw types** match exactly. Twenty-three generated declarations move to the strengthened proof cores with genuinely changed raw types. Three existing private wrapper types also change because their generated constants belong to the new cores; their literal source headers remain identical. Every delta is recorded using complete literal types and axiom arrays, without normalization, renamed binders or obsolete generated aliases.

Next: connect the stronger recursive post to the original General fold and its actual index terminal. Consume internally derived missing membership and provider bases in public and Session observations, including the actual first row's span. Connect the exact prepared function model to the stored-call parent and shared measured family, and populate the remaining ordinary/principal routes. General callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: General failure posts and exact public/Session missing diagnostics

The latest implementation checkpoint is `7167660d`, following `fe7c0b09`.

The original General expression preservation and reflection folds now retain primitive failure posts through their two existing support inductions. Concrete literal, read, proxy, recursive and index providers are assembled internally. Index base and key failures keep their actual ordered Source prefix, intermediate heap and complete native result, map, world, store and model association. The terminal case retains the genuine Header, lookup form, base/key representations and exact `reasonAt`. Generic reflection has no added uniqueness assumption; concrete read and missing policies remain genuine pointwise inputs. Builtin, named, call and imperative joins remain to be connected.

Public and Session missing-diagnostic observations now derive missing membership and provider bases internally from the actual accepted preparation. Canonical base lookup and runtime mapping views, together with the genuine receiving metadata representation, identify the raw key and value views. Reserved ranges and fixed-row separation select the actual first rebuilt additional row. Full specialization-key ownership, Source views and occurrence uniqueness fix its raw error, occurrence and span. The same sealed allocation, table rebuild, registry and filtered callable append transfer the exact diagnostic to public and Session observations. A diagnostic observation alone does not provide a runtime Source fault, heap or event association.

Prepared ordinary lambda formation, storage, selection and invocation remain available from the preceding checkpoint. Connecting that exact function model to the stored-call parent and shared measured family remains unfinished. The proposed next factor retains the existing finite callee, guard, ordered argument and application proofs while making their model explicit. Genuine prior General alternatives, principal prepared population, initial and captured heap coverage, precise reached-table interpretation and outer stage/coercion routes remain separate obligations.

At `7167660d`, the registered Solcore modules and `Tests.Main` build passed **5479 jobs**. Strict verification checked **11851 declarations**, including **68 declarations attributed to four new or modified modules**, and **21 signatures**. All final sources and the complete original-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4987 protected original-file checks** pass. This checkpoint factors one existing proof module and adds three proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **49 original axiom arrays** match saved actual normal source and regular objects. **43 same-name raw types** and **four relocated raw types** match exactly. Two generated matcher declarations move to the strengthened support cores with genuinely changed raw types. Four existing compatibility aliases point to the actual relocated helpers and retain their exact raw types and axiom arrays. Every delta is recorded using complete literal types and axiom arrays, without normalization, renamed binders or new obsolete generated aliases.

Next: connect the exact prepared function model to the stored-call parent through the existing finite prefix proofs, then assemble the shared measured family and remaining ordinary/principal population. Carry the stronger General fault post through builtin and larger named/call/imperative joins. Runtime Source failure and heap attribution, general callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Builtin argument failure origins and reached mapping diagnostics

The latest implementation checkpoint is `cd5a61ab`, following `387cbe06`.

Builtin expression preservation and reflection now carry primitive failure posts through the original two support inductions and the two existing finite builtin-head proofs. Actual argument-list failures retain their Source evaluation prefix beneath the two inserted native slots, their failing child and their complete result, map, world, store and model association. Concrete literal, read, proxy, General and index providers are assembled internally. Successful represented builtin inputs exclude the actual builtin application-fault branch. Generic reflection adds no uniqueness assumption. Named, call and imperative fault joins remain unfinished.

A reached mapping-index failure now supplies the canonical mapping view and receiving metadata from its actual leaf fields, Source lookup and raw key/value runtime views. The genuine specialization and Source/reason issuer receipt, occurrence uniqueness and receiving-registry extension remain explicit. Existing first-row reconstruction, sealed public allocation and Session registry receipts then derive the exact raw missing-value diagnostic, occurrence and Source span. This observation does not establish a whole-program Source fault or identify the restored runtime heap or events.

Prepared ordinary lambda formation, storage, selection and invocation remain available. The stored-call prefix proofs are being factored to retain that exact function model. A compiler producer for a chosen contextual Site is also being connected to the existing static body collector. Genuine prior General alternatives, ordinary/principal population, initial and captured heap coverage, precise reached-table interpretation and outer stage/coercion routes remain separate obligations.

At `cd5a61ab`, the registered Solcore modules and `Tests.Main` build passed **5483 jobs**. Strict verification checked **11994 declarations**, including **143 declarations attributed to six new or modified modules**, and **38 signatures**. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. This checkpoint factors two existing proof modules and adds four proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **73 original axiom arrays** match saved actual normal source and regular objects. **67 same-name raw types** and **four relocated raw types** match exactly. Two generated matcher declarations have recorded literal type changes. The four existing compatibility aliases retain their exact raw types and axiom arrays while pointing to the strengthened helpers. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution or new obsolete generated aliases.

Next: connect the exact prepared function model to the stored-call parent through the existing finite prefix proofs, retain the actual compiler factory and chosen Site, then assemble the shared measured family and remaining ordinary/principal population. Carry fault posts through larger named/call/imperative joins. Runtime Source failure and heap attribution, general callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Prepared stored-call reflection, compiler ownership and reached read diagnostics

The latest implementation checkpoint is `219b4b63`, following `75d980c6`.

Stored indirect stage, callee, argument, application and parent prefixes now share their original proofs through an explicit function model. The existing General interfaces remain finite wrappers. The prepared parent retains the selected ordinary closure, its immutable captured history and the actual callee and argument posts. A new application reflection endpoint uses physical argument counts, the original whole fourth-bind bound and strict child body continuations. It restores the caller once from the actual argument state and retains the complete pool, cumulative effects and independent Source and native grades. Its forward preservation connection remains unfinished.

The contextual ordinary-lambda compiler producer now invokes the existing generation and joint static body collector once. Its receipt keeps the literal owning Compilation, diagnostics, emitted named code, chosen Site, complete solved ledger and body recipe. The actual mixed compiler factory, initial and captured heap coverage, prior General and principal branches, shared measured family and pointwise policy population remain separate obligations.

Admitted builtin outcomes retain the reached primitive fault path, its actual native evaluation and token, and the Source post admission. A finite determinism bridge aligns the same returned value because the generic expression post omits it. A reached read certificate also derives the exact binder, location and Source span in public and Session diagnostics. Genuine issuer, Source lookup, receiver registry and first-row receipts remain explicit; these observations do not establish whole-program Source failure or restored heap attribution. Larger sequence, named-call and imperative fault joins remain unfinished.

At `219b4b63`, the registered Solcore modules and `Tests.Main` build passed **5489 jobs**. Strict verification checked **12184 declarations**, including **261 declarations attributed to twelve new or modified modules**, and **42 signatures**. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. This checkpoint changes six existing proof modules and adds six proof modules. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **71 original axiom arrays** match saved actual normal source and regular objects. **57 raw types at their original names** match exactly. Fourteen declarations retain their names but have recorded literal lambda-binder name changes; these are counted as raw type changes, with separate Lean-expression equivalence evidence. Every original explicit declaration header remains unchanged. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution, relocation or generated compatibility aliases.

Next: connect forward preservation of prepared stored applications and authentic indirect compiler leaves, then assemble the shared measured family and remaining ordinary/principal population. Retain actual expression fault posts through readiness sequences, named calls, invocation restoration and imperative joins. Runtime Source failure and heap attribution, general callee classification, rejection/coercion and staging coverage, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Prepared stored-call preservation, actual compiler policy and reached argument faults

The latest implementation checkpoint is `51626f35`, following `3dc12014`.

Prepared stored indirect calls now have a forward preservation endpoint alongside the existing reflection endpoint. The shared finite suffix proof invokes the prepared body from strict children and restores the caller once at the actual argument state. The body-child and physical-count obligations apply only to the called suffix; an argument fault needs neither. The endpoint retains immutable captured history, the complete current argument pool, cumulative effects, genuine Source typing and independent Source and native grades. It still requires authentic selected closure, support, stage and caller receipts.

Ordinary closure facts now derive the original Source function type and closure frame from actual Source typing, runtime validity and evidence coverage. Indirect compiler receipts retain the owning Compilation, diagnostics, emitted named code, solved ledger and exact contextual special-body callback. Finite metadata producers derive the indirect pointwise policy agreement from that same selection. Actual initializer absence and empty raw requirements, node coercions and argument coercions remain genuine inputs. These additions do not establish a complete mixed compiler factory.

Admitted expression sequences now retain the reached fault post through their original readiness and reflection cores. Named argument-fault endpoints join that same ordered argument failure to the actual named call and emitted slot, retaining the primitive fault path, literal native token, Source outcome, current heap, cumulative effects and post admission. They do not cover named body failure or invocation restoration. The generic expression post still omits the returned native value, so an actual evaluation witness and determinism align the literal fault token; no inverse fault relation is assumed.

At `51626f35`, the registered Solcore modules and `Tests.Main` build passed **5498 jobs**. Strict verification checked **12500 declarations**, including **411 declarations attributed to eleven new or modified modules**, and **82 signatures**. The checkpoint changes two existing proof modules and adds nine proof modules. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. The most recent actual native and interpreted test executions remain those at `3ff3daf4`.

All **95 original axiom arrays** match authentic saved normal Source and regular objects. **91 same-name raw types** match exactly. Three generated reflection helpers have explicit relocations and literal type changes. One declaration keeps its name with a recorded literal lambda-binder name change; its separate saved-original Lean-expression equivalence check also passes. All **63 original explicit declaration headers**, including the stored-call completion inductive, remain unchanged. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution or generated compatibility aliases.

Next: populate the mixed compiler factory using the same selected policy at every child budget, then close the shared measured expression and body family. Retain reached named body faults through real invocation restoration and imperative joins. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Same-policy callable leaves, named body fault restoration and prepared primitive family members

The latest implementation checkpoint is `b3557065`, following `0d4387a9`.

The contextual compiler now produces ordinary-lambda and indirect-call leaf receipts under one actual root policy. It retains the owning Compilation, selected special-body callback, body recipe, allocator, raw body and expression hooks, callable profile, projector and solved ledger. Each leaf uses the actual generic child acceptance at its original child budget. Lambda selection and joint static extraction occur once at the same chosen Site. The original Generation entry remains available with its exact declaration header. Complete mixed compiler-tree population remains unfinished.

Named invocation now retains a body fault post through actual caller restoration. The original finite preservation and reflection cores are shared with compatibility wrappers. The receipt keeps the genuine parameter/body entry, literal native fault token, Source outcome and heap, cumulative effects, complete current pool and actual pre-restoration body store. Restoration runs once at that body post; the fault predicate is not assumed invariant under arbitrary stores. Source and native body grades remain independent. Producing the post from the full imperative body and carrying it through outer expression heads are subsequent obligations.

Prepared primitive bodies now derive admitted expression preservation and reflection internally from their actual support certificate and builtin compiler tree. Ordinary literal context validity, read policies and missing policies remain genuine pointwise static inputs at the same certified context. The resulting expression family supplies actual flow and typed Source/native parameter continuations. Native flow reflection uses the original strict bound at size+1 without equating it to a Source grade. Finite smaller-member extraction reuses the existing measured family interface; the full mixed recursive family remains unfinished.

At `b3557065`, the registered Solcore modules and `Tests.Main` build passed **5504 jobs**. Strict verification checked **12670 declarations**, including **268 declarations attributed to eight new or modified modules**, and **47 signatures**. The checkpoint changes two existing proof modules and adds six proof modules. All sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

All **98 original axiom arrays** match authentic saved normal Source and regular objects. **96 same-name raw types** match exactly. Two generated named-invocation helpers have recorded relocations and literal type changes. All **36 original explicit declaration headers** remain unchanged. Comparisons use complete literal types and axiom arrays, without normalization, binder substitution or generated compatibility aliases.

Next: populate the actual mixed compiler Tree from the same-policy leaf receipts, then close the shared measured expression and body family. Carry named body fault posts through the outer named-call heads and derive them from actual imperative body producers. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Mixed compiler trees, named-call body posts and actual prepared formation

The latest implementation checkpoint is `2de0da30`, following `4434e246`.

Compiler extraction now combines named calls, ordinary lambdas and indirect calls in one finite call-head family. Lambda parent metadata and Source frame facts come from the same accepted branch and genuine Source typing. Indirect calls retain their physical callee and ordered argument entries, including duplicates. Static metadata covers actual admitted extra nodes before acceptance; native typing and collector inputs apply to successful accepted lambda children. The existing compiler induction builds the mixed Tree once under the same root policy and body recipe. This result covers the canonical caller Source and native prefix; mixed coverage of each selected body's own certificate factory remains unfinished.

Named call expressions now retain the selected body post through their original finite preservation and reflection cores. The route distinguishes actual argument failure from invocation after successful arguments. Invocation retains the live argument-state capture, original ReturnedAt receipt at bodyStore, complete reached pool and literal equality from the outer caller restoration. Source and native grades remain independent. The original outer named/direct dispatcher is unchanged; forwarding this stronger route there and deriving body posts from real imperative producers remain subsequent work.

Prepared formation now attaches its literal ordinary body index to the actual formed closure. The producer calls the original formation once at identity inclusion in the unchanged prepared model. Its returned relation supplies native typing; the known captures, Code, Support and history construct membership directly. Finite map/world and key transports retain the same body and captured history. All prior model cases remain available. Carrying this receipt through actual storage, reads and returns, and covering initial/prior/principal closure population, remain unfinished.

At `2de0da30`, the registered Solcore modules and `Tests.Main` build passed **5509 jobs**. Strict verification checked **12808 declarations**, including **172 declarations attributed to six new or modified modules**, and **40 signatures**. This checkpoint changes one existing proof module and adds five proof modules. All final sources and complete original-module diffs passed parent and two independent semantic reviews. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

All **34 original same-name raw types and axiom arrays** match authentic saved normal Source and regular objects exactly. All **28 original explicit declaration headers** remain unchanged. Replacing only the two factored call cores and removing their new providers/import reconstructs the original Source byte for byte. The raw comparison uses complete types and axiom arrays, without normalization, binder substitution or generated aliases. The mixed compiler inventory uses actual imported module indices, including eight deferred Head equation declarations generated in the Certificates module.

Next: attach mixed compiler coverage to each actual selected body factory, carry formed membership through real storage/read/return producers, and populate the runtime mixed heads from strict shared-family children. Forward named body posts through the outer named/direct dispatcher and derive them from actual imperative producers. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Selected body factories, primitive named body fault producers and finite mixed runtime branches

The latest implementation checkpoint is `a6896205`, following `d7ae55e9` and `94413e52`.

The selected lambda compiler receipt now retains its actual collector inputs, certificate factory, read fuel and body entry. Mixed body certificates use these same inputs under the original root policy and body recipe. At the current Source context and scope, the existing compiler induction derives trees for named calls, ordinary lambdas and indirect calls, including the physical callee and ordered arguments. Recaptured support keeps the same factory. Source admission, metadata, native typing and assignment readiness remain explicit requirements; this does not yet establish runtime meaning for every body.

A named function whose body is one primitive expression, either a trailing expression or an explicit return, now has preservation and reflection of its body fault post. The proof derives the fault path from the actual child execution and runs the original builtin expression proof once. It retains the literal native token, Source fault and reached heap, and the actual store when the body finishes. Source and native grades are independent. These producers feed the existing named body-post interfaces; they do not cover arbitrary imperative bodies or return an additional native-bound packet.

Finite runtime adapters now connect the actual mixed named and lambda constructors to their existing proofs. Lambda adapters use the same chosen receipt and compiler fields. Named adapters obtain body continuations from strictly smaller members at the actual parameter receipt. Selected prepared ordinary calls obtain expression continuations from the actual captured body index; the original ordered argument effects, whole fourth-bind bound and caller restoration remain intact. The full prepared function model, including prior alternatives, is unchanged. These adapters do not close the mixed runtime family or recover formed membership from an opaque stored value.

At `a6896205`, the registered Solcore modules and `Tests.Main` build passed **5514 jobs**. Strict verification checked **13048 declarations**, including **242 declarations attributed to six new or modified modules**, and **45 signatures**. This checkpoint changes one existing proof module and adds five proof modules. All final sources and the complete modified-module diff passed parent and two independent semantic reviews. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Both original declarations in the modified module retain their complete same-name raw types and axiom arrays. Both explicit declaration headers, original imports and the indirect-call implementation remain unchanged. The comparison uses authentic saved normal Source and regular objects, without normalization, binder substitution or generated aliases. Inventories attribute declarations by their actual imported module indices.

Next: use the retained body factories and finite runtime branches to populate and close the shared measured family. Carry formed membership through actual storage, reads and returns. Extend named body fault producers to imperative bodies and forward their posts through the outer named/direct dispatcher. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen body runtime, initialized stored members and sequential named fault posts

The latest implementation checkpoint is `1d2aea21`, following `4ec24148` and `eb30a3e4`.

Lambda formation now retains a positive receipt for the chosen compiler factory at its actual ordinary body index. The original formation proof runs once; the same capture, code, support and prepared body remain attached to its result. Preservation and reflection of expressions in that support use the existing admitted runtime fold at the actual owning caller. This bounded domain excludes indirect calls throughout the Source graph and still requires strictly smaller named-family members and the current static compiler and diagnostic policies. It does not close the full mixed family or connect the base parameter carrier to nested body continuations.

A known prepared ordinary function now remains qualified through actual initialized allocation, writes and local reads. Allocation retains the real three native cells and capture/frame receipts. Read qualification uses the actual binder, Source cell and native optional payload; the nominal cell type stays separate from the reported occurrence type. The original callee post and parent prefix retain their native and Source grades, gate and conditional resolver. Future heap/store transport requires actual reads of the same payload. Broad heap representation does not recover membership or the stronger chosen-factory receipt, and prior, principal and global alternatives remain open.

Named bodies containing a discarded builtin expression followed by a trailing expression or explicit return now derive their fault posts from their actual executions. A fault in the first expression stops before the suffix. A successful first expression supplies the reached middle heap, native store, admitted state and all stable rows used by the next expression. Each executed child uses the original builtin proof once. The Source fault path and native prefix share the same middle witness and final primitive origin, token and body store. Source and native grades remain independent. General imperative bodies and forwarding these posts through the outer dispatcher remain unfinished.

At `1d2aea21`, the registered Solcore modules and `Tests.Main` build passed **5520 jobs**. Strict verification checked **13122 declarations**, including **74 declarations attributed to six new proof modules**, and **38 signatures**. All six complete sources passed parent and two independent semantic reviews. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Existing proof-module sources are unchanged; inventories use actual imported module indices, including generated declarations. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: connect typed nested body continuations to the actual chosen runtime factory and shared measured family. Retain the stronger chosen receipt through actual stored values and construct selection from known ordinary members. Extend named body fault producers to imperative bodies and forward their posts through the outer named/direct dispatcher. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen nested continuations, retained factory selection and outer named body posts

The latest implementation checkpoint is `ac58faf5`, following `eb8d42b0` and `9f194b00`.

A chosen ordinary lambda now derives its nested body continuations from its actual compiler Support. Genuine parameter packets, Source typing and all stable rows supply the same nested state. The existing runtime fold feeds the original prepared flow and typed finish proofs. Their result retains the actual packet, complete pool, exit and readiness; the base continuation projects that same returned state. This domain still excludes indirect calls throughout the Source graph and requires strictly smaller named-family members and pointwise compiler, model and diagnostic policies.

The positive receipt for the chosen factory now survives actual initialized allocation, writes and local reads at the known ordinary index. Callee qualification retains the same original post and parent prefix, including the actual Source closure and native payload, map/world extensions, separate grades, gate and conditional resolver. The actual lexical occurrence and compiler read type construct ordinary selection. Coverage of initial closures and the prior, global and principal alternatives, physical arity and complete dispatch remain separate obligations.

The outer named/direct dispatcher now retains the actual selected low call route beside its root outcome. Its two finite cores are shared with the original wrappers. Bodies containing a single builtin, or a discarded builtin followed by a final builtin expression or return, obtain their parameter Source receipt and all stable rows from the actual successful arguments. Their proofs retain the body fault post through the existing invocation and caller restoration. The post remains at the actual body store; root Source, low call and native grades remain independent. General imperative body paths and the full measured family remain unfinished.

At `ac58faf5`, the registered Solcore modules and `Tests.Main` build passed **5525 jobs**. Strict verification checked **13248 declarations**, including **164 declarations attributed to five new proof modules and one modified module**, and **53 signatures**. All six complete sources and the complete modified-module diff passed parent and two independent semantic reviews. All **38 original complete raw types and axiom arrays** and **32 original explicit declaration headers** remain unchanged. Comparisons retain every line of each literal type without normalization or aliases. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: feed positive chosen ordinary members into actual accepted invocation and close the shared measured family. Extend concrete named fault paths to broader imperative bodies. Initial and captured heap coverage, prior General and principal selection, general callee classification, physical rejection, coercion and staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen invocation, accepted argument receipts, conditional body posts and local formation

The latest implementation checkpoint is `4246eb3d`, following `350a2921`, `30d7b328` and `b55a5b86`.

Invocation of a positively chosen ordinary closure now uses the original typed invocation proof with continuations derived from its actual compiler Support. The source and native endpoints retain the same owner, capture, history, live heap, argument packet and complete returned pool. Their finite application adapters preserve the original Source and native grades. The body domain still excludes indirect calls throughout its Source graph and requires strictly smaller named-family members and pointwise static and diagnostic policies.

Selected-call receipts retain the exact callee post, genuine first-stage acceptance, physical arity, dispatch row and successful ordered arguments. Qualification consumes one actual success step; its fourth-bind bound, argument effects and current admission stay attached to the same chosen closure. It does not construct a complete parent invocation or classify arbitrary function values.

Conditional named bodies now retain the fault from the actual condition or selected return branch. Both directions follow the real compiler finish, sequence, conditional and fallthrough wrappers, including the empty tail. The unselected branch is not evaluated. The post keeps the same primitive origin, body store, Source heap and token. Connecting this producer to the outer dispatcher and extending it to broader imperative bodies remain separate steps.

Ordinary closure formation now has a shared core accepting a static membership constructor for the same actual closure and its independently obtained native typing. Existing public wrappers retain their exact types and headers. Each direction uses one actual formation tuple, keeping the full heap, packet, post and effects. This enables a stronger function model to retain the positive chosen factory; it does not populate that model by itself.

At `4246eb3d`, registered Solcore modules and `Tests.Main` built successfully (**5529 jobs**). Strict verification checked **13354 declarations**, including **149 declarations attributed to four new proof modules and one modified module**, and **47 signatures**. All complete sources and the modified-module diff passed parent and two independent semantic reviews. All **43 original complete raw types and axiom arrays**, including generated declarations, and **12 original explicit declaration headers** remain unchanged. The comparisons include every line of each literal type. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: assemble the actual accepted stored-call parent from the chosen callee and argument receipts, populate a function model retaining the positive chosen factory, and connect conditional fault producers to the outer named dispatcher. The shared mixed family, initial and captured heap coverage, prior General and principal selection, general callee classification, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen function model, accepted stored parent and outer conditional fault posts

The latest implementation checkpoint is `529e4c2c`, following `04c98460`, `af5f8ef7`, `f8f9b774` and `0718b79e`.

The function value model now retains the actual chosen compiler factory, capture index, history and independently typed closure. Its prior branch retains the existing General representation. Forward forgetting is available; recovering a factory from an arbitrary prior value is still unproved. Actual formation receipts populate the positive branch through the shared formation core. Source and native expression heads use the same model and retain the complete heap, packet, post and effects.

The accepted stored-call adapter composes the real selected callee, ordered arguments, physical arity and current argument state with the chosen invocation proof. Both directions retain the original body continuation and full returned pool. Native reflection uses the authentic successful argument step and whole fourth-bind bound. The owning Source domain still excludes indirect calls, and strict callee induction and arbitrary callee classification remain separate obligations.

Conditional fault producers now feed the outer named dispatcher. Actual compiler acceptance derives the finish/sequence/conditional/return/fallthrough envelope, including the empty tail. The original argument and parameter receipts keep body-entry admission, stable rows and the same causal primitive fault, heap and token. Each direction uses the original conditional producer and outer call core once. Broader imperative bodies and complete static policy population remain open.

At `529e4c2c`, registered Solcore modules and `Tests.Main` built successfully (**5535 jobs**). Strict verification checked **13508 declarations**, including **155 declarations in separate inventories of six new proof modules**, and **54 signatures**. The separate inventories share one generated lemma, counted once in the combined audit. Every complete source passed parent and two independent semantic reviews. No original proof modules changed in this checkpoint. Policy, whitespace, exact Source hashes, regular normal objects and **4985 protected original-file checks** pass. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: generalize the existing body and invocation proofs to the chosen function model, connect strict callee induction to accepted stored parents, and extend outer fault posts to broader imperative bodies. The sole mixed-family closure, initial and captured heap coverage, prior General and principal selection, general callee classification, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Receiving function models, strict callee posts and lexical named-body faults

The latest implementation checkpoint is `ae0f3086`, following `9b8510f9`, `ad21b5c2`, `d35da032`.

The existing body, nested-continuation and invocation proofs now accept the receiving function model. They retain genuine formation membership, parameter Source receipts, current admission, the complete row pool and the actual selected body factory. Existing prepared-model APIs forward to these shared cores with their original types. The chosen model still retains the genuine General prior branch; these proofs do not recover a chosen factory from an arbitrary prior value.

The actual strict callee child now supplies its complete reached post and the model's selection at that same tuple. A callee fault retains the actual child post and stops before arguments. Accepted stored-call adapters receive the selected current model, complete ordered argument post and genuine physical dispatch receipts. Their body and caller-restoration proofs run once. The selected body's owning Source domain still excludes indirect calls; it remains distinct from the parent call's Source. Arbitrary callee qualification and the full mixed-family closure remain open.

The original lexical Tree, control and function-finish cores now carry a causal fault witness alongside their usual result. Their existing wrappers keep their exact APIs. The witness follows actual allocation, condition, branch, prefix and block joins and retains the current heap, all stable rows, native token, independent Source/native grades and final body store. A concrete named-body producer derives its builtin expression ports internally and uses those same Tree and finish proofs. Its current domain is finite discarded-expression prefixes ending in a final expression or an explicit return. Empty bodies, allocation prefixes and broader imperative producers remain separate work.

At `ae0f3086`, all registered Solcore modules and `Tests.Main` built successfully (**5540 jobs**). Strict verification checked **13762 cumulative declarations**, **450 declarations attributed to 14 new or modified proof modules**, and **166 signatures**. All **197 original declarations**, including generated helpers, retain their complete same-name literal types and axiom arrays. One original generated helper belongs to an already imported formation module; the normal audit checks its actual global declaration without counting it twice. The cumulative increase is 254 declarations.

All 14 frozen Sources passed strict compilation with warnings treated as errors. Two independent reviewers read every complete Source and all original-module diffs. The parent read all complete Sources outside the three original lexical modules, every added lexical proof region, and all four new lexical modules. Separate parent installation guards checked the exact reviewed hashes, authentic normal snapshots and complete literal original types. The integrated normal audit confirms actual imported modules, regular Source and object files, policy, whitespace, English text and **4985 protected original-file checks**. This checkpoint changes nine existing proof modules, adds five proof modules and updates the aggregation imports. Actual native and interpreted test executions remain those at `3ff3daf4`.

Next: derive the positive chosen-model callee post from a real initialized local read, connect that post to the actual accepted indirect parent, and extend the concrete named-body producer to an absent local allocation followed by its supported suffix. Keep the sole measured family induction. Initial and captured heap population, prior General and principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Chosen storage/read posts, strict indirect prefixes and absent local allocation

The latest implementation checkpoint is `3c770d21`, following `9469886c` and `5def781c`.

Actual initialized writes and marked allocations now retain the chosen receiving function model and the same known ordinary member. The existing heap producers run once. Allocation retains the capture, frame, marker, optional payload and literal map/world extension. An actual initialized local read keeps that positive member and constructs selection from independent occurrence and nominal-type receipts. Its callee endpoint derives the complete value post, Source admission and current pool. A separate same-post association endpoint identifies an already produced callee post using the real read witness; it does not run another read producer.

The strict callee child now supplies a conditional accepted indirect-parent resolver at its exact reached tuple. Both directions retain the actual chosen closure, original physical dispatch and stage facts, ordered arguments, argument faults, body effects and full returned pool. Native reflection also retains the original whole fourth-bind bound and successful prefix. Callee faults stop before arguments. The genuine positive chosen index and compiler/type/dispatch receipts remain required; arbitrary prior values are not classified by these endpoints.

The lexical named-body producer now exposes the same shared proof through additive `StaticBodyInputs`, without the earlier discard/return profile restriction. The original `BodyInputs`, public headers and wrappers remain unchanged. A concrete producer constructs a genuine absent local declaration followed by the supported discard/return suffix, then invokes the original lexical Tree and finish proofs once. It retains the allocated middle heap, current frame and all rows, causal fault, independent grades and actual final body store. Initialized declarations and forwarding these lexical body posts through the outer named/direct dispatcher remain next steps.

The accepted chosen invocation still requires `NoIndirect` over its entire owning Source. The parent call's Source may be distinct. This is a real domain restriction: when the actual parent and selected body use the same owning Source, the parent's indirect occurrence contradicts that hypothesis. The current endpoints therefore do not close a same-Source mixed runtime family. The next domain factor must use genuine static body/support coverage while retaining the actual chosen factory, nested bodies and strict children.

At `3c770d21`, all registered Solcore modules and `Tests.Main` built successfully (**5544 jobs**). Strict verification checked **13832 cumulative declarations**, **124 declarations attributed to five new or modified proof modules**, and **32 signatures**. All **54 original declarations**, including generated helpers, retain their complete same-name literal types and axiom arrays. All 124 private declaration blocks also match the normal compiled declarations literally. The cumulative increase is 70 declarations. Actual module ownership includes the generated `extendIndex.congr_simp` helper in the stored-post module; it is counted once.

All five complete Sources and the full 313-line original-module diff passed parent and two independent semantic reviews. Separate parent installation guards checked exact reviewed Source and regular object hashes, authentic before snapshots and actual compiled imports. The normal audit confirms **2225 actual project imports**, regular Source and both object files, policy, whitespace, English text and **4985 protected original-file checks**. This checkpoint changes one existing proof module, adds four proof modules and updates aggregation imports. Actual native and interpreted test executions remain those at `3ff3daf4`; this checkpoint changes proofs only.

Next: replace the whole-Source exclusion with genuine body/support coverage at the existing proof cores, connect initialized-read callee receipts to nonvacuous mixed runtime leaves, and forward lexical/absent-allocation body posts through the existing outer named/direct dispatcher. Keep the sole measured family induction. Initial and captured heap population, prior General and principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Invocation proofs with body domains and lexical outer call posts

The latest implementation checkpoint is `30658fc4`, following `13eb4e17` and `d97e6b75`.

The new chosen invocation path requires `NoIndirectOn` only for the expressions approved by the selected body factory. An indirect parent elsewhere in the same retained Source no longer contradicts this condition. Compiler coverage retains the actual approved occurrence on extra leaves and derives the non-indirect form of named leaves from their real receipts. The existing compiler fold and runtime head, tree and support proofs each run once. The legacy `NoIndirect`, certificates, public types and wrappers remain unchanged.

That restriction now passes through the actual nested continuation, payload application, ordered argument state and accepted stored parent. The scoped static inputs retain the same chosen factory, captures and diagnostics when map/world proofs extend. The source and native indirect endpoints build the strict callee post internally and keep prior alternatives, physical dispatch, argument faults, the whole fourth bind and the exact restored caller pool. These remain conditional producers: an actual chosen member, accepted compiler/dispatch receipts and supported body inputs are required. They do not construct those inputs automatically or close the complete mixed family.

A concrete outer named-call producer now obtains lexical body ports from the existing discard/return and absent-allocation producers. Actual argument evaluation constructs the real named parameter receipt, Source admission and stable rows. The original outer-call core then carries the same body result, causal fault, native token, final body store, independent execution grades and reached caller tuple through one physical restoration. Argument faults retain their real outer route. Initialized declarations, arbitrary blocks and branches are outside these concrete producers' current domain.

At `30658fc4`, all registered Solcore modules and `Tests.Main` built successfully (**5545 jobs**). Strict verification checked **13930 cumulative declarations**, **400 declarations across eight audited proof modules**, and **73 signatures**. One audited selected-call module is unchanged. All **302 original declarations** and all 400 private declaration blocks retain their complete same-name literal types and axiom arrays. Generated declarations are included and counted once under their actual module ownership; no supplements were needed. The cumulative increase is 98 declarations.

Each of the seven changed or new source files and every original-module diff received at least two complete reviews independent of its author. The parent read the two compiler/runtime files, the new outer-call producer, both complete diffs and the stored-parent parameter block; its independent guards verified all reviewed hashes, original types, regular source/object files and actual import closures. The normal audit confirms **2224 actual project imports** against the recursive compiled import graph and **4985 protected original-file checks**. Two unchanged-source consumers rebuilt their `.olean` files after their affected imports changed; their original Source and `.ilean` bytes remain exact, and the guards record the actual build and import paths. This checkpoint changes six existing proof modules, adds one proof module and updates the aggregation import. Actual native and interpreted executions remain those at `3ff3daf4`; this checkpoint changes proofs only.

Two parent metadata checks were corrected during verification: one omitted the audit's separate `COUNT` records; the other treated the two expected dependent rebuilds as unexpected changes. Final metadata checks pass. No proof changes or compiler reruns were required for these corrections.

Next: populate the chosen factory and supported body domain from actual accepted compiler results, starting with the checked literal-return lambda and its same-Source indirect parent. Use these genuine receipts to close the shared measured family. Extend the concrete body producers for initialized declarations and broader imperative bodies. Initial and captured heap population, prior General and principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Mixed lexical call posts and an accepted literal lambda fixture

The latest implementation checkpoint is `3c2026ca`, following `7e66e744`, `adb7db57`, `712e95bb` and `8ef65a35`.

The mixed lexical body producer now derives causal Source/native body posts from genuinely smaller expression children. Actual arguments construct the named parameter receipt, Source admission and stable rows. The outer named expression adapters consume these internally constructed body ports and the original ordered argument producer once. They retain the actual body store, independent execution grades, fault origin, restored caller pool and strict native completion bound. Static body typing, compiler receipts and the strict child induction remain genuine inputs.

Literal lambda static facts are derived from an independent Source lambda typing judgment and the actual compiler/frame receipts. A literal-root receipt retains one original contextual selector, its authentic plan record and the fixed read budget of the prepared compiler. The literal body shell constructs parameter entry, return syntax and native body typing internally. Its local domain excludes indirect calls only at the approved literal occurrence; an indirect parent elsewhere in the same Source is allowed. Source typing, runtime/Covers, constructor/profile coverage and broader builtin static facts remain explicit inputs to this conditional construction.

The new accepted fixture uses the actual parser, checker, worklist and public preparation for `accepted()`, whose local lambda returns `7` and whose indirect parent calls it with `(1, 2)`. It retains the untouched Source, original named slot, cached code, contextual compilation equations, numeric requirements and their valid evidence. The parent output is proved at the same selected initializer root using pointwise ordinary-branch equality. The proof keeps the original initializer budget 499, parent budget 498 and fixed read budget 500. It derives no equality between policies at different budgets.

A computable finite graph receipt derives the original occurrence-graph invariants: unique occurrence IDs, owned nodes/roots and existence of roots/child edges. Together with the real numeric ledger and declaration-context fields, it supplies `SourceRuntimeValid` for the fixture. Genuine lambda typing and the association of that context with the actual public Header remain to be constructed. Chosen factory/support population, whole mixed-family closure and Source/Core execution equivalence for the fixture remain open.

At `3c2026ca`, all registered Solcore modules and `Tests.Main` built successfully (**5553 jobs**). Strict verification checked **14618 cumulative declarations**, **691 declarations attributed to nine new or modified modules**, and **74 signatures**. All 691 private declaration blocks and all **three original declarations** retain their complete same-name literal types and axiom arrays. Only the three permitted standard axioms occur. The cumulative increase is 688 declarations. The newly registered fixture checker was executed successfully against the normal cache; it checks actual compiler and metadata receipts. The existing full registered test executions remain those at `3ff3daf4`.

All nine complete Sources passed strict compilation with warnings treated as errors, and each received at least two full semantic reviews independent of its author. Normal installation copied Source files only. Independent guards confirmed the reviewed Source/object hashes, **2225 pre-install Source/object pairs**, and exact agreement between **2221 actual compiled project imports** and the Lean environment. Two unchanged-source consumers rebuilt their `.olean` files after the original body-post module changed; their Source and `.ilean` bytes remain exact, and actual build/import paths explain those rebuilds. Policy, English text, registration, whitespace and **4985 protected original-file checks** pass. The checkpoint changes one existing proof module, adds seven proof modules and one test module, and updates the proof umbrella and test import/runner.

Next: construct independent lambda Source typing and actual public Header/context receipts for the accepted fixture, then populate its literal shell/domain and chosen factory from those genuine inputs. Feed those receipts into the sole measured mixed family. Initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Accepted literal Source typing and original public Header

The fixture retains the original accepted specialization, lambda initializer and indirect parent in one unchanged Source. Finite metadata checks now prove absence of matches, empty coercion rows, the actual parameter inventory and successful Core projection of the literal return type. Independent declarative Source rules construct the lambda's parameter context, numeric literal typing, return statement, body typing and completion summary. Core typing is not used to infer these Source judgments.

The public Header association comes from the original specialization worklist, exact cached row, original compilation and genuine Source frame validity. It retains the Source owner, assumptions, parameter layout, body roots, ledger, contextual policy and actual compiler acceptance. This constructs the Header/context correspondence and runtime validity without a body execution or whole-program well-formedness premise.

The literal shell now requires equality of place diagnostics rather than equality of the entire program metadata. Installing the callable root table changes that metadata but preserves the actual places and their diagnostic reasons. The construction still uses genuine Source typing, compiler/frame receipts, runtime coverage and static builtin/constructor facts. The older shell remains unchanged.

Implementation commits: `2cacd8e1` (body metadata), `ca33552c` (independent lambda typing), `c7273ade` (original Header and checker registration), and `67a50253` (place-diagnostic shell and proof registration).

At `67a50253`, all registered Solcore modules and `Tests.Main` built successfully (**5557 jobs**). Strict verification checked **14863 cumulative declarations**, **245 unique declarations attributed to four added modules**, and **59 signatures**. All **246 private declaration occurrences** have exactly the same complete literal types and axiom arrays as the normal build. The generated `Tests.SourceCoreChosenOrdinaryAcceptedFixture.initialScope.eq_1` helper belongs to both isolated private inventories for BodyMetadata and Header, but to BodyMetadata in the combined normal inventory. Both occurrences match exactly. Only the three permitted standard axioms occur. The cumulative increase is 245 declarations.

All four complete Sources passed strict compilation with warnings treated as errors and received at least two independent full semantic reviews. Installation copied Source files only. Guards confirmed **2221 unchanged pre-install Source/object pairs**, exact agreement between **2211 actual compiled project imports** and the Lean environment, regular Source/olean/ilean files, and **4985 protected original files**. English, policy, registration and whitespace checks pass. Three newly registered checkers ran successfully; they validate actual compiler and static receipts, and do not establish Source/Core execution equivalence. Full registered executions remain those at `3ff3daf4`.

Next: construct independent typing of the outer let/indirect-call body, populate the literal shell/domain and chosen factory from these actual receipts, and connect them to the sole measured mixed family. Initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Accepted outer body typing and literal Source input population

Independent declarative typing now covers the actual outer let, its fresh local binder and paired requirement tables, both numeric argument literals, their physical pair, the indirect call and the return. The complete body and completion summary are transported to the original public Header using its actual inferred result and context. All node types, numeric evidence and Source rows remain unchanged.

A finite check identifies every retained Source node through actual lookup receipts. It proves absence of unary assignments, value assignments, for-header assignments and constructors, and identifies the five numeric/local-reference/tuple rows in the builtin fragment. The original root's read and special callbacks retain their actual ordinary and generalized-local gates at each child scope and budget. The constructor law holds at the genuine residual context through form absence.

The selected compilation's diagnostic row and original preparation now construct an IssuedSource with the actual assignment table and place providers. The same-Produced callback retains its diagnostics, code and Compilation identities. The accepted Header, lambda typing and body metadata supply the literal shell's remaining local Source fields. Genuine issuer and policy/view identity inputs are retained by that shell adapter; automatic population of the entire chosen factory is still incomplete.

Implementation commits: `7124d2d6` (original diagnostic issuer), `6f6a199e` (outer Source typing), `494a8a8d` (full finite static inventory), and `c2ec5a7a` (literal Source inputs and test registration).

At `c2ec5a7a`, all registered Solcore modules and `Tests.Main` built successfully (**5561 jobs**). Strict checks verified **15036 cumulative declarations**, **173 declarations across four added modules**, and **53 signatures**. All 173 private complete literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. Every Source passed strict compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2225 pre-install Source/object pairs** and **4985 protected original files**; **2215 actual compiled project imports** match the Lean environment exactly. Registration, English, policy and whitespace checks pass.

The two new finite checkers executed successfully against the normal cache. They check actual compiler/static fields and do not establish Source/Core execution equivalence. Full registered executions remain those at `3ff3daf4`.

Next: derive native typing of the actual initializer before Site selection, construct singleton catalog order and SourceTypes from original specialization/signature receipts, and populate the chosen literal factory without an external body execution premise. Then feed this support into the sole measured mixed family. Initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Native typing and automatic selection of the literal body factory

The actual initializer now has Core typing before a lambda Site is selected. Its original accepted certificate supplies the real parameter compiler and literal body callback. The singleton parameter projection determines the packed native bundle; the unchanged native prefix supplies the frame cell, and the original expression hook supplies the callable descriptor. The proof uses no Produced, Site or completed body execution law as an input.

Original worklist specialization and executable checker interface receipts now determine the singleton Header catalog's raw parameters and specialized result. They construct SourceTypes in the genuine receiving context using its signature equality. Lexical variables and residual mode remain unchanged. The finite Source inventory supplies builtin read/special callbacks and constructor/coercion facts at each actual child scope.

The fixture now constructs the original diagnostic issuer, literal body inputs and shell internally. Its initializer selects one lambda Site, retaining the same Compilation, policy, body recipe, Source view and reason provider. The approved domain is fixed to literal occurrence 3 before collection. The chosen factory retains the actual collector inputs, certificate family and body entry. Its read budget is the original indexed budget 500; the initializer's lambda certificate uses compiler fuel 498. The independent static read index changes no generated code or execution budget.

`chosen_initializer` obtains the original named compilation and initializer root internally. `globals_at` and `domain_at` construct the literal compiler domain from the actual catalog, inventory and Source inputs. The Source still contains the outer indirect call at occurrence 5. This checkpoint constructs the chosen static factory and domain; the same recaptured Support's runtime meaning and the complete measured mixed family remain unfinished.

Implementation commits: `69b301b2` (original catalog SourceTypes), `bec71734` (native typing before Site selection), `22b4f9e0` (original issuer and body inputs), and `024a3491` (chosen initializer factory, literal domain and test imports).

At `024a3491`, all registered Solcore modules and `Tests.Main` built successfully (**5566 jobs**). Strict checks verified **15093 cumulative declarations**, **57 declarations across five added modules**, and **34 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. All five complete Sources passed strict compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2229 pre-install Source/object pairs** and **4985 protected original files**. **2219 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass.

The five added modules are proof connections and add no executable checker. Existing full registered executions remain those at `3ff3daf4`; earlier finite fixture executions remain recorded at their original checkpoints. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts are not progress percentages.

Next: derive each current-context domain and the local absence of indirect calls from the same chosen and recaptured Support, then prove the literal body meaning from its original expression and finish receipts. Retain the outer indirect parent and genuine capture, parameter and heap identities. The complete mixed family, initial/captured heap population, prior General/principal qualification, complete dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Selected literal return semantics

Original singleton return receipts now retain the compiler's actual child, emitted finish and callback budget. The literal factory derives its current-context domain and expression coverage from the same selected Support. Its approved domain remains literal occurrence 3; the unchanged outer Source contains the indirect parent at occurrence 5. The indexed read budget 500, initializer compiler fuel 498 and independent Source/native execution grades remain separate.

The actual Word node and its selected numeric evidence prove admitted expression preservation and finite-completion reflection. Both use the existing literal producer and retain the same initial heap, store, mapping, world and complete ordered record vector. No whole-program well-formedness or finished body semantics is assumed.

The body proof derives the certified child and return flow from the actual expression tree and Source syntax. Genuine parameter admission supplies the reached entry, Source receipt and all rows. The original finish transfers the return once; Source control establishes that break and continue cannot escape this body. Source/native continuations retain the same reached pool and returned value. Fixture helpers obtain the original body inputs, compiler receipt and Word facts internally.

Implementation commits: `ca7b7b57` (original singleton return compiler receipts), `d620422d` (admitted Word literal semantics), `b4dbc7db` (selected literal domain and coverage), `8a170eac` (literal body continuations and proof imports), and `77f71db7` (accepted compiler receipt connections and test imports).

At `77f71db7`, all registered Solcore modules and `Tests.Main` built successfully (**5571 jobs**). Strict checks verified **15161 cumulative declarations**, **68 declarations across five added modules**, and **37 signatures**. All 68 complete private literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2235 pre-install Source/object pairs** and **4985 protected original files**. **2225 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass.

These proof modules add no executable checker. Full registered executions remain those at `3ff3daf4`; earlier finite fixture executions retain their original checkpoints. The estimates remain about 70% for the second goal and about 85% overall. Declaration counts do not measure progress.

Next: derive the remaining current body ledger, capture/global, argument and deep Source heap receipts from actual initialization and invocation. Connect these literal continuations through the real stored-callee parent and caller restoration. The complete mixed family, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and final compiler theorem remain unfinished.

### 2026-10-09: Literal invocation and finite Source admission

The selected literal Support now supplies its body ledger and runtime validity internally. Its original body continuation feeds the actual frame installation and marked parameter allocations. The body finishes once, and invocation restores the saved caller in the same reached pool. Application uses that invocation directly; reflection retains the original strict child bound and independent Source/native grades.

Initialized callee admission now follows from the actual Source occurrence typing, initialized cell, environment correspondence and deep heap typing. The original read producer supplies the callee value relation at the same heap and complete ordered records. This finite connection does not require whole-program well-formedness or a broad runtime coverage premise.

The actual numeric argument occurrences 7 and 8 evaluate in order to the physical pair at occurrence 6. Their selected evidence excludes missing-evidence, coercion and literal faults. The resulting pair has raw parameter typing in any receiving Source context. Its actual trace and administrative effects establish successful admission at the same reached heap and transfer every stable record row.

The accepted fixture derives the literal parameters, result, body context, Word facts and original return receipts internally. Its invocation and application ports retain genuine dynamic captures, history, Source origin, captured globals, reference authority, Source heap typing, raw arguments and represented native arguments.

Implementation commits: `ef031a04` (actual paired Source argument admission), `0353c372` (initialized callee admission), `a6fcef3f` (literal invocation, application and proof imports), and `e55949f5` (accepted fixture invocation and test imports).

At `e55949f5`, all registered Solcore modules and `Tests.Main` built successfully (**5575 jobs**). Strict checks verified **15194 cumulative declarations**, **33 declarations across four added modules**, and **26 signatures**. All 33 complete private literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2245 pre-install Source/object pairs** and **4985 protected original files**. **2234 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass.

These proof modules add no executable checker. Full registered executions remain those at `3ff3daf4`; earlier finite fixture executions retain their original checkpoints. Estimates remain about 70% for the second goal and about 85% overall. Declaration counts do not measure progress.

Next: connect the actual paired Core argument tree, stored-callee dispatch, sidecar and selected codebook to the new invocation proofs at parent occurrence 5. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished.

### 2026-10-09: Accepted parent, paired arguments and stored application

The accepted fixture now retains the actual indirect parent compiler receipt under the same chosen root, policy, body lowerer, read budget and Header. Its callee is occurrence 9, its physical argument list is the singleton occurrence 6, and the parent is occurrence 5. Header equality transports these original receipts without selecting another root.

The actual parent acceptance derives the pair compiler tree and its two numeric children. Their original literal and tuple producers prove argument preservation and finite-completion reflection, including raw Source typing, deep heap admission and every ordered record row. No child execution law or whole-program well-formedness is supplied.

The selected function's genuine stage and physical parameter count derive the actual dispatch row's acceptance. Application uses the existing selected literal invocation once, preserving captures, history, reference authority and the reached pool. Independent Source inversion of the real call allocation and singleton return derives final heap typing and successful result admission. The original physical caller restoration occurs once.

Reflection of the original fourth bind retains its full SuccessPrefix, SuccessStep and PassedAt witnesses, then constructs the real parent Source outcome with an independent Source grade. The complete native callee and argument prefix still needs to be derived from whole parent completion. Actual sidecar, dispatch, stored-member and capture associations remain genuine inputs to this finite endpoint.

Implementation commits: `782d7013` (selected-row acceptance), `4cbfb0e3` (original parent compiler receipt), `646de0f0` (closed paired argument semantics), and `fdf51087` (stored application, actual call outcome and test imports).

At `fdf51087`, all registered Solcore modules and `Tests.Main` built successfully (**5579 jobs**). Strict checks verified **15311 cumulative declarations**, **119 declarations across four added modules**, and **35 signatures**. All 119 complete private literal types and axiom arrays match the normal build; only the three permitted standard axioms occur. The cumulative increase is **117**: the actual inventories also include two deferred `RecursiveNamedLoopContracts.ExecutesAt` equations already counted in the prior cumulative environment. Independent prior/current name censuses show no removals, and both complete original equation types and axiom arrays match literally.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2250 pre-install Source/object pairs** and **4985 protected original files**. **2236 actual compiled project imports** match the Lean environment exactly. English, policy, registration and whitespace checks pass. No executable checker was added; full registered executions remain those at `3ff3daf4`.

Next: derive the same chosen parent's actual sidecar, lambda origin, dispatch and selected codebook from its static receipts. Connect the original initialized stored read and closed pair argument tree to whole native parent completion. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

### Chosen dispatch and whole native parent prefixes (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `CallableIndexedOwnedChosenOrdinaryArgumentBundles` | The actual callee value relation and known chosen carrier identify native parameter and result types. Original parameter alignment consumes actual argument values at the reached map and world. Source arity and raw binder types remain independent inputs. |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts` | The positive chosen member and original Prepared callsite supply the real sidecar, lambda origin, complete codebook rows, dispatch and selection. Runtime association to the actual callee post remains explicit. |
| `CallableIndexedOwnedStoredIndirectPurePrefixBounds` | Whole Core parent completion aligns the native callee child with the supplied genuine callee value post and extracts the ordered argument post, cumulative effects, successful prefix, successful step and full fourth bind. It uses genuine callee admission, accepted guards, strict argument children and finite Source argument fault exclusion. The measured application child remains for the existing application theorem. |
| `SourceCoreChosenOrdinaryAcceptedParentEntryReceipts` | The same accepted parent receipt supplies the initialized callee trace and value post and the original pair tree with all-size preservation and reflection. Initial heap, environment, stored lookup, native typing and admission retain their original authority. |

Implementation commits: `c236c562` (native argument bundles), `e57a93d5` (actual chosen dispatch), `5cc73e36` (whole native prefix and production imports), and `49f420e0` (accepted parent entry producers and test import).

At `49f420e0`, all registered Solcore modules and `Tests.Main` built successfully (**5583 jobs**). Strict checks verified **15402 cumulative declarations**, **91 declarations across four added modules**, and **25 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic prior/current name censuses show **91 additions**, no prior overlap and no removals. Generated helpers are counted by the actual Lean module index.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2256 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2233 actual project imports** match their compiled closure and Lean environment exactly. Independent stored Source snapshots also retain their original hashes. English, policy, registration and whitespace checks pass. No executable checker was added; full registered executions remain those at `3ff3daf4`.

Next: compose these producers and the existing literal application theorem into preservation and reflection for the accepted whole parent, deriving the callee post, argument meanings, fault exclusion, dispatch and native bundle internally. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

### Accepted whole parent preservation and reflection (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport` | Genuine Source equality transports the original compiler sidecar, lambda origin, dispatch and selected rows at the same chosen root. |
| `SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes` | Independent sized Source traces fix the actual singleton pair values and heap and exclude argument faults. |
| `SourceCoreChosenOrdinaryAcceptedParentPreservationBounds` | The whole Source parent derives its actual callee and pair producers, selected guards and native bundle internally, then uses the literal application proof once to construct Core evaluation and the full returned result. |
| `SourceCoreChosenOrdinaryAcceptedParentReflectionBounds` | Whole Core parent completion yields the real successful prefix. One unpack of its successful step retains the same argument state and cumulative effects; the original application reflection runs once, and the independent Source parent is reconstructed. |

Both directions retain the original compiler, receiving function model, positive chosen carrier, closure capture, history and physical caller restoration. Final value and heap relations, mapping/world extensions, administrative preservation, Source heap metadata and returned caller admission are composed at the same actual intermediate witnesses. Initial heap, environment, stored-cell authority, native typing and input admission remain genuine inputs. These proofs assume no completed child/body execution law or whole-program well-formedness.

Implementation commits: `48f9dc42` (actual Source transport) and `3a99ac67` (whole parent preservation/reflection, argument outcomes and test imports).

At `3a99ac67`, all registered Solcore modules and `Tests.Main` built successfully (**5587 jobs**). Strict checks verified **15455 cumulative declarations**, **53 declarations across four added modules**, and **20 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic prior/current name censuses show **53 additions**, no prior overlap and no removals. Generated helpers are attributed by actual Lean module index.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2260 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2249 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. No executable checker was added; full registered executions remain those at `3ff3daf4`.

Next: derive the actual initialized-let allocation and outer-return flow from original named-body acceptance, then connect real lambda formation and one marked allocation to the proved parent. Initial/captured heap population, the complete mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

### Accepted initialized allocation and finite outer-body ports (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts` | Original body acceptance supplies the initializer, marked Allocation/Annotated receipts and exact initialized-let/return flow and finish under the same selected root. |
| `SourceCoreChosenOrdinaryAcceptedInitializerAdmission` | Actual lambda typing, frame coverage and captured-environment agreement derive the same receipt's raw closure typing, pure Source outcome and unchanged-state admission. |
| `CallableIndexedOwnedChosenOrdinaryInitializedAllocationState` | One original stateful marked allocation retains every reached-state output and attaches positive `ChosenStoredAt` for the actual initialized cell in the receiving model. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyBounds` | Actual native initializer, allocation and parent traces compose value/fault completion. Whole completion yields a genuine strict parent child; finite Source body inversion retains the initializer, allocation and parent outcome. |

The allocator keeps actual environments, Source/native heaps, mappings, worlds, frame references and metadata, every ordered row, and reached-state admission. The finite native ports retain the literal final body store and fault token. Source inversion retains its own execution grades independently of native child grades. These are concrete composition ports; complete whole-body preservation and reflection with admission have not yet been assembled.

Implementation commits: `5121afc3` (positive initialized allocation state) and `b024dfd3` (actual compiler receipts, initializer admission, finite outer-body ports and registrations).

At `b024dfd3`, all registered Solcore modules and `Tests.Main` built successfully (**5591 jobs**). Strict checks verified **15541 cumulative declarations**, **87 declarations across four added modules**, and **42 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic name censuses show **86 additions** and no removals. The one prior overlap, `Tests.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason.eq_1`, has exact complete type/axiom agreement with an independent probe of the original imports. Generated helpers are attributed by actual Lean module index; the four private inventories have no shared declaration names.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2266 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2255 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. No executable checker or IO runner was added; full registered executions remain those at `3ff3daf4`. Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-outer-body-ports-checks.json` and its actual command receipts.

Next: retain the actual Header constructor's empty evidence, compose formation, one marked allocation and the initialized parent at the same reached state, and align the parent child with whole native completion by reconstruction and determinism. Complete preservation and reflection of that body with admission, initial/captured heap population, the shared mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, all-pass composition and the final compiler theorem remain unfinished. The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.


### Accepted whole outer-body preservation and reflection (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedHeaderEvidence` | The same original Header constructor retains `HeaderAt` and genuine empty evidence; no equation is inferred from emitted code. |
| `SourceCoreChosenOrdinaryAcceptedInitializedEntry` | One original formation and one stateful initialized allocation retain the actual admitted parent entry, positive stored member and original formation history. |
| `SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction` | Actual initializer execution, Source allocation and parent outcome construct the original initialized-let/return body with independent Source grades. Raw admission transports to Γ0 at the same reached state. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds` | `preserves_body` and `reflects_body` compose the admitted parent internally and retain the full final body result, cumulative effects, actual restored caller and all rows. |

Preservation inverts the original Source body, obtains its real allocation, and runs the initialized parent at the same reached state. Reflection constructs a genuine Source allocation independently of a Source execution premise, extracts the original strict native parent child, and reflects that child once. The resulting parent evaluation reconstructs whole native execution; determinism identifies both its final value and final store with the supplied whole completion. The finite Source constructors then build the independent body trace. Source and native grades remain independent.

The returned result keeps the actual final heap/store, mapping and world extensions, administrative preservation, Source heap metadata, restored caller pool and every ordered row. Successful raw value and deep heap typing transport from the local binder context to the original Γ0. Lexical scope restoration preserves the same reached pool and records.

Initial Source environment `[]`, actual captures and history, raw/native heap correspondence, native environment typing, frame/global references and reads, genuine allocator readiness and initial all-row admission remain explicit. These finite body ports contain no completed child/body law or whole-program well-formedness premise. The actual Header evidence equation remains explicit in the body ports and is available from the authentic Header constructor.

At `57485ac4`, all registered Solcore modules and `Tests.Main` built successfully (**5595 jobs**). Strict checks verified **15605 cumulative declarations**, **64 declarations across four added modules**, and **18 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic prior/current name censuses show **64 additions**, no prior overlap and no removals. Generated helpers are attributed by actual Lean module index; the four private inventories have no shared declaration names.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2270 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2259 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. No executable checker or IO runner was added; full registered executions remain those at `3ff3daf4`. Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-outer-body-preservation-bounds-checks.json` and its actual command receipts.

The work estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: connect these finite body ports to the public BodyState interface and populate the genuine initial heap, captured environment, frame and complete rows. The shared mixed family, prior General/principal qualification, general dispatch, rejection/coercion/staging routes, public Source admission, composition of all passes and the final compiler theorem remain unfinished.

### Accepted body correspondence at the actual parameter state (2026-10-09)

At `0a48ccf2`, four additive modules connect the accepted whole-body proofs to the original named parameter Receipt. BodyStatePorts derives the actual empty Source entry, captures, global references, native typing, readiness and admission. InitialBodyAdmission derives deep heap typing and all rows from real empty-parameter allocation and singleton hook effects. HeaderRuntimeEvidence retains the actual global count and empty evidence. BodyStateCorrespondence supplies preservation, reflection and the existing SourceBodyAt/NativeBodyAt interfaces at the same reached state.

The full returned pool, cumulative effects and successful raw PostAdmission are retained. No completed body law or ProgramWellFormed premise is added. Complete catalog and zero-prefix receipts remain genuine inputs. Stronger ReachedExit/LexicalResult witnesses are not asserted.

The registered build passed 5599 jobs. Strict checks verified 15684 cumulative declarations, all 79 declarations of the four new modules and 32 signatures. Complete private/normal types and axiom arrays match literally; only the three permitted standard axioms occur. Authentic name censuses show 79 additions, no prior overlap and no removals. Normal Source/object guards and all 4985 protected-file checks pass. No executable fixture checker was added in this checkpoint.

Next: retain the actual successful public Recipe preparation, bootstrap constructor fields and concrete store/capture association, then join the same singleton pool, hook and parameter producer to this Receipt. Public Session association, the shared mixed family and all-pass compiler correctness remain unfinished.

### Accepted public bootstrap and actual parameter Receipt (2026-10-09)

| Module | Proven connection |
| --- | --- |
| `RecursiveNamedCatalogPreparedInitializationReceipts` | `stored_capture` and `entry_with_constructor` retain the prescribed initialized capture and actual initialization authority, with frame zero, empty current/ghost ownership and no records. |
| `SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt` | `prepare_public` retains one actual Recipe.prepare equation. `complete_bootstrap` retains one original runStateful completion; `completed_store` identifies its initialized store without rerunning either producer. |
| `SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence` | The same authentic Header constructor retains runtime evidence, layout equality and empty Source captures. Native captures remain the actual installer data. |
| `SourceCoreChosenOrdinaryAcceptedPublicParameterEntry` | Derives the singleton checker ledger, Complete and initial state at the actual completed store, then uses the original hook installation and parameter action once to return the same Receipt and ContinuationAgreement. |

The unchanged accepted fixture has one named row. Its positive public bootstrap checker succeeds at fuel 10000 and observes a two-cell initialized store. The symbolic receipt retains the original Recipe acceptance and exact machine completion.

The parameter entry derives native store typing, the empty Source heap relation, every initial stable row and the prescribed live capture from that same initialization constructor. Original named hook history and real frame installation feed `parameters_with_state` once. The returned parameter Receipt keeps the actual BodyState, reached pool, ordered records, Source admission and complete prefix/body ContinuationAgreement. The parameter proof uses the retained Recipe acceptance, machine completion and Header evidence; its function model and metadata registry remain parameters. It assumes no completed body law or ProgramWellFormed premise.

At `783a716f`, all registered Solcore modules and `Tests.Main` built successfully (**5603 jobs**). Strict checks verified **15836 cumulative declarations**, all **152 declarations across four added modules**, and **45 signatures**. Every complete private literal type and axiom array matches the normal build; only the three permitted standard axioms occur. Authentic censuses show **152 additions**, no prior overlap and no removals. Generated helpers are attributed by actual Lean module index.

The initial normal validation passed Source, type/axiom, signature and fixture checks, then failed because its cumulative census omitted `Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization.environment.eq_1`. An independent probe of the same environment identifies its actual owner as `RecursiveNamedPublicBootstrapGlobals` and confirms complete literal type/axiom agreement. The corrected census includes that one genuine helper. The original failure is preserved; only the cumulative stage was rerun, and the original successful bootstrap execution remains the single new checker run.

Each complete Source passed compilation with warnings treated as errors and at least two independent full semantic reviews. Source-only installation preserved **2278 pre-install Source/object pairs** and **4985 protected original files**. The four audited modules' **2267 actual project imports** match their compiled closure and Lean environment exactly. Original Source snapshots retain their hashes. English, policy, registration and whitespace checks pass. Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-public-parameter-entry-checks.json` and its actual command receipts.

One positive bootstrap IO call is newly registered. Existing full registered executions remain those at `3ff3daf4`. The work estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: compose the existing admitted body preservation/reflection and SourceBodyAt/NativeBodyAt interfaces at this actual public Receipt. Association with a returned public Session, stronger ReachedExit/LexicalResult witnesses, general mixed bodies, all-pass composition and the final public compiler theorem remain unfinished.


### Accepted public body, invocation and ready Session receipts (2026-10-09; `46df219c`)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence` | One actual public parameter receipt supplies BodyAtReceipt, admitted whole-body preservation/reflection and the existing SourceBodyAt/NativeBodyAt interfaces. |
| `SourceCoreChosenOrdinaryAcceptedPublicInvocation` | Genuine public initial state and capture supply each original named invocation. Its own parameter child is packaged as the actual receipt, with body meaning derived internally and caller restoration retained. |
| `SourceCoreIndexedSession` | Erased RecipeAt/InitialAt receipts share original artifact mint and session construction. Actual ready inversion retains native completion and the same Session authority, world/store, full prefix, physical registry and initial metadata context. |
| `SourceCoreChosenOrdinaryAcceptedPublicSessionEntry` | The retained actual ready equation supplies CompletedBootstrap proof-only. Body and invocation ports use the same actual Session native world/store and checked static registry. |

The body proof retains its full admitted returned result and successful raw PostAdmission. The low invocation proof retains original parameter execution, caller restoration, returned pool and cumulative effects; it does not assert stronger invocation post-admission or ReachedExit/LexicalResult. Header, Source typing, inventory and genuine compiler/root receipts remain inputs. Source and native execution grades remain independent.

The original Recipe.open, Artifact.bootstrap and bootstrapFresh operational types remain exact. The shared receipt producers perform one artifact mint and one session-authority creation. Original finish/resume validation, error, fuel-exhaustion and impossible native-fault branches remain unchanged. NativeDone alone does not establish readiness: resume_ready_receipt requires the actual successful ready equation. BootstrappedFrom retains the entire supplied prefix; metadata RegistryAt is distinct from the physical handle registry.

Strict normal Source checks are empty and use warningAsError. The 117-line public body module has a full audit of 13 declarations and 8 positive API checks; the 250-line public invocation module has 28 declarations and 11 API checks. The 2315-line Session module has 1441 declarations and 20 API checks. That whole-module count includes the original declarations and is not a net-addition count. The 158-line public Session consumer has 39 declarations and 10 API checks, plus an actual ready IO run. The complete four-module audit has 1521 declarations and 49 API checks, with no cross-module shared names. The private before union covers 2282 Source/object pairs, and the complete normal pre-install snapshot covers 5526 modules, including the Tests.Main registration cone.

Complete unnormalized original/current comparison reports 1412 exact original declaration types and axiom arrays, one explicitly approved generated-helper change and no missing original names. The genuine generated Artifact.bootstrap._proof_1 changes from native initial-state typing to Recipe reflexivity after factoring. Its original 2750-byte TYPE/AXIOMS block appears literally unchanged at the new generated Artifact.bootstrapWithReceipt._proof_1. The exact old/new same-name blocks and movement were independently reviewed; raw comparison failures are preserved. No helper alias, type normalization, deleted declaration or extra axiom is used.

The newly registered normal Session check prepares the unchanged fixture and Recipe once, opens one artifact, creates one fresh checkpoint and resumes it once at fuel 10000. It actually returns ready with two native cells and zero physical handles. Its proof-only receipt retains the same initialization store. This test exercises public bootstrap readiness; it does not execute a public root call or authenticate a successful exported program result. The Session consumer uses the retained completion directly, without first running a standalone bootstrap and then resuming it again.

The code checkpoint is `46df219c`. The registered normal build passed 5606 jobs. Strict checks verify 15944 cumulative declarations, all 1521 current declarations, 49 signatures and complete literal private/normal TYPE/AXIOMS agreement using only the standard three axioms. The cumulative census adds 108 names, overlaps 1413 prior names and removes none; the overlap retains 1412 exact originals and the one explicitly approved generated-helper change. The actual compiled closure equals the 2270-module Lean environment. All 49 changed existing object pairs are covered by the original reverse dependency cone and actual successful build records; independent Source/paired-object snapshots and all 4985 protected original files pass. The new registered public Session runner executes once in normal validation and returns ready at fuel 10000 with two native cells; its exact log is 113 bytes. Two existing registered regression units pass separately with a 163-byte log. This does not claim execution of every registered test. The preceding committed verification sections remain historical records. The estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: connect actual public root start/call and native completion, Source program admission/staging, and authentic success/export receipts to the pointwise invocation bounds. Stronger invocation post-admission/ReachedExit/LexicalResult, arbitrary mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, all-pass composition and the final public compiler theorem remain unfinished.

### Accepted public program outcomes and Word exports (2026-10-10; `7b0f562f`)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission` | Finite full-catalog equality retains the original singleton checked function and absence of methods. Original checker typing and actual stage analysis derive ProgramWellFormed and ProgramHasStages without a global inference-soundness premise. |
| `SourceCoreChosenOrdinaryAcceptedPublicRootStart` | The actual successful Session.start selects the singleton Header. The original global/capture read and invocation give preservation and reflection at the same native checkpoint and initialization store. |
| `SourceCoreChosenOrdinaryAcceptedPublicResultObservation` | The receiving chosen model gives exact Word equality or the genuine language-fault relation from the full invocation result. |
| `SourceCoreIndexedSession` | One resumeWithReceipt shares the original runStateful and completion action. Actual success/failure inversion retains decoding, slots, the full store/prefix and authority; requested raw Source typing and Word export facts remain tied to the real checkpoint. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome` | One StaticReceipt collector and actual public action chain derive admitted independent ProgramOutcome, sufficient native fuel and identical successful Word export. The same full low returned-state relation remains. |

For the retained accepted fixture, the same public Session root start and actual resume receipt now connect independent Source ProgramOutcome to native completion and the identical exported Word. Original checker typing and the actual stage analysis establish program admission internally. Reflection uses the successful public decoder equation; a Source Word result crosses the same boundary with sufficient native fuel and a positive export budget. The full low invocation result retains final heap correspondence, the restored owned pool and cumulative effects. Source and native budgets remain independent.

The static collector checks originalCatalog once on the same retained fixture. Full original checked-function equality, the original checker budget of 1024, genuine body typing and actual stage analysis establish Source admission. It does not assume global checker soundness or accept a completed body/pass law. The original empty Source heap and nil raw argument typing are derived at the actual Header context.

The public collector keeps the original ready Session, starts its selected root once and resumes that root checkpoint once. Native completion reflects to a genuine Source ProgramOutcome. An independent Source completion yields sufficient native fuel for that same checkpoint. Actual successful export excludes the native language-fault branch by its retained decoder equation and returns the identical Source Word and raw result type. Source Word preservation requires a positive export budget. This unit does not claim general correspondence for public failed/export-error outcomes.

The erased completion receipt shares the original resume/mint action. Original operational signatures and finish branches remain exact. The whole Session baseline comparison reports 1440 original same-name literal TYPE/AXIOMS matches and one explicitly reviewed generated resume-helper migration. Its moved proof has two generated binder-label differences; the literal blocks and original comparison failure are retained. No type normalization or manual alias is used. All 1678 current private/normal TYPE/AXIOMS blocks match literally in normal validation.

All five private packets are frozen. Their full audits contain 1551 Session declarations, 19 original-program declarations, 18 root-start declarations, 10 result-observation declarations and 80 consumer declarations; the corresponding positive API counts are 58, 12, 8, 7 and 16. The independent normal audit verifies 1678 unique declarations, equal to the private occurrence total; the cumulative net growth is recorded separately. The authentic private consumer run returns public Word 7 at native fuel 10000 with a 127-byte log. It also measures originalCatalog acceptance on that same fixture. The separately recorded first normal-environment run also returns Word 7 with a 127-byte log; the declaration-name census repair retains both successful execution receipts.

The code checkpoint is `7b0f562f`. The registered normal build passed 5610 jobs. All five strict Source checks produced empty logs. The normal audit verifies 16181 cumulative declarations, all 1678 current declarations and 101 signatures, using only the standard three axioms. Every current private/normal TYPE/AXIOMS block matches literally. The cumulative census adds 238 names and removes the single reviewed generated resume helper, for net growth of 237; all 1440 prior/current overlapping declarations remain literal exact. The pre-install snapshot retains 5539 original Source/object triples. The actual compiled closure equals the 2287-module Lean environment; all 35 changed existing object pairs have successful rebuilds within the original dependency cone. All 4985 protected original files remain unchanged. The first normal public program runner returns Word 7 at fuel 10000 with a 127-byte log. Two existing Session and packed-invocation regression units pass separately with a 163-byte log, covering suspension/resumption, shared writes, handles, stage checks and language-fault state. These executions do not cover the full registered suite. Successful IO, Source and full/API audit receipts were retained during the bounded declaration-name census repair.

Stronger invocation PostAdmission and actual lexical ReachedExit/LexicalResult remain unfinished. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final theorem for the complete public compiler remain unfinished. The estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress. The existing dated checkpoints remain historical records.

### Accepted public program post-admission (2026-10-10; `4aa849f8`)

| Module | Proven connection |
| --- | --- |
| `CallableIndexedOwnedNamedProgramAdmission` | Genuine ProgramOutcome supplies successful raw value and deep heap typing in the actual Header function context. Saved stable rows follow the final administrative frame at the same returned state. |
| `CallableIndexedOwnedBodyRestorationAdmission` | The original caller restore runs once and retains its complete tuple. Saved rows and the actual restored frame retain every returned history; successful typing moves only through genuine TypeContextSupports. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission` | The existing native/Source and Word-export proof producers run once. The enriched ResultAt keeps the original six effects, same returned State, Relates and PostAdmission. |

For the retained accepted fixture, preservation and reflection now retain successful raw Source value typing, deep heap typing and every returned row's own stable history at the same actual restored caller state. The companion keeps the original heap correspondence, cumulative effects and returned pool. It consumes each existing program/export producer once and retains independent Source and native budgets. Faults retain stable rows without claiming successful value or deep heap typing.

The generic proof derives the actual Header body identity and successful typing from the original admitted program outcome. It accepts no arbitrary body law or ProgramWellFormed premise. `after_program_transition` eliminates the original transition once and retains that same witness. The optional restoration helper keeps the body's raw heap and the returned pool's exact records. Fault post-admission requires stable rows, with no successful value/deep heap claim. The public companion changes proof interfaces only; it performs no execution action.

The code checkpoint is `4aa849f8`. The registered normal build passed 5613 jobs. All three strict Source checks produced empty logs. The normal audit verifies 16201 cumulative declarations, all 20 declarations of the three added modules and 16 signatures, using only the standard three axioms. Every complete current private/normal TYPE/AXIOMS block matches literally. Authentic name censuses show 20 additions, no prior overlap and no removals. The pre-install snapshot retains 5543 original Source/object triples. The actual compiled closure equals the 2290-module Lean environment. The two changed existing object pairs are covered by the five-module dependency cone and five actual successful rebuilds. All 4985 protected original files remain unchanged. This checkpoint adds no runner and executes no IO or test suite; the public Word 7 and two existing regression receipts at `7b0f562f` remain historical evidence.

Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/accepted-public-program-post-admission-checks.json` and its actual command receipts.

Genuine lexical ReachedExit/LexicalResult and their propagation through general body finish and caller restoration remain unfinished. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final theorem for the complete public compiler remain unfinished. The estimates stay about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: retain genuine lexical exit from the actual outer body finish, populate the stronger named parameter Receipt body ports, and propagate that witness with admission through the original caller restoration.

### Accepted body lexical exit at the actual public parameter Receipt (2026-10-10; `f0274543`)

| Module | Proven connection |
| --- | --- |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit` | The real initialized binder and parent Source outcome produce genuine lexical exit at the same final map/world. Both whole-body ports retain the original represented result, returned pool and admission. |
| `SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts` | The actual BodyState supplies the full lexical administrative context, authentic capture/packet/readiness and Source admission. One outer-body proof in each direction fills the existing strong parameter Receipt result. |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts` | One original public parameter entry retains the same initial state, actual Receipt and ContinuationAgreement, then supplies both strong body contracts for every size. |

The accepted initialized body now preserves and reflects genuine lexical exit and LexicalResult with the same represented result, cumulative effects, returned pool and PostAdmission. The BodyState adapter uses the actual parameter Receipt's full administrative environment; creator capture remains separate. One public parameter entry supplies the same initial state, Receipt and ContinuationAgreement and both strong body contracts at independent grades.

Lexical exit comes from the actual Source body/control constructors and represented reached binder environment. The BodyState administrative context is `packTypes (caller.bindings.map Prod.snd) :: receipt.administrative`; the shorter creator capture is not used to identify that suffix. Header scope/source/context and the genuine empty parameter environment are transported while every dynamic index remains fixed. Native reflection retains its independently constructed Source grade and actual whole-body value/store alignment. The public factory reuses the existing receiving chosen model and actual completed bootstrap. It does not replay a parameter, bootstrap or execution action and assumes no completed body law or ProgramWellFormed premise.

The registered normal build passed 5616 jobs. All three strict Source logs are empty. The normal audit covers 60 unique declarations and 17 signatures; complete private/normal TYPE/AXIOMS blocks match literally and use only the standard three axioms. The cumulative census is 16260, up from 16201: 59 new names, one exact prior overlap and no removals. The overlap is `Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captures_at_entry.congr_simp`; its saved-before TYPE/AXIOMS block matches the current block literally. The pre-install snapshot retains 5546 original Source/object triples. The compiled closure equals the actual 2271-module Lean environment. The sole changed existing object pair, `Tests.Main`, is covered by the four-module dependency cone and exactly four successful rebuilds. All 4985 protected original files remain unchanged.

The complete normal full log is 81655504 bytes, the API log 60583 bytes, the saved-before overlap log 792345 bytes and the cumulative log 1841739 bytes. These are retained successful command receipts. No declaration or imported namespace is omitted from the census.

No runtime/Core specification changes, runner or IO are added. The earlier public Word 7 and existing regression executions remain historical evidence. This checkpoint does not establish a stronger public Session or generic invocation theorem.

Generic named invocation must still carry this same body exit and admission through caller restoration. The existing low interfaces discard these fields, and a protocol Transition or successful PostAdmission cannot supply lexical exit. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final all-pass compiler theorem remain unfinished. The estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: retain the same strong body result through the original invocation callback and actual caller restoration, preserving the genuine lexical witness and admission without projecting through the low body interface.

### Generic named invocation retains the same body fact through caller restoration (2026-10-10; `8d2289c5`)

| Module | Proven connection |
| --- | --- |
| `NamedInvocationFaultPostContracts` | A dependent BodyExtra and the actual restored frame are retained inside the original causal existential. Forgetting preserves every original entry, state, trace, history and effect witness. |
| `CallableIndexedOwnedInvocationBounds` | Both directions consume the real body callback once, keep its same completed state and perform the original caller restore once. Legacy post-only ports wrap the same witness with TrivialExtra. |

Generic named invocation now retains a supplied `BodyExtra` at the same actual body entry, parameter state and completed body state. Preservation and reflection keep that fact inside the original causal receipt, together with the actual restored frame. Each core consumes its original body callback once and performs the original caller restore once. Source and native grades remain independent. Legacy post-only interfaces attach `TrivialExtra` to the same body witness and forget the added fields.

The next unit connects genuine strong named parameter Receipt results to this retained family, then uses `restore_post` with saved stable rows, the actual restored frame and genuine context support to add caller admission. The generic factor does not itself derive lexical exit or successful admission. Neither follows from a protocol Transition. General mixed bodies and the final all-pass compiler theorem remain unfinished.

All 50 retained same-name original TYPE/AXIOMS blocks match literally. Two generated proof helpers move from the legacy `with_post` cores to `with_extra`; the reviewed differences are their generated names and hygienic binder labels. All other TYPE fields and complete axiom arrays are retained. These moves are recorded separately from the same-name matches.

Normal verification passed: 5616 build jobs, two empty strict Source logs, 62 declarations (15 lower / 47 upper) and 36 signatures (26 retained / 10 new), with all private/normal TYPE/AXIOMS blocks literally equal and only the standard three axioms. The cumulative census is 16270 from 16260: 12 additions, two reviewed generated-helper removals and 50 retained overlaps, for net growth of 10. The 5549-row before snapshot and 1954-module import environment passed; 10 changed existing object pairs are covered by the 360-module reverse dependency cone and 360 actual rebuilds. All 4985 protected artifacts remain unchanged. Registrations are unchanged, and this factor adds no IO or runner. Earlier public Word 7 and regression executions remain historical evidence.

The two reviewed generated moves are `invocation_preserves_bounded_at_with_post._proof_1_1` to `invocation_preserves_bounded_at_with_extra._proof_1_1` and the corresponding reflection helper, within `CallableIndexedOwnedInvocationBounds`. The public legacy declarations remain at their original names and signatures. The private original census has 52 declarations: 50 exact same-name matches and these two expressly reviewed moves. The measured cumulative census has 12 additions, these two reviewed removals and 50 retained overlaps; net growth is 10.

No stronger public Session, successful caller admission or new lexical-exit derivation follows from the uninterpreted retained family alone. The downstream strong Receipt adapter and its accepted public companion remain uncompiled W-only drafts. General mixed bodies, prior General/principal qualification, general dispatch, rejection/coercion routes, specialization/evidence/comptime composition and the final all-pass compiler theorem remain unfinished. The estimates remain about 70% for the second goal and about 85% overall; declaration counts do not measure progress.

Next: use the genuine universal strong body callbacks and pure restore_post to retain lexical exit, body admission and caller admission at the same returned pool, without another restoration.

### Strong Receipt exit and caller admission in one named invocation (2026-10-10; `06f2635c`)

`CallableIndexedOwnedPreparedNamedInvocationAdmission` preserves the actual parameter Receipt, full body administrative context, lexical exit and PostAdmission through the generic core. The pure restoration proof uses genuine caller-context support, saved stable rows and the actual restored frame at the same causal witness; the fault path needs frame/row transport. `SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission` closes these inputs for the accepted initial/completed pair without replaying bootstrap or parameters. Public root/program exit companions remain uncompiled drafts.

The Source hashes are `09fe9750` and `89b3a705`; Source creation followed a 2293-module before capture. Normal verification at `06f2635c` passed 5618 registered build jobs, two empty strict Source logs, 27 complete declarations (10 generic / 17 accepted) and 20 signatures. Every private/normal TYPE/AXIOMS block matches literally and uses only the standard three axioms. The cumulative census is 16297 from 16270: 27 additions, no prior overlaps and no removals. The 5549-row pre-install snapshot and actual 2295-module import environment passed. The two changed existing object pairs, `Tests.Main` and `CoreLowering`, are covered by the four-module dependency cone and four successful rebuilds. All 4985 protected artifacts remain unchanged. The unit adds two Source modules and two registration imports, with no IO or runner. Runtime/Core specifications and public execution actions are unchanged; no IO is added. Generic mixed bodies, specialization/evidence/comptime composition and the final all-pass theorem remain unfinished. The 70% / 85% estimates and earlier dated checkpoints retain their scope.

## Contextual closure storage/read audit (2026-10-10; `d51edb70`)

Contextual ordinary and method-principal members now retain the original code, owner, capture, history, Source syntax and escaped-control diagnostic. Both formation factories use the existing producer once. Initialized allocation and local read preserve that same positive member; forward projection supplies strict invocation Association without recovering authority from an erased value relation.

One original marked allocator returns the full reached tuple, fresh Source/native cell reads, extended member and caller admission. Transport to a later state requires genuine live reads in that state. One original initialized read constructs an independently sized Source callee trace and same-state ValuePost. Source value and deep heap admission use actual Source typing and input heap validity. The selected formation helper is ordinary-only; the shared storage/read ports handle both member constructors. No completed body law is assumed.

The positive member projects original contextual syntax directly to the existing strict Association. It does not invert the general value relation to invent an owner, history or method Header. The only new list induction identifies reported Source types from actual occurrence typing; it proves no execution or body law. The actual selected Code supplies the escaped-control diagnostic. Future transport requires both Source and native live reads at the future state.

Normal verification at `d51edb70` passed 5622 registered build jobs, two empty strict Source logs, 33 complete declarations (12 member / 21 storage-read) and 24 signatures. Every private/normal TYPE/AXIOMS block matches literally and uses only the standard three axioms. The cumulative census is 16361 from 16328: 33 additions, no prior overlaps and no removals. The 5553-row pre-install snapshot and actual 2100-module import environment passed. The sole changed existing object pair, `CoreLowering`, is covered by the four-module dependency cone and four successful rebuilds. All 4985 protected artifacts remain unchanged. The unit adds two proof Source modules and two `CoreLowering` imports. No runner, IO or runtime/Core specification change is added.

Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-initialized-closure-receipts-checks.json`. The authentic before closure contains 2098 modules. The private full/API logs are 12296685 / 78036 bytes and match the complete normal blocks literally. Earlier public Word 7 and regression executions retain their historical scope.

Next: connect these same-state callee producers to whole selected-call preservation and reflection for ordinary and method-principal closures, then complete the joint mixed expression/body family and compose specialization, evidence and staging. Actual raw heap/typing, current rows, accepted gates and strict child continuations remain inputs. Whole-call integration is not established by this storage/read unit. General public failures, export errors and the final all-pass theorem remain unfinished. The 70% / 85% estimates remain unchanged.

### Shared contextual stored-call ports (2026-10-10; `45a38df8`)

Stored local calls now share preservation and reflection ports for ordinary and method-principal closures. The actual positive member supplies callable origin and a same-state callee trace, ValuePost and invocation Association. The original codebook rows and selected carrier authenticate Dispatch and its Source gate. Descriptor equality does not identify the member’s hidden code, owner or history with the externally selected code.

The original ordered Source types, binder count and native packing feed the existing selected-call proof once in each direction. Preservation consumes a genuine measured SourceSuffix; reflection consumes whole native EvaluationSize. Both retain the actual argument, body and returned caller states with independent Source/native grades. Current live cell reads, raw heap and environment relations, runtime validity and universal strict argument/body continuations remain inputs. Principal formation retains its genuine method authority and uses the original formation producer once.

Normal verification at `45a38df8` passed 5624 registered build jobs, two empty strict Source logs, 20 complete declarations (16 common call / 4 principal) and 11 signatures. Every private/normal TYPE/AXIOMS block matches literally and uses only the standard three axioms. The cumulative census is 16381 from 16361: 20 additions, no prior overlaps and no removals. The 5555-row pre-install snapshot and actual 2112-module import environment passed. The sole changed existing object pair, `CoreLowering`, is covered by the four-module dependency cone and four successful rebuilds. All 4985 protected artifacts remain unchanged. The unit adds two proof Source modules and two `CoreLowering` imports. No runtime/Core specification change is added.

Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-stored-member-call-bounds-checks.json` and its six actual command receipts. Source creation followed an authentic 2110-module before capture. The full normal log is 7133003 bytes and the API log is 56335 bytes. These checks execute no public action or test runner.

Next: derive the Source suffix from the original whole Source trace at the admitted expression head. Retain live member receipts through actual allocation, assignment, child and body posts, then close the joint mixed expression/body family and compose specialization, evidence and staging. Heap typing and map/world growth alone do not preserve a cell’s function value. General public failures, export errors and the final all-pass theorem remain unfinished. The estimates remain about 70% for the second objective and about 85% overall; declaration counts do not measure completion.

### Admitted contextual stored expression heads and actual writes (2026-10-10; `09faa42c`)

The admitted stored expression head now derives SourceSuffix internally from the original whole Source indirect-call trace. Finite inversion and the actual initialized local callee read retain the original argument and application grades and fault branches. The shared selected-call producer runs once in each direction and returns the same reached caller post. `preserves_at` and `reflects_at` keep independent Source/native grades and genuine strict argument/body continuations. Their `LiveFor` premise requires a positive live member, actual Source/native reads and matching selected compiler receipts at every input state. This unit supplies the head endpoint under that invariant; it does not prove universal LiveFor or close the mixed expression/body family.

`written_member` uses one original initialized write with the independently authenticated raw Source cell type, then retains the new member and actual optional-cell reads at that written state. `preserves_other` retains another cell only from the real Source/native writes and an injective location map. Administrative preservation alone does not protect mapped function values.

Normal verification at `09faa42c` passed 5626 registered build jobs, two empty strict Source logs, 74 complete declarations (72 expression head / 2 write receipts) and nine API checks. All private/normal TYPE/AXIOMS blocks match literally and use no axioms beyond the standard three. The measured cumulative census is 16455 from 16381: 74 additions, no prior overlaps and no removals. The 5557-row pre-install snapshot and actual 2113-module import environment pass. The sole changed existing object pair, `CoreLowering`, is covered by the four-module dependency cone and four successful rebuilds. All 4985 protected artifacts remain unchanged. The unit adds two proof Source modules and two `CoreLowering` imports; Tests.Main registration is unchanged. No IO or runtime/Core specification change is added.

Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-stored-expression-heads-checks.json` (SHA-256 `8b1bbafbf87305b887f894276f3a32d0828fba5b56e4d42a8a05c6dca0939ce3`) and six actual closed command receipts. Normal validation closed at `933a2b` / session 36560 / `4e4645`; the registered build closed at `3a65de` / session 68302 / `de2f3d`. The full and API logs contain 9164016 / 21406 bytes. No public action or test runner is added.

Next: carry positive function-cell origins in the joint family inputs and posts through actual allocation, writes and every child/body result, then discharge its live-cell obligation. The current LiveFor quantifies over the old general model; strong cell origins do not supply an inverse for that model. The CellOrigins backend and ordinary/principal formation companion are reviewed text drafts; their kernel and integration checks are pending. General public failures, export errors, mixed bodies and all-pass composition remain unfinished. Heap representation and administrative transport alone cannot supply live function cells. The 70% / 85% estimates remain unchanged.

### Positive cell origins and actual contextual formation (2026-10-10; `53095e76`)

Closure leaves retain a genuine positive Member through the existing recursive payload/heap relation. Actual allocation and writes preserve that relation only with their genuine action and typing receipts; the initialized read requires its exact ordinary Source type. Ordinary/principal formation each runs its original factory once, then attaches strong payload/result evidence at the unchanged heap/store. `PostWithOrigins` stays at the same reached state.

Normal checks pass: two empty strict logs, full 39 (37 / 2), API 21, build 5628 and cumulative 16494 (+39, no overlaps or removals). All private/normal literal TYPE/AXIOMS blocks pass with no axioms beyond the standard three. The 5559-row snapshot, 2102-module environment, one existing `CoreLowering` object delta, four-module cone/rebuild and 4985 protected artifacts pass. No IO is added. Sized child/body retention, compatible/scheme cell views, genuine callee classification and selected-code association, mixed-family closure and all-pass correctness remain incomplete. The allocator/write companion (179 lines) and generic reflection companion (225 lines) have text reviews only.

Validation records: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-cell-origin-formation-receipts-checks.json` (SHA-256 `7428d1e91a1f8a928cd2b9f88cf69b9cb9750c3f4ad72183130982487de0fb9e`) and six actual closed command receipts. Normal validation closed at `68b8a0` / session 74096 / `fd6ff8`; the registered build closed at `743e8c` / session 7160 / `10d9ef`. The full/API logs contain 4116203 / 48029 bytes; the prior-overlap/cumulative logs contain 172286 / 1871923 bytes. No public action or test runner is added.

### Receiving-model stored-call reflection (2026-10-10; `31b073bf`)

`application_reflects_of_bundles` reconstructs the actual ordered binder arguments from separate raw/native bundle receipts and extends the genuine callee Association along the real map and world. It calls the original admitted stored-closure reflector once with strict body children under the authenticated receiving model. `reflects_selected` retains that model's result and heap at the same restored caller state, together with cumulative effects and an independent Source grade. Raw PostAdmission comes from the reconstructed whole Source trace; no erased General relation supplies positive origins.

Original Source `ed77c2f6` compiled without repairs. Before capture `df6789` / session 18006 / `ffaf00`, strict compile `2c0d0e` / session 54461 / `3c28ca`, and whole-module/API audit `614a14` / session 33715 / `427afe` closed successfully. Normal verification passes all 5 literal private/normal TYPE/AXIOMS blocks and 2 API checks, one empty strict Source log and build 5630. Cumulative 16510 adds 5 names to 16505 with no overlaps or removals. The 5562-row snapshot, actual 2092-module environment, one existing `CoreLowering` object delta, three-module cone/rebuild and 4985 protected artifacts pass. No IO or runtime/Core specification change is added. The 162-line positive read and 256-line origin-post companions remain text-only; joint-family closure and all-pass correctness are unfinished.

Validation: `/private/tmp/solcore-owned-functions-resume-20261007/stored-indirect-call-for-model-reflection-checks.json` (SHA-256 `f6a7de9a97336a2e4282041c01a0597e08f85f8e7afa03d808274cf041bf5d9c`). Five normal command receipts closed at `0a2753` / session 48878 / `532234`; the registered build closed at `ff1fff` / session 87236 / `eb311d`. Full/API logs contain 751920 / 16905 bytes; prior-overlap/cumulative logs contain 172577 / 1874696 bytes. Code commit `31b073bf2ba32ea9158b7da49d8b27d37cbab5df` closed at `c98bd4`. No public action or test runner is added.

### Positive callee-origin read receipts (2026-10-10; `201d1b22`)

`initialized_read_at` retains an actual initialized local cell at its original raw type. It uses the original `GenericHeap.read` once and keeps the same positive payload, Source read, reference representation and native optional-cell read. `callable_at` follows only the positive payload constructors and compatible wrappers at a genuine Source `IsFunction` witness. Closure classification retains its exact contextual Member; global and builtin classification retain their original source-shaped receipts. This pure read adapter performs no callee execution and does not infer selected compiler code or generalized scheme-cell views.

The positive callee-read unit is validated at `201d1b22`. Original 162-line Source `e30b3083` compiled on its first attempt without repairs. Before Source creation, the genuine capture authenticates 2101 independent normal Source/object triples and the same actual import environment; the compiled/import closure contains 2102 modules. Whole-module audit, two independent Source reviews, filesystem guards and all five normal command receipts pass. Normal verification passes all 18 literal private/normal TYPE/AXIOMS blocks and 9 API checks, one empty strict Source log and build 5631. Cumulative 16528 adds 18 names to 16510 with no overlaps or removals. The 5563-row snapshot, actual 2102-module environment, one existing `CoreLowering` object delta, three-module cone/rebuild and 4985 protected artifacts pass. No IO or runtime/Core specification change is added. Registry/codebook association, physical arity, stage gates, generalized cells and the strong joint child/body family remain open.

Validation: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-callee-origin-read-receipts-checks.json` (SHA-256 `68898808ee2b8be2e96dccd57e2208163bd890391a282c226de91f0880097a70`). Before capture `40e360` / session 11891 / `b9d15d`, strict direct `755c53`, and whole-module/API audit `46cfd8` / session 88088 / `3caf8d` closed successfully. Five normal command receipts closed at `16e5d8` / session 56098 / `c74153`; the registered build closed at `be5899` / session 2907, with 5631 jobs. Full/API logs contain 362265 / 13766 bytes; prior-overlap/cumulative logs contain 172678 / 1876880 bytes. Code commit `201d1b223f42ac78dabe33e7375c51aa75fb4a61` closed at `5ec1c2`. No public action or test runner is added.

### Pointwise stored-call origin posts (2026-10-10; `1ec31128`)

`preserves_selected` derives the genuine application leaf internally from the original admitted stored-closure invocation and strictly smaller body callbacks. `reflects_selected` reuses the receiving-model reflector once. Both retain strong heap cells, represented result and raw PostAdmission inside the original returned caller witness, with all cumulative effects and independent Source/native grades. `ResultAt.at_value` observes that same successful post; `ResultAt.forget` projects the original contract without constructing another state.

These are pointwise accepted-call ports. The actual callee traces, static Association, ordered raw/native bundles, initial admission and strict argument/body children remain genuine inputs. Preservation still consumes the original SourceSuffix. The body registry and outer payload registry remain distinct. This unit does not supply the mixed expression dispatcher or its callee and body callbacks.

Original 256-line Source `329c8e61` compiled on its first attempt without repairs. Before Source creation, the genuine capture authenticates 2112 independent normal Source/object triples and the same actual import environment; the compiled/import closure contains 2113 modules. Whole-module audit, two independent Source reviews, filesystem guards and all five normal command receipts pass. Normal checks pass full 6 / API 6, one empty strict Source log, build 5632 and cumulative 16534 (+6, no overlaps or removals). All six private/normal TYPE/AXIOMS blocks and complete API logs match literally. The 5564-row snapshot, 2113-module environment, one existing `CoreLowering` object delta, three-module cone/rebuild and 4985 protected artifacts pass. No IO is added.

An authentic diagnostic cut remains open: contextual code uses internal Word zero, whose public decoder names function fallthrough, while the current Member and Association records require an escaped-control fault row at that same token. The typing-based finish already excludes break/continue using the actual Source body receipt, but it cannot manufacture that unconditional row. Formation and invocation wiring must retain the genuine typed origin without changing the runtime token protocol.

Validation: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-stored-call-origin-posts-checks.json` (SHA-256 `40afae58432055fb664a99c02329013d60dbb9ea410bea9ee7e6f9c16daf40fe`). Before capture `fd0ce4` / session 68781 / `e399c9`, strict direct `e414ce`, and full/API audit `e69762` / session 24840 / `892617` closed successfully. Five normal receipts closed at `82a1ae` / session 41166 / `bb34bf`; the registered build closed at `885699` / session 22976 / `f7e9cd`. Full/API logs contain 1215247 / 32921 bytes; prior-overlap/cumulative logs contain 172777 / 1877537 bytes. Code commit `1ec311280f3ed35a5ecc7639abf6933e3cd481b5` closed at `a283cc`. The 205 / 158 / 183 / 137-line future drafts remain text-only; joint-family and all-pass closure are unfinished. Estimates stay 70% / 85%.

## 2026-10-10: Typed contextual closure receipts (`df034b25`)

Actual ordinary and method-principal formation now retains the complete static Code/body/Syntax receipt without an unconditional escaped-control diagnostic. `Association` is Type-valued; `StaticMember` retains its existential receipt in Prop. `source_binders`, `parameter_core`, `projected_bindings`, `native_type`, `stage_origin`, `selection`, `represents` and `extend` expose genuine compiler and forward representation facts. A physical argument count still requires the actual binder vector, and Source stage acceptance requires its original gate receipt.

`preserves_at` and `reflects_at` consume strict typed body flow at the same retained Association. They use the original typed parameter/body invocation once and preserve the returned pool through the actual saved caller restoration. Source and native grades remain independent. The original typed finish excludes escaping loop control using genuine Source syntax/body typing. This connects conditional formation and invocation; the complete mixed dispatcher and its body callbacks remain unfinished.

Normal verification passes build 5635, full 56 / API 24, one empty strict Source log and complete literal private/normal TYPE/AXIOMS and API agreement. Cumulative 16605 adds 56 names to 16549 with no overlaps or removals. The 5567-row snapshot, 2094-module environment, one existing umbrella object delta, three-module cone/rebuild and 4985 protected artifacts pass. Final Source SHA-256: `b366f169489d486a2e6d1c1b4cdff690cad11c39af00c0d97688d07530402ef8`. Three name-only proof-port corrections preceded the final strict pass.

Validation: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-typed-closure-receipts-finalize-committed-checks.json` (SHA-256 `846f8791b0001864c30ef03bd4cb464332a155d13b3636a5dba5ef99fc2b5251`). The finalized record authenticates code commit `df034b25dfbc095a3075db905cfd15c39469daa9`, the actual Source, all closed normal receipts and the dependency cone. No public action or test runner is added.

### Positive-cell typed receipt migration (`350e4336`)

The existing positive-cell backend now carries typed `StaticMember` leaves. `Member.to_static` and `StoredAt.to_static` preserve genuine legacy authority forward. `TypedStoredAt` retains the same Source/native physical cell and actual reads; `payload_static_member`, `CellOrigins.stored_at` and the callee-read projections carry the typed receipt at the actual reached state. Recovering a legacy escaped-control diagnostic from a typed receipt remains unsupported.

| Module | Complete owned declarations |
| --- | --- |
| `CallableIndexedOwnedContextualStoredClosureAssociationReceipts` | 13 |
| `CallableIndexedOwnedContextualInitializedClosureReceipts` | 23 |
| `CallableIndexedOwnedContextualCellOrigins` | 38 |
| `CallableIndexedOwnedContextualCalleeOriginReadReceipts` | 18 |

All four strict Source logs are empty on their first attempts. Normal verification passes all 92 complete private/normal literal TYPE/AXIOMS blocks and 22 byte-exact API checks, using only the standard three axioms. The original/current ownership census changes 88 → 92: 80 same-name literal matches, eight explicitly reviewed TYPE changes, four additions and no removals. Seven changed types replace `Member` with `StaticMember`, including generated recursors; `CellOrigins.stored_at` replaces `StoredAt` with `TypedStoredAt`. Each changed type has a separate reviewed disposition.

The measured cumulative census is 16609 from 16605, with four additions and no removals. Registered build 5635, the 5568-row pre-install snapshot, actual 2110-module import environment, all 11 existing object deltas, the 15-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit changes only these four existing proof modules, with 64 insertions and 13 deletions. Registration roots and imports remain exact; no runner or runtime/Core specification change is added.

Validation: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-typed-closure-receipts-consumer-migration-checks.json` (SHA-256 `b9567fb12973ffa5796e71003b983f1be5a52b766e53bde48383a2288f6859bf`). The independent Root normal review is `contextual-typed-closure-receipts-consumer-migration-root-normal-review.json` (SHA-256 `953c59ffefc94021c991e914301d5fa4094b958fc8c32226ee77d65b1c6457f1`). The actual code-commit record is `contextual-typed-closure-receipts-consumer-migration-code-commit.json` (SHA-256 `37484d43c5f831f4fb07ab898d9853ab20a59e802329be8dd5bfca4374563e84`) and binds commit `350e43367707611bb20810b04c357e3408737027` to those closed normal checks. This records completed code and normal validation; subsequent documentation/metadata finalization is separate.

### Reviewed drafts and the remaining proof boundary

The 392-line two-registry closure flow adapter and 648-line indirect call join have passed two independent full Source reviews. They retain all original body fields, the same Association and all four original typed invocation branch proofs. The actual reached positive callee post supplies the typed call receipt; its existential StaticMember is eliminated inside Prop. Strict body flow and real caller restoration retain the parent result and state. Physical arity and Source stage acceptance remain authentic separate receipts.

The 250-line named-body continuation and 122-line invocation adapter connect the actual Header/profile Tree, genuine `SourceReceipt.of_named`, parameter state and canonical protocol to the original typed finish. They retain the same actual pool and invoke the original finite body/invocation producer once per direction. Their shared named/global flow family and actual profile/diagnostic sites remain unfinished. These drafts have no kernel or integration claim.

The remaining substantial work is to close one real mixed expression/body family, prove the actual specialization/evidence/comptime transformations, and connect all results, failures, export errors and shared state to the public compiler and validated input boundary without unproved body/pass laws. The estimates remain 100% / about 70% / about 85%.

## 2026-10-10: Typed stored-call and selected stage receipts (`7e85f0bb`)

Typed stored-call and selected stage-boundary receipts now pass normal verification at `7e85f0bb`. `CallableIndexedOwnedContextualStoredCallTypeReceipts` derives ordered Source/native aggregate equalities from the original compiler receipt, raw Source typing, argument Tree and the positive callee's retained StaticMember. `at_callee_post` keeps Source admission and positive cells at that same reached state. Body and receiving registries remain separate. Physical binder arity and stage decisions require their own receipts.

`CallableIndexedOwnedContextualCalleeStageReceipts` uses the retained origin and actual caller preparation to construct a user Dispatch or authentic builtin row. `BuiltinAt.parameter_count` retains the builtin's physical parameter-list length. Its absent guard proves the original first-gate result `.inRight .word .unit`; `resolve_prefix` preserves the original argument/application suffix, unchanged gate store and strict suffix grade. User rejection, second-gate arity/application and whole indirect body composition remain separate.

Normal verification passes 5638 registered build jobs, two empty final strict Source logs, all 47 complete module-owned declarations (22 typed-call / 25 stage-boundary) and 17 API checks. Private/normal TYPE/AXIOMS blocks and complete API logs match literally. The cumulative census is 16666 from 16619: 47 additions, no overlaps or removals. The 5569-row pre-install snapshot, actual 2126-module environment, one existing umbrella object delta, four-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds two proof Sources and two umbrella imports.

The final Source fixes address dependent typing elaboration, an unused open, the builtin constructor alternative and the first-gate result index. The accepted gate uses `CallableContract.resultValue none = .inRight .word .unit`. Failed attempts remain preserved separately; each final normal Source log is empty. The unit changes proof modules and registration only.

Validation: `/private/tmp/solcore-owned-functions-resume-20261007/contextual-stored-call-static-member-receipts-checks.json` (SHA-256 `f267cd2fa0f43b0a0f946af4a2ca5a985bbc13e1c1197fd8ef858427a964bf1f`). Root's independent normal review is `contextual-stored-call-static-member-receipts-root-normal-review.json` (SHA-256 `7b156c9772c396156f0442680311a374be54e42f9e790b9c14786037b4b779d2`). The actual code-commit record is `contextual-stored-call-static-member-receipts-code-commit.json` (SHA-256 `edf32c701942d458d55c7ef955debd360a9d4b678dc230b5836b66c6563e9019`) and binds commit `7e85f0bb93de1c8dd5a5f442f0c6fedb31ec2d01` to those completed checks. Documentation and metadata finalization are separate.

The prepared receipt/model unit, compiler child collectors and new protocol adapters remain unintegrated drafts. The strict mutual expression/body family still has to build typed continuations at the actual parameter packets, retaining canonical global slots, the selected Source seed and the method dictionary. Runtime typing and immutable support alone do not recover that packet.

The whole admitted dispatcher, mixed family, receiving diagnostic interpretation, live-cell obligations, specialization/evidence/comptime passes and final public all-pass theorem remain unfinished. The estimates remain 100% / about 70% / about 85%.

## 2026-10-10: Prepared closure receipts and stored cell origins (`0451cd62`)

Prepared closure receipts and cell origins now pass normal verification at `0451cd62`. Ordinary and selected-principal support retain the actual compiler preparation, one JointBody, the same Code and typed body, and Source provenance. Principal support also retains the selected implementation, dictionary and cached named compilation. These receipts project forward to the existing typed model; an existing plain leaf cannot be upgraded to prepared authority.

The prepared Association, payload and cell model preserve that authority through map/world growth and actual allocation, writes and reads. Formation uses its original ordinary or principal factory once and retains the prepared member, represented result, positive cells and Source admission at the same reached state. Graded preservation and reflection retain the Source value/fault alternatives and independent Source/native grades. The body's static registry and receiving registry remain separate; function observations and runtime views project forward to the General model.

Normal verification passes one registered build with 5645 jobs, seven empty final strict Source logs, all 274 module-owned declarations and 79 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 16666 to 16940: 274 additions, no overlaps or removals. The 5571-row pre-install snapshot, actual 2172-module environment, one existing umbrella object delta, nine-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds seven proof Sources and seven umbrella imports.

Final elaboration fixes retain the original assumptions and proof steps: include the actual support/Site witnesses, name the real `FunctionCalls.value` constructor and use explicit `CallableIndexedLambdaValues.History.native` projections. Failed attempts remain preserved separately. Each final strict log is empty. The unit changes proofs and registration only.

Validation: `prepared-contextual-closure-receipts-checks.json` (SHA-256 `442c40d6e450b6e8f3be4fbeb0ad2c19ed5ac7b2f70906db4fc8bc05ce1b867c`) and the bounded independent normal summary `prepared-contextual-closure-receipts-root-normal-summary.json` (SHA-256 `948a00e7b7bf5e719ca6bc6e062dd3b2b0a64bdc0fa58406d43cc37878ef4d76`). The actual code-commit record `prepared-contextual-closure-receipts-code-commit.json` (SHA-256 `b06907e478271d2f2419c8784f2a6a8c2eb149f05e447f03b301e26132c7466e`) binds these checks to `0451cd621ba299ac60f59e991bef821f352e20e0`. Documentation and metadata finalization are separate; this entry records completed code and normal verification.

Compiler child collectors, protocol-specific finish/packet adapters and qualified-call helpers remain unintegrated drafts. The shared expression/flow E/F family must still use authentic Nested or Principal Origin parameter packets, retaining canonical globals, the Source seed and selected method dictionary. The selected Principal Site must also align with its actual administrative prefix. Receiving-registry diagnostic-table success and reached error interpretations remain explicit where required; registry extension alone does not establish them. Whole ordered dispatch, mixed bodies and final public all-pass composition remain unfinished. The first objective remains 100%, the second about 70%, and the equally weighted overall estimate about 85%. Declaration counts do not measure completion.

## 2026-10-10: Compiler child collectors and prepared function qualification (`e27c3ccb`)

Compiler child collectors and prepared function qualification now pass normal verification at `e27c3ccb`. The ordinary collector derives child coverage from the actual retained compiler inventory. The selected-principal collector keeps the actual method, dictionary, cached compilation and same Site; its original joint-body producer runs once. Concrete ordinary/principal qualification travels with the same Code and Support through function values, payloads and cells, including forward map/world extension. These static receipts retain compiler authority for the subsequent semantic proof.

Normal verification passes one registered build with 5649 jobs, four empty final strict Source logs, all 159 module-owned declarations and 36 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 16940 to 17099: 159 additions, no overlaps or removals. The 5578-row pre-install snapshot, actual 2187-module environment, 1 existing umbrella object delta, 6-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds four proof Sources and four umbrella imports.

Three actual elaboration failures were preserved before the final strict Sources passed: an ordinary section-variable collision and omitted runtime parameter, ambiguous qualified Association projection, and an incorrectly inferred dependent LocalView transport. The bounded repairs retain the original proof premises and factory actions. The compiled-qualification History projection was made explicit before its first successful attempt.

Validation: `prepared-compiler-qualified-child-collectors-checks.json` (SHA-256 `2f979370ed4f2b7f74ebe25fa0e194da26dce024a1e1108f6f02739372ea6fc9`) and the independent normal summary `prepared-compiler-qualified-child-collectors-root-normal-summary.json` (SHA-256 `1d154d5039ddb531d5535b74d1b10b422ca8fb2b1a501f59e37d0003a2635211`). The actual code commit is `e27c3ccb6f237c33b862c249feb75006b12515e5`. Documentation and metadata finalization are separate; this entry records completed code and normal verification.

Protocol-specific finish/packet adapters and qualified formation/call helpers remain unintegrated drafts. The shared expression/flow E/F family must still construct authentic Nested or Principal Origin parameter packets and use actual compiler occurrence typing, retaining canonical globals, the Source seed and selected method dictionary. Broad accepted-child certificates alone do not supply local occurrence typing or align a selected Principal Site with its administrative prefix. Receiving-registry diagnostic-table success and reached error interpretations remain explicit where required; registry extension alone does not establish them. Whole ordered dispatch, mixed bodies and final public all-pass composition remain unfinished. The first objective remains 100%, the second about 70%, and the equally weighted overall estimate about 85%. Declaration counts do not measure completion.

## 2026-10-10: Canonical parameter protocols and qualified closure flow (`0338a276`)

Canonical parameter protocols and qualified closure flow now pass normal verification at `0338a276`. Ordinary and selected-principal packet producers retain the original parameter entry, canonical bindings, globals and base pool. Typed continuations consume the body flow under that same caller protocol and keep the original Source body receipt. Qualified formation retains compiler authority with the represented closure, positive cells and Source admission. The canonical flow producer uses one retained JointBody and transports the actual returned pool through its protocol bridge. Source and native grades remain independent.

Normal verification passes one registered build with 5655 jobs, six empty strict Source logs, all 128 module-owned declarations and 29 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 17099 to 17227: 128 additions, no overlaps or removals. The 5582-row pre-install snapshot, actual 2192-module environment, one existing umbrella object delta, eight-module dependency cone/rebuild and all 4985 protected artifacts pass. Six proof Sources and six umbrella imports are added.

Protocol-specific finish, ordinary/principal parameter packets, qualified formation and canonical flow are integrated. The shared expression/body family still needs actual compiler occurrence typing, canonical capture and selected method-prefix alignment, reached diagnostic interpretations, and a concrete common induction over expressions and function bodies. The canonical flow producer requires genuine diagnostic table readiness and both reached error interpretations; registry extension alone supplies neither. Named and indirect dispatch, mixed bodies and the final public theorem across specialization, evidence and comptime remain unfinished.

The next nine compiler occurrence modules are independently text-reviewed drafts. Their native compilation, inventory and integration have not run. Further raw compiler trees, child typing inversions and a concrete lambda-body producer are also drafts. The second objective remains about 70%, and the equally weighted overall estimate remains about 85%; declaration counts do not measure completion.

## 2026-10-10: Native typing at compiler occurrences (`e0edb2ec`)

The nine compiler occurrence modules are integrated and pass normal verification. Ordinary and selected-principal capture receipts preserve the actual canonical environment and globals. Principal root-prefix typing and literal lambda result normalization recover the native type of the same emitted body or occurrence.

The lexical, ordered match, assignment, for-header and imperative collectors derive each used child witness from actual enclosing Core typing. Present assignment RHS typing comes from the emitted assignment operator; key typing follows the original ordered compiler occurrences. These collectors retain genuine Source and compiler authority. Their certificate factories still have to be instantiated at the same actual Site.

Normal verification passes one registered build with 5664 jobs, nine empty strict Source logs, all 134 module-owned declarations and 28 API checks. Complete private/normal TYPE/AXIOMS blocks and the complete API logs match literally, using only the standard three axioms. The cumulative census grows from 17227 to 17361: 134 additions, no overlaps or removals. The 5588-row pre-install snapshot, actual 2039-module import environment, one existing umbrella object delta, eleven-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds nine proof Sources and nine umbrella imports.

Four bounded elaboration repairs preserve the original premises: explicit capture/state indices and theorem declarations for propositional admission; normalization of the existing raw assignment RHS proof; disambiguation of Scope and the present-RHS Boolean; and binding the existing arbitrary native type before both match callback proofs. Failed attempts and their exact Sources/logs remain preserved. An omitted BEFORE chronology field was bound to the original completed capture in a fresh metadata packet; no successful native action was replayed.

Validation: `prepared-compiler-assignment-occurrence-receipts-checks.json` (SHA-256 `f1a05b0c47fd2a7e6c78badf14560d27c3e1476e8b3f1e4bbd9c2d69360cf985`). The independent Root summary is `prepared-compiler-assignment-occurrence-receipts-root-normal-summary.json` (SHA-256 `f440ca7b4aadbc978f6c70eace3100be4667942788f87bb4ba952a1d4deb8452`). Both reside in the local verification directory `/private/tmp/solcore-owned-functions-resume-20261007`; they are validation records rather than repository dependencies.

The next static authority producers derive parameter kinds and match hidden-ID freshness from same-source LocalIdentityOwnership, and exact policies from one Named Compilation and Site. They remain unintegrated drafts. The concrete same-Site shell, raw compiler Tree/native child inversions and the expression fold are also under development. The expression fold keeps an explicit lambda/named/indirect call-leaf obligation; a completed mixed family is not assumed.

Next, construct the real static shell and receiving diagnostics, then close one shared expression/body induction with strict body children and independent Source/native grades. Generalized cells, named/global/method and indirect dispatch, specialization/evidence/comptime composition, general failures/export errors and the final public compiler theorem remain unfinished. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure completion.

## 2026-10-10: Local identity freshness and compiler Site policies (`27abbb6f`)

Two static authority modules are integrated and pass normal verification. `CallableIndexedOwnedLocalIdentityFreshness` proves that actual lambda parameter IDs are disjoint from the same Source inputs, transports their ordinary kinds to the actual lowered parameter vector, and derives match hidden-ID freshness from genuine `LocalIdentityOwnership`. The proof reconciles the actual declaration and hidden-ID inventories; runtime graph validity alone is not an ownership proof.

`CallableIndexedOwnedPreparedNativeSitePolicies` keeps one actual Named Compilation and Site. It derives the ambient match context, binder/read policies, physical reference slot and allocator, and constructs assignment/unary policies from the actual issued assignment table and place providers. Root policy equality, solved ledger, scope and selected issuer identities remain explicit compiler authority. This module does not infer Source body typing or an execution law.

Normal verification passes one registered build with 5666 jobs, two empty strict Source logs, all 99 module-owned declarations (86 freshness / 13 policies) and 16 API checks. Complete private/normal TYPE/AXIOMS blocks and the complete API logs match literally, using only the standard three axioms. The cumulative census grows from 17361 to 17460: 99 additions, no overlaps or removals. The 5597-row pre-install snapshot, actual 2207-module import environment, one existing umbrella object delta, four-module dependency cone/rebuild and all 4985 protected artifacts pass. Kernel policy also passes. The code commit adds two proof Sources and two umbrella imports; execution and Core specifications are unchanged.

Validation: `prepared-native-site-authority-receipts-checks.json` (SHA-256 `3e4ba271f0ac08ffece6f77dcf078e328845e2130864b0333d556580ee788495`). The independent Root summary is `prepared-native-site-authority-receipts-root-normal-summary.json` (SHA-256 `c322f1f396364f9776eaeea427bfb9669ac7f5accb371cd9a348592ad6826a7c`). Both reside in the local verification directory `/private/tmp/solcore-owned-functions-resume-20261007`; they are validation records rather than repository dependencies.

The same-Site shell and native compiler dependency chain have isolated author-check results, while their shared integration remains pending. A raw compiler Tree proof and typed named continuation required bounded repairs during those checks; original Sources and every failed attempt remain preserved. The admitted expression fold still has explicit lambda, named and indirect call-leaf obligations. The three actual call branches are being connected to strict body continuations and the original caller restoration, with independent Source/native grades.

Next, finish and verify the actual dependency-closed expression/body family. Its static inputs must come from the same compiler Site and selected receiving diagnostic issuer; no completed body execution law may replace the induction. Generalized cells, general dispatch, specialization/evidence/comptime composition, failures/export errors and the final public compiler theorem remain incomplete. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure completion.

## 2026-10-10: Reached diagnostics and public decoding (`ef85a057`)

Seven proof modules connect the actual selected compiler issuer and public decoder to expression preservation and reflection. Local reads use the reached lexical cell witness. Missing mapping defaults use the actual index header, key, form, ordered Source prefix and unavailable raw element. These occurrence-specific facts replace the new proof path's unnecessary universal error assumptions. The original conditional modules retain their original contracts.

The selected issuer keeps the real ordinary or principal compilation and dictionary. The read/index policy producer constructs decoder error views internally from authentic runtime witnesses. It retains the selected reason, issuer identity and receiving registry. Caller Header reason alignment and remaining compiler branch factories still require proofs.

Normal verification passes one registered build with 5673 jobs, seven empty strict Source logs, all 76 module-owned declarations and 24 API checks. Complete private/normal TYPE/AXIOMS blocks and complete API logs match literally, using only the standard three axioms. The cumulative census grows from 17460 to 17536: 76 additions, no overlaps or removals. The 5599-row pre-install snapshot, actual 2222-module import environment, one existing `CoreLowering` object delta, nine-module dependency cone/rebuild and all 4985 protected artifacts pass. Kernel policy passes. The change adds seven proof Sources and seven umbrella imports.

Each Source had two genuine independent reviews before Root compilation. The independent before capture measured 2215 modules and completed before any private proof Source existed. Root compiled only Source copies; author objects were not promoted. All seven final strict logs were empty on their first Root attempts. Earlier author failures and immutable snapshots remain preserved.

Validation: `reached-expression-diagnostic-receipts-checks.json` (SHA-256 `a768f59b87f66efb48581dd3986395076d0ec99c60945f10a2a0dc3f50247931`). The independent Root summary is `reached-expression-diagnostic-receipts-root-normal-summary.json` (SHA-256 `78ba8b2b8c69d9a7739a17c2fc795bd6887eb2cd934b6a757438bd333b2fb111`). Both reside in the local verification directory `/private/tmp/solcore-owned-functions-resume-20261007`; they are validation records rather than repository dependencies.

Next, integrate the direct prepared value and formation model, instantiate actual lambda/named/global/builtin call leaves and close one strict expression/body induction. Static occurrence factories must cover genuine evidence, coercions and generalized local alternatives. Independent staged rejection must propagate through the full Source syntax. Specialization, evidence and comptime composition, general failures/export errors and the final public compiler theorem remain incomplete. The estimates remain 100% for the first objective, about 70% for the second and about 85% overall. Declaration counts do not measure completion.

## 2026-10-10: Direct prepared closure formation and source scopes (`6dbfa243`)

Four modules keep ordinary and method-principal closures attached to their actual compiled Code, History, captures, static Support and independent Source origin. Their forward representation and runtime views use the same prepared member. One actual formation supplies the value or fault trace; preservation and reflection retain the returned heap, store, positive cells and Source admission with independent grades. The receiving registry remains separate from the body registry. The stage-scope producer recovers the original owner and dictionary from authentic compiled sidecars. It does not establish guard acceptance or complete recursive staging coverage.

Normal verification passes one registered build with 5677 jobs, four empty strict Source logs, all 139 module-owned declarations (74 origins / 30 formation / 20 bounds / 15 scopes) and 47 API checks. Complete private/normal literal TYPE/AXIOMS blocks and complete API logs agree, using only the standard three axioms. The cumulative census grows from 17536 to 17675: 139 additions, no overlaps or removals. The 5606-row pre-install snapshot, actual 2190-module import environment, one existing `CoreLowering` object delta, six-module dependency cone/rebuild and all 4985 protected artifacts pass. The change adds four proof Sources and four umbrella imports.

Each Source had two genuine nonauthor reviews before Root compilation. The independent before capture measured 2186 modules and completed before any private proof Source existed. Root compiled Source copies at the correct module paths. All four final strict logs were empty on their first Root attempts. Existing conditional interfaces retain their original premises.

Validation: `prepared-direct-cell-formation-receipts-checks.json` (SHA-256 `bf9fe94b43fb7f230bffb9cb1f23791415a3b4d009e3bf9513172a3479a73635`). The independent Root summary is `prepared-direct-cell-formation-receipts-root-normal-summary.json`. Both reside in `/private/tmp/solcore-owned-functions-resume-20261007`; they are local verification records. Successful checks are reused during commit finalization.

Next, construct a finite inventory of actual issuer-aligned named Headers and their retained Source dictionaries, then connect closure/named/global/builtin calls through one strict expression/body induction. Static occurrence factories must cover real evidence, coercion and generalized-local alternatives. Recursive staged rejection, specialization/evidence/comptime composition, general failures/export errors and the final public compiler theorem remain incomplete. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall. Declaration counts do not measure completion.

## 2026-10-10: Selected named static receipts (`ee27dc50`)

Four modules construct ordinary named Headers with the actual selected diagnostic issuer and retain the original Source view, substitution order and resolved dictionary. Real ordinary selection derives emptiness only for the selected dictionary. The same Header certificate supplies Source types and declaration validity. Authenticated named metadata and the actual dispatch guard supply the full physical binder count; guard acceptance remains a separate obligation. No Header identity is inferred from matching native types or cached code.

Normal verification passes one registered build with 5681 jobs, four empty strict Source logs, 27 module-owned declarations (10 Header / 9 evidence / 2 Source facts / 6 arity) and 15 API checks. Complete private/normal literal TYPE/AXIOMS blocks and API logs agree, using only the standard three axioms. The cumulative census grows from 17675 to 17702: 27 additions, no overlaps or removals. The 5610-row pre-install snapshot, actual 2222-module environment, one existing umbrella object delta, six-module dependency cone/rebuild and all 4985 protected artifacts pass.

Each Source had two genuine nonauthor reviews. The independent BEFORE capture measured 2218 modules and completed before any private proof Source existed. All four strict Source logs were empty on their first Root attempts. The first full audit rejected an unrecorded path after successful full/API elaboration: the overlay had made extra identical object copies. That failed attempt and its copies were preserved. Correct aliases to the independently captured Source and both object files passed a fresh full audit. Strict Sources were not replayed. Eight successful normal receipts are retained for metadata-only commit finalization.

Validation: `selected-named-static-authority-receipts-checks.json` (SHA-256 `d0945377acf47c2fc5cc1abc459faa308ce5d680721b4ba05c6498c742617b47`) and `selected-named-static-authority-receipts-root-normal-summary.json`, both local verification records in `/private/tmp/solcore-owned-functions-resume-20261007`.

The finite Header inventory and raw per-occurrence compiler factories are still being constructed. Closure/named/global/builtin recursion, recursive staged rejection, full evidence/coercion/generalized-local alternatives, specialization/comptime composition, general failure/export-error correspondence and the final public theorem remain open. Estimates stay at 100% for the first objective, about 70% for the second and about 85% overall.

## 2026-10-10: Prepared named inventories and bootstrap correspondence (`ae3d5594`)

Fourteen proof modules connect actual selected named definitions to compiler body profiles and initialization authority. A finite inventory keeps each selected Header, diagnostic issuer, Source view, complete substitution and resolved dictionary. Body profiles come from the coupled compiler collector at the actual parameter-entry state. Typed continuations preserve the original caller pool, ordered arguments, dictionary and independent Source/native grades.

Bootstrap receipts use the actual prepared initialization and retain its complete ownership key through key embeddings. The finite inventory supplies cache, global-size and empty-local facts. Reached range receipts transport the complete substitution range, including unused replacements, from genuine valid instantiation. They do not infer Source entry validity from public compiler acceptance.

Normal verification passes one registered build with 5695 jobs, fourteen empty strict Source logs, all 344 module-owned declarations and 102 API checks. Complete private/normal literal TYPE/AXIOMS and API logs agree, using only the standard three axioms. The cumulative census grows from 17702 to 18046, with no overlaps or removals. The 5614-row pre-install snapshot, actual 2241-module environment, one existing umbrella object delta, sixteen-module dependency cone/rebuild and all 4985 protected artifacts pass.

Each Source had two genuine nonauthor reviews. Authentic BEFORE captured 2227 modules before any private proof Source existed. Source copies compiled on their first Root attempts; author objects were not installed. Eighteen successful normal receipts are retained. A metadata-only verifier attempt failed because Root omitted the prior census count from its bindings; the immutable corrected bindings use the actual count 17702. No successful Source check was replayed.

Validation: `prepared-catalog-named-profile-bootstrap-checkpoint-checks.json` (SHA-256 `53001c0f2cc55657926a05cc0d23121ddedd78b56e7a0d3c056385f9bd33c9be`) and `prepared-catalog-named-profile-bootstrap-checkpoint-root-normal-summary.json`, local verification records in `/private/tmp/solcore-owned-functions-resume-20261007`.

The common function/cell model must retain positive bootstrap and selected compiler provenance through formation, reads and state extension. Actual reached-input coverage, receiving diagnostic interpretation, remaining compiler alternatives, strict expression/body induction and all-pass public correctness remain unfinished. Work estimates remain 100% for the first objective, about 70% for the second and about 85% overall.

### Shared function model and native compiler foundations at `922ac60f` (2026-10-10)

The code unit adds 27 proof Sources and their `CoreLowering` imports. Positive origins retain actual bootstrap ownership, compiler associations, captures and full Source dictionaries. Native occurrence collectors and typed closure/global/builtin dispatch use those retained receipts. This unit changes proof infrastructure; public runtime signatures and behavior remain as previously verified.

Genuine Source peer reviews and independent tool reviews preceded native integration. The private environment uses explicit Source and both object aliases with no normal-library fallback. Normal validation checks all 568 declarations and 165 APIs against the private results with literal TYPE/AXIOMS and complete API agreement. Only the standard three axioms occur. The cumulative census is 18614 from 18046, with no overlaps or removals. All 27 strict logs are empty. Build 5722, the actual 2306-module environment, the 29-module dependency cone/rebuild and 4985 protected artifacts pass.

The original successful tool receipts are retained: native BEFORE `7daa60` / session 93654 / closure `30f834`; private full/API `08c07c` / session 92107 / closure `27c479`; registered build `e06174` / session 71932 / closure `ea453c`; normal validation `fe28a7` / session 49243 / closure `0da14f`. The normal checks artifact SHA256 is `15be61fa750a7148625eda13a72a6916a94c4c2d74c5ac0f3f0983a662cc404d`. Commit finalization reuses these successful receipts without rerunning Lean.

Concrete accepted argument producers, eligible ordinary/principal expression roots and the strict shared body induction remain incomplete. Actual body compilation at an administrative prefix and fixed-prefix lambda compilation require independent compiler receipts. Neither packed argument typing nor erased representation supplies physical arity or original Source authority.


## 2026-10-10: Paired compiler typing and constructive call packets (`2caef32a`)

The paired lexical, match and imperative collectors derive actual-context and fixed-prefix child typing independently from the same accepted lowering. Named profile extraction keeps the original actual administrative context, compiler Tree and diagnostic issuer; its fixed body typing comes from the same cached code and authentic context support.

Closure and named argument factories now derive their packets from accepted call branches, preserving original Source argument types, physical parameter count, bootstrap owner, selected dictionary and the same argument post. Selected ordinary and principal lambda producers retain their literal compiler receipt, issuer and body read budget. Eligible body flow ports request the expression hypothesis only at a genuine ordinary Header with caller evidence or an actual selected principal with its dictionary. They retain the reached pool and independent Source/native grades.

Normal verification passes one registered build with 5742 jobs, 20 empty strict Source logs, 273 complete module-owned declarations and 75 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally. The cumulative census grows from 18614 to 18887, with 273 additions, no overlaps and no removals. The pre-install snapshot has 5655 rows; the actual compiled environment has 2313 project modules. The one existing CoreLowering object delta, 22-module dependency cone/rebuild, all 4985 protected artifacts and all 24 normal receipts pass.

The original successful receipts are retained: native BEFORE `3694ab` / session 21842 / closure `2a4f40`; private full/API `1d3029` / session 89445 / closure `6efd19`; registered build `8763b5` / session 72048 / closure `019a92`; normal validation `b59293` / session 13003 / closure `c79a89`. The normal checks artifact SHA256 is `05bc8dc256737b69c0d9453137013592f7a1629f760a052f3e105ef876182ee4`. Documentation and checkpoint finalization reuse these successful receipts.

The actual and fixed native result types may differ. Both witnesses come from their own enclosing-code derivation at the same lowering; no child is rebased from an arbitrary administrative context. Original Source parameter metadata, selected issuer and runtime effects remain attached to the same receipt.

The final numeric induction over eligible expressions and bodies still has to assemble these conditional ports and supply the authentic occurrence, syntax, ledger and receiving-diagnostic factories throughout the actual compiler alternatives. Ordinary Dynamic execution still requires genuine stage-guard acceptance at each reached indirect call. A rejected stage guard has its own Source staging judgment at the callee post, before arguments; full recursive rejection coverage remains unfinished. Specialization/evidence/comptime composition, generalized cells, general failures and export errors, and the final public theorem remain incomplete. The estimates stay 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure completion.

## 2026-10-10: Accepted indirect calls and caller restoration (`22a68060`)

The accepted closure, global and builtin branches construct their argument packets from the retained Source rows, physical parameter count and selected owner or dictionary. Whole-parent preservation and reflection use the original callee, ordered argument and application derivations, preserving the actual argument post and restored caller pool. Builtin application uses its original primitive proof. User application retains strict closure or named body hypotheses.

Paired named extraction keeps actual-context and fixed-prefix typing independently. The selected Header action yields the contextual root receipt at the same source, scope, diagnostic issuer, reason and lowered expression. Positive lambda recipes manufacture the compiler packet at the retained body read budget. Callee reflection transports ordinary values and failures at the reached caller state. These receipts preserve the actual compiler and Source authority.

Normal verification passed one registered build (5752 jobs), ten empty strict Source checks, and literal private/normal agreement for all 129 owned declarations and 36 APIs. The cumulative census grew from 18887 to 19016 (+129), with no overlap or removals. The saved normal inventory contained 5675 module rows before installation, and the compiled project environment contained 2335 modules. The registration changed the existing CoreLowering object; all twelve modules in the reverse dependency cone were rebuilt, and all 4985 protected rows remained unchanged. All fourteen normal receipts closed with exit code 0.

Each Source had two independent nonauthor reviews before native integration. Tool reviews covered the full adaptation and preserved the literal type/axiom and ownership guards. The independent BEFORE capture measured 2325 project modules before any private proof Source existed; the private environment measured 2335. All ten strict Source logs were empty, and the private audit checked 129 declarations and 36 APIs. The recorded normal Source and both object aliases point to the independently captured BEFORE files.

The independent BEFORE capture closed at `c89ac2` (`7d090d`, session 52648); the private full/API audit at `c5bafb` (`df6494`, session 49322); the registered build at `8c622c` (`f5090f`, session 37174); and normal verification at `078e8b` (`b86ca5`, session 65204). Code commit: `22a68060394eeedc703dfcf31b7d4d4b656b823e`. The saved `accepted-indirect-parent-function-families-checks.json` has SHA-256 `dbc73eaf96a40be80ceb820f047a4bce7eef6b2f830cb98ee98ab896d07cd5e7`. The checkpoint uses the original fourteen closed normal receipts; metadata finalization does not repeat their kernel runs.

The numeric expression/body induction and complete occurrence, syntax, ledger and receiving-diagnostic factories remain unfinished. Actual stage gates are premises of the accepted-call results. A rejected first-stage guard remains a separate Source staging outcome at the callee post before arguments; scoped callsite/reason alignment and complete recursive rejection coverage are not established by these results. Second-stage rejection occurs after argument evaluation and remains a separate pending branch. Specialization/evidence/comptime composition, generalized cells, general failure/export-error correspondence and final public correctness remain open. Work estimates remain 100% / about 70% / about 85%.

## 2026-10-10: Staged indirect call runtime bounds (`d9f2a0c4`)

The normally verified `staged-indirect-call-runtime-bounds` unit adds ten proof Sources and ten CoreLowering imports at `d9f2a0c4`. It checks 234 owned declarations and 71 selected APIs, with genuine author checks and two nonauthor Source reviews per Source. The preceding baseline was HEAD `8ce195d527d56533a169b482d78ca3c5448b68b4`, with cumulative census 19016. Core syntax, runtime evaluation and public operational definitions retain their existing behavior.

| Boundary | Exact retained evidence | Remaining composition |
| --- | --- | --- |
| Recursive staged grading | Four mutually recursive grades mirror the 46 original supported rules. Soundness and trace sizing preserve scopes, heaps and exact semantic/stage failures. | Full recursive Source grammar and public compiler coverage. |
| Reached admission | The genuine graded trace and concrete administrative frame retain the same dependent reached caller state and relation. Values have original Source admission; stage faults have stable rows. | Construct the strict staged E hypotheses by numeric induction. |
| Callee failure | Strict child E supplies its exact semantic or nested stage failure. The original callee-failure contract runs once at the actual reached heap/store. | Whole dispatch and application/body alternatives. |
| Whole-parent native prefix | Actual Prepared lowering and first-bind inversion expose strict native callee completion. Reflection reconstructs an independent Source grade and retains the original gate suffix after a value. | First-gate resolution followed by the actual ordered arguments and application. |
| Scoped original call | Forward SourceView transport retains original codebook node/metadata, actual substituted call metadata, unchanged callee/ordered IDs, and the same Prepared caller/site/table. | Actual scoped receiving-diagnostic composition for each reached rejection. |
| First-stage rejection | Genuine selected guard and callee trace yield a stage failure before arguments, with the full receiving model and actual callee post. | Complete recursive dispatch and failing-scope diagnostic coverage. |
| Second-stage rejection | Selected physical arity and original codebook row yield a semantic arity fault after arguments. Source/native derivations retain the same argument effects and caller post. | Original-node receiving transport and complete whole-parent classification. |
| Ordered arguments | Genuine Tree, unique/typing rows and strict staged E construct sequential value/fault results and reflect actual pack evaluation. Both fault tags and the reached state remain exact. | Connect every compiler occurrence and accepted application/body branch. |
| Closure body flow | Paired eligible E specializes at the same retained fixed prefix before the original Association flow. | Numeric E/F induction and staged body failures. |
| Named body flow | Same finite Issued packet and Header root construct actual children with independent actual/fixed native witnesses; original body flow is used once. | Static Domain/syntax and receiving diagnostics for all selected bodies, numeric E/F induction. |

Stage rejection remains `Failure.stage` at the callee post. Physical arity rejection remains `Failure.semantic` at the argument post. Ordinary Dynamic erasure applies only to the corresponding value or semantic-fault branch. Stable rows are attached to the concrete reached caller state and frame; they do not supply deep heap admission for a stage failure. Source and Core grades are independent.

Normal verification passed one registered build with 5762 jobs, ten empty strict Source checks, and literal private/normal TYPE/AXIOMS and complete API agreement for all 234 owned declarations and 71 selected APIs, using only the standard three axioms. The cumulative census grew from 19016 to 19250 (+234), with no overlap or removals. The normal pre-install snapshot contained 5685 module rows; the independent BEFORE environment measured 2314 project modules and the compiled environment measured 2324. The existing CoreLowering object changed for registration; all twelve modules in the reverse dependency cone were rebuilt, and all 4985 protected artifacts passed. All fourteen original normal receipts closed with exit code 0.

The actual independent BEFORE capture closed at `b06ac5` (`93e376`, session 32268); private full/API audit at `37afb7` (`049c04`, session 30036); registered build at `c23ee3` (`f0abd0`, session 2959); and normal validation at `ae72a4` (`d1d98b`, session 63612). Code commit `d9f2a0c412f2315193c6e4c196826a9b8763d286` closed at `d4b0be`. The saved `staged-indirect-call-runtime-bounds-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `3265acc0c522928261051cc31bcc4b20a30931101377c2996cd2ea7f6db183e5`. The checkpoint uses the original fourteen closed validation receipts; metadata finalization does not repeat their kernel runs.

The package excludes later staged builtin application, terminal statements, receiving diagnostic adapters, whole argument-prefix and body drafts. The common numeric E/F proof, complete static compiler factories, supported-profile expansion to remaining Source forms, specialization/evidence/comptime composition, general failure/export-error correspondence and final public all-pass theorem remain open. The first objective is complete; estimates remain about 70% for the second and about 85% overall.

## 2026-10-11: Staged call diagnostics and terminal bodies (`1507404b`)

The normally verified `staged-call-diagnostics-terminal-bodies` unit adds twelve proof Sources and twelve CoreLowering imports at `1507404b`, checking 184 owned declarations and 66 selected interfaces. Its preceding baseline was code `d9f2a0c4`, documentation `1a84839a6a2ae4013c191b3988a92f129e0bc68c` and cumulative census 19250. Author checks, failed attempts, exact Source snapshots and two independent nonauthor Source reviews per Source are preserved. Core syntax, runtime evaluation and public operational definitions retain their existing behavior.

| Boundary | Concrete proof route | Remaining obligation |
| --- | --- | --- |
| Receiving preparation | Successful public preparation bounds actual decoded tokens. Authentic IssuedAt rebuild and sealed callable allocation preserve existing lookups. | Select the same real issuer throughout every compiler occurrence. |
| Original-row diagnostic | Original Selected and Site.reasonAt transport the literal token to the actual completion table. | Complete compiler occurrence factories and dispatch linkage. |
| First-gate rejection | StageErrorView retains actual invocation/scope, guard frame, SourceView, CallView and original selected rejection. Receiving post stays at the callee heap/store. | Compose whole staged parent preservation/reflection and recursive scope coverage. |
| Second-gate arity | Original BoundaryAt plus actual physical mismatch yields receiving semantic arity representation at the reached argument state. | Complete whole-parent second-gate/application classification. |
| Public semantic decoding | Existing assignment view and concrete arity counts follow the literal table decoder; values forward through the original model. | Broader semantic and export-error coverage. |
| Terminal statement | Actual Head and strict child E construct the four return/tail value/fault rules, with independent Source/Core grades. | General statement alternatives and recursive control flow. |
| Terminal body | Actual return/tail and footer binds produce BodyResult for code.rename and retain reached effects/admission. | Recursive nonterminal bodies and function application linkage. |
| Compiler terminal receipt | Accepted returnSome/singleton tail exposes exact used child, predecessor, result type and footer. SourceView recovers the original occurrence. | Construct authentic child certificates for complete compiler alternatives. |
| Terminal body meaning | Same compiler receipt and SourceView supply Head; strict child hypotheses establish meaning of the literal emitted code.rename. | Shared numeric E/F induction and general body factory. |
| Builtin application | Represented ordered scalar inputs rule out arity/type branches; original primitive P/R supplies the actual builtin rule at the argument state. | Join the whole parent and other application branches. |
| Whole indirect argument prefix | Actual parent inversion uses strict callee E, original SourceParent typing, scoped first gate and concrete ordered-argument reflection. | Preserve/reflect the remaining user application/body suffix and close numeric induction. |

First-gate arity remains Failure.stage with the actual failing invocation and scope. Second-gate arity remains Failure.semantic after arguments. The receiving table decoder alone does not determine a failing scope; StageErrorView retains the invocation and guard evidence. Original codebook nodes/metadata and actual substituted compiler nodes/metadata remain separate. Stable rows and PostAdmission stay attached to the concrete reached caller relation, heap/store and frame; deep Source admission follows successful values.

The terminal compiler and SourceView route removes a separate supplied Head or complete body meaning premise. It still requires original Source expression typing and the authentic used child compiler certificate. The argument-prefix route derives raw callee/argument typing from original Source rows while keeping actual SourceParent, Tree, uniqueness, SourceView and guard-frame cuts. Its successful argument branch retains the native application suffix for the next proof.

Core AST/runtime and public operational definitions retain their existing behavior. Complete staged call applications, recursive bodies, numeric E/F, static compiler factories and remaining supported-profile grammar are open. Specialization/evidence/comptime composition, generalized cells, general failures/export errors and final public all-pass correctness remain unfinished. The first objective is complete; estimates stay about 70% for the second and about 85% overall.

Normal verification passed one registered build with 5774 jobs, twelve empty strict Source checks, and literal private/normal TYPE/AXIOMS agreement for all 184 complete owned declarations and complete API agreement for 66 selected interfaces, using only the standard three axioms. The cumulative census grew from 19250 to 19434 (+184), with no overlap or removals. The normal pre-install snapshot contained 5695 module rows; the current snapshot contains 5707. The independent BEFORE environment measured 2195 project modules and the compiled environment measured 2207. The existing CoreLowering object changed for registration; all fourteen modules in the reverse dependency cone were rebuilt, and all 4985 protected artifacts passed. All sixteen original normal receipts closed with exit code 0.

The independent BEFORE capture closed at `95d226` (`5e30b5`, session 27207); private full/API audit at `e7c58a` (`c4bffc`, session 59109); packet freeze at `ffc386` (`36c4ae`, session 8576); registered build at `335796` (`dc06e6`, session 62711); and normal validation at `8d3298` (`b29544`, session 57723). Code commit `1507404b20264fc300b656e9971205f3ecbf90a8` closed at `07591c`. The saved `staged-call-diagnostics-terminal-bodies-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `f3558384cf298fe7fd4d535eaafe4cd535435adef662b8e24db3b3cf80e013ba`. The checkpoint uses the original sixteen closed validation receipts; metadata finalization does not repeat their kernel runs.

## 2026-10-11: Staged call dispatch and terminal closures at `6c165e33`

`staged-call-dispatch-and-terminal-closures` is committed and normally verified at `6c165e33`. The twelve proof Sources contribute 106 complete module-owned declarations and 42 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19434 to 19540: 106 additions, no overlaps and no removals.

| Boundary | Selected proof route | Remaining obligation |
| --- | --- | --- |
| Receiving fault relation | Same actual table forwards semantic assignment/arity and first-gate stage representation with exact scope/call/token. | Broader semantic/export errors and authentic compiler occurrence coverage. |
| First-gate rejection | Strict callee preservation constructs the actual selected boundary and reached stage post; reflection uses the rejected prefix. | Construct the shared numeric child hypothesis and complete scoped static factories. |
| Ordered argument fault | Actual first-gate success and concrete strict argument fold retain the reached dependent caller state and both fault tags. | Close ordered-expression induction across the remaining Source forms. |
| Native parent fault dispatch | Whole-parent inversion uses its callee/argument prefix once; all fault outcomes retain the actual final state. | The right application suffix still needs its actual application producer. |
| Second-gate arity | Original row and real physical count produce semantic arity after arguments and literal receiving representation. | Supply authentic per-payload named provenance and complete accepted application dispatch. |
| Application suffix | Accepted second gate and pure payload normalization preserve the argument store and strict native child. | Derive full application meaning for each actual payload branch. |
| Builtin rows | Actual callee admission, BuiltinAt and equal count yield literal Source/native rows and ordered scalar ValuesRep. | Compose an authentic retained callee prefix with the builtin whole-parent proof in a later unit. |
| Terminal factory/body | Retained NativeLambda recipe constructs the terminal receipt; whole Source-body inversion gives the actual used child. | Original typing, required SourceView direction, child certificates and supported terminal shape remain explicit. |
| Closure invocation/post | Real parameter entry and strict body post return through the saved physical caller once; context support follows runtime validity. | Construct strict body hypotheses and authentic selected child Scope/source identity for every closure. |

Successful values retain Source admission at the actual reached state. Faults retain stable rows, the exact semantic/stage tag and the same reached state/relation; no diagnostic decoding supplies a failing Scope. Original codebook metadata and substituted call metadata remain distinct. Administrative frame, map/world extension, heap metadata and transient callee/argument effects stay inside the same causal result. This unit adds proof Sources and registration imports. Core syntax/runtime and public execution definitions retain their existing behavior.

The registered build passes 5786 jobs. The independent selected dependency BEFORE contains 2250 modules; the compiled native environment contains 2262. The complete normal module snapshot changes from 5707 to 5719 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint uses these original sixteen closed receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `0799ac`; code commit `6c165e334b61a044e480e96ea9da7d414894817c` closed at `215010`. The saved `staged-call-dispatch-and-terminal-closures-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `dc631c0c098aee0e8a9fec163b3141d0142c3cb429aa78878f272d15a57c1ee3`. The corrected summary distinguishes the selected BEFORE environment of 2250 modules from the complete pre-install snapshot of 5707 module rows.

Retained-callee argument prefixes (258), builtin whole-parent reflection/preservation (134/154), terminal body typing (96), metadata-body bounds (131), parameter-admission and concrete body-join drafts, and retained-callee fault/builtin dispatch drafts (127/216) are outside this twelve-Source checkpoint.

The numeric staged expression/argument/application/body induction, authentic static factories for complete compiler alternatives, general call/body dispatch and remaining recursive Source grammar remain unfinished. Specialization, evidence and comptime composition, general failure/export-error correspondence and the final public all-pass theorem are open. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure semantic completion.

## 2026-10-11: Staged parent and terminal lambda producer audit at `6844f7b0`

`staged-parent-and-terminal-lambda-producers` is committed and normally verified at `6844f7b0`. The twelve proof Sources contribute 74 complete module-owned declarations and 26 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19540 to 19614: 74 additions, no overlaps and no removals. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews.

The registered build passes 5798 jobs. The independent selected dependency BEFORE contains 2218 modules; the compiled native environment contains 2230. The complete normal module snapshot changes from 5719 to 5731 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint will use those original sixteen receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `cc2cfe`; code commit `6844f7b0f788069d858f42a29343c7c5900829ba` closed at `5cea3d`. The saved `staged-parent-and-terminal-lambda-producers-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `bf9f5a5635e9876005265366485f4f31bad0d297b3478785aa453b778561c456`. The selected BEFORE environment of 2218 modules is separate from the complete pre-install snapshot of 5719 module rows.

The strict child hypotheses are induction assumptions for the actual executed child: its Source trace grade is smaller for preservation, or its native evaluation grade is smaller for reflection. The shared numeric induction must still construct these hypotheses; the static compiler receipts do not contain a completed execution law.

| Boundary | Retained authority and constructive proof | Remaining obligation |
| --- | --- | --- |
| Callee/argument transport | Actual callee PostAdmission and raw typing survive the original strict ordered fold at the reached state. | Construct the common smaller-child induction hypotheses for all supported occurrences. |
| Builtin signature and parent | Actual BuiltinAt and physical count identify ordered scalar rows; the original primitive, suffix and binds construct preservation/reflection. | Complete numeric/compiler coverage and user/named dispatch. |
| Dispatch classification | Actual scoped row selects faults, builtin application, arity rejection or the retained user prefix without rerunning children. | The user payload/body branch and an integrated preservation dispatcher. |
| Parameter state | Authentic allocation and frames update the real row histories and construct Source entry admission. | Genuine captures, Code/history, caller rows and raw typed arguments. |
| Terminal Source and scope | Original body typing/metadata recover the used child; Code/registry derive its Source scope. | The actual supported terminal compiler receipt and child certificate. |
| Body/application result | Strict expression preservation/reflection feeds the real terminal footer and saved-caller restoration; full reached posts are retained. | Construct the shared numeric expression/body induction; cover nonterminal bodies and general callable alternatives. |

Semantic and stage failures retain distinct tags, scopes and actual receiving interpretations. No packed native type establishes physical arity, no token establishes arbitrary scope, and no completed body or application meaning is a static premise. The scope is twelve proof Sources and twelve registration imports; runtime/Core and public execution definitions are outside this proof change.

| Validation item | Actual result |
| --- | --- |
| Selected proof scope / interfaces | Twelve Sources / 26 public interfaces. |
| Complete owned declarations / literal audit | 74; complete private/normal TYPE/AXIOMS and API logs agree literally. |
| Independent selected BEFORE / compiled native environment | 2218 / 2230 modules. |
| Native and normal strict Source checks | Twelve empty logs in each phase. |
| Cumulative census | 19540 → 19614 (+74); no overlaps or removals. |
| Registered build | 5798 jobs passed. |
| Complete normal module snapshot | 5719 → 5731 rows; twelve new regular Source/BOTH triples. |
| Existing object delta / dependency cone / actual rebuilds | Only `CoreLowering` / 14 / 14. |
| Protected artifacts / original normal receipts | All 4985 unchanged / sixteen CLOSED0 receipts. |
| Code commit | `6844f7b0f788069d858f42a29343c7c5900829ba`; twelve Sources and registration. |

The shared numeric induction for expressions and function bodies, general user and named application dispatch, full statement grammar and authentic compiler occurrence coverage remain open. Specialization, evidence and comptime composition, general failures/export errors and the final public all-pass theorem are unfinished. Finite proofs for literals and grouping, the separate closure argument-typing producer and the whole builtin preservation dispatcher are outside this checkpoint. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.

## 2026-10-11: Staged call parent dispatch audit; normally verified at `910e3e1d`

`staged-call-parent-dispatch-bounds` is committed and normally verified at `910e3e1d`. Its seven proof Sources have 117 complete module-owned declarations and 19 selected interfaces. Every native and normal strict Source log is empty. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete 19-interface API logs are byte-identical. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews; the tooling has independent Root and Entry reviews.

The cumulative census is 19730 from 19614: 116 additions, one prior overlap and no removals. The overlapping generated helper, `ContextualCellOrigins.functions.congr_simp`, is literally unchanged. Build 5805 passes. The selected dependency BEFORE contains 2228 modules and the compiled native environment 2235; the complete normal snapshot changes from 5731 to 5738 rows. Seven new Source/olean/ilean triples are installed. Only the existing `CoreLowering` object pair changes, within the nine-module dependency cone and nine actual rebuilds. All 4985 protected artifacts remain unchanged.

The eleven original normal validation receipts are closed with exit code zero. Normal validation closed at `ce446f`; code commit `910e3e1d9f18c1fde867b7d56ef3321b5a0dd943` closed at `83f21b`. The saved `staged-call-parent-dispatch-bounds-checks.json` has SHA-256 `9360372c1f3e5abb9ab873e023f542f20bcfd58b301b46851ee5d9e7a108df4c`. Metadata finalization reuses the original eleven closed validation receipts without repeating their kernel checks.

| Proof boundary | Retained authority and result | Unfinished obligation |
| --- | --- | --- |
| Closure arguments | Actual positive callee, original raw argument typing, physical Source bindings and represented contextual rows. | Compiler occurrence/typing factories and the shared child induction. |
| Terminal application | Genuine Code/support and actual selected scope, independent Source/native grades, body result and exact saved-caller restoration. | Supported terminal selection and smaller executed expression/body hypotheses; general bodies remain open. |
| Builtin/user classification | Actual codebook row and physical count; original primitive parent or unchanged user application prefix with reached Admission. | General named/global application assembly. |
| Source prefix failure | Actual scoped first-gate rejection or semantic failure at its reached callee/argument post. | Authentic receiver authority and exact original SourceView/CallView; no whole-source equality is inferred. |
| Receiving arity rejection | Actual second-gate mismatch, selected receiving row and same argument state, heap/store and caller PostAdmission. | Shared numeric caller family and complete supported occurrence coverage. |

The strict child hypotheses describe the actual executed child: preservation uses a smaller Source trace grade, and reflection uses a smaller native evaluation grade. The shared numeric induction must still construct these hypotheses. Source and native grades are independent, and static compiler receipts retain authority rather than a completed execution law.

No packed native type establishes physical arity, and no erased token establishes an arbitrary Source scope. First-guard stage rejection and after-arguments semantic arity failure retain their distinct tags and Source rules. The selected change is seven proof Sources and seven registration imports; no runtime/Core or public operational definition is changed by this proof package.

The whole indirect parent reflection and preservation dispatch proofs, and terminal named invocation reflection, have saved author passes and genuine peer reviews in W. They are outside the seven registration targets, and their normal integration remains open. The whole parent proofs retain the actual named/global application prefix for further composition. Named invocation constructs the real parameter receipt, reflects the supported terminal body at its selected scope, and restores the caller; joining original raw global arguments, named physical arity, the outer indirect parent and the preservation direction remain separate obligations.

| Validation item | Actual result |
| --- | --- |
| Selected proof scope / interfaces | Seven Sources / 19 interfaces; all seven have genuine Source2. |
| Complete owned declarations / literal audit | 117; complete private/normal TYPE/AXIOMS blocks agree literally and complete API logs are byte-identical. |
| Native and normal strict Source checks | Seven empty logs in each phase. |
| Selected dependency BEFORE / compiled native environment | 2228 / 2235 modules. |
| Cumulative census | 19614 → 19730 (+116); one literally unchanged generated-helper overlap; no removals. |
| Registered build | 5805 jobs passed. |
| Complete normal module snapshot | 5731 → 5738 rows; seven new regular Source/BOTH triples. |
| Existing object delta / dependency cone / actual rebuilds | Only `CoreLowering` / 9 / 9. |
| Protected artifacts / original normal receipts | All 4985 unchanged / eleven CLOSED0 receipts. |
| Code commit | `910e3e1d9f18c1fde867b7d56ef3321b5a0dd943`; seven proof Sources and registration. |

The shared numeric expression/function-body induction, general named application, full statement grammar and authentic compiler occurrence coverage remain open. Specialization, evidence and comptime composition, general failures/export errors and the final public theorem across all passes are unfinished. Finite literal, group and product-tree proofs remain a separate reviewed W unit. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.


## 2026-10-11: Finite staged expressions and named call parents; normally verified in two code commits

`staged-finite-expressions-and-named-call-parents` is committed and normally verified in two logical code groups. The finite expression commit `5a5bdeffec4008cb4d6e972224b90b8a2df048db` contains four proof Sources, 102 module-owned declarations and 32 selected interfaces. The whole-call and named-call commit `ef75b2c3b86a2e2bc140ea274ae9ff55d86c99d2` contains seven Sources, 89 declarations and 18 interfaces. Together they add eleven Sources with 191 complete owned declarations and 50 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native strict logs and all eleven normal strict logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 191 declarations. The complete 50-interface API logs are byte-identical: 112327 bytes, SHA-256 `df758c72f09c97d7e7f17fee86fd94d67595c6adf117e6103b2bd158aa7f4058`. The independent selected BEFORE contains 2240 modules and the compiled native environment 2251.

The cumulative census grows from 19730 to 19921: 191 additions, no prior overlaps and no removals. Build 5816 passes. The complete normal snapshot grows from 5738 to 5749 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The original package tooling has independent Root and Entry reviews. The separate snapshot-copy successor was authored by Root and independently reviewed by Entry and Formal. Both code commits closed with exit code zero at actual receipt `0cb4aa`; normal validation records fifteen original CLOSED0 receipts. Its complete checks have SHA-256 `d48582c7b3291b9093a30b010b37f4805312f1b812e93c272b08ec96ed21d8cc`. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

| Proof boundary | Retained authority | Unfinished obligation |
| --- | --- | --- |
| Finite expression extraction | Same accepted compiler Tree, LiteralSites, Source lookup/type identities and exact emitted children. | Every compiler alternative and the general numeric E/F family. |
| Transparent grouping | Structural child receipt; reflection uses the same native grade. | No blanket strict-native-grade descent is assumed for transparent heads. |
| Ordered pairs | Actual left/right native bind children and intermediate caller state. | Independent Source/native grades and real strict child hypotheses at evaluated binds. |
| Whole indirect calls | Actual scoped gates, receiving fault rows and exact caller post for completed branches. | The retained global prefix still needs its independent named argument/arity/application join. |
| Terminal named invocation | Same Header, dictionary, parameter receipt, selected body scope and restored returned pool. | General named bodies, invocation preservation and outer parent composition. |

The finite expression fold constructs preservation and reflection for literals, transparent grouping and ordered two-element products from the actual compiler Tree and LiteralSites receipts. It retains original Source typing, the represented result, both staged and semantic failure interpretations, and the reached heap, store and caller post. Preservation descends on the independent Source trace grade. Reflection descends structurally through a transparent group at the same native evaluation grade; only children of actual evaluated pair binds require a strictly smaller native grade. The finite fold constructs its child meanings internally.

The whole indirect parent dispatch composes real callee, first-gate, ordered argument and physical-arity failure branches with accepted builtin and supported terminal closure application. Completed cases keep the exact restored caller PostAdmission at the returned pool. The named/global alternative retains the literal application prefix and reached Admission for an independent named consumer. First-gate stage failure and after-arguments semantic arity failure retain their distinct Source rules, tags and scopes.

The five named-call proofs retain the positive payload, original Header, selected record, Source scope, dictionary and actual parameter/body state. Supported terminal body preservation and reflection use the genuine compiled child with a separate strict child hypothesis. Invocation reflection constructs the parameter receipt, reflects the supported body once, and restores the saved caller in the actual returned pool. Its complete caller post refers to that same execution.

| Validation item | Actual result |
| --- | --- |
| Selected proof scope / interfaces | Eleven Sources / 50 interfaces; all eleven have two genuine nonauthor Source reviews. |
| Logical code groups | Finite expressions: four Sources / 102 declarations / 32 interfaces; whole and named calls: seven Sources / 89 declarations / 18 interfaces. |
| Complete owned declarations / literal audit | 191; complete private/normal TYPE/AXIOMS agreement and byte-identical complete API logs. |
| Native and normal strict Source checks | Eleven empty logs in each phase. |
| Independent selected BEFORE / compiled native environment | 2240 / 2251 modules. |
| Cumulative census | 19730 → 19921 (+191); no overlaps or removals. |
| Registered build | 5816 jobs passed. |
| Complete normal module snapshot | 5738 → 5749 rows; eleven new regular Source/BOTH triples. |
| Existing object delta / dependency cone / actual rebuilds | Only `CoreLowering` / 13 / 13. |
| Protected artifacts / original normal receipts | All 4985 unchanged / fifteen CLOSED0 receipts. |
| Finite-expression code commit | `5a5bdeffec4008cb4d6e972224b90b8a2df048db`; four Sources and their registration. |
| Whole-and-named-call code commit | `ef75b2c3b86a2e2bc140ea274ae9ff55d86c99d2`; seven Sources and their registration. |

The shared numeric expression/function-body induction still has to provide strict hypotheses for the actual executed children; Source and native grades remain independent. Joining the original raw global argument list to the Header, connecting the independent named physical-arity receipt, composing the outer indirect parent and proving named invocation preservation remain open. General bodies, the full expression/statement grammar and authentic compiler occurrence and receiving-diagnostic coverage are unfinished. Specialization, evidence and comptime composition, general failures/export errors and the final public theorem across all passes remain open.

The separate real-cell read proof and finite compiler-factory proof remain reviewed work in the private proof area, outside these eleven registration targets. The first objective remains 100%; the second stays about 70%, and the equally weighted overall estimate stays about 85%. These estimates describe completed work, not declaration counts or remaining time.

## 2026-10-11: Finite reads and named body composition; normally verified in two code commits

`staged-finite-reads-and-named-body-composition` is committed and normally verified in two logical code groups. The finite read/body commit `6d4fcbd855b387845dba4ca511ea66d6dde0c020` contains six proof Sources, 64 module-owned declarations and fourteen selected interfaces. The closure/named commit `ed30cd3be8a2f9b11e5ff21387a19f8fcfdbde99` contains five Sources, 56 declarations and twenty-two interfaces. Together they add eleven Sources with 120 complete owned declarations and 36 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native and eleven normal strict Source logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 120 declarations. The complete 36-interface API logs are byte-identical: 108225 bytes, SHA-256 `79a0c159998685d6e97f3c1c1302f389d6ffcba81df469023faf1e62582b2e2c`. The independent selected BEFORE contains 2274 modules and the compiled native environment 2285.

The cumulative census grows from 19921 to 20041: 120 additions, no prior overlaps and no removals. Build 5827 passes. The complete normal snapshot grows from 5749 to 5760 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The selected tooling has independent Root and Entry reviews; the inherited snapshot-copy change retains its genuine Entry and Formal reviews. Both code commits and all fifteen original normal validation receipts are closed with exit code zero. The complete checks have SHA-256 `ce9c5751d088be73b668e9f76a8f64ce7f2c126d873dc8ae03102f7ccf498ed6`. Metadata finalization reuses the original fifteen closed normal validation receipts without repeating their kernel checks.

| Proof boundary | Retained authority | Remaining obligation |
| --- | --- | --- |
| Real-cell read | Certified lowered-read occurrence, actual represented cell, raw typing and exact lazy mapping write. | Generalized local alternatives and wider grammar remain outside the finite fold. |
| Read diagnostic | Actual Header/diagnostic receipt/receiving issuer, original binder/span/token and decoder priority. | No decoded diagnostic is treated as evidence that a Source fault occurred. |
| Finite tree | Same accepted Tree.WithLiterals and LiteralSites, actual emitted child and intermediate caller state for each ordered pair. | Transparent group reflection uses structural descent at the same native grade. |
| Finite named body | Original Header and terminal receipt, actual child typing and selected parameter/body state. | Authentic ledger/runtime/coverage, ordinary metadata and finite syntax remain explicit. |
| Named rows and application | Original selected node/metadata, actual ordered Source values, independent named physical count and literal carrier. | Finite invocation specialization and outer global composition remain separate work. |

A completed finite body keeps the actual parameter entry and selected body scope, and carries the returned heap, store, map, world, relation and PostAdmission. Completed applications retain full PostAdmission at their actual returned caller state. Static factories carry compiler authority and exact child membership; they contain no completed execution law. First-gate stage failure and semantic read/arity failure keep their distinct Source tags and scopes. Source and native grades remain independent.

The eleven isolated author results and twenty-two genuine nonauthor Source reviews remain immutable evidence for the selected texts. Native and normal validation use those exact Sources and the complete literal declaration/API audits. The separate finite invocation/application design remains uncompiled and excluded from the eleven targets. The saved finalization procedure consumes the original closed normal receipts; these proof results do not establish full compiler correctness.

| Validation item | Actual result |
| --- | --- |
| Selected scope / interfaces | Eleven Sources / 36 interfaces; all eleven have two genuine nonauthor Source reviews. |
| Logical code groups | Finite read/body: six Sources / 64 declarations / 14 interfaces; closure/named: five Sources / 56 declarations / 22 interfaces. |
| Complete literal audit | 120 owned declarations; exact private/normal TYPE/AXIOMS and complete API bytes. |
| Native and normal strict Source checks | Eleven empty logs in each phase. |
| Independent selected BEFORE / compiled native environment | 2274 / 2285 modules. |
| Cumulative census | 19921 → 20041 (+120); no overlaps or removals. |
| Registered build / normal module snapshot | 5827 jobs passed / 5749 → 5760 rows; eleven regular new Source/BOTH triples. |
| Existing object delta / dependency cone / actual rebuilds | Only `CoreLowering` / 13 / 13. |
| Protected artifacts / original normal receipts | All 4985 unchanged / fifteen CLOSED0 receipts. |

The next finite named invocation/application proof will retain the substantive parameter-entry and restoration proofs and replace their body call with the finite named body producer. It must preserve the actual Source-selected child in preservation and the authenticated Header/descriptor scope in reflection, with real ledger, runtime, coverage, ordinary-metadata and finite-syntax premises. The shared numeric expression/function-body family, outer named/global joins, full compiler and Source grammar, general bodies and complete receiving-diagnostic coverage remain open. Specialization, evidence and comptime composition, general failure/export-error correspondence and the public theorem across all passes are unfinished. Estimates remain 100% for runtime unification, about 70% for the second objective and about 85% overall.

## 2026-10-11: Finite call body and global join boundaries; normal verification complete

The selected `staged-finite-call-bodies-and-global-joins` work contains nine proof Sources and 37 selected interfaces. The three generic parent/global joins expose seven interfaces; the two static closure-child producers expose twelve; the four finite call/body proofs expose eighteen. Each selected Source has an isolated author pass and two genuine nonauthor Source reviews. Normal verification passes for all nine Sources, 177 module-owned declarations and 37 selected interfaces. The generic joins contribute 68 declarations, the static closure-child producers 27, and the finite call/body proofs 82. The three code commits are `c37620a6`, `b568df64` and `ef72f57e`.

Preservation constructs native execution from an actual Source derivation. Reflection reconstructs a Source derivation from native completion with an independent Source grade. Both retain the actual reached heap, store, map, world, relation and returned pool. Completed application and parent results retain full caller PostAdmission, including the original tag and scope of nested stage failures.

| Proof boundary | Retained authority | Remaining obligation |
| --- | --- | --- |
| Finite named invocation | Actual Header, prepared diagnostic, receiving issuer, selected parameter entry and body scope, returned pool and saved caller. | Ordinary metadata, finite syntax, ledger/runtime validity and coverage for each actual selected child remain authentic inputs. |
| Finite named parent/global | Original node/metadata, ordered Source arguments, represented native rows and the independently selected physical count. | Actual callee/argument prefixes and outer numeric recursion remain explicit. |
| Static closure child | Both original and compiler Source trees from the same accepted Code, terminal occurrence and exact used child. | Arbitrary certificate families are not identified with the finite family; no metadata typing equality is assumed. |
| Finite closure application | Fixed finite BodyWith, raw typed child at the real parameter context and actual Source-selected scope. | Genuine finite certificate transport, certified read-fault interpretation, registry and runtime authority remain explicit. |
| Generic whole-call join | Literal callee/argument/application suffixes, independent grades, cumulative effects and complete restored caller PostAdmission. | Strict child induction and authentic terminal factory coverage still have to be assembled into the shared family. |

Finite named invocation and application now call the finite named body producer directly at the actual parameter entry. Preservation retains every actual Source-selected body scope; reflection retains the authenticated Header/descriptor-selected scope. The proof runs the original parameter installation and body prefix once, uses the finite read/literal/group/pair body once, and restores the saved caller at the actual returned pool. It no longer takes an external child-expression meaning hypothesis or arbitrary certificate callback.

The finite named parent derives typed Source arguments and represented native parameters from the authentic ordered rows and independent physical-count receipt. Its accepted suffix uses that same finite application once. The finite global dispatcher recovers the real Header, dictionary, capture and Source frame from the positive named payload. It either runs the finite parent at the selected equal count or proves the actual Source semantic arity failure with the exact receiving diagnostic at the reached argument post. First-gate `Failure.stage` and second-gate semantic arity failure remain separate.

The finite closure body proof retains a fixed accepted BodyWith with both compiler-view and original-Source trees. Authentic frame typing and the selected Source scope provide the raw child type; the exact original child certificate feeds the finite evaluator. Its application proofs construct read/literal/group/pair child meaning internally and retain the restored caller post. Genuine finite-family compiler transport, terminal/read policy, certified read-fault interpretation, registry extension and runtime premises remain explicit.

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

The shared numeric expression/function-body family and general callee/argument recursion remain open. The finite named and closure application proofs do not yet instantiate every generic whole-call child hypothesis. Constructing the fixed finite closure support from every actual compiler path still needs genuine reachable certificate transport. Wider expression/statement grammar, general bodies, complete receiving-diagnostic coverage, specialization/evidence/comptime composition and the final public theorem across all passes are unfinished. Runtime unification remains 100%; the second objective remains about 70%, with an equally weighted overall estimate of about 85%. These are estimates of completed work, not declaration counts or remaining time.

## 2026-10-11: Finite closure dispatch and arbitrary tuple proof boundaries

`staged-finite-call-dispatch-and-tuple-folds` is normally verified in three code commits: `fb42f8c2` adds the finite closure parent, static transport and terminal packet (three modules, thirteen interfaces); `280557de` adds the arbitrary tuple fold and compiler issuer (two modules, six interfaces); `a48286e4` connects the whole-call and user dispatch branches (six modules, eight interfaces). The eleven modules expose 27 selected interfaces and 156 owned declarations. Each Source has two genuine nonauthor Source reviews.

All eleven fresh private and normal strict Source checks closed with empty output. Complete TYPE/AXIOMS and API audits passed, and the private and normal API logs are byte-identical (142486 bytes). The native import closure grew from 2319 to 2330 modules. The registered build completed 5847 jobs; normal Source/BOTH rows grew from 5769 to 5780. The only changed existing object was `CoreLowering`; all eleven new modules have regular objects, all thirteen modules in the reverse dependency cone were rebuilt, and 4985 protected artifacts stayed unchanged. The cumulative census grew from 20218 to 20374, with 156 additions, no overlap and no removals. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

| Boundary | Retained authority and limit |
| --- | --- |
| Finite closure body and packet | Same Association, accepted tree and parameter context; actual selected Source scope and certified read diagnostics remain inputs. No external child meaning is assumed. |
| Compiler-view transport | Genuine reachability, LocalView and Avoids; raw expression typing remains independent of metadata transport. |
| Arbitrary tuples | Actual ordered compiler vector and intermediate caller states; Source grades remain independent of native grades, with structural same-grade reflection for erased singleton packing. |
| Whole-call dispatch | Actual callee/argument/application suffix and receiving table; strict caller child hypotheses remain until the recursive static caller fold is implemented. |

| Validation item | Current state |
| --- | --- |
| Proof selection | Eleven integrated modules, 156 owned declarations and 27 selected interfaces. |
| Native checks and literal audit | Eleven empty strict checks; complete TYPE/AXIOMS and byte-identical private/normal API logs; import closure 2319 → 2330. |
| Normal validation and build | Fifteen closed validation receipts; 5847 build jobs; normal Source/BOTH rows 5769 → 5780; thirteen affected modules rebuilt; 4985 protected artifacts unchanged. |
| Census and code commits | 20218 → 20374 (+156, no overlap or removals); `fb42f8c2`, `280557de`, `a48286e4`. |

The next substantive cut is a recursive static caller certificate whose read/literal/group/tuple/call fold constructs those child hypotheses internally. The current tuple issuer admits groups only inside its older leaf grammar, not groups around a new arbitrary tuple or call. Finite closure transport and terminal bodies still use the narrower read/literal/group/binary-pair grammar. Authentic compiler policy, raw typing, selected Header or Association, registry/receiving diagnostics, runtime ledger and coverage remain inputs. Shared numeric expression/application/body induction, general recursive bodies, broader expression and statement grammar, and the final public all-pass theorem remain unfinished. Runtime unification stays 100%; the second objective stays about 70%, and the equally weighted overall estimate stays about 85%.

## 2026-10-11: Recursive caller static receipts and structural proof boundaries; normal verification complete

The selected `staged-recursive-callers-and-static-receipts` unit is normally verified in `e8607d82` and `abe72325`: six proof Sources, 198 owned declarations and 37 selected interfaces. Each Source has an isolated strict author pass and two independent nonauthor Source reviews.

All six native and normal strict Source checks have empty logs. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete API logs are byte-identical (89589 bytes, SHA-256 `05cacd2519262ad3ad8a8762e6110fde41596f12f27aa90b3638ffdfdfe4eafb`). The selected native environment grows from 2324 to 2330 modules. Build 5853 passes; the normal Source/BOTH snapshot grows from 5780 to 5786 rows. The cumulative census grows from 20374 to 20572: 198 additions, no overlap and no removals. All 8 modules in the affected dependency cone are rebuilt and all 4985 protected artifacts remain unchanged.

Metadata finalization reuses the original ten closed validation receipts without repeating their kernel checks.


| Boundary | Evidence retained by the proof |
| --- | --- |
| Original call metadata and raw types | Compatible Source read, actual original indirect-call node, original callee typing and ordered argument types, before constructing the child tree. |
| Static recursive certificate | Actual compiler entries, callee head membership, ordered argument vector and recursive certificates for each literal entry, including duplicates. |
| Structural child laws | Preservation/reflection quantified over grades and reached states; same-grade group and singleton reflection descend through the actual certificate. |
| Call authority | `CallsReady` for actual reachable receipts of the exact issued root; actual prepared/Source/sidecar/guard/caller ports remain required. |
| Called bodies | Genuine finite named/Association body packets with their exact context, read diagnostics, registry authority and coverage; general recursive body meaning is still open. |

The compiler issuer starts from the actual accepted lowering action and original Source typing. It recovers the original indirect-call node, raw callee type and ordered argument types before building the child certificate. The certificate retains groups, tuples and indirect calls recursively, including groups around new tuple or call nodes. Argument entries keep their original order and repeated identifiers.

Structural induction on that certificate proves both preservation and reflection at every actual reached state. Child execution hypotheses are constructed internally. Group reflection and erased singleton tuple packing can use the same native grade; induction follows the child certificate rather than assuming a smaller execution grade. An indirect call uses the actual callee entry and ordered argument tree, then the existing finite whole-call proof once. Results retain the reached heap, store, map and world, exact staged fault scope, returned pool, caller relation and PostAdmission. Source and native grades remain independent.

The compiler-facing wrapper constructs its root certificate internally. Its `CallsReady` premise refers only to call receipts reachable from that exact generated root. Actual preparation, Source view, sidecar, guard frame, selected Header or Association, receiver, registry extension, diagnostic interpretation, ledger and coverage remain static or runtime premises. Called bodies still use the existing finite read/literal/group/binary-pair family. No public child execution or arbitrary body meaning callback is supplied.

General recursive called bodies, the shared numeric expression/application/body family, other expression and statement forms, and specialization/evidence/comptime composition remain unfinished. The final public theorem across all compiler passes is incomplete. Estimates remain 100% for runtime unification, about 70% for meaning preservation and about 85% overall.

| Validation item | State |
| --- | --- |
| Selected proof scope | Six integrated Sources, 198 owned declarations and 37 selected interfaces. |
| Native and normal verification | Six empty strict checks in each phase; complete literal private/normal TYPE/AXIOMS and byte-exact API agreement; selected native environment 2324 → 2330. |
| Build and cumulative census | 5853 jobs; 5780 → 5786 normal rows; 20374 → 20572 (+198, no overlap or removals). |
| Code commits | `e8607d82` and `abe72325`. |

The saved lexical closure records the registered CoreLowering umbrella and these six new targets. Its import relation is separate from the native environment and declaration ownership measured during normal validation.

The static Source/compiler receipt group (`e8607d82`) contains two Sources, 125 declarations and 25 selected interfaces. The semantic head/fold/compiler composition group (`abe72325`) contains four Sources, 73 declarations and twelve interfaces. Interface and declaration counts do not measure proof completion.

## 2026-10-11: Selected terminal body recursion and original Source authority; normal verification complete

The selected `staged-selected-callers-and-recursive-body-bounds` unit is normally verified in `7db7dd2c`, `dda78f9c`, `31549a17`: sixteen proof Sources, 376 owned declarations and 53 selected interfaces. Each Source has an isolated strict author pass and two independent nonauthor Source reviews, excluding contributing repair authors.

All sixteen native and normal strict Source checks have empty logs. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete API logs are byte-identical (215570 bytes, SHA-256 `40020d9c5a18129f8d398856d30533f3fbbb94a7d853a9d9bc783fc51eb820e9`). The selected native environment grows from 2317 to 2333 modules. Build 5869 passes; the normal Source/BOTH snapshot grows from 5786 to 5802 rows. The cumulative census grows from 20572 to 20948: 376 additions, no overlap and no removals. All 18 modules in the affected dependency cone are rebuilt and all 4985 protected artifacts remain unchanged.

Metadata finalization reuses the original twenty closed validation receipts without repeating their kernel checks.

| Boundary | Retained evidence |
| --- | --- |
| Terminal selection | One actual Header/Association packet and its original child, scope and lowering. |
| Call behavior | Ordered callee/argument traces, physical arity, exact nested staged fault identity, returned pool and restored caller post. |
| Structural caller induction | The actual issued recursive certificate; duplicate entries and same-grade group/singleton branches. |
| Numeric body induction | Genuine selected original RootAt and strict smaller semantic budgets; body child laws constructed internally. |
| Original Source authority | Raw typing and context, real accepted compiler action, paired-policy view transport and actual selected scope. |
| Validation | Sixteen native and normal strict checks, complete literal audits and twenty closed normal validation receipts. |

The saved lexical closure has 2780 canonical Source rows from the registered umbrella and sixteen targets. That import relation is separate from the native environment and physical module-owned declarations, measured independently during integration.

The call chain selects one authentic terminal packet for the actual named Header or contextual closure Association. Its certificate is narrowed to that packet's original expression, scope and lowered child. Closure and named dispatch retain the real argument order, physical arity, staged rejection and selected scope. The accepted application keeps its actual returned pool and restores the saved caller, including caller relation and PostAdmission.

The selected caller fold constructs callee and argument preservation/reflection internally from the actual recursive certificate. Group reflection and erased singleton tuple packing may keep the same native grade; their induction follows the child certificate. Ordered argument entries retain repeated identifiers and use the actual intermediate state. Numeric strong induction then constructs meaning for supported selected terminal bodies at strictly smaller semantic budgets. The caller-from-bodies adapter consumes that constructed body family. These endpoints require no external child execution or body meaning callback. Source and native grades remain independent.

Static body support retains the original Source root, raw context, actual Header or Association body context and every genuinely selected child scope. The compiler support issues a certificate from the actual accepted original action and indexes call readiness by that exact proof. The compiler-view transport proves accepted lowering on the original Source from paired policies, reached unedited metadata and the real compiler action. Compiler callbacks, reason functions, original typing/declarations, receiver, registry extension, diagnostics, runtime ledger and coverage remain explicit authority inputs.

This closes the supported selected terminal body/caller recursion. Constructing these authentic roots and authority packets for every compiler path remains unfinished. Wider expression and statement grammar, unrestricted function bodies, complete receiving-diagnostic coverage, specialization/evidence/comptime composition and the final public theorem across all passes are still open. Runtime unification remains 100%; meaning preservation remains about 70%, with an equally weighted overall estimate of about 85%. These estimates describe completed work, not interface counts or remaining time.
