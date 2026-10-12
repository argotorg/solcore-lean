# Core runtime unification and semantic preservation

Status: The first goal (runtime unification on Core) is complete. Implementation and proofs for the second goal (preserving meaning across the full compilation pipeline) are ongoing.

Created: 2026-09-30. Updated: 2026-10-13.

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

## Lexical named bodies and actual captured locals (2026-10-13)

Commits `8537c3c2` and `a0cd0dba` connect straight-line named bodies with local declarations to the recursive semantic family and public execution. The supported statements are initialized and uninitialized monomorphic `let`, initializer failure, discarded expressions, return and Unit fallthrough. The Source context may grow during the body. The proof retains the actual allocated cells and restores the native caller frame, including the complete heap, function pool and returned History.

Read conditions now cover expressions reachable from the selected body. Unrelated reads in the original source table no longer require the same lexical scope. Compiler receipts construct these conditions from the original metadata and actual reached contexts.

Commit `a20e0891` supplies a closed public example: `make(seed)` initializes `local` from `seed` and returns a closure reading `local`. Actual compilation and `make(10)` derive the local allocation, its capture in the closure environment and the cell containing Word `10`. Two later direct calls use the successive returned sessions and prove Source results `10 / 10`, with reusable histories. The fixture supplies no body meaning or input representation assumption.

An initial failed public execution can also seed a History at its actual reached state. The generic theorem derives final heap typing from Source fault preservation. A closed failure-then-continuation example and lexical declarations inside closure bodies are the next integration work.

Validation: full build (6108 jobs), all registered tests and kernel policy pass. Twelve production endpoints and three new fixture endpoints were audited; each uses only `propext`, `Classical.choice` and `Quot.sound`. Core instructions and runtime behavior are unchanged. General imperative bodies, general forward public result export, constructor/mapping output selection, suspended/export-error continuations, model changes and final composition across all compiler passes remain open.

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

## Packed closure arguments through actual public execution (2026-10-13)

Commit `ac3a55b3` connects direct closure calls with packed arguments to independent Source applications and returned histories. The registered `SourceCoreCapturedPackedPublicExecution` fixture compiles `make(seed: Word)`, whose result is `lam(x: Word) { return seed; }`, then performs `make(10)`, `invokePacked(handle, 99)` and `invokePacked(handle, 123)`. It proves the exact Source argument lists `[99]` and `[123]`, results `10` and `10`, and continuity of the actual sessions and captured heap.

The genuine lambda parameter context now comes from Source binder ownership and the original compiler receipt. Packed application uses the selected callable's real parameter count, preserving the distinction between no arguments and one Unit argument. The public wrapper derives Source input meaning from History, the structural input description and the actual encoder. Scalar/handle/product trees derive unchanged metadata; the resumption wrapper also admits metadata-bearing inputs with the genuine encoder-to-receiver extension.

The selected handle's raw signature and the Source signature need only agree after runtime normalization. Nested product export may erase annotations on function leaves. The proof retains both raw signatures and derives their compatibility from actual handle resolution. Exact raw equality is used only where an actual whole-function export guarantees it.

Validation: strict Lean, full build (6054 jobs), all registered tests, kernel policy and independent reviews pass. Eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Native preservation also derives sufficient execution fuel at the original packed checkpoint. Direct named/builtin semantic dispatch, direct failure continuation, new output collection, forward public export/fuel composition and the broader compiler theorem remain open. Estimates remain unchanged. Earlier dated sections retain their checkpoint-specific scope.

## Direct public calls preserve distinct captures (2026-10-13)

Commit `dbfcaf47` connects direct `invokePacked(handle, unit)` calls to independent Source applications and the actual returned histories. The registered `SourceCoreCapturedDirectPublicExecution` fixture performs `make(10)`, `make(20)`, direct invocation of the first handle, `make(30)`, direct invocation of the second handle, and direct invocation of the first handle again. It proves Word results `10`, `20` and `10`, using the exact previous session and Source heap at every step.

The native startup receipt retains the actual selected callable, descriptor gate, packed input, captured payload, store and metadata. Existing recursive body proofs construct the application meaning. Successful export preserves earlier handles through native slot extension and the corresponding Source heap extension. The fixture derives each closure and its raw handle type from its original factory execution and export.

Validation: strict Lean, full build (6042 jobs), all registered tests, kernel policy and independent reviews pass. All eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

This completed public connection covers successful calls to zero-parameter closures in the supported static body family. Direct calls with arguments, direct failure/history continuations, output collection from direct calls and the forward public fuel theorem remain open, alongside broader body coverage and the final compiler theorem. Estimates remain unchanged.

## Named body support across actual scope selections (2026-10-13)

The named terminal connection now derives its canonical sidecar from the actual compiler hook and its Source origin from the prepared specialization. Shared scope coherence proves the selected guard frame for both named and anonymous selections, including different specialization keys. The connection no longer requires a lambda-free body or a unique specialization key per Source owner. It retains the existing Source typing, metadata, policy and supported body grammar requirements.

The six-call captured-closure proof uses this general connection. Its obsolete owner-key runtime check has been removed. Full build (6035 jobs), all registered tests, kernel policy and a four-endpoint axiom audit pass. The audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`. Direct public `invokePacked` meaning preservation remains in progress; estimates are unchanged.

## Current Implementation Status

| Item | Status |
| --- | --- |
| Removal of direct runtime evaluation | Completed in `a3168382` (2026-10-01). The public SourceCompiler uses a shared Core artifact, Value, Session, and Checkpoint. |
| Preservation of meaning across the full compilation pipeline | Ongoing. The estimate based on work completed is about 70%. The final theorem connecting general function values, call bodies, and all passes to the public entry point is incomplete. |
| Latest verified implementation | `a20e0891`, following `8537c3c2` and `a0cd0dba`: lexical named bodies reach public execution; an actual locally allocated capture is exported and reused with exact Source results and continuous histories. |
| Latest completed verification | Strict Lean, full build (6108 jobs), all registered tests and kernel policy pass. Production review and fifteen endpoint audits pass with only the standard three axioms. |
| Working implementation | Supported successful and failed public calls return reusable histories at their actual reached states. Named lexical bodies can allocate locals and form closures over them. Product outputs can add selected function leaves. |
| Latest proof scope | Actual captured closures, including a captured named-body local, are created, exported and called through later public executions with exact Word results and continuous histories. Static conditions come from authentic compiler receipts. The generic model and registries stay fixed. |
| Current implementation priority | Connect lexical closure bodies and closed failure continuations, then widen forward public preservation and actual compiler/body coverage. Imperative statements, suspended/export-error continuations, non-product output collection, model changes and all-pass composition remain open. |
| Next phase | Unify the comptime evaluator on Core and connect new source contract/storage/external-call support to ContractRuntime. |

### Returned captures reused through six public calls (2026-10-13)

Commit `c187ce09` adds `SourceCoreCapturedReusePublicExecution`, which instantiates the public proof for a checked two-function program: `make(seed)` returns a closure that reads `seed`, and `read(f)` calls that closure. The actual public sequence creates captures for Word `10` and `20`, reads the first, creates a third capture for `30`, reads the second, then reads the first again. `sequence_meaning` derives six independent Source applications, with read results exactly Word `10`, `20` and `10`.

Each call uses the preceding returned public session. Its Source trace starts at the preceding returned heap, and its History belongs to that same session, native store and owned caller. The first two exported handles are distinct. All earlier entries remain in order as the third export is appended and later reads retain the three-entry history. The fixture constructs both actual header packets, the complete inventory, named read support, captured-read closure family, Source typing and receiving diagnostics internally.

The input and returned metadata conditions are also derived from actual execution. `recover_start` recovers the selected function and original encoded arguments; `StartAt.function_registry` and `StartAt.returned_registry` preserve the real registry across a handle input and successful return. Word result inversion uses the same full semantic result and actual public decoder. The fixture supplies no argument representation or execution/body law.

This proves a public path for invoking returned closures through `read(f)`. The earlier direct `invokePacked` check remains separate runtime coverage. The closed proof covers this concrete captured-read program. Mutable assignment/match bodies, broader compiler alternatives, suspended/export-error continuations, non-product output collection, model/registry changes and the full public compiler theorem remain open. Work estimates stay at 100% / about 70% / about 85%.

Validation: strict Lean, the actual six-call runtime fixture, full build (6035 jobs), all registered tests and kernel policy pass. Independent review found no issues in the exact input, session, heap and history connections. All eleven audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

### Captured-read factory connected to public execution (2026-10-13)

Commit `4c2dbe39` adds `SourceCoreCapturedLambdaPublicExecution`, which checks and compiles `function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; }`, then calls it with Word `10`. Its `public_factory_meaning` theorem constructs an independent Source application and a singleton History for the handle and session returned by that actual public execution. The checker, compiler, initialization, Word input encoder, nonempty header inventory and run receipts supply all premises of the public seed theorem.

The closure family now handles the actual single captured-reference return. `SingleReadSequence.sequence` builds its static sequence conditions from the complete original occurrence table and the authentic compiler provenance of each Association. The named producer constructs the same-Code body receipt, parameter captures and Source declarations. Read faults refer to the actual diagnostic issuer and receiving table. No caller supplies an argument representation, Source typing judgment, child execution theorem or body execution law in the closed fixture.

The same model retains the original compiler policy, metadata equality on reached body expressions, ordinary lexical declarations and issued diagnostic tokens. The policy keeps the original outer compilation fuel even when a nested Site is compiled at a smaller budget. Actual producers derive these facts; generic adapters for arbitrary Sites retain the corresponding static receipts. `StartAt.simple_registry` derives the input metadata relation for the actual Word argument. Core language forms and public runtime behavior are unchanged.

The fixture also invokes the exported handle and checks that it returns Word `10`. That last invocation is runtime coverage; the formal conclusion currently covers factory execution, capture formation, export and returned History. Connecting a later public `read(f) { return f(); }` call to that History is in progress. Broader bodies, suspended/export-error continuations, non-product output collection, changes of model or registry, and the final theorem across all passes remain open.

Validation: strict Lean, full build (6019 jobs), all registered tests, kernel policy, the concrete public fixture and the six-endpoint axiom audit pass. The audited endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

Estimates remain 100% for runtime unification, about 70% for meaning preservation and about 85% overall. Earlier dated sections below retain their checkpoint-specific scope and validation.

### Closed compiler-to-public lambda factory (2026-10-12)

Commit `6b22e7b5` adds `SourceCoreClosedLambdaPublicExecution`, a registered test of `function make() returns (function() returns ()) { return lam() {}; }`. Its actual checker, compiler, initialization, input encoder and public execution receipts instantiate `public_run_succeeded_remembers`. The theorem concludes an independent Source application and a singleton History for the same handle and returned public session. Source typing, complete nonempty inventory, compiler body support, the closure family and initial metadata relation are constructed inside the fixture.

`OrdinarySequenceFor.empty` admits genuine empty unit bodies. The static producer derives the emitted footer from the same retained compiler callback. Its execution bounds use the heap and store after actual parameter allocation and retain caller restoration. `NamedEmptyLambdaFormation.of_terminal` derives the native child type from the accepted terminal compiler receipt and constructs the original empty-body certificate. `StartAt.empty_registry` derives metadata identity for an actual empty input vector.

This concrete case proves first formation, export and History construction. It does not yet call the returned closure or capture a variable. The diagnostic receiver comes from a separate genuine indexed execution of the same artifact, with its receiving metadata extension proved from actual initialization. The mutable assignment/match regression remains runtime coverage beyond the admitted static body grammar. Captured-body fixtures, broader body coverage, suspended/export-error continuations and final all-pass composition remain open.

Validation: strict Lean, full build (6008 jobs), all registered tests, kernel policy and independent review pass. Eleven checked endpoints, including the closed public theorem, use only `propext`, `Classical.choice` and `Quot.sound`. The work estimates remain unchanged.

### Histories after failed public calls (2026-10-12)

Commit `aba75ce5` connects a supported failed public call to a reusable history at its actual failure heap. `CallableIndexedOwnedPreparedStagedHistoryPublicFailures.public_run_failed_retains` derives the initial Source runtime, callable type and packed argument typing from the existing history, real input encoding and selected declaration frame. `RecursiveNamedPublicHistoryFrontdoor.public_run_failed_retains` also recovers startup and Source selection from the accepted public start. Neither endpoint requires a separate assumption that the final heap is well typed.

`Staging.Recursive.FaultPreservation` proves heap typing and type-identity preservation for the existing recursive staged trace grammar. The proof follows faulting children and retains the effects of successful prefixes and real binder allocations. It covers both semantic and staging faults without identifying their failure tags. The public consumer uses this result immediately to construct `History.after_failure`.

The actual failed-session receipt preserves each earlier handle's full native payload through registry extension. The Source result preserves its raw type, code, captured references and meaning at the returned heap. A later supported call may reuse any retained entry, and no new export is fabricated on failure.

The runtime regression mutates the first of two retained product-output closures from `21` to `30`, then fails on an uninitialized local. An intervening recursive call returns `31`; the original handles then return `31` and `112`. This checks retention of the mutation and independence of the second capture. As before, these mutable regression bodies exceed the current static body grammar, so this runtime test is not a closed instance of the semantic endpoint.

Validation: strict Lean, full build (6003 jobs), all registered tests and the kernel policy pass. Independent review found no issue in the failed-session, history or public adapters. The twelve checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The preceding startup/product/lambda unit is `82944a4e`, documented in `4bea6081`. Suspended/export-error continuations, an initial history from a first failed call, full body coverage, non-product output collection, model/registry changes and all-pass composition remain open.

### Public startup, product outputs and terminal lambda formation (2026-10-12)

Validation: strict Lean, full build (5997 jobs), all registered tests and kernel policy pass. Independent reviews found no issues in output collection, public startup recovery or the lambda state connection. The twenty-one checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`. The empty-body certificate helper also passes the full build and axiom audit.

`RecursiveNamedPublicHistoryFrontdoor` derives the real indexed checkpoint, `StartAt`, selected root and `NamedSourceAt` from an accepted public `Session.start`, complete inventory and the current history. That history fixes the starting world and store. Its successful endpoints return the same recovered packet with the complete Source trace, native result, caller `ResultAt` and reusable returned history. Input descriptions and metadata coverage remain structural boundary conditions.

A successful call may now collect selected function leaves from its product output. `RecursiveNamedPublicOutputSelections.Selection` specifies positions only. The actual output encoding and Source result derive each entry's raw type, native payload, Source typing and recursive validation fuel. Ordered concatenation preserves duplicates and earlier entries. Both initialized history seeds and subsequent public calls consume this producer.

`CallableIndexedOwnedPreparedStagedNamedBodySupport.Support` keeps the existing recursive alternative and adds an ordinary lambda at the exact named terminal expression. `Formation.of_actual` retains the compiler Site and same-code body certificate, deriving runtime validity and evidence coverage from the Header. The actual parameter receipt supplies the nested state and current captures. Existing recursive clients wrap their previous certificate in `.recursive`.

Complete inventory, authentic compiler/body certificates, exact raw structural inputs, the actual encoder-to-receiving metadata extension and one fixed function model and registries remain explicit. The new lambda branch requires an ordinary terminal lambda and zero capture prefixes. Output collection currently traverses products; constructor, mapping and raw comptime-wrapped product outputs remain separate work. Reusable failed continuations, suspended snapshots, model/registry changes, full statement grammar and all-pass composition remain open.

The mutable runtime fixture still uses assignment and match outside the admitted body grammar; its results do not instantiate these public semantic theorems. The closed empty unit-lambda fixture is now complete through first export and History construction; captured bodies and returned-closure invocation remain open. Estimates stay at 100% for runtime unification, about 70% for meaning preservation and about 85% overall.

The dated sections below retain their original scope and verification records.

### Used-session issuance and ready snapshot restoration (2026-10-12)

Code commit: `9092656b`. This unit extends the verified history checkpoint below. Strict Lean, full build (5991 jobs), all registered tests and kernel policy pass. Independent snapshot review found no issues. The eighteen checked endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

Actual named and builtin issuance can now add entries to a history after supported executions. Named meaning comes from the retained inventory packet, accepted preparation and current owned pool; builtin meaning comes from its actual closed factory. The public issuance adapters retain the real completion and append the entry, so the existing nested input and public execution theorems can consume it together with earlier exported closures. A repeated issuance may reuse a physical handle while recording the new issuance receipt.

`Session.snapshotWithReceipt` retains the successful observation of a ready session. Restoration preserves that captured branch's exact store, world, authority and raw metadata. Observing heap cells may append handle slots; the proof preserves every earlier handle's full payload. `RecursiveNamedPublicRestoredHistory` transports the saved history, and `CallableIndexedOwnedPreparedStagedRestoredHistoryPublicBounds` consumes it in all three public endpoints. Later mutations on the original branch are excluded from the restored branch. Suspended snapshots and automatically remembering newly observed heap-cell handles are outside this connection.

The history, continuation, initialization-seed and restored public adapters now derive executable-plan preparation from `SourceCoreUnifiedPreparationCertificates.compiled_planPrepared`. This uses the original compiled records and removes a separate caller-supplied `acceptedPlan` premise.

The combined runtime test starts with captures `38` and `109`, reissues named and builtin handles, and passes them with both closures through a constructor and mapping. It returns integer `233`, then `47` and `117`, and rejects an incompatible nested handle. An independent snapshot branch saves `38`/`109`, mutates the original to `47`, then restores and obtains `39`/`110` with the original handles. The restored heap excludes later allocations. Swapping duplicate mapping rows leaves aggregates `176` and `233` unchanged but changes the follow-ups from `38`/`109` to `39`/`108`, and from `47`/`117` to `48`/`116`; those follow-ups establish row-order coverage.

These mutable runtime fixtures do not instantiate the current public semantic theorems: their assignment and match statements lack the required static body certificates. The connection still requires the supported ordinary sequence family, named terminal/support evidence, exact raw input receipts and the genuine encoder-to-receiving metadata extension. The model and registries remain fixed. Broad body coverage, reusable failed continuations, suspended snapshot histories, nested output collection and all-pass composition remain unfinished. Progress estimates are unchanged.

### Retained function histories (2026-10-12)

Code commits: `1bf7248d` and `b5be3856`.

Validation: strict Lean, full build (5986 jobs), all registered tests, kernel policy and independent review passed. The fourteen checked handle-transport, history, argument, public-continuation and initialization endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

A finite history retains several independently exported functions across supported successful calls. Intervening calls may allocate or mutate captured cells and may return only data. Each retained closure keeps the identity of its captured references; its later execution observes the current Source heap and native store. Actual named/builtin issuance may occur between calls without changing that state.

`RecursiveNamedPublicFunctionHistory.History` records the actual selected startup, native success and full semantic `ResultAt` for each execution. Startup provenance fixes the selected root, raw signature and native argument vector. A successful step keeps earlier entries and may remember its newly exported function. `History.current` derives current encoding, representation and Source typing for every retained entry, together with the actual caller, stable rows and heap conditions.

`CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers` starts the history from the actual fresh bootstrap and finite resumption chain. It consumes the existing nested data/named/builtin input receipts and an observed successful function export. The initialized public theorem produces the Source application, full `ResultAt`, reached caller and first retained entry at the actual returned session. Subsequent supported calls extend that history without replaying initialization.

`RecursiveNamedPublicFunctionHistoryInputs` permits distinct retained functions and repeated aliases at arbitrary finite depth inside products, constructor payloads and ordered mapping keys or values. Independent data certificates retain raw annotations, including comptime wrappers and proxies. The encoder and argument producers preserve exact positions, complete argument lengths, metadata, mapping defaults and duplicate-key order.

`CallableIndexedOwnedPreparedStagedHistoryPublicBounds` consumes this history in public success/failure reflection and Word preservation. The continuation adapters return a new history for the actual successful returned session, either keeping the existing entries or also remembering a function returned directly as the result. Collecting functions nested inside an output container remains separate work; nested inputs are supported. Full Source outcomes, native results and stores, caller relations and `ResultAt` remain in the conclusions.

All steps currently share one function model, body registry and receiving registry. Exact raw input descriptions, valid constructor metadata, the encoder's genuine extension to the receiving registry and supported static body facts remain explicit. Public failure reflection is connected; retaining a reusable history after failure remains open. Restored sessions, adding freshly issued named/builtin handles directly as used-session input leaves, receiving-model changes, complete body coverage and the final theorem across all compiler passes also remain unfinished.

The runtime regression extends the existing `81`, `29` and `101` checks. After successful mutation calls and later factory issuance, a product/mapping input invokes two independently captured closures and repeats the older one. It returns Word `176` (`31 + 37 + 108`); subsequent calls observe captures `38` and `109`. The later issued factory handle is not an input to this call. These runtime checks exercise retained handles and mutation; the proof still requires its actual history and supported body receipts.

Progress estimates are unchanged. The dated sections below preserve their original scope and verification records.

### Returned closure inputs (2026-10-12)

Code commits: `62001b99` and `f950c96c`.

The public semantic connection now continues from a preceding successful call that returns a function handle. The next call can receive arbitrary finite lists of independently typed data and repeated occurrences of that same returned function. Those occurrences may appear inside products, constructor payload vectors and ordered mapping keys or values. Exact raw types, comptime wrappers, proxy annotations, payload order and duplicate mapping keys are retained.

The preceding call supplies both its actual native success receipt and full semantic `ResultAt`. `SucceededResultAt.reimports`, `reimports_payload` and `reimports_function_after` recover the original exported payload with its actual handle registry and complete captured references. `RecursiveNamedPublicReturnedValues.returned_value` extracts Source meaning, the reached owned caller, stable histories, heap typing and representation from the same returned semantic result. `header_context_supports` derives transport between the actual Source declaration contexts. `RecursiveNamedPublicReturnedSessionInputs.StartAt.after_succeeded` identifies the next startup with the preceding returned store and world.

`RecursiveNamedPublicReturnedInputs` describes the ordered arguments independently of their native representations. The argument producer combines those descriptions with the previous result and the actual nested encoder. `CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds` consumes the produced arguments in public success/failure reflection and Word preservation. The endpoints retain the reached Source heap, location map, native store, caller relation and complete resulting `ResultAt`. Initialization is not replayed. The immutable global references come from genuine finite inventory membership and the fixed prepared environment.

Both calls currently use the same function model, body registry and receiving registry. The next encoder's genuine extension to that registry remains explicit for metadata-bearing arguments. The exact prior success and semantic result, raw input certificates, valid constructor metadata and supported static body family also remain premises. Between the returned completion and the next startup, the connection permits a finite sequence of actual state-preserving named/builtin issuances.

The returned-input certificate covers one returned function identity, reused any finite number of times alongside data. It does not yet combine several independently exported old handles or mix that returned handle with additional issued function inputs. Arbitrary intervening executions, restored sessions, changes of receiving model/registry, complete static body coverage, broader compiler grammar and final all-pass composition remain unfinished. Progress estimates are unchanged.

The public runtime regression exercises broader behavior: it allocates an independent closure, mutates an older closure, then issues named and builtin handles before passing them together in nested carriers. Two occurrences of the older closure share its current captured state, and duplicate mapping keys select the first entry. The call returns `81`; subsequent calls observe the original capture at `29` and the independent capture at `101`. These are runtime checks for preserved mutation and aliasing. They do not instantiate the narrower theorem for multiple independent handles and arbitrary intervening execution.

Validation: Strict Lean, full build (5978 jobs), all registered tests, kernel policy and independent review passed.

Axiom checks: The twelve checked reimport, returned-state, argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

### Nested named and builtin inputs (2026-10-12)

Code commits: `9181cd2b` and `708e3f8b`.

Public success/failure reflection and Word preservation accept named and builtin handles inside arbitrary finite products, constructor payload vectors and ordered mapping keys or values. Constructor packing covers empty, singleton and longer payload vectors. Repeated handles, duplicate mapping keys and original argument order are retained. Raw typing keeps comptime wrappers and exact proxy annotations.

`RecursiveNamedPublicNestedInputs` describes each public value and its independent Source value structurally. Function leaves retain genuine issuance chains; named leaves also retain the exact finite inventory packet, imported specialization and dictionary. The initialized owned state supplies the capture. The selected startup producer follows the actual nested encoder, constructs leaf meaning from those receipts, and derives representation and Source typing for the complete value. The argument fold preserves every original Source and native position.

`CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds` consumes this result in all three public endpoints. The initial caller, stable rows, global references and heap conditions still come from the actual fresh bootstrap, any finite sequence of resumptions and state-preserving issuance. Conclusions retain the staged Source outcome, native result and store, actual public returned session and complete caller relation.

The receiving registry must extend the actual encoded registry: `Extends encodedValues.registry receiving`. Exact raw input certificates, valid constructor metadata and supported static body facts remain explicit. Runtime type projection cannot recover all raw annotations; two registries extending a common ancestor do not establish the required metadata relation.

The public runtime regression nests a constructor and an ordered mapping inside products, reuses earlier named and later builtin handles, and retains duplicate mapping keys. It checks result `71` and rejects an incompatible handle separately inside a mapping payload and inside a constructor payload.

Validation: Strict Lean, full build (5971 jobs), the focused public runtime regression, all registered tests, kernel policy and independent review passed.

Axiom checks: The eleven checked encoding, leaf, argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

Closure inputs, restored or previously executed sessions, complete static body coverage, broader compiler grammar and composition across all compiler passes remain unfinished. Progress estimates are unchanged. The dated entries below retain their original scope and validation.

### Mixed function and data inputs (2026-10-12)

Code commits: `91a42c32` and `8964ff88`.

Public success/failure reflection and Word preservation now accept an arbitrary-length flat list of named handles, builtin handles and handle-free data. Each position is checked against the selected root's exact raw Source signature. Data may contain constructors, proxies, products and ordered mappings; repeated arguments and duplicate mapping keys retain their original order.

`Session.IssuanceChain` records actual successful named and builtin issuance steps. Its proofs preserve earlier handles through both slot reuse and append, so a handle issued before a later handle can still be passed to the final session. The data producer obtains each payload from that same accepted mixed startup. `RecursiveNamedPublicMixedArgumentReceipts.Inputs` retains structural data typing and the original function issuance and inventory receipts. Its fold constructs complete argument representation and deep Source typing internally. The initialized public endpoints also derive the caller, globals and heap conditions from the actual bootstrap, including any finite sequence of resumptions.

The receiving registry must still extend the actual encoded registry: `Extends encodedValues.registry receiving`. Raw data typing and exact function types remain explicit. An arbitrary shared registry ancestor or erased native type does not supply these conditions.

The runtime regression uses five arguments in this order: an earlier named handle, Word `3`, a `mapping Word Word` with rows `(3, 7)` and `(3, 99)`, a later `wordToInteger` handle, and the earlier named handle again. It checks result `72` and rejection when the function handles occupy incompatible positions.

Validation: Strict Lean, full build (5962 jobs), the focused public runtime regression, all registered tests, kernel policy and independent review passed. Axiom checks: the ten checked issuance, data, mixed argument and public endpoints use only `propext`, `Classical.choice` and `Quot.sound`.

The remaining input boundaries are handles nested inside data carriers and closure inputs. Restored or previously executed sessions, complete static body coverage, broader compiler grammar and composition across all compiler passes remain unfinished. Progress estimates are unchanged. The dated entries below retain the scope and validation of their original commits.

### Singleton named input connection (2026-10-12)

Committed in `be545d01` and `f7c07bf1`.

A named handle issued from the initialized session now reaches the same public success/failure reflection and Word preservation endpoints as the builtin boundary. Accepted recipe preparation identifies its complete native carrier, identity, descriptor and physical global slot. The actual bootstrap-owned pool supplies the capture; the real cached row and store read identify the complete installed closure.

The imported function is the exact `Issued` packet retained by `Inventory.HasRow`. Its Source value keeps the original retained instantiation and resolved dictionary. The argument producer derives representation and deep Source typing for the receiving caller. The selected root must have one raw parameter equal to the imported specialization's Source function type. The public endpoints construct the initial caller, heap and argument conditions internally and retain the complete returned state.

The scope includes any finite sequence of actual bootstrap suspensions and state-preserving issuance. Closure inputs, mixed lists, nested handles, restored or previously executed sessions, broader static body coverage and the theorem across all compiler passes remain open. Progress estimates are unchanged.

Validation passes: strict Lean, full build (5959 jobs), all registered tests, kernel policy and independent review. The seven checked named factory, input and public endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`.

### Function input connection (2026-10-12)

`54bc83a5` connects original handle issuance to state-preserving public startup. `83bf7430` completes the Source argument connection for a single builtin handle at its exact raw parameter type. Accepted recipe preparation fixes its closed code, identity and descriptor. Actual issuance and encoding supply that same native value, from which the proof constructs the receiving function representation and Source typing. The final public success/failure and Word endpoints consume those facts and retain complete returned state.

The builtin public regression invokes a root with an issued `wordToInteger` handle as its only argument. The newer named connection above retains genuine Source provenance and initialized capture. Closure provenance, mixed argument lists and nested handles remain separate work. No arbitrary function meaning follows from native authentication alone.

### Actual initialization and encoded inputs (2026-10-12)

Commits `9b6cb2c7` and `6976ab8c` remove the supplied initial-state and argument conditions from the supported fresh public entry. `Artifact.bootstrapWithReceipt` retains the original fresh checkpoint. Its ready result identifies the same indexed session used by startup, so the actual completed bootstrap fixes the entire initial store and world.

The existing initialization constructor supplies the owned pool, stable rows, real global references and empty Source heap correspondence. Successful scalar/product encoding supplies both Source argument typing and representation at the body's receiving registry. Public success/failure reflection recovers the Source arguments existentially; Word preservation matches the arguments in its supplied Source trace. These facts are consumed immediately by the existing public execution endpoints, retaining the full staged result and returned state.

`1ebb4c6a` extends this connection to any finite sequence of actual bootstrap suspensions. `b6c24d8f` connects metadata-bearing data to the same public endpoints under independent raw structural typing and preservation of actual metadata IDs in the receiving registry. Scalar/product inputs still derive typing directly from accepted encoding. Runtime projection alone does not establish exact raw Source typing for every metadata-bearing value. The newer function connections above cover one builtin or named argument at its exact raw type. Closure input meaning and restored or previously executed sessions remain open. Static inventory, supported body grammar, compiler policy, diagnostics and genuine startup receipts remain explicit. The final theorem across all compiler passes remains unfinished; the percentage estimates are unchanged.

### Cached roots and public execution outcomes (2026-10-12)

Commits `6199f27d` and `a3d8877f` extend the ordinary caller connection to the actual cached named body and public execution API. The public facade retains proof receipts for the original open, start and resume actions. Each action executes once; the existing API delegates to the receipt-producing operation and returns its value.

`preserves_root` and `reflects_root` consume the mixed recursive body proof internally. `public_run_succeeded_reflects` and `public_run_failed_reflects` connect the actual public result to that same body, staged Source application, native result/store, full returned heap/caller relation and exact indexed export session. `public_word_preserved` proves that a Source Word result exports successfully with sufficient execution fuel and a positive output budget. Input and output budgets remain independent. Stage rejection retains its staged outcome.

The final staged endpoints do not assume a body execution law. This lower-level API requires genuine initialized owned-pool/global-slot receipts, represented arguments and heaps, named/principal static support, compiler policy and diagnostics. The initialized consumer above now constructs its state and argument conditions for the fresh scalar/product boundary. Broader grammar, unrestricted methods/generalized-local bodies and composition across specialization, evidence and comptime remain unfinished. The progress estimates are unchanged.

### Connected ordinary sequence callers (2026-10-12)

Committed in `80a41cf5`. `CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_compiled` and `reflects_compiled` now connect actual preparation and retained compiler recipes to the existing recursive caller/body proof.

For ordinary closure Associations, the consumer obtains its scope from the actual Code, constructs the sequence packet with `choose_for`, and derives call readiness for each used child. It also derives readiness for the accepted caller's exact expression certificate. Both directions use the combined named/anonymous stage registry, including its named branch. The resulting packets and readiness are consumed by `MixedCoveredCallerCompilerBounds`.

Principal Associations retain their original dependent packet/support pair, so method owners are not incorrectly treated as ordinary function owners. Named support, supported sequence grammar, original typing and metadata, retained compiler policy, diagnostic interpretation, and heap/admission conditions remain explicit. This closes a supported caller connection; it does not establish all-program coverage.

The cached-root and public outcome connection is recorded above. Further work prioritizes initialization and compiler coverage for that same family. Generalized-cell drafts remain deferred until a concrete consumer needs them. New helper counts are not used to increase the progress estimate.

Validation: strict Lean compilation, full build, registered tests, repository kernel policy, and independent review pass. Both final theorem axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`.

### Verified applied source and runtime materialization

The four modules in `f0f6a910` connect an actual runtime instantiation of a generalized local closure to its compiler-selected source and lambda header.

Authenticated source ancestry tracks ordinary, lambda and applied views. Closed-scheme matching determines the same substitution lookups as the actual runtime instantiation. Equal substitution lookups preserve complete typed sources, contexts and closures, including the masking of quantified variables. The combined theorem retains the actual produced evidence followed by caller evidence.

Private and normal strict checks have empty logs. The 90 selected declarations and sixteen interfaces agree between private and normal checks. Of those declarations, 84 are new; six imported generated helpers match their existing types and axiom lists exactly. All 18449 preceding declarations retain their complete types and axiom lists; the scope grows to 18533 with no removals. Build 5947 rebuilds all 6 affected modules. Registered tests and repository policy pass.

The runtime theorem still requires the descriptor's authenticated source attachment, captured environment, unique source occurrences and matching scheme and raw type. Producing those conditions at generalized allocation and reading, executing the selected body, broader grammar and the final public semantics theorem remain open.

### Verified applied ancestry and ordinary sequence readiness

The two modules in `55fe02aa` connect actual applied-read ancestry to its lexical code owner and construct ordinary discard-sequence call readiness from public preparation.

A sealed applied read and its original code history identify the full owner key. Successful sidecar preparation at that key gives the same guard frame and principal method specialization. The ordinary sequence theorem uses each child's actual compiler certificate and original typing to derive call readiness.

Private and normal strict checks have empty logs. The 5 declarations and five interfaces agree between private and normal checks. All 18444 preceding declarations retain their complete types and axiom lists; the scope grows to 18449 with no removals. Build 5943 rebuilds all 4 affected modules. Registered tests and repository policy pass.

Actual code history, source receipts, original typing and compiler policy remain explicit. General method call readiness, live generalized-local allocation and reading, wider grammar and the final public semantics theorem remain open.

### Verified ordinary annotation call readiness

The three modules in `0d7c0a62` derive ordinary call readiness directly from original source annotations. A checked body's result annotation is either unit or its stored statement annotation. Equal original rigid sources therefore recover equal result annotations across independent declarative contexts.

Actual ordinary origins identify the common original function. Accepted concrete replacements recover its rigid source, and annotation agreement gives the same stage analysis and selected guard frame. The prepared scope then inherits canonical call ports without requiring raw range formation for every retained row.

All three private and normal strict checks have empty logs. Their 11 declarations and eight interfaces agree between private and normal checks. All 18433 preceding declarations retain their complete types and axiom lists; the scope grows to 18444 with no removals. Build 5941 rebuilds all 5 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5871 to 5874.

The readiness theorem retains original function typing, actual preparation, full source receipts, exact compiler certificates and the supported compiler policy. General methods, live generalized-local cells, wider grammar and the final public semantics theorem remain open.

### Verified prepared ordinary call provenance

The seven modules in `5b8c8727` connect successful executable-plan preparation to the catalog origin of every retained specialization. Each row comes from an ordinary function request or an actual implementation-method selector. Signature catalog disjointness then identifies the ordinary rows at a function owner.

Authentic paired ancestry preserves canonical source correspondence after erasing requirement IDs. For ordinary functions, the original checked function determines the requirement profiles and recovers equality of the canonical contextual sources. This derives the selected guard frame and transfers the real canonical call ports. A separate theorem combines admissible reached-call metadata with accepted concrete replacements to establish complete catalog type formation for the matched callee.

All seven private and normal strict checks have empty logs. Their 98 declarations and 24 interfaces agree between private and normal checks. All 18335 preceding declarations retain their complete types and axiom lists; the scope grows to 18433 with 98 additions and no removals. Build 5938 rebuilds all 9 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5864 to 5871.

Ordinary call readiness still requires raw replacement formation for the selected owner's retained rows, original typing, full source receipts and genuine compiler certificates. Qualified generalized-local materialization, general method-frame correspondence, wider grammar and the final public semantics theorem remain open.

### Verified ordinary specialization coherence and calls

The three modules in `4f01d1fb` prove that original statement annotations determine body-result summaries across independent declarative contexts. For authentic ordinary specializations, equal complete sources after local substitution recover equal rigid bodies, inferred results and stage analyses. The resulting guard-frame equality transfers canonical call authority to the selected ordinary scope.

All three private and normal strict checks have empty logs. Their 570 selected declarations and twelve interfaces agree between private and normal checks. There are 565 new declaration names; five imported generated helpers match their existing types and axiom lists exactly. All 17770 preceding declarations retain their complete types and axiom lists; the scope grows to 18335 without removals. Build 5931 rebuilds all 5 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5861 to 5864.

The call theorem requires genuine program typing, ordinary specialization origins, complete raw range formation, full source receipts and the original compiler certificate. Arbitrary applied views, implementation-method histories and the final public semantics theorem remain open. Core instructions and runtime behavior are unchanged.

### Verified specialization and source-instance foundations

The nine-module foundation in `74b762a7` connects successful executable-plan preparation to the actual specialization receipts for every retained row. Accepted canonical replacements are concrete and contain no flexible variables. Equal local instances of one original source recover its complete rigid instances, including ordered nodes, binders and qualified metadata. Genuine ordinary catalog origins identify the same original checked function. A separate congruence theorem transports successful stage analyses when their actual inputs agree.

All 2505 affected modules pass private strict compilation and rebuild normally. The nine selected strict logs are empty. Their 758 owned declarations and 21 selected interfaces agree between private and normal checks. Of those declarations, 640 already belonged to the existing specialization checker; 118 names are new. The expanded baseline includes that checker's existing declarations, and the scoped census grows from 17652 to 17770, with every old type and axiom list exact and no removals. Build 5928, registered tests and repository policy pass. The normal source/object inventory grows from 5853 to 5861.

Concreteness does not establish nominal catalog membership or arity validity. These foundations do not yet derive every selected stage frame or the public all-pass semantics theorem. General method identity, complete formation coverage and broader grammar remain open. Core instructions and runtime behavior are unchanged.

### Verified recursive discard-sequence exits

The module in `552dfdfd` connects both preservation and reflection for supported recursive discard sequences to their exact exits. Ordinary returned values and semantic faults carry the reached lexical exit. Stage rejection retains its original scope, call, reason, context and prefix heap. The strict child laws are constructed inside the proof.

Private and normal strict checks have empty logs. All 19 selected declarations and four public interfaces agree literally between private and normal checks. The scoped census grows from 16993 to 17012; every preceding declaration keeps its full type and axiom list, with no removals. Build 5920 rebuilds all 3 affected modules. Registered tests, all 38 Tests.Main declaration blocks and repository policy pass. The normal source/object inventory grows from 5852 to 5853.

The result still requires genuine compiler packets and support for the selected closure and named bodies. Broader grammar, complete formation coverage, selected-frame correspondence and the final public theorem across all compiler passes remain unfinished.

### Verified canonical call readiness and ordinary body exits

The three modules in `3059a7f5` construct call readiness at the canonical invocation of the same generated Code. The proof recovers the original supported grammar from the compiler certificate, follows each actual call occurrence and combines original typing with the retained compiler policy.

The staged body projection preserves ordinary returned values, fallthrough and semantic faults with their exact stopping context and heap. Genuine map/world growth and heap metadata construct the lexical exit used by the existing body consumers. Stage rejection keeps its separate semantics.

All three private and normal strict checks have empty logs. Their 19 new declarations and 9 interfaces agree literally between private and normal checks. All 16974 preceding scoped declarations retain their complete types and axiom lists; the scope grows to 16993 without removals. Build 5919 rebuilds all 5 affected modules. Registered tests and repository policy pass. The normal source/object inventory grows from 5849 to 5852, and all 38 Tests.Main declaration blocks remain exact.

The call-readiness theorem still requires original metadata, source provenance, occurrence uniqueness and the actual compiler certificate. Other selected invocation frames need their own correspondence proof. Complete formation coverage, broader grammar and the final public theorem across all passes remain unfinished.

### Verified prepared policy and canonical call contracts

The five modules in `23ac1a6c` derive supported compiler policies from the retained callbacks and original metadata conditions. Ordinary and principal formations carry the same policy through recapture and prepared qualification. Original root typing supplies the raw parent type at each compiler-issued nested call. The actual Code selects its canonical sidecar and call contract.

All five private and normal strict checks have empty logs. Their 256 selected declarations and 31 new interfaces agree between private and normal checks. Nine existing generated helpers appear in the selected-only audit; their complete types and axiom lists match the preceding scope. There are 247 genuinely new declaration names. All 16727 preceding scoped declarations retain their complete types and axiom lists; the scope grows to 16974 with no removals. Build 5916 rebuilds all 7 affected modules. Registered tests and repository policy pass, and the normal source/object inventory grows from 5844 to 5849. All 38 Tests.Main declaration blocks remain exact.

The call contract proof covers the canonical invocation selected from the same Code. Other selected invocation scopes still need their stage-frame correspondence. Global metadata conditions, complete formation coverage, broader grammar and the final public all-pass theorem remain unfinished.

### Verified contextual compiler policy retention

The three modules in `806e809c` retain the actual contextual compiler policy together with the body recipe, named compilation and generated Code. The receipt records initializer overrides, evidence, local reads and the original fuel choices. Generation and producer projections preserve this same witness.

All 753 affected modules pass private strict compilation and rebuild normally. The three selected normal strict checks have empty logs. The selected modules own 133 declarations and expose eleven new interfaces. All 16679 preceding scoped declarations retain their complete types and axiom lists; 48 declarations are added and none are removed. All 16727 complete private/normal declaration blocks and the API logs agree. Build 5911, registered tests and repository policy pass. The normal source/object inventory grows from 5843 to 5844, and all 38 Tests.Main declaration blocks remain exact.

The wider baseline includes existing dependencies; its growth from the preceding 8862-declaration scope does not measure new semantic coverage. Policy profiles, formation coverage, original typing, supported grammar and exact call readiness still need to be composed. The final public all-pass theorem remains incomplete.

### Verified retained-recipe factories and original typing

The four Sources in `96a60f2f` construct discard and sequence packets from the retained production recipe of the actual Code. Both ordinary and principal Associations retain their named compilation and body context. Original closure typing supplies parameter declarations and per-scope typing conditions.

All four private and normal strict checks pass with empty logs. Their 139 new declarations and 32 interfaces agree literally; all 8723 preceding scoped declarations retain their complete types and axiom lists. The scope grows to 8862 without removals. Build 5910 rebuilds all six affected modules, and registered tests and repository policy pass with zero findings. The normal Source/BOTH snapshot grows from 5839 to 5843. Unrelated user work is preserved.

Compiler policy, captured declarations, supported grammar and readiness at the exact issued calls remain genuine static obligations. Complete production coverage and the public all-pass theorem remain unfinished.

### Verified sequence bodies and lambda applications

The changes in `a0778ccc` connect any supported finite discard prefix and terminal statement to the actual closure body and lambda application. The packet retains the accepted compiler receipt; its support retains the original closure frame and each used child Root at every actual selected Source scope. Original full-body typing fixes the declared result. The proofs preserve the intermediate heap, nested faults and restored caller state, with independent Source and Core execution sizes.

All 24 affected modules pass private strict compilation and rebuild normally. The five selected Sources own 169 declarations and expose 27 interfaces; all 17 existing selected interfaces remain exact. The scope grows from 8646 to 8723 with 77 additions and no removals. Seven generated TYPE changes are reviewed: three change only binder names and four add the new sequence branch. All complete private/normal TYPE/AXIOMS blocks agree. Build 5906, registered tests and repository policy pass.

Compiler packet coverage for all actual formations, wider statement grammar and the final public all-pass theorem remain open. Core language forms and public execution paths are unchanged.

### Verified production recipe retention

The changes in `1bc5d609` retain the actual compiler body recipe through ordinary and principal formation, provenance and prepared projections. The diagnostics, named code and compilation remain existential data inside a proposition. Recapture preserves the lowerer recipe for its resulting Code.

All 355 affected modules pass private strict compilation and the normal build. The nine selected Sources own 325 declarations and expose 26 checked interfaces. The expanded audit measures 8635 → 8646 declarations, with 52 reviewed TYPE changes, eleven additions and no removals. All 21 existing selected interfaces retain their types and axioms. Build 5903, registered tests and repository policy pass.

This provides the compiler identity needed by later packet factories. Child syntax, original policy and typing conditions, scope/coercion authority and exact call readiness still need genuine proofs. Core language forms and public runtime entry points are unchanged; complete production coverage and the public all-pass theorem remain open.

### Verified compiler factories and discard bodies

Original body typing and compiler support for ordered discard sequences are verified in `de3c71e5`. The original closure frame and parameter extension supply each used expression's stored node and raw type. Full body typing fixes the terminal result to the function's declared type. Each actual compiler action issues its own certificate; static call readiness refers to that same proof. Build 5902, registered tests and repository policy pass. Application joins for longer sequences and complete formation coverage remain open.

Ordered discard sequences and propositional support coverage are verified in `37b62b0b` and `5d708d56`. The sequence receipt retains every accepted child action and its predecessor fuel. The flow proof uses structural tail recursion and strict child hypotheses, preserving actual intermediate states and early faults. The coverage wrapper keeps a chosen dependent packet/support pair local to each theorem. Build 5900, registered tests and repository policy pass; the original body typing connection is verified above, while application joins for longer sequences remain open.

The compiler connection and ordinary closure factory are verified in `c2d799e7` and `46a03ca1`. Accepted expression compilation now supplies the mixed recursive caller certificate, while the same produced closure supplies its accepted body action and static packet. Both execution directions retain original raw typing and genuine call readiness. All 52 preceding scoped modules retain their literal declarations; build 5897, registered tests and the repository policy checker pass. Coverage of arbitrary and principal Associations and longer statement sequences remains open.

The recursive caller/body composition is verified in `a6cb5ab2` and `2f22789d`. Its six Sources construct the supported body semantics internally from static packets and genuine call authority. All 46 preceding scoped modules retain their literal declarations; build 5895, registered tests and the repository policy checker pass. Packet coverage for actual formations and the wider grammar remain open.

Eight mixed body/application Sources are normally verified and committed in `448ad204` and `333c5d61`: 150 owned declarations and 28 interfaces with complete literal private/normal TYPE/AXIOMS and API agreement. Build 5889, registered tests and the repository policy checker pass with zero findings. The exact scope grows from 1182 to 1332 without removals; all 38 preceding scoped modules retain their declarations. The normal Source/BOTH snapshot grows from 5814 to 5822 and the ten-module dependency cone is rebuilt.

The same ordinary or principal Association retains a terminal or discard packet at its actual parameter context. Discard flow, body application and caller restoration preserve the reached state, exact returned pool, failures and independent Source/native grades. Compiler/static authority stays explicit. The subsequent recursive composition is verified above; complete packet factories for actual formations, wider grammar and the public all-pass theorem remain incomplete.

The three compiler-root/support/caller Sources were integrated in `d5d5e123` and `02006e66`: 219 owned declarations and 36 interfaces, with complete private/normal literal agreement. Their authentic accepted compiler actions produce original Source roots and static support; the caller proof constructs supported selected body meaning internally. Constructive replacements in `db1ab3d2` preserve all 25 public interface types and private/normal agreement for 175 declarations. The scoped census changes from 595 to 597 through two generated proof additions.

The following nine Sources in `7a321ac5` and `18031d7a` derive concrete closure/named callbacks, recipes and support from the same retained compiler site. Original discard head/tail typing and accepted child actions produce exact roots; preservation and reflection assemble the actual flow and body footer. Genuine raw typing, compiler policy/read conditions, selected scope and call authority remain explicit. Broader grammar, general mixed recursive body composition and the public all-pass theorem remain open.

The historical full census last confirmed 20948. Lost temporary census evidence prevents continuous verification from that count; a new exact module scope was measured at 376 and reached 957 after the nine additions. Policy validation expands that explicit scope to include the existing witness modules and their dependents, measuring 1117 → 1182. At `87b08905`, seven replacements retain the actual Seed/Inventory witnesses and construct profiles inside propositions. Complete private/normal literals agree for 184 owned declarations and 47 interfaces. All twelve dependency modules are rebuilt; registered tests and the repository policy checker pass, removing all nine prior findings. The 43 intentional TYPE changes, 72 additions and seven generated proof removals are recorded explicitly. Core language forms and public runtime entry points are unchanged. The estimates remain 100% for runtime unification, about 70% for semantic preservation and about 85% overall.

Original public operational signatures and finish branches remain exact. The completion receipt shares the original resume/mint action. The `7b0f562f` compatibility audit retains 1440 original same-name literal types and axiom arrays and one explicitly reviewed generated resume-helper migration with two binder-label differences. All 1678 declarations audited at that checkpoint match literally between private and normal builds. The estimates remain about 70% for the second objective and about 85% overall.

The accepted initialized body now preserves and reflects genuine lexical exit and LexicalResult with the same represented result, cumulative effects, returned pool and PostAdmission. The BodyState adapter uses the actual parameter Receipt's full administrative environment; creator capture remains separate. One public parameter entry supplies the same initial state, Receipt and ContinuationAgreement and both strong body contracts at independent grades.

Generic named invocation now retains a supplied `BodyExtra` at the same actual body entry, parameter state and completed body state. Preservation and reflection keep that fact inside the original causal receipt, together with the actual restored frame. Each core consumes its original body callback once and performs the original caller restore once. Source and native grades remain independent. Legacy post-only interfaces attach `TrivialExtra` to the same body witness and forget the added fields.

The preceding Receipt-to-invocation unit connects genuine strong parameter Receipt contracts to `BodyExtra` at the same completed body state. The actual callback entry and reached state reconstruct the Receipt without replaying parameters. Pure `restore_post` uses the caller context, saved stable rows, actual restored frame and genuine `TypeContextSupports` to retain caller admission inside that same causal returned-state witness. Faults use the pure frame/row transport. Source and native grades remain independent; lexical exit still comes from the strong body contract.

The accepted companion exposes `ResultAtWithExit`, `to_post`, `preserves_at_initial`, `reflects_at_initial` and `at_completed`. One actual completed-bootstrap proof supplies its initial state and strong invocation pair. Both directions retain the actual returned pool and independent grades.

The public root adapter derives its strong invocation pair from the same actual ready Session and initial-state factory. Authentic root selection and capture identify the original root machine. Preservation provides sufficient native fuel; reflection retains the actual measured invocation child and an independent Source grade. Both keep genuine lexical exit, body admission and restored caller admission inside the same causal result. Existing low interfaces use pure forgetting of that witness.

The program adapter joins that same result to genuine ProgramOutcome and successful positive Word export through the original start/resume receipts. The successful Word boundary requires its genuine positive validation budget. These ports cover the finite accepted fixture; general failures, export errors, mixed bodies and the final all-pass theorem remain incomplete. No bootstrap, parameter entry or public action is replayed.

The historical staged parent and terminal lambda checkpoint was committed and normally verified at `6844f7b0`. The typed contextual receipt unit was introduced at `df034b25`, and the positive-cell backend migrated at `350e4336`. `CallableIndexedOwnedContextualTypedClosureReceipts` retains actual ordinary and method-principal lambda formation through a typed `Association` and a propositional `StaticMember`.

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

Native compiler occurrence typing and collectors are integrated at `e0edb2ec`. Ordinary/principal capture retains canonical bindings; actual enclosing Core typing supplies used child witnesses for lexical, match, assignment, for-header and imperative extraction. Normal verification passes build 5664, nine empty strict logs, 134 declarations and 28 API checks, with literal private/normal agreement. The measured cumulative census is 17361. Same-Site certificate manufacture and the strict mixed expression/body family remain unfinished.

Static compiler authority is integrated at `27abbb6f`. Same-source `LocalIdentityOwnership` separates actual lambda parameters from inputs and match hidden IDs from declared locals. One actual Named Compilation and Site supply the match, binder, read, reference-slot, allocator and issued assignment/unary policies. These results preserve their genuine Source, scope, ledger and selected-issuer premises. Normal verification passes build 5666, two empty strict logs, 99 declarations and 16 API checks, with literal private/normal agreement; the cumulative census is 17460. The complete same-Site factory and shared expression/body induction remain unintegrated.

Reached read and index diagnostics are integrated at `ef85a057`. The proof uses the actual local-cell read or raw missing-index witness, the selected compiler issuer and the receiving public decoder. The ordered Source prefix, diagnostic reason, returned state and independent grades remain attached to that occurrence. Normal verification passes build 5673, seven empty strict logs, 76 declarations and 24 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17536.

Direct prepared closure origins and ordinary/principal formation are integrated at `6dbfa243`. The actual Code, History, Support, Source origin, captures and positive cells remain together in the returned state. The stage-scope receipts recover the original owner and source scope from authentic sidecars. Receiving and body registries remain independent. Normal verification passes build 5677, four empty strict logs, 139 declarations and 47 API checks with complete literal private/normal agreement; the cumulative census is 17675. Invocation adapters and the shared expression/body family still need normal integration and complete compiler occurrence factories.

Accepted indirect call preservation and reflection are integrated at `22a68060`. Constructive builtin and user argument packets retain the actual selected callee, ordered argument post and runtime gates; the original application restores the saved caller in the same returned pool. Paired named profiles, selected Header root receipts and positive lambda recipes retain compiler authority and independent actual/fixed typings. Normal verification passed build 5752, ten empty strict Source checks, and literal private/normal agreement for 129 declarations and 36 APIs. The cumulative census grew from 18887 to 19016, with no overlap or removals. Strict user body hypotheses, the numeric expression/body induction, complete compiler occurrence coverage and recursive staged rejection remain unfinished.

The shared expression/body family remains incomplete. Static factories must construct the same retained body's compiler Tree at every genuine occurrence context, scope and read budget. Source typing alone does not justify globally empty evidence or coercions, or exclude generalized local cells. Actual compiler alternatives require their own coverage. Ordinary execution also needs authentic guard acceptance at each reached indirect call; separate staged judgments preserve guard rejection before arguments. The final recursive staging proof must cover the remaining Source forms.

Next: close one receiving-model expression/body family across closure, named/global, builtin and method calls, with positive cells and genuine physical arity, Source stage gates and public diagnostic inclusion. Then compose the actual specialization, evidence and comptime transformations through the public compilation and input boundary. Generalized/scheme cells, compound assignment, general failure/export-error correspondence and the final all-pass theorem remain incomplete. The first objective remains 100%; the second stays about 70%, and the equally weighted overall estimate stays about 85%. These are estimates of completed work, not declaration counts or remaining time.

At the preceding `8d2289c5` factor checkpoint, all 50 retained same-name original TYPE/AXIOMS blocks match literally. Two generated proof helpers move from the legacy `with_post` cores to `with_extra`; the reviewed differences are their generated names and hygienic binder labels. All other TYPE fields and complete axiom arrays are retained. These moves are recorded separately from the same-name matches.

At the preceding public root/program checkpoint, normal verification at `6bbea5e` passed 5620 registered build jobs, two empty strict Source logs, 31 complete declarations (14 root / 17 program) and 14 signatures. Every private/normal TYPE/AXIOMS block matches literally and uses only the standard three axioms. The cumulative census is 16328 from 16297: 31 additions, no prior overlaps and no removals. The 5551-row pre-install snapshot and actual 2297-module import environment passed. The one changed existing object pair, `Tests.Main`, is covered by the three-module dependency cone and three successful rebuilds. All 4985 protected artifacts remain unchanged. The unit adds two Test Source modules and two `Tests.Main` imports; the proof umbrella is unchanged. No IO or runtime/Core specification change is added.

Anyone resuming implementation should first read the current status and the handoff at the end of the [implementation record](core-runtime-unification-progress.md). Public API users should consult the [API migration record](core-runtime-unification-api.md); see the [T0 audit](core-runtime-unification-audit.md) for the initial compatibility and semantics investigation.

Design approach: Combine a small number of Core extensions with helper libraries implemented using ordinary Core data types and functions.

Reading order:

- Review the approach: Sections 1 and 3
- Implement Core: Sections 4 and 5
- Develop proofs: Sections 6 and 7
- Choose a task to resume: The implementation status above and Sections 8, 9, and 12
- Assess completion: Sections 10 and 11

## Staged call diagnostics and terminal bodies (2026-10-11; `1507404b`)

The normally verified `staged-call-diagnostics-terminal-bodies` package adds twelve proof Sources and twelve CoreLowering imports at `1507404b`, with 184 owned declarations and 66 selected interfaces. Its preceding baseline was code `d9f2a0c4`, documentation `1a84839a6a2ae4013c191b3988a92f129e0bc68c` and cumulative census 19250. Author checks and two independent nonauthor Source reviews per Source are preserved. This proof package retains the existing Core syntax, runtime and public execution definitions.

Receiving diagnostic adapters use the same accepted preparation, original codebook row and actual receiving `IssuedAt` to transport the literal call token into the completion table. Original and substituted call metadata remain distinct. First-gate rejection retains the actual invocation, failing Source scope, guard frame and callee post as `Failure.stage`, including an arity error raised by that guard. Physical arity rejection at the second gate is `Failure.semantic` after evaluated arguments, with the actual argument state and effects. The public decoded semantic view adds concrete arity counts to the existing assignment view.

Terminal proofs cover accepted `returnSome` or singleton expression-tail bodies. The compiler receipt supplies the actual child action, predecessor fuel, result type and emitted footer. The same SourceView recovers the original terminal occurrence. Strict child preservation/reflection proves the literal emitted `code.rename`, retaining the original BodyResult, independent Source/Core grades, exact failure tags and reached caller relation. Successful values carry Source admission; stage failures retain stable rows at the reached state. The body meaning follows from the concrete compiler and child receipts.

The builtin application producer uses represented ordered scalar arguments and the original primitive proof. The whole indirect argument-prefix reflection starts from the actual native parent, constructs raw callee and argument typing from the original Source rows, resolves the first gate and uses the concrete ordered-argument fold. It retains stage rejection at the callee post, argument failures at the reached argument post, or the actual remaining application suffix after values.

Complete application/body dispatch, recursive statement bodies, the numeric E/F induction and authentic static factories for every compiler alternative remain open. The supported recursive Source profile still needs its remaining grammar. Specialization, evidence and comptime composition, general failure/export-error correspondence and the final public all-pass theorem are unfinished. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.

Normal verification passed one registered build with 5774 jobs, twelve empty strict Source checks, and literal private/normal TYPE/AXIOMS agreement for all 184 complete owned declarations and complete API agreement for 66 selected interfaces, using only the standard three axioms. The cumulative census grew from 19250 to 19434 (+184), with no overlap or removals. The normal pre-install snapshot contained 5695 module rows; the current snapshot contains 5707. The independent BEFORE environment measured 2195 project modules and the compiled environment measured 2207. The existing CoreLowering object changed for registration; all fourteen modules in the reverse dependency cone were rebuilt, and all 4985 protected artifacts passed. All sixteen original normal receipts closed with exit code 0.

The independent BEFORE capture closed at `95d226` (`5e30b5`, session 27207); private full/API audit at `e7c58a` (`c4bffc`, session 59109); packet freeze at `ffc386` (`36c4ae`, session 8576); registered build at `335796` (`dc06e6`, session 62711); and normal validation at `8d3298` (`b29544`, session 57723). Code commit `1507404b20264fc300b656e9971205f3ecbf90a8` closed at `07591c`. The saved `staged-call-diagnostics-terminal-bodies-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `f3558384cf298fe7fd4d535eaafe4cd535435adef662b8e24db3b3cf80e013ba`. The checkpoint uses the original sixteen closed validation receipts; metadata finalization does not repeat their kernel runs.

## Staged indirect call proof package (2026-10-10; `d9f2a0c4`)

The ten-Source package is normally verified and committed at `d9f2a0c4`, based on prior HEAD `8ce195d527d56533a169b482d78ca3c5448b68b4` and cumulative census 19016. It changes proof infrastructure. Core syntax, runtime behavior and the public execution API retain their existing definitions. Normal validation checked 234 owned declarations and 71 APIs, build 5762 and cumulative census 19250.

The new graded Source judgments mirror the 46 rules of the existing supported recursive staging profile. Expression, ordered-expression, application and statement traces retain their actual heaps and scopes, with independent Source and Core grades. Staged admission uses the actual reached caller state and relation. Successful values retain original Source admission; a stage failure retains stable rows and its exact scope, call and reason.

Strict callee bounds preserve semantic and nested stage failures. Whole-parent native inversion supplies that strict child completion and retains the actual first-gate suffix after a value. Scoped receipts recover the original codebook call while preserving the actual substituted call metadata. Second-gate rejection derives physical arity from the selected row and produces a semantic arity fault after arguments. The ordered-argument fold derives its result from strict child hypotheses at successive reached states.

Paired closure and issued named-body connectors consume the genuine eligible expression hypothesis. They still require its numeric proof. Complete call classification, scoped receiving-diagnostic composition, staged body recursion, all compiler alternatives and the remaining Source grammar are open. Staged builtin application, terminal statements, receiving diagnostic adapters, the whole argument-prefix draft and later body drafts are outside this ten-Source package. The second-goal and overall estimates remain about 70% and 85%.

Normal verification passed one registered build with 5762 jobs, ten empty strict Source checks, and literal private/normal TYPE/AXIOMS and complete API agreement for all 234 owned declarations and 71 selected APIs, using only the standard three axioms. The cumulative census grew from 19016 to 19250 (+234), with no overlap or removals. The normal pre-install snapshot contained 5685 module rows; the independent BEFORE environment measured 2314 project modules and the compiled environment measured 2324. The existing CoreLowering object changed for registration; all twelve modules in the reverse dependency cone were rebuilt, and all 4985 protected artifacts passed. All fourteen original normal receipts closed with exit code 0.

The actual independent BEFORE capture closed at `b06ac5` (`93e376`, session 32268); private full/API audit at `37afb7` (`049c04`, session 30036); registered build at `c23ee3` (`f0abd0`, session 2959); and normal validation at `ae72a4` (`d1d98b`, session 63612). Code commit `d9f2a0c412f2315193c6e4c196826a9b8763d286` closed at `d4b0be`. The saved `staged-indirect-call-runtime-bounds-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `3265acc0c522928261051cc31bcc4b20a30931101377c2996cd2ea7f6db183e5`. The checkpoint uses the original fourteen closed validation receipts; metadata finalization does not repeat their kernel runs.

## 1. Goals and Agreements

This design has two goals, in priority order.

1. **Remove direct runtime evaluation of typed-source and unify the runtime backend on Core.**
2. **Prove that compilation from typed source to Core preserves the meaning of execution relative to an independent `SourceSemantics`.**

Typed source remains as an intermediate representation in the compiler. The runtime evaluator is what is removed.
Core safety proofs alone do not establish compilation correctness, so the second goal is treated as a separate deliverable.

### 1.1 Conditions Confirmed with the User

| Item | Decision |
| --- | --- |
| Functional compatibility | Preserve every feature executable through typed-source at the start of migration through Core before removing the old evaluator. |
| Strength of the proof | Prove correspondence of execution results and state changes with independent `SourceSemantics`, in addition to type preservation. |
| New contract integration | Defer new connections for source contract methods, persistent storage, and external calls to the next phase. |
| comptime | This phase removes direct runtime evaluation. Unifying the existing direct comptime evaluator on Core is deferred to the next phase. |
| Termination | Successful termination of all programs is not a requirement. Allow general recursion and use execution with finite fuel. |
| Core size | Do not add Core types or instructions for each source feature. Prefer representations using existing features and helper libraries; decide additions by recording comparisons and reasons. |

If these conditions change, consult the user rather than reducing the feature scope solely at the implementer's discretion.
The specific module names and internal data structures below are design recommendations, distinct from the agreements above.

### 1.2 Scope of This Phase

- Preserve the current closed roots, finite specialization plans, and currently supported range of trait evidence.
- Preserve the behavior of existing Core, Core Wire, HostRunner, and ContractRuntime.
- Changes to existing ContractRuntime required by Core syntax or state changes are in scope.
- Designing acceptance, ABI, or storage layout for new source contracts is out of scope.
- Compilation of every type-checked program, unlimited specialization, and new open dictionary support are not required.
- Exact equality of source and Core fuel counts, heap indices, internal cell counts, or diagnostic strings is not required.
- Preserve existing computational results, shared state, evaluation order, and language failures. Track compatible diagnostic categories and source locations in the migration table as well.

### 1.3 How to Pursue the Two Goals

Completing every proof for the second goal is not a prerequisite for completing the first goal.
However, design the representation relations and main theorem first, and develop Core extensions, compilation, and basic lemmas in parallel.
The complete proof can still be finished against `SourceSemantics` after the old runtime evaluator is removed.

Use agreement tests with the old evaluator for checks during migration. Do not use the old evaluator as the definition of semantics or as a permanent proof assumption.

### 1.4 Record of the Initial Implementation and Audit (2026-09-30)

This section preserves the initial results and the scope that was incomplete at that time. Do not read "current" or "incomplete" below as the latest status. See the opening status and the [implementation record](core-runtime-unification-progress.md) for subsequent implementation, completion of the first goal, and the latest proof boundaries.

As of 2026-09-30, the [T0 audit material](core-runtime-unification-audit.md) contains migration tables for expressions, statements, values, evaluation order, failures, public inputs, and comptime.
Reachable missing-default examples, migration destinations for all features, and failure regression checks still needed confirmation; creating this list alone did not complete T0 or the first goal.

Positive missing-default fault rules were added for expression indexing, reads during place resolution, and latest-root updates after the RHS.
They make the successful prefix and its heap explicit, and prove that pure path failure is exclusive with successful execution of the same read / update.
This change does not cover other rules for invalid shapes, type mismatches, or similar conditions, or failure coverage and determinism for all source executions.

The [StagedValue correspondence proof](../../Solcore/SourceSemantics/CoreLowering/StagedValue.lean) is implemented.
For the existing `SourceStagedValue.toCoreExpr`, it proves structural correspondence with independent source values, typing on both sides, successful Core checking, preservation and reflection of evaluation, store invariance, and the connection to execution with fuel.
This proves **embedding a staged value that has already been obtained**. It does not yet prove that the pre-evaluator computed that value correctly, lowering of all typed source expressions, shared heaps, or preservation of the meaning of recursion.

The [Literals correspondence proof](../../Solcore/SourceSemantics/CoreLowering/Literals.lean) also connects to lowering actual source expressions.
Its scope is finite trees recursively combining unit, Bool, in-range Word, and two-element products, with explicit uniqueness of occurrences, exact type information, and empty requirements / coercions.
Using an internal wrapper for the existing lowerer and the existing `Resolved.Expr.lower?`, it proves successful lowering with a sufficient compilation budget, successful Core checking, correspondence of finite successful results in both directions with independent `Dynamic.ExpressionEvaluates`, and heap/store invariance on both sides.
Sufficient execution fuel is derived from finite source evaluation and distinguished from the traversal budget for compilation. General expressions, failures, staging, and correctness of whole-function compilation are outside this proof's scope.

The full build, all tests, and kernel policy checks passed with both proof files included. These results are distinct from completion of T3 and T6, and can be used by later source expression / comptime proofs.

The pure Core machine's `StateHasType` now uses the world-dependent `RuntimeStoreHasTypes`.
`BoundedSafety` handles world extension for execution steps and finite step sequences, typing of suspended states, and runtime typing of completed values.
Type preservation for finite evaluation also moved to the same store relation, and cell payload restrictions were removed from checker and frame typing. Constructor payloads admit general well-formed types.
The unconditional normalization proof for all Core was removed, and APIs deriving completion and sufficient fuel now require actual finite `Evaluates` evidence.
The old `StoreHasTypes` remains in limited theorems requiring first-order inputs or literal equality of final stores.

[CoreGeneralCells](../../Solcore/Test/CoreGeneralCells.lean) proves infinite execution of a self-referential closure accepted by the checker, with typed suspension and resumption for all fuel.
[CoreRecursiveCells](../../Solcore/Test/CoreRecursiveCells.lean) also validates handwritten Core examples of terminating self-recursion, mutual recursion, function arguments, and shared captures. It checks exact step counts, final values, references and stores, type preservation, suspension, and resumption.
These examples initialize cells with placeholder functions, so handling of uninitialized reads was supplied by later implementation.
The added [OptionalCell](../../Solcore/Core/OptionalCell.lean) stores any well-formed Core payload type in `sum unit T`, allowing allocation without constructing a placeholder payload.
[LanguageResult](../../Solcore/Core/LanguageResult.lean) represents success and language failure with ordinary `sum Word T`, and proves typing, short-circuiting bind, and safe observation and decoding of finite runs.
The [ContractRuntime adapter](../../Solcore/ContractRuntime/CoreLanguageResult.lean) passes successful payloads to the existing entry codec and connects language failures to frame traps and top-level rollback. Fuel exhaustion is not terminal.
The new [local-read lowerer](../../Solcore/Frontend/SourceCoreLocalCell.lean) and [LocalCell correspondence proof](../../Solcore/SourceSemantics/CoreLowering/LocalCell.lean) cover initialized reads and uninitialized failures for ordinary unit/bool/word/product values.
They prove successful actual compilation, independent source outcomes, structural correspondence of both heaps, completion with sufficient fuel, and reflection of values and stores for every completed Core run.
[SourceCoreBasic](../../Solcore/Frontend/SourceCoreBasic.lean) composes these reads into ordinary monomorphic let, `=` to a bare local, expression statements, explicit return, and trailing expressions.
The type scope remains unit/bool/word/product; it does not yet handle evidence for functions, blocks, loops, mappings, or Integer literals.
[HeapMutation](../../Solcore/SourceSemantics/CoreLowering/HeapMutation.lean) proves correspondence of allocation, writes, and lexical environments. [BasicExpressions](../../Solcore/SourceSemantics/CoreLowering/BasicExpressions.lean) derives correspondence of actual compilation, typing, independent source success and uninitialized failure, and finite Core execution from structural expression proofs.
[BasicStatements](../../Solcore/SourceSemantics/CoreLowering/BasicStatements.lean) contains lemmas composing statement sequences and full correspondence for the uninitialized failure of `let x:T; return x;`. A successful `let Bool; = true; return` example was also validated using actual compilation output.
For general statement sequences, the proof assumes correspondence proofs for child expressions and continuations, and evaluation in the actual environment containing inserted temporary Core binders. It does not prove preservation of meaning for every accepted statement sequence.
At that time, `SourceCoreControl` added conditional expressions, if/block, scope restoration, and early return; `SourceCoreBasicEntry` added typed startup and resumption. The public compiler tries this route after the old direct Core route.
The ordinary-read reason/site table preserves expression IDs, binders, and spans, and reconstructs diagnostics from language failures. Expression proofs from actual compilation, extraction of Core typing for statement sequences, and preservation of meaning for whole sequences from a static statement-sequence Tree without external child-evaluation assumptions were also added.
This still excludes semantic correspondence for the origin and input/output layout of actual entries, whole if/block constructs, the full source failure table, captures, and recursion.
It does not settle the recursion approach for all source programs or complete T1. Details and integrated verification are recorded in the [implementation record](core-runtime-unification-progress.md).

## 2. Current State and Reasons for the Change

### 2.1 Current Path for Unification on Core

The public `SourceCompiler` re-exports `SourceCoreExecution`. `SourceCoreCompiler` and `SourceCoreUnifiedCompilation` validate plans and prepare Core code, then create bootstrap, session, and checkpoint from a shared artifact. Root execution and calls to returned functions use cached Core bodies and `Core.runStateful`. Backend preference, automatic fallback, and choosing between `runCore` / `runTyped` have been removed.

Typed source remains as an IR for preparation, compilation, and authentication. `SourceRuntimeValues` and similar modules retain the `SourceTypedRuntime` namespace as a value, observation, and validation carrier, rather than a runtime evaluator for expressions, statements, or calls. Existing direct comptime evaluation remains in the preparation phase.

The existing pure `SourceProgramExecution → SourceCoreDirectLinking` path remains as a focused adapter that generates Core. Its cell allocation differs from the public unified path, so distinguish where proofs apply (Section 6.6.1).

### 2.2 Implemented Representations and Remaining Proofs

- General cells, constructor payloads, world-dependent store typing, finite safety, suspension, and resumption are implemented.
- Uninitialized cells use the `OptionalCell` sum; language failures use the `LanguageResult` sum. Public diagnostics and the existing ContractRuntime trap/rollback adapter are connected.
- Recursion and mutual recursion use existing closure / apply and optional function cells. No new Core function definition table was added.
- Arbitrary-precision Integer was added as a Core scalar with operations. Mappings and proxies use ordinary Core data and helper functions.
- Execution of return, break, continue, while/for, non-tail statements, match, local instantiation, selected methods/coercions, and helpers has migrated to Core.

Registered regression checks confirmed functional compatibility for the first goal. Do not infer preservation of meaning for all source programs from these implementations or Core type safety. Actual provenance of function values, all captured environments, dynamic AuthorityPool and general bodies, composition of all passes, and the final main theorem from public inputs remain for the second goal.

### 2.3 Limits of the Current Proof Assets

Reuse Core proofs of type preservation, progress, and correspondence between execution and declarative evaluation.
The successful Core checker evidence returned by the current lowerer establishes typing of generated code, rather than preservation of source meaning.

`SourceSemantics` has values, heaps, and execution relations independent of the evaluator.
It also has type preservation proofs for successful finite execution, so use it as the reference for compilation proofs.
However, some bridging theorems from the source checker to declarative semantics still have explicit assumptions.
This document does not assume that correctness from raw source through execution has already been proved.

## 3. Target Architecture

```text
CheckedProgram / TypedSource
    |
    | SourceCompilationPlan / SourceSpecializationWorklist
    | Validate root, staging, evidence, and reachability; required existing comptime calculations
    v
SourceCompiler / SourceCoreExecution
    |
    | SourceCoreCompiler / SourceCoreUnifiedCompilation
    | Compile types, functions, local instantiations, control, and state to Core; run checker
    v
Shared Artifact + source locations, public types, and authentication catalogs
    |
    | Validate public inputs and prefix; Bootstrap / Session
    | cached Core body / Core.runStateful
    v
Successful completion / language failure / typed Checkpoint
```

ContractRuntime uses the host-aware execution form of the same Core. New connections for source contract methods, persistent storage, and external calls belong to the next phase.

### 3.1 Conditions on the Execution Path

- Core execution does not refer to the `TypedSource` node table.
- Core execution does not call the type inferencer, trait solver, or specialization worklist.
- Core closure bodies are Core code.
- Core instructions do not call the old typed-source evaluator.
- Diagnostic source correspondence tables are separate from executable code.
- Moving specialization or validation to another module must not leave a runtime interpreter there.

The existing pure Core machine and host-aware machine may remain as execution forms of the same Core language.
What is prohibited here is retaining a separate backend that evaluates source syntax.

### 3.2 Separating Compilation Work

The following work has been separated from the runtime evaluator into `SourceCompilationPlan`, `SourceSpecializationWorklist`, and the Core preparation layer.

- Canonical revalidation of specialization plans
- Collection of selected operator/coercion methods and their helper frontier
- Collection of first-class function references and concrete uses of locally polymorphic functions
- Validation of stage conditions and evidence
- Determination of public roots and signatures

Compilation plans retain functions, types, required methods, local instantiations, and source correspondence.
Their success conditions include "every call or reference destination exists."
Agreement with rerunning the plan does not replace a proof that it covers all semantically reachable targets.

### 3.3 Boundary Between the Core Kernel and Helper Libraries

The Core specification contains typed functions and application, a mechanism for recursion, general cells, products, sums, nominal data, scalar operations, general failure results, and the existing host boundary.
The default approach is to compile source-specific behavior into Core code written with these features.

| Feature | Default placement |
| --- | --- |
| Recursion and mutual recursion | The adopted closure / apply and optional function cells (Section 4.1). |
| Mutable captures | General typed cells and existing closure / apply. |
| Uninitialized variables | Represent initialization state with a sum and check it with ordinary branching. |
| mapping dictionaries | Entry sequences and Core helper functions for lookup, update, key comparison, and defaults for each type. |
| proxy | Tags in ordinary data types. Do not add dedicated type-reflection instructions. |
| loop, return, break, continue | Compilation using recursive functions and sums. Do not add dedicated source-statement instructions. |
| trait, evidence, local polymorphism | Compile-time instantiation and compilation to Core functions and records. |
| Integer | The adopted arbitrary-precision Core scalar and operations. See Section 4.4.1 for the comparison and reasons for adoption. |
| Diagnostics | Retain source locations and source-specific failure categories in correspondence tables. |

Helper libraries are ordinary Core code checked by the Core checker.
They do not directly evaluate mappings or similar features with special host functions or interpret the source IR.
Their execution uses the same evaluator, typing, and fuel rules as other code.

### 3.4 Criteria for Adding Core Features

Before adding a new Core type, value, instruction, or special evaluation rule, compare and record the following.

1. A representation using existing functions, sums, data, cells, and helper libraries.
2. An addition as a Core primitive.
3. The scope of changes to the specification, checker, type safety, host, and Wire for both options.
4. The impact of both options on compilation, helper libraries, preservation-of-meaning proofs, and generated code size.
5. Measurements of representative examples if performance is a reason for the decision. Do not rely on unmeasured speedups.

The goal is not merely to minimize the number of Core syntax forms.
Assess the combined burden of Core safety proofs and correctness proofs for libraries and compilation.
A primitive may be chosen for a feature such as Integer if a data-structure representation would require extensive arithmetic implementation and proofs.
Do not add dedicated mapping or proxy types or instructions by default; if that changes, retain the comparison and reasons for adoption described above.

Based on the T0 candidates and T1/T3 implementation and proofs, recursion uses existing mechanisms and Integer uses a scalar extension. Public API and Wire compatibility were validated. Record the same comparison if further additions become necessary.

## 4. Core Representation and Execution

### 4.1 Representation of Recursion (Adopted)

Decision on 2026-10-01: **Use existing closure / apply and optional function cells.** Source compiler regressions passed for self-recursion, mutual recursion, higher-order arguments, returned lambdas, and shared mutable captures, maintaining execution and checkpoint type safety without adding a Core function definition table.

1. Allocate optional function cells for all globals first.
2. Compile each body to Core code and create closures capturing shared global references and required cells.
3. Store the closures in their cells and call them with existing `apply`.
4. Treat calls and iterations of generated loops as ordinary machine transitions that consume fuel.

Represent uninitialized values with sums and propagate read failures through explicit language results. Do not construct placeholder function payloads. Tie suspended states to the same generated code and store. Source self-cell recursion uses the same closure / cell combination.

The initial proposal for `FunctionId`, signatures, a function definition table, and dedicated calls was considered for comparison and was not adopted. No other recursion instructions such as `fix` / `letrec` were added. Runtime body inlining is not required.

Type safety of generated code is implemented, but preservation of meaning connecting arbitrary captures, caller/lexical history, catalog permissions during calls, and all source bodies remains ongoing under the second goal.

### 4.2 General Cells and Cyclic References

Remove the `CellPayload` restriction and handle storability through Core type well-formedness and world-dependent value typing.
Align the constraints on nominal constructor payloads as well.
This checker admission, finite safety, uninitialized-value compilation, and source-recursion compilation are implemented. Semantic correspondence with arbitrary Source heaps and capture history remains ongoing under the second goal.

The central type-safety structure has the following form (definition names are pseudonotation).

```text
D                       Core data definitions
Σ                       Declared type of each cell
ValueTyped D Σ v T      Value type under data definitions D and cell types Σ
StoreTyped D Σ H        Each cell value has a type under the same D and Σ
StateTyped D Σ state R  Type of execution state, including continuations
```

Typing a cell reference `loc` only checks `Σ[loc] = T`.
Closure typing does not recursively reread heap contents.
Typing every heap cell separately under the same `Σ` handles closure → cell → closure cycles.

The required basic lemmas are type-world extension, allocation, read, write, environment extension, and type preservation for closure creation and application.
Type preservation alone does not require introducing a step-indexed definition that traverses the whole heap.
If semantic correspondence between higher-order source and Core values requires another technique, introduce it in that proof layer.

### 4.3 Uninitialized Cells

The adopted `OptionalCell` represents a mutable source cell `T` as Core `cell (sum unit lower(T))`.

- `inLeft unit`: Uninitialized
- `inRight value`: Initialized
- Reads branch and produce the prescribed failure if the cell is uninitialized.

This lets the Core store itself retain a structure in which every cell always contains a value.
Preserve the current treatment of an uninitialized mapping as an empty mapping, distinguishing it from ordinary uninitialized reads.

The proposal to change Core store values to `Option Value` was not adopted. If this representation changes in the future, update the comparison in Section 3.4 together with heap correspondence and public input validation.

### 4.4 Data Types, Integer, mapping Dictionaries, and proxy

In this document, `mapping` refers to the source language's dictionary type `mapping(K => V)`.
For example, in `let table: mapping(Word => Word); table[7] = 42;`, it is the type of `table`.
It does not mean a correspondence from source to Core or a connection to persistent contract storage.

| Feature | Adopted implementation | Conditions to preserve |
| --- | --- | --- |
| nominal data | Associate instantiations of closed source types with Core data type IDs. Allow general well-formed payloads. | Constructor identity, payload order and types, and pattern-matching order. |
| Integer | Added an arbitrary-precision Core scalar and operations. See Section 4.4.1 for the comparison and reasons for adoption. | Arbitrary-precision operations, signs, comparisons, bitwise operations, and Word conversions. |
| mapping dictionaries | Represent entry sequences for each concrete key and value type with existing data types, and generate lookup, update, and similar operations as ordinary Core functions. Do not default to a dedicated `Core.Ty.mapping` or mapping instructions. | Key comparison, insertion and replacement order, defaults, nested updates, and the distinction between copying and sharing. |
| proxy | Represent with ordinary nominal data. The public compatibility path retains authenticated raw metadata IDs in Word payloads. Core does not interpret source `Ty`. | Type identity and behavior as mapping keys. |

The mapping helper library implements entry sequences, lookup, and update for each concrete `K` and `V` as ordinary Core code. Its basic structure is shown below. This is design pseudonotation, rather than a proposal to add polymorphic types to Core.

```text
EntryList_KV = Nil | Cons(lower(K), lower(V), EntryList_KV)
keyEqual_K   : lower(K) × lower(K) → Bool
lookup_KV    : EntryList_KV × lower(K) → sum unit lower(V)
insert_KV    : EntryList_KV × lower(K) × lower(V) → EntryList_KV
default_V    : unit → sum unit lower(V)
```

Entry sequences use existing nominal data and recursive data definitions.
Lookup misses and absent defaults return explicit values; compilation of source index operations handles applying defaults or producing the prescribed failure.
Insert preserves current insertion order and replacement rules. Nested updates reconstruct the required outer values and ultimately write back to the original local cell.
These bodies are entirely Core code, rather than wrappers calling old runtime operations.

Do not optimize all proxies away to unit until unchanged observable behavior has been proved.
Even when source types lower to the same Core representation, do not merge types distinguished by proxy comparison into the same tag.
Changing mapping values to independent reference objects could change assignment and copy semantics, so do not do this in the initial implementation.

Do not assume general mathematical map laws unconditionally for key comparison.
The original `valueEqual` does not consider ordinary closures or mapping values equal to one another; for global functions it compares specialization keys and evidence.
Prove correspondence between the old comparison and Core operations for each supported key type. The compatibility carrier retains authenticated IDs for raw type metadata and function provenance/evidence to reconstruct comparison and defaults. These IDs are not a general Core function-equality instruction.
Generate this comparison from the type-specific `keyEqual_K`. Retain provenance and evidence identity needed for function-key comparison as ordinary data in the value representation.
Do not choose a function representation that loses this identity or solve the problem by adding a general Core function-equality instruction.
Do not replace this with generic Core value equality or assume reflexivity or `lookup(insert(k,v),k)=v` for all keys without checking the specification.

Mapping lookup and update consume multiple Core steps by executing helper functions. Their fuel counts do not match the old runtime.
Integer is a primitive, but an operation taking one Core step does not necessarily have constant computational cost.
Fuel in this phase is an evaluator transition budget, rather than EVM gas or an upper bound on total computation.

### 4.4.1 Comparison and Adoption of Integer Representations (2026-10-01)

Integer has been added as an arbitrary-precision Core scalar. Mappings and proxies use ordinary data and functions.

| Option | Scope of changes and proof burden |
| --- | --- |
| Sign and Word limb sequences in ordinary Core | Can be represented without changing existing kernel, host, or Wire syntax. However, normalization, carry/borrow, multiplication, Euclidean div/mod, signed bitwise operations, and Word conversions must be implemented anew, and agreement with the original Int operations must be proved for sequences of arbitrary length. |
| native Integer | Add Ty/Value/literal and operations, and update exhaustive branches in the checker, CEK, evaluation correspondence, type safety, renaming, host transitions, and Wire. Use existing Lean Int operations and prove agreement with independent source primitives for each operation. |

Reading the existing code suggested that the native option would change about 25–35 production/proof modules, including about 8–10 Wire modules. This was an estimate before implementation, rather than a measured diff size. File counts, generated code size, and speed for the limb option were not measured.

The reason for adoption is to avoid reimplementing and proving an arbitrary-precision arithmetic library while limiting the added Core specification to one scalar and its operations. Speed is not a basis for the decision. Keep host storage and external-call ABIs based on Word, with explicit conversions as needed. Do not add a dedicated source interpreter, mapping primitive, or proxy primitive.

Preserve current source semantics. Both div and mod return 0 on division by zero; nonzero cases use Lean Int Euclidean operations. Bitwise operations follow the current rules, including combinations of positive and negative operands; Integer→Word is modulo 2^256. Preserve old Wire tags and decoding, and extend representation of new syntax through new explicit tags and budget accounting. Projection to the old format returns unrepresentable instead of silently discarding Integer.

### 4.5 Locally Polymorphic Functions

In the currently supported scope, quantified local binders are limited to lets initialized directly by lambdas, and assignment to such binders is rejected.
Use this constraint and collection of use sites by the existing worklist to keep Core monomorphic by default.

- Determine concrete code from the outer specialization, lambda location, accumulated type substitution, and handling of required evidence.
- Generate code for each reachable usage type.
- Instantiations belonging to the same activation share the same captured cells.
- Do not re-execute initializer expressions or duplicate captured values or heaps.
- Local cells allocated for each function call are fresh and specific to that call.
- Do not assume the source cell of a generalized descriptor corresponds to a single Core cell.

Validate and prove that the catalog of local instantiations covers every use site.
If this catalog is incomplete, fix compilation rather than adding fallback to the source evaluator.

### 4.6 Trait Evidence, Operators, and Coercion

Compile selected implementation methods to Core functions.
Where the required implementation differs by call, pass dictionary arguments using Core function values or typed records.
Statically fixed cases can use direct function references.

Do not interpret source predicates, requirement IDs, or the trait solver during Core execution.
Retain them as compile-time validation evidence and source correspondence information.

Check the following reachability in particular.

- Helpers called by selected methods
- First-class function references first discovered inside methods
- Evidence captured by function values
- Evidence specific to each use site of locally polymorphic functions
- Coercion order and coercion of the full argument list for indirect calls

### 4.7 Statements, Control, and Evaluation Order

Conceptually, statement compilation returns a typed control result distinguishing `fallthrough`, `returned R`, `break`, and `continue`.
The implementation uses existing Core sums and generated recursive functions.

- A statement sequence executes the next statement only on fallthrough.
- Return does not execute the rest of the statement sequence.
- While returns to condition evaluation on continue.
- For executes the post part after continue, then returns to the condition.
- Break is consumed by the innermost loop.
- Scope exit removes local names but retains cells reachable from closures.
- Preserve handling of values from trailing expressions and the presence or absence of semicolons.
- Short-circuit operations and conditional branches do not execute side effects of unselected expressions.

Fix the evaluation order of function values, arguments, assignment-target indices, right-hand sides, and coercions in a table based on `SourceSemantics` and existing behavior.
Do not introduce changes such as evaluating the same index expression twice in compound assignment.

After resolving the target and indices, compound assignment retains the **leaf value from before RHS evaluation** as the operation's left operand.
The final structural write uses the **latest root value after RHS evaluation**, preserving changes that the RHS made to other fields or mapping entries.
The current `ResolvedPlace.selected` retains the former. Do not reread the leaf from the new root as the left operand or write back the entire old root.
Typing, compilation, and proofs handle the state at target resolution separately from the state after the RHS.

## 5. Execution Results, Fuel, and Public Inputs

### 5.1 Result Categories

| Category | Treatment |
| --- | --- |
| Successful completion | Return a value and final store. |
| Language failure | Return the failure category and state up to that point. |
| Fuel exhaustion | Retain a well-typed intermediate state that can be resumed. |
| Internal error | Invalid instructions, type inconsistencies, and similar conditions. Prove that these do not arise from checked code and valid inputs. |
| Public input rejection | A boundary error before execution, distinct from language failure during execution. |
| Insufficient compilation budget | A compilation error in plan creation, staged evaluation, or similar work, distinct from runtime fuel exhaustion. |

The adopted representation is an explicit language-failure result using existing Core `sum Word T`.
`inLeft reason` is failure, `inRight value` is success, and `LanguageResult.bind` propagates failure and suppresses subsequent processing.
Expression, function, and statement-sequence lowering interprets and composes these results. It must not use ordinary `letE` alone to continue processing after failure.
Do not confuse this with existing `MachineFault`. Core syntax, machines, and runner result types have not changed.
Restore source locations from correspondence tables without introducing a source-syntax dependency into Core.

The host-aware runner and HostDriver retain the carrier as an ordinary completed value, and the `ContractRuntime.CoreLanguageResult` adapter interprets the outer sum.
Connect failure to the existing frame's trapped outcome and TopLevelExecution rollback; do not treat it as success or pending resumption.
On success, pass only the envelope payload to the existing entry codec. Preserve entry-outcome conventions based on return values.
Do not route it to current unreachable internal-fault branches. On fuel exhaustion, retain the typed state/context without finalizing.
The reason is a Word argument to helpers; the actual compilation fault/site table and public `diagnostic` / `handleDiagnostic` reconstruct the source category and location. Preservation and reflection of all independent Source failures remain for the second goal.

Even typed source can encounter uninitialized reads and similar failures.
It is therefore not claimed that every input produces only successful completion or fuel exhaustion.

### 5.2 Termination Guarantees

Completion and sufficient-fuel APIs such as `checked_runStateful_has_sufficient_fuel` now require actual finite `Evaluates` evidence. The unconditional normalization proof for general Core has been removed. Returning a result with finite fuel and successfully terminating are treated as separate guarantees.

The guarantees retained for general Core are as follows.

- The execution function returns a result for finite fuel.
- Types are preserved at each step.
- Correct code and state do not produce internal errors.
- Fuel-exhausted states are also typed.
- Additional fuel for the same suspended state corresponds to execution with the total fuel.
- Given a terminating semantic execution, finite fuel exists that realizes it.

Do not introduce unbounded recursion that consumes no fuel in Core helpers or implementations of calls and loops.
Do not change ContractRuntime to commit fuel exhaustion as a successful transaction.

### 5.3 Public Inputs and API

The public `SourceCompiler` boundary is unified around one opaque artifact, Value, Session, Outcome, and Checkpoint. `BackendPreference`, automatic fallback, two result carriers, and the old session implementation have been removed.

Functions in public Values use handles with ownership. Authenticate artifact, session, export generation, and slot; reject different ownership, unknown handles, and type mismatches before execution. This supports named / builtin inputs, repeated calls to returned functions within the same session, and repeated state updates.

Input validation goes beyond checking the outer tag.

- Validate payloads, heaps, captures, and code provenance under the same type world.
- Convert ordinary initial data to a sealed prefix with `SourceCoreHeapInput`.
- Validate historical raw heaps containing closures through explicit `SourceCoreLegacyHeapImport`. This process does not execute Source expressions or statements.
- Handle snapshots carrying evidence of actual allocation and capture through restoration or `exportPrefix`. Implicit transfer to another artifact is not provided.

See the [API migration record](core-runtime-unification-api.md) for actual API signatures, execution and observation budgets, source/native snapshot cell counts, and ownership constraints. Do not confuse internal compatibility carriers in old namespaces with continued existence of the old public execution path.

### 5.4 Core Wire Compatibility

The adopted format retains the fixed `schema` string `solcore-semantic-core`. No separate version field or Core function table was added. The Program codec retains its 4 existing required fields.

- Preserve old tags, decoding, and existing roundtrips.
- Extend native Integer types, values, and operations with explicit tags, accounting for decode depth, node, and byte budgets.
- Generated code for mappings, proxies, and closures uses existing data, function, and cell representations without dedicated Wire tags.
- Projection to the old representation is a partial conversion that checks representability and does not silently discard Integer or similar constructs.
- Codec, Core conversion, budget, and roundtrip proofs and rejection tests have been updated.

The initial `solcore-semantic-core-v2` and new function-table proposals were not adopted. If required fields change in the future, design identification of compatible formats at that point. Wire is an external representation, rather than an additional runtime backend.

## 6. Proof of Meaning Preservation

### 6.1 Reference and Scope

The main subject is typed source with valid declarative typing and stage conditions, and its execution.
Use `SourceSemantics.Dynamic.ProgramEvaluates` and associated failure relations as the reference for ordinary outcomes. Runtime staging guards also require independent Source staging judgments: a rejected indirect call stops after evaluating its callee and before evaluating any arguments. Keep the failing caller scope, call occurrence, guard reason, and heap at that point.
The final theorem's input `S` is typed source before specialization and comptime pre-evaluation/substitution.
Theorems concerning only residual code after specialization and staging are intermediate results.

Do not redefine semantics as "the generated Core behaves this way" or embed old evaluator return values into semantics.
If existing semantics lacks rules, supply them with source-language reasons and examples.

Declarative stage classification does not imply that every runtime indirect-call guard accepts. In particular, `Staging.HasStage.indirectCall` classifies the callee and arguments without requiring their stages to satisfy the dynamically selected callable's parameter and result contract. A proof of ordinary `Dynamic` execution may therefore require genuine guard acceptance at each reached call; that is an intermediate profile, not the complete public theorem.

`Staging.CallBoundary` already gives independent acceptance and rejection rules at one call boundary. `Staging.Recursive` propagates the original staged failure through nested expressions, lexical scopes, and callable bodies. Its current rules cover only the documented subset and must be extended for remaining forms, including evidence, coercions, assignments, and loops, before claiming complete public coverage. Successful staged execution and ordinary semantic faults project to the existing `Dynamic` judgments. A stage rejection has its own outcome and public diagnostic; do not convert it into a `Dynamic.SemanticFault` or claim that a boundary-only theorem closes the recursive proof. These proof extensions require no new Core syntax or runtime backend.

Distinguish full correctness from parsing and name resolution of raw source from this compilation theorem.
Track the connection that supplies declarative assumptions from executable checking / stage analysis as separate theorems.

### 6.2 Correspondence Relations

Define at least the following. The names are provisional.

```text
ProgramRel       Correspondence of source definitions and instantiations with actual generated code and closure inventory
Representation   Correspondence information for types, locations, generated code, and local instantiations
ValueRel         Correspondence of source values and Core values
HeapRel          Correspondence of source heaps and Core stores
EnvironmentRel   Correspondence of source local environments and Core environments
OutcomeRel       Correspondence of successful results or prescribed failures and the state at that point
```

Requirements:

- Make correspondence for scalars, products, nominal data, mappings, and proxies explicit.
- Represent closure code correspondence and sharing of captured locations.
- Allow one generalized source closure to correspond to multiple monomorphic Core bodies.
- Allow extension of location correspondence upon allocation.
- Handle source descriptor cells, erased staged cells, and Core helper cells.
- Do not assume equality of entire heaps or one-to-one correspondence of all cells.

### 6.3 Shape of the Main Theorem

The following is mathematical pseudonotation describing the proof contract, rather than a currently existing Lean API.

Assumptions:

```text
compile(S, root) = ok C
SourceAdmitted(S)
EntryValid(S, root, sourceInputs, sourceHeap)
InputsRelated(ρ₀, sourceInputs, sourceHeap, coreInputs, coreStore)
```

Successful `compile` includes plan validation, compilation, and successful Core checking.
Compilation success does not itself establish `EntryValid`. Public specialization can accept an unused type substitution containing a nominal type absent from the Source program. Entry validity checks the full substitution range, including unused replacements. Such an input is outside this theorem until its independent entry validity is established.
Do not make the main theorem trivial by requiring callers to supply proof fields that assume meaning preservation itself.

**A. Preservation of Successful Execution**

```text
SourceEvaluates(S, root, sourceInputs, sourceHeap, v, H)
  → ∃ fuel, vC, HC, ρ₁,
      CoreRun(C, coreInputs, coreStore, fuel) = done(vC, HC)
      ∧ Extends(ρ₀, ρ₁)
      ∧ ValueRel(ρ₁, v, vC) ∧ HeapRel(ρ₁, H, HC)
```

**B. Reflection of Successful Execution**

```text
CoreRun(C, coreInputs, coreStore, fuel) = done(vC, HC)
  → ∃ v, H, ρ₁,
      SourceEvaluates(S, root, sourceInputs, sourceHeap, v, H)
      ∧ Extends(ρ₀, ρ₁)
      ∧ ValueRel(ρ₁, v, vC) ∧ HeapRel(ρ₁, H, HC)
```

`ρ₀` is the initial representation relation; `ρ₁` is the final relation, including allocation during execution and similar changes.
`Extends` expresses preservation of existing correspondences and sharing, with the ability to add correspondence for new locations and similar entities.

**C. Preservation and Reflection of Prescribed Failures**

Provide bidirectional failure theorems corresponding to A and B.
Relate the side effects and state before failure as well as the failure category.
Because internal representations of types and locations differ, literal equality of error values is not required.

**D. Safety of Finite Execution**

No internal type inconsistency occurs for any fuel.
Successful results, prescribed failures, and suspended states each retain the required typing invariants.

A and B guarantee that compilation does not introduce divergence into terminating source or produce successful termination absent from the source.
However, they do not by themselves prove equivalence of infinite traces or overall source progress.
If an independent theorem for infinite execution or correspondence with the source prefix at fuel exhaustion is required, design additional small-step / coinductive semantics separately.
The finite observations in this phase do not require new source small-step semantics from the outset.

### 6.4 Decomposing the Proof

| Layer | Required results |
| --- | --- |
| Core | Soundness of the extended checker, type preservation, progress, result categories, and fuel/resumption laws. |
| Basic representation | Correspondence of types, values, heaps, environments, primitives, and allocation/read/write. |
| Helper libraries | Core typing and semantic correspondence for type-specific generated entry sequences, key comparison, lookup, update, defaults, and proxy tags. |
| Expressions | Correspondence for variables, calls, closures, operations, coercions, constructors, and mappings. |
| Statements | Correspondence for statement sequences, scopes, early return, loops, break/continue, and match. |
| Specialization | Preservation of type substitutions, local instantiations, evidence, and reachability. |
| comptime | Correctness of pre-evaluation, constant replacement, and branch elimination actually performed. |
| Whole pipeline | Theorems A–D connecting roots, arguments, initial states, and compilation artifacts. |
| Public boundary | Executable validation supplies the main theorem's initial conditions. |

Develop preservation by induction on source big-step derivations.
For reflection, use generated-code and continuation structure and invariants of the correspondence relations.
Extend the existing correspondence theorems between Core declarative evaluation and the machine with fuel, and connect concrete fuel theorems.

Reuse general Core safety through typing of helper functions.
This alone does not establish mapping or similar specifications, so separately prove correspondence of lookup results, insertion order, defaults, comparison, failures, and state changes.
Show that helper generators can apply these lemmas for each accepted type and representation.
Also establish finite lookup and insert execution on valid finite entry sequences, preventing correspondence from being satisfied vacuously by functions that fail to terminate successfully.
Maintain the same proof contract for keys containing function values or proxies, and do not take old runtime equality as an unproved callback.

### 6.5 Specialization Proofs

Separate specialization revalidation from semantic coverage.

- Revalidation: The supplied plan can be reconstructed from the program and has not been altered.
- Coverage: Functions, methods, and local instantiations reachable at runtime within the supported scope exist in the plan.
- Preservation: Execution based on original types and evidence corresponds to execution of instantiated bodies.

If plan creation does not finish within budget, a compilation error is acceptable.
A runtime path back to source is not permitted to compensate for omissions in a successful plan.

### 6.6 Treatment of comptime

Retain the existing direct comptime evaluator in this phase.
The final theorem from typed source to Core concerns source before pre-evaluation, so correctness of the pre-evaluation actually applied is also required.

- The returned staged value is also obtained by declarative evaluation.
- Constant replacement and embedding of the value in Core preserve correspondence relations.
- Branch and short-circuit choices are correct.
- Eliminated computations do not remove runtime-observable side effects.
- For staged computations with heaps, make the relation between their state and residual code explicit.

New pre-evaluation optimizations are not required in this phase. Do not add constant folding that is unnecessary for moving existing features to Core execution.
Do not retain existing runtime evaluation by relabeling it "for comptime."

Intermediate composition lemmas may assume `StagingCorrect` or similar conditions.
The final result for the second goal must connect theorems showing that the passes actually applied supply those assumptions.

### 6.6.1 State Correspondence for Erased comptime Cells

Inspection of the implementation on 2026-10-05 confirmed that replacing comptime expressions with constants can produce cells existing only in source execution.

- `SourceCoreElaboration.lowerExpressionFuelWith` replaces accepted comptime function calls or whole conditional expressions with `SourceStagedValue.toResolved`. Independent Source execution may allocate function arguments and locals while generated Core does not allocate them.
- In `lowerStatementsFuelWith`, the monomorphic Integer `let` branch adds the value to the compile-time environment and returns only the body. The Source `let` cell is erased.
- Staged `let` for Word, Bool, and similar types retains a value binding through `.letE` even when its initializer becomes a constant. `Resolved.Evaluates.letE` and `Core.Evaluates.letE` extend the value environment without allocating physical cells. Retaining a syntactic binding alone does not preserve Source cell allocation.

Distinguish allocation by execution path. The pure `SourceCoreElaboration.lowerFunctionBody → BodyDraft.finalize → Resolved.Expr.lower?` path also passes inputs in the value environment, and `Resolved.Evaluates.store_eq` establishes store invariance. The public `SourceCompiler.compileChecked → SourceCoreUnifiedCompilation.prepare` path uses `SourceCoreSourceCells.bindParameters` / `letInitialized`. The current indexed allocator allocates a snapshot, marker, and payload for each Source cell; the existing heap relation associates payload locations with Source cells.

The current public artifact is generated from the original specialized `TypedSource` and does not apply the pure Integer `let` erasure or constant replacement above. `prepareContexts` authenticates local evidence and does not pre-evaluate expressions. Pure erasure reaches `elaborateFunction` and the existing `SourceProgramExecution → DirectLinking` path. State each actual path's proof scope, and do not claim complete state correspondence for the public compiler from `Resolved.Evaluates.toCore` alone. Introducing new erasure into the public path is not added as a required task for this phase.

The current `GenericHeap.HeapRepresents` / `GeneralHeap.HeapRepresents` associate each Source cell with a Core cell. Their `length_eq` requires the length of the location correspondence table `LocationMap` to equal the number of Source heap cells. This is a proof table relating cell locations, distinct from the language's `mapping<K,V>`.
Existing "whole heap invariance" theorems for expression evaluation alone cannot connect the full compilation pipeline, which includes argument and `let` allocation described above.

**Implemented relation:** [SourceStagingHeapRelation.HeapRel](../../Solcore/SourceSemantics/CoreLowering/SourceStagingHeapRelation.lean) in the comptime-pass proof layer relates the complete Source heap before compilation to the Source heap of residual code. Reuse the existing all-cell relation for correspondence from residual code to Core. Adding Core syntax or execution rules is not a condition for solving this problem.

This relation and the pass theorems must satisfy at least the following.

1. Preserve all initial heap cells and the contents, sharing, and references of retained cells. Changes in locations caused by subsequent allocation must also be reflected consistently in values, environments, and closure references.
2. Identify erased cells from the actual accepted pass and the original Source evaluation derivation. Do not arbitrarily remove cells merely believed to be unreachable.
3. For erased Integer bindings and similar cases, maintain equality between values in the actual staged environment and original Source cells. Prove that erased locations do not leak into return values, captures of remaining closures, update targets, public handles, or similar places.
4. Relate retained side effects and states at failure. Supply successful evaluation of erased computations as independent Source derivations from acceptance by the actual evaluator.
5. Retain the original complete heap and evaluation derivation without changing Source semantics to fit residual code. Do not add equality of Source/Core cell counts or internal indices as a final-theorem condition.

The first unit covers actual Integer `let` and argument allocation in accepted staged functions. Supply local-variable validity and freshness from independent Source typing. `8f356765`, `7740d7aa`, and `618cd059` connect the structural relation, actual let erasure, residual Word/Bool computations, and pure function outputs. General staged computations, remaining closures, failures, and composition of all passes remain.


#### Implemented Proof Units and Their Scope

The first `SourceStagingHeapRelation` unit assigns an `Option` target to each Source location. The targets of retained locations enumerate all residual heap positions `0, …, n-1` in their original allocation order; candidate erased locations have no target. Retained values relate all product, constructor, and language-mapping elements and their order. Closures and generalized closures retain code, context, evidence information, and every location in their captured environments. Erasure candidates are limited to initialized ordinary Integer cells. This is a structural location correspondence relation; correctness of erasure decisions by the actual pass is proved separately.

The first application theorem uses acceptance by actual `evaluateStagedIntegerFunction` and the original execution derivation obtained from independent Source typing. It shows that Integer cells for inputs and selected `let` bindings are appended in order to the complete initial heap, and that the result is an Integer value containing no references. Preservation of reads for every initial heap cell is shown for arbitrary heaps. Where needed, derive from `HeapWellTyped` and typing of values and captured environments that initial closures do not capture locations appended later. Do not add rules permitting captures of erased locations or unproved body-execution laws to the relation.

`7740d7aa` extracts the accepted initializer expression, updated staged environment, code for only the recursively lowered body, and requirement-consumption order from the actual `lowerStatementsFuelWith` Integer `let` branch. [SourceStagedIntegerResidualMeaning](../../Solcore/SourceSemantics/CoreLowering/SourceStagedIntegerResidualMeaning.lean) in `618cd059` connects actual acceptance of pure `elaborateFunction` with Word/Bool inputs and computations, Integer let, block, if, and return to independent original Source execution including the complete heap and actual Resolved/Core results. Reflection of finite completion of the original Core uses determinism and existing machine correspondence.

This result preserves meaning in the pure path and does not add Integer erasure to the public unified path. Code and captures of general remaining closures, all staged-value functions, states up to failure, and correspondence of the full public compiler remain subsequent obligations.

Distinguish Source input cells erased by replacing entire function calls with constants from paths retaining Core argument values even when known staged inputs are used. Do not infer cell allocation from retained argument values; check derivations of the actual allocator and correspondence of value environments. Tie every erasure plan to actual lowering branches.

## 7. Specification Audit and Known Gaps

### 7.1 Failure Rules

`SourceSemantics.Dynamic.Fault` defines failures with structural grounds.
It does not guarantee coverage of every case, uniqueness of failures, or a first-fault policy for arbitrary malformed carriers.

First list the following for the valid source programs in scope.

- Successful execution rules
- Prescribed execution failures
- Invalid inputs rejected at compile time
- Invalid values/heaps rejected at the execution boundary
- Internal validation errors found only in the old evaluator

Prove required determinism and exclusivity with failure for the supported scope.
Do not promote every defensive error of the old evaluator to language semantics.

### 7.2 Resolved Gaps and Remaining Boundaries

For missing mapping keys whose value type also lacks a default, positive failure rules for indexing, place reads, and latest-root updates after the RHS have been added to independent `Dynamic.Fault`. They retain successful evaluation prefixes and heaps, and prove exclusivity with success of the same read / update. Core regressions also preserve diagnostics for absent defaults and evaluation order.

Do not treat this change as establishing coverage or uniqueness of all failures, or preservation and reflection for all syntax. The final theorem including stage guards, arity, general call bodies, methods/coercions, and all passes remains ongoing.

The old `RuntimeBoundaryAccepts` / `RuntimeExpressionEvaluatesOutcome` cover a narrow historical runtime representation boundary. Connect to independent Source through the actual compiler's value, heap, and outcome relations rather than accepting current Core values unconditionally.

### 7.3 Coexistence with Proofs in Progress

At the time this design was written, source inference and parser proofs had uncommitted changes.
Recheck `git status` and the relevant files when implementation starts, and preserve other work.
If subsequent work discharges bridging-theorem assumptions, inspect the actual theorems and update this design's assumption list.

## 8. Current Module Structure

| Responsibility | Implementation entry points |
| --- | --- |
| Core types, general cells, finite safety | `Core/Syntax.lean`, `Core/Safety.lean`, `Core/BoundedSafety.lean`, `Core/OptionalCell.lean`. |
| Explicit language failures and Integer | `Core/LanguageResult.lean`, `Core/IntegerPrimitives.lean`, and the existing checker, machine, host, and Wire. |
| Compilation plan validation and closure | `Frontend/SourceCompilationPlan.lean`, `SourceSpecializationWorklist.lean`. |
| Core compilation for public execution | `Frontend/SourceCoreCompiler.lean`, `SourceCoreUnifiedCompilation.lean`, `SourceCoreCompatibleFunctions.lean`, and feature-specific generators. |
| Ordinary Core helpers and cells | `Frontend/SourceCoreMappingWithDefault.lean`, `SourceCoreCompatibleDataEquality.lean`, `SourceCoreSourceCells.lean`, and similar modules. |
| Representation relations and meaning preservation | `SourceSemantics/CoreLowering.lean` and `SourceSemantics/CoreLowering/`. The independent spec umbrella does not import frontend. |
| Public API | `Frontend/SourceCompiler.lean` re-exports `SourceCoreExecution.lean`. `SourceCoreIndexedSession.lean` manages ownership, state, and checkpoints. |
| comptime and pure lowering | `Frontend/SourceCoreElaboration.lean`, `SourceCoreDirectLinking.lean`. State allocation differences from the public unified path explicitly. |

The initial `Core/Functions.lean`, `SourceCoreLowering.lean`, and `SourceCoreLibrary/` are not adopted filenames. New proof units should reuse existing relations and induction, and be added after checking actual placement.

### 8.1 Files to Read First

Links are relative to this document. Line numbers change, so search for the names below.

| File | Definitions and uses to focus on |
| --- | --- |
| [SourceCompiler](../../Solcore/Frontend/SourceCompiler.lean) / [SourceCoreExecution](../../Solcore/Frontend/SourceCoreExecution.lean) | `compileChecked`, `compileEntry`, `compileStaticWord`, `Compiled.open`, and the shared public API. |
| [SourceCoreCompiler](../../Solcore/Frontend/SourceCoreCompiler.lean) / [SourceCoreUnifiedCompilation](../../Solcore/Frontend/SourceCoreUnifiedCompilation.lean) | Actual plan validation, preparation, and cached Core code. |
| [SourceCoreIndexedSession](../../Solcore/Frontend/SourceCoreIndexedSession.lean) | Artifact, Bootstrap, Session, Outcome, Checkpoint, snapshot, and ownership. |
| [SourceCompilationPlan](../../Solcore/Frontend/SourceCompilationPlan.lean) | Revalidation of plans, evidence, and specialization. |
| [SourceCoreElaboration](../../Solcore/Frontend/SourceCoreElaboration.lean) | `lowerType`, `BodyDraft.finalize`, `evaluateStaged*`. |
| [SourceCoreDirectLinking](../../Solcore/Frontend/SourceCoreDirectLinking.lean) | `validatePlan`, `linkWithStagingFuel`, `evaluateStagedIntegerFunctionFuel`, `evaluateStagedValueFunctionFuel`. |
| [SourceRuntimeValues](../../Solcore/Frontend/SourceRuntimeValues.lean) | Compatibility carriers for values, state, and observations, rather than a runtime expression/statement evaluator. |
| [SourceCoreHeapInput](../../Solcore/Frontend/SourceCoreHeapInput.lean) / [SourceCoreLegacyHeapImport](../../Solcore/Frontend/SourceCoreLegacyHeapImport.lean) | Validation of initial data and explicit raw prefix migration. |
| [SourceSpecialization](../../Solcore/Frontend/SourceSpecialization.lean) | `SpecializedFunction` and the allowed scope of locally quantified variables. |
| [SourceSpecializationWorklist](../../Solcore/Frontend/SourceSpecializationWorklist.lean) | `Plan`, `collectContextualLocalLambdaInstances`, `closeLocalLambdaInstancesAux`, `run`. |
| [Core Syntax](../../Solcore/Core/Syntax.lean) | `Ty`, `CellPayload`, `Expr`, `Value`. |
| [Core Data](../../Solcore/Core/Data.lean) | `ConstructorPayload`. |
| [Core Safety](../../Solcore/Core/Safety.lean) | `RuntimeValueHasType`, `RuntimeStoreHasTypes`, the old `StoreHasTypes`, type preservation, progress, and completion assuming finite evaluation evidence. |
| [Core BoundedSafety](../../Solcore/Core/BoundedSafety.lean) | Type safety of finite execution, world extension, and typed suspension. |
| [Core Correspondence](../../Solcore/Core/Correspondence.lean) | `runStateful_evaluation_sound`, `evaluation_runStateful_complete`. |
| [Staged value proofs for Core lowering](../../Solcore/SourceSemantics/CoreLowering/StagedValue.lean) | Implemented value-embedding correspondence. `toCoreExpr_infers`, `toCoreExpr_evaluates_iff`, `toCoreExpr_run_complete`, `toCoreExpr_run_sound`. |
| [Core FuelResumptionProperties](../../Solcore/Core/FuelResumptionProperties.lean) | `runStateful_resume`. |
| [SourceSemantics Dynamic Program](../../Solcore/SourceSemantics/Dynamic/Program.lean) | `ProgramEntryValid`, `ProgramEvaluates`, `ProgramEvaluates.preserves`. |
| [SourceSemantics Dynamic Value](../../Solcore/SourceSemantics/Dynamic/Value.lean) | Values, closures, and failures independent of the evaluator. |
| [SourceSemantics Dynamic Evaluation](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean) | Independent big-step rules for expressions, statements, and calls. |
| [SourceSemantics Dynamic Fault](../../Solcore/SourceSemantics/Dynamic/Fault.lean) | Failure and side-effect propagation, and the old runtime boundary. |
| [SourceInferenceProgramBridge](../../Solcore/SourceSemantics/SourceInferenceProgramBridge.lean) | Check bridging assumptions requiring `InferStatementsFuelSoundness` and similar conditions. |
| [CheckedCoreProgram](../../Solcore/ContractRuntime/CheckedCoreProgram.lean) | Completion guarantees from finite evaluation evidence and type safety of finite execution and checkpoints. |
| [HostDriver](../../Solcore/ContractRuntime/HostDriver.lean) | Connection between Core state and host suspension. |
| [TopLevelExecution](../../Solcore/ContractRuntime/TopLevelExecution.lean) | `TopLevelRunResult`, fuel exhaustion, resumption, finalize. |
| [Core Wire](../../Solcore/Core/Wire.lean) | External representation, codec, and fixed host boundary. |
| [SourceStagedIntegerResidualMeaning](../../Solcore/SourceSemantics/CoreLowering/SourceStagedIntegerResidualMeaning.lean) | Preservation and reflection between original Source execution of pure staged Integer functions and actual Core completion. |
| [CallableIndexedAuthorityPool](../../Solcore/SourceSemantics/CoreLowering/CallableIndexedAuthorityPool.lean) | Preservation of owner keys, shared frames, and all records. |
| [CallableIndexedLambdaTemplatePermission](../../Solcore/SourceSemantics/CoreLowering/CallableIndexedLambdaTemplatePermission.lean) | Derive static template permission from actual receipts. |
| [RecursiveNamedExpressionCompilerCertificates](../../Solcore/SourceSemantics/CoreLowering/RecursiveNamedExpressionCompilerCertificates.lean) | Connect ordered additional child expressions to the same compiler-fuel induction. |

## 9. Implementation Tasks and Dependencies

For each task, record changed APIs, proved claims, remaining assumptions, and verification results.
"Complete" below includes passing the build for the relevant code without introducing proof escape hatches.

| Task | Current assessment |
| --- | --- |
| T0 | Audit of migration scope, representation decisions, and regression scope is complete. Proof obligations for all semantics continue under T6. |
| T1 | Core foundations, adopted recursion representation, and host/Wire updates are complete. |
| T2 | Separation from the runtime evaluator and revalidation of plans are complete. Connect semantic coverage under T6. |
| T3/T4 | Runtime features in scope have migrated. Partial preservation and reflection proofs are implemented; composition for all syntax and general bodies continues under T6. |
| T5 | Public unification and removal of the old evaluator for the first goal are complete. |
| T6 | Ongoing. The overall claims of the second-goal checklist are incomplete. |

The deliverable lists below define implementation and proof scope. Completion of runtime migration for T3/T4 does not mean completion of all correspondence proofs.

### T0: Audit of Features and Semantics in Scope

Dependencies: None.

Initial findings are recorded in the [T0 audit material](core-runtime-unification-audit.md). Update the table by tying each item to concrete migration destinations and regression checks.

Deliverables:

- Feature-by-feature inventory of existing runtime/compiler tests and their Core migration destinations.
- Classification table for successful execution, prescribed failures, input rejection, and insufficient budgets.
- Confirmation of evaluation-order, sharing, and mapping-default specifications.
- A design expressing this document's main theorem and assumptions as Lean types.
- An explicit list of work remaining in comptime.
- A comparison of candidate Core extensions and representations using helper libraries. Record effects on specifications, safety proofs, compilation proofs, generated code, fuel, and Wire/host.
- Decisions on the recursion mechanism, mapping/proxy helpers, and whether to adopt Integer.

Completion criteria: Every unimplemented or unproved item is listed, leaving no room to silently discard old evaluator features.
For each candidate addition, distinguish changes to Core specifications from work placed in compilation and helpers.

### T1: Foundations for Core Cells, Functions, and Results

Dependencies: T0 representation and failure policies.

Deliverables:

- General cells, the adopted closure / apply and optional function cells, and representation of prescribed failures.
- Updates to the Core checker, typing, machine, runner, and basic declarative evaluation.
- Type-world extension and type preservation/progress for read/write, closure, and call.
- Review of unconditional termination theorems and their uses.
- Compatibility and conversion for host, ContractRuntime, and existing Wire, with updates to Core fixtures. Finalizing extended Wire and the public API is excluded.

Completion criteria: Handwritten Core programs execute recursion, mutual recursion, shared captures, and self-cell recursion, with type safety and fuel-resumption laws passing.
Dedicated mapping, proxy, or source-statement instructions have not been added as prerequisites for these foundations.

Current status: Implemented and verified together are checker admission for general cells, finite-execution type safety, a self-referential closure that suspends for all fuel, and terminating self-recursion, mutual recursion, and shared-capture examples.
Uninitialized cells and language-failure results using ordinary sums, allocation of function payloads without placeholder values, and the ContractRuntime failure/rollback adapter are also implemented and verified together.
Source failure envelopes, reason/site tables, recursion selection, and compilation are implemented, so the T1 Core foundations are considered complete. Preservation of meaning for all source programs remains under T6.

### T2: Independent Compilation Plans

Dependencies: T0. Can partly proceed in parallel with T1.

Deliverables:

- Move plan validation, method reachability, first-class references, and local instantiation to an independent compilation layer.
- Deterministic ID assignment for types, functions, and instantiations.
- Registration and deduplication of generated helper functions and data definitions. Include dependencies in the plan and track budgets required for generation.
- Preserve existing rejection of externally forged plans.
- Expose invariants needed to prove coverage.

Completion criteria: New runtime lowering can obtain a complete input plan without importing the old evaluator.

### T3: Minimal source → Core Path and Correspondence Proofs

Dependencies: Required parts of T1 and T2.

Scope:

- Scalars and products
- Let, assignment, conditional branching, return
- Calls using adopted closure / apply and optional function cells
- Closures capturing mutable cells and self-cell recursion
- A small prototype handling lookup and update for `mapping(Word => Word)` and proxy tags with ordinary Core data and functions

Deliverables: In addition to an executable path, establish `ValueRel` / `HeapRel` and basic preservation/reflection lemmas for this small scope.
For the mapping prototype, check helper typing and lookup/update correspondence without first fixing native mapping types or instructions.

Completion criteria: Confirm that shared-heap and recursion representations support the proofs. Result-agreement tests alone do not complete this task.
Assess the implementation and proof burden of helper representations, providing evidence for comparison with candidate Core extensions.
This is the minimum condition for starting to finalize Wire and public API formats.

### T4: Extending Feature Coverage

Dependencies: T3.

Scope:

- Nominal data, match, and Integer in the adopted representation
- Helper generation for mapping, proxy, key comparison, and defaults, with typing and semantic correspondence
- While / for, break / continue, non-tail control, scope
- Locally polymorphic functions, nested instantiation, first-class function values
- Trait evidence, operators/coercions, and their helper frontier
- Stage boundaries and connection to existing comptime work
- Public inputs containing function values and existing heaps

Add representation, compilation, Core type checking, tests, and correspondence lemmas together for each feature.
If native mapping/proxy support or similar changes are considered necessary, update the comparison in Section 3.4 before changing the implementation.
State the associated scope of changes to Core, host, Wire, and proofs.

Completion criteria: Core can execute every typed-source runtime feature available at the start of migration, with no successful cases exclusive to the old path.
For T0 prescribed failures, also check compatibility through regressions for categories, evaluation order, and side effects up to failure.

### T5: Unify the Public API and Remove the Old Evaluator

Dependencies: T4 and verification of all features, including T0 prescribed failures and side effects up to failure as well as successful results.

Deliverables:

- Consolidate backend selection and duplicate carriers in `SourceCompiler`.
- Move deep input validation and code-ownership validation to the new Core boundary.
- Migrate tests, proofs, and umbrella imports depending on the old runtime.
- Remove `SourceTypedRuntime` execution features and public types specific to the old runtime.
- Update README, public API migration examples, and treatment of Core Wire format changes.
- Finalize the extended Wire format and public API based on T3 verification and T4 extension decisions.

Completion criteria: Satisfy the first-goal checklist in Section 10.

### T6: Complete Meaning-Preservation Proofs for the Full Compilation Pipeline

Dependencies: T3/T4 lemmas. May begin before T5.

Deliverables:

- Preservation and reflection of successful execution and failures for all syntax.
- Connect typing and semantic correspondence of generated helper libraries to the full compilation theorem.
- Correspondence of specialization substitution, reachability, and evidence.
- Correctness of comptime transformations actually applied.
- A connection enabling use of the main theorem from successful public compilation and input validation.
- A final theorem leaving no unproved pass correctness as external assumptions.

Completion criteria: Satisfy the second-goal checklist in Section 10.

### Division of Work

Multiple contributors must not independently change Core representations. Assign Core type, store, and result representations to one owner.
After fixing that boundary, work on data operations, control compilation, specialization/evidence, and correspondence proofs can be divided.
Changes to the Core kernel and changes to helper libraries generating ordinary Core code are separate responsibilities.
Agree on shared type and theorem signatures first, and avoid concurrent editing of the same foundational files.

## 10. Completion Criteria

### First Goal: Remove Direct Runtime Evaluation

- [x] The T0 feature inventory contains no item executable only through the old path.
- [x] Regression checks pass for failure categories, evaluation order, and side effects up to failure for T0 prescribed failures.
- [x] All runtime expressions, statements, and calls execute through Core.
- [x] The Core evaluator contains no `TypedSource` interpretation or calls to the old evaluator.
- [x] Helper libraries are ordinary Core code and conceal no separate host-side evaluator for mappings or similar features.
- [x] Every Core addition has a comparison and reasons for adoption, with no duplicated mechanism for recursion or source control.
- [x] Mappings and proxies use helper functions and data, or the comparison and reasons for dedicated features are recorded.
- [x] Runtime values retain no closures interpreting the source node table.
- [x] No values, states, or results specific to `SourceTypedRuntime` remain in the public API.
- [x] Validation of public-input references, heaps, and closures is preserved.
- [x] Specialization and preparation are separated from the old evaluator.
- [x] The direct-evaluation work retained as comptime is explicitly listed.
- [x] Core checker, bounded safety, host, ContractRuntime, and Wire are updated.
- [x] Before finalizing Wire and the public API, type safety and meaning-preservation lemmas for the minimal path and comparisons of extension candidates have been checked.
- [x] Tests for existing features, the build, and kernel policy pass.

First-goal assessment (2026-10-01, `a3168382`): Complete. An independent re-audit of the dependency paths and actual definitions of public `SourceCompiler` / `SourceCoreExecution`, registration of existing T0 test groups, and the public initial-heap/snapshot/handle boundaries found no concrete unresolved items. Full `lake test` passed with 8338 jobs and all execution tests, and kernel policy passed. See the [implementation record](core-runtime-unification-progress.md) and [API migration record](core-runtime-unification-api.md) for details.

This assessment concerns the TypedSource runtime backend and public execution path. An independent old `Syntax.Expr/Term` evaluator for fragment proofs remains in an isolated module, unreachable from the shared public compiler / Current dependency paths. The agreed comptime evaluator remains in compilation preparation. Meaning preservation across the full pipeline for the second goal remains ongoing.

### Second Goal: Meaning Preservation Across the Full Compilation Pipeline

- [ ] Preservation and reflection of successful execution are proved against independent semantics.
- [ ] Correspondence of prescribed failures in scope and states at those failures is proved.
- [ ] A heap relation including shared captures, allocation, and local instantiation is defined and proved.
- [ ] Correctness of specialization, evidence, and actual comptime transformations is connected.
- [ ] For mapping key comparison, lookup, update, defaults, and proxy representation, semantic correspondence of helper libraries or adopted Core primitives is connected.
- [ ] The final theorem does not require callers to assume unproved meaning preservation of passes themselves.
- [ ] Malformed raw `CheckedProgram` values or arbitrary input closures are not trusted unconditionally.
- [ ] The relationship between declarative input validity and conditions guaranteed by the executable public boundary is explicit.
- [ ] The document does not incorrectly claim proofs of equal fuel, successful termination of all programs, or equivalence of infinite traces.
- [ ] The build and kernel policy pass without proof escape hatches.

## 11. Verification

### 11.1 Priority Regression Cases

- Recursion, mutual recursion, fuel exhaustion, and resumption with additional fuel.
- Self-cell recursive closures and multiple closures updating the same variable.
- Use of locally polymorphic functions at different types and shared captured state.
- Returned closures and validation in initial heaps, accepted global / builtin function arguments, rejection of unsupported closure arguments, and rejection of invalid function handles from different artifacts.
- Higher-order values in nominal data, pattern matching, and payload types.
- Mapping copies, nesting, defaults, proxy keys, and update order.
- Type-specific mapping key comparison, proxy types that must remain distinct despite representation changes, and registration/reuse of helper functions.
- Arguments with side effects, assignment-target indices, coercions, and short-circuit expressions.
- For continue and post, break, early return, and captures after scope exit.
- First-class constrained functions, globals discovered inside selected methods, and helper frontiers.
- Integer signs, bitwise operations, Word conversions, and comptime acceptance/rejection.
- Uninitialized reads, mappings without defaults, and altered boundary inputs.
- Existing host, transactions, commit/rollback, suspension, and resumption.

Differential tests during migration compare values, observable state, and failure categories.
Do not judge by equal fuel or string equality of entire raw heaps.
Repeated executions with different fuel are supplementary tests and do not replace meaning-preservation proofs.
When comparing Core primitives and helper libraries, record generated code size, execution steps, and elapsed time separately for the same examples.
Do not conclude that total burden is smaller merely because there are fewer syntax forms.

### 11.2 Basic Commands

Run from the repository root.

```sh
lake build
lake test
node scripts/check-kernel.mjs
```

Lean warnings are treated as errors.
Kernel policy rejects `sorry`, `admit`, `partial`, `unsafe`, `axiom`, and similar constructs in semantic modules.
Do not fill unproved declarations with escape hatches even at intermediate stages. Record unfinished claims in the design/tasks, and add lemmas as they are proved.

Main tests to migrate:

- [SourceCompiler](../../Solcore/Test/SourceCompiler.lean)
- [SourceTypedRuntime](../../Solcore/Test/SourceTypedRuntime.lean)
- [SourceTypedRuntimeStateInteractions](../../Solcore/Test/SourceTypedRuntimeStateInteractions.lean)
- [SourceTypedRuntimeOperators](../../Solcore/Test/SourceTypedRuntimeOperators.lean)
- [SourceTypedRuntimeFirstClassEvidence](../../Solcore/Test/SourceTypedRuntimeFirstClassEvidence.lean)
- [SourceStagedRecursion](../../Solcore/Test/SourceStagedRecursion.lean)
- [Tests/Main](../../Tests/Main.lean)

Tests may be renamed or split, but removing tests from imports alone does not complete feature migration.

## 12. Procedure for Resuming Implementation

1. Check this document's current implementation status, the opening and latest additions of the [implementation record](core-runtime-unification-progress.md), applicable AGENTS.md, and `git status`. Preserve other inference/parser work.
2. Use the latest committed verification point in the current status table and inspect subsequent proof changes. Shared registrations and owned Values/Entries/State are committed; rerun appropriate checks for later changes.
3. Thread the concrete reached state through ordered expressions, actual marked allocations, lexical tails and five-way imperative flow. Reuse the existing static Tree/CatalogSites and Source/Core size proofs.
4. Retain actual SourceReceipt, complete type substitution and capturePrefix, and the same Source/Core value model and Entry. Do not force actual general captures of nested lambdas into existing theorems limited to prefix0.
5. Call restoration installs saved frames in the reached AuthorityPool. Preserve records added during callee, argument, or body evaluation, shared and distinct frames, all captures, and snapshots.
6. Connect the actual lowerer's callee and ordered arguments, original Source derivations, and strict child sizes in original Core to the existing single mutual induction. Static child-expression authentication and template permission do not replace body meaning preservation.
7. Integrate general indirect calls, lambdas, methods/coercions, and local instantiations into the same relation, and supply final assumptions from actual specialization, evidence, and staging passes.
8. From public compilation success and input validation, complete preservation of successful results, language failures, and all state against independent Source before pre-evaluation, together with reflection of finite completion of the original Core. Leave no unproved body/pass laws in the final theorem.
9. Complete required verification and shared registration for each logical unit, then commit. Reflect proof scope, remaining assumptions, and actual completion results in the progress record. Do not mark complete until the second goal in Section 10 is satisfied.

If implementation changes the design, record the reasons, affected theorems, compatibility, and verification results in this document or adjacent records.
If reducing the goals, removing existing features, or introducing new source-language semantics becomes necessary, state these as matters to confirm with the user.

## Shared function model and native compiler foundations (2026-10-10)

The proof model now retains positive closure and named origins through their actual compiler associations. Each origin keeps the original bootstrap owner, ordered keys, captures and full Source dictionary. Formation and map/world extension preserve these receipts. Bootstrap transport uses the same initialized store and keys.

Selected native occurrence collectors retain the actual compiler site, diagnostic issuer, child typing and lambda tags. Typed named calls and the indirect closure/global/builtin dispatcher consume the same retained argument and body receipts and restore the actual caller. Source and native execution grades remain independent.

This unit supplies proof interfaces and compiler facts. Concrete accepted argument producers and the strict expression/body induction still need to discharge their hypotheses. Actual arity, stage rejection, reached diagnostics and the remaining compiler alternatives must be proved at genuine occurrences before the final public semantic preservation theorem can be assembled.


## Paired compiler typing and constructive call packets (2026-10-10)

The paired lexical, match and imperative collectors derive actual-context and fixed-prefix child typing independently from the same accepted lowering. Named profile extraction keeps the original actual administrative context, compiler Tree and diagnostic issuer; its fixed body typing comes from the same cached code and authentic context support.

Closure and named argument factories now derive their packets from accepted call branches, preserving original Source argument types, physical parameter count, bootstrap owner, selected dictionary and the same argument post. Selected ordinary and principal lambda producers retain their literal compiler receipt, issuer and body read budget. Eligible body flow ports request the expression hypothesis only at a genuine ordinary Header with caller evidence or an actual selected principal with its dictionary. They retain the reached pool and independent Source/native grades.

The final numeric induction over eligible expressions and bodies still has to assemble these conditional ports and supply the authentic occurrence, syntax, ledger and receiving-diagnostic factories throughout the actual compiler alternatives. Ordinary Dynamic execution still requires genuine stage-guard acceptance at each reached indirect call. A rejected stage guard has its own Source staging judgment at the callee post, before arguments; full recursive rejection coverage remains unfinished. Specialization/evidence/comptime composition, generalized cells, general failures and export errors, and the final public theorem remain incomplete. The estimates stay 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure completion.

## Accepted indirect calls and caller restoration (2026-10-10)

The accepted closure, global and builtin branches now preserve and reflect the whole indirect call through the original callee, ordered arguments and application. Each branch retains the actual first-stage acceptance and second-stage physical arity checks. Constructive argument factories keep the selected owner or dictionary and the exact argument post. Application restores the saved caller in the same returned pool. Builtin application uses its original primitive proof; user application still consumes strict closure or named body hypotheses.

Named body profiles retain both actual-context and fixed-prefix child typing at the original parameter-entry state. The selected Header action supplies the contextual root receipt with the same compiler issuer, source, scope, reason and lowered expression. Positive lambda recipes construct their compiler packet at the retained body read budget and keep the ordinary Header or selected principal dictionary. Callee reflection preserves either the represented value or the ordinary failure at the reached caller state. Source and native grades remain independent.

The numeric induction joining eligible expressions and function bodies remains unfinished. Static occurrence, syntax, ledger and receiving-diagnostic factories still need complete compiler coverage. The accepted-call results require the actual runtime gates; they do not establish acceptance at every reached call. A rejected first-stage guard remains a separate Source staging outcome at the callee post, before arguments. Its scoped diagnostic and complete recursive coverage are next. Second-stage rejection occurs after argument evaluation and remains a separate pending branch. Specialization/evidence/comptime composition, generalized cells, general failures and export errors, and the final public theorem remain open. Estimates stay 100% for the first objective, about 70% for the second and about 85% overall.

## Staged call dispatch and terminal closures (2026-10-11; normally verified at `6c165e33`)

`staged-call-dispatch-and-terminal-closures` is committed and normally verified at `6c165e33`. The twelve proof Sources contribute 106 complete module-owned declarations and 42 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19434 to 19540: 106 additions, no overlaps and no removals.

The registered build passes 5786 jobs. The independent selected dependency BEFORE contains 2250 modules; the compiled native environment contains 2262. The complete normal module snapshot changes from 5707 to 5719 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint uses these original sixteen closed receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `0799ac`; code commit `6c165e334b61a044e480e96ea9da7d414894817c` closed at `215010`. The saved `staged-call-dispatch-and-terminal-closures-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `dc631c0c098aee0e8a9fec163b3141d0142c3cb429aa78878f272d15a57c1ee3`. The corrected summary distinguishes the selected BEFORE environment of 2250 modules from the complete pre-install snapshot of 5707 module rows.

The common decoded fault relation uses the actual receiving table. Semantic assignment/arity failures retain their decoded error and token. First-gate stage failures retain the exact invocation, call, failing scope and token. First-gate preservation uses the strict callee result and original stage-lowering proof at the reached callee state. Reflection consumes the authentic rejected prefix. Argument-fault preservation constructs the successful first gate and uses the concrete ordered-argument fold; effects and caller admission stay attached to the reached argument state.

The native fault dispatcher inverts the actual parent through the existing callee/argument prefix once. It returns the callee, first-gate or argument fault result with its Source trace and reached post, or retains the actual right application suffix. A separate second-gate classifier derives physical arity from the original selected row. A mismatch produces semantic arity failure after evaluated arguments. Named payloads retain authentic Header/NamedSourceAt provenance. Equal count retains the physical row fact for the application proof.

The application-suffix ports normalize the literal payload application and preserve the unchanged argument store and strict native application child. Builtin argument rows use original callee admission, authentic BuiltinAt and equal physical count before identifying Source/native packs. They retain exact ordered scalar representations at the same argument map/world. The builtin whole-parent composition is outside this package.

The selected lambda compiler factory derives the actual accepted terminal receipt from its retained NativeLambda recipe. Terminal Source-body inversion extracts the genuine child from the whole body trace. Supported body preservation uses that child and strict expression preservation for accepted returnSome or singleton expression-tail bodies. Closure invocation/application ports install parameters and restore the saved physical caller once, retaining the full body post and caller PostAdmission for values, semantic faults and nested stage faults. Caller context support follows from genuine closure-frame and caller runtime validity.

Strict body hypotheses still need their numeric construction. Authentic child Scope/source identity, original typing, compiler certificates, SourceView and entry admission remain explicit where required. Source and Core grades are independent, and all returned relations, transient effects, heaps/stores and administrative frames refer to the actual reached state.

Retained-callee argument prefixes (258), builtin whole-parent reflection/preservation (134/154), terminal body typing (96), metadata-body bounds (131), parameter-admission and concrete body-join drafts, and retained-callee fault/builtin dispatch drafts (127/216) are outside this twelve-Source checkpoint.

The numeric staged expression/argument/application/body induction, authentic static factories for complete compiler alternatives, general call/body dispatch and remaining recursive Source grammar remain unfinished. Specialization, evidence and comptime composition, general failure/export-error correspondence and the final public all-pass theorem are open. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure semantic completion.

## Staged parent and terminal lambda producers (2026-10-11; normally verified at `6844f7b0`)

`staged-parent-and-terminal-lambda-producers` is committed and normally verified at `6844f7b0`. The twelve proof Sources contribute 74 complete module-owned declarations and 26 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19540 to 19614: 74 additions, no overlaps and no removals. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews.

The registered build passes 5798 jobs. The independent selected dependency BEFORE contains 2218 modules; the compiled native environment contains 2230. The complete normal module snapshot changes from 5719 to 5731 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint will use those original sixteen receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `cc2cfe`; code commit `6844f7b0f788069d858f42a29343c7c5900829ba` closed at `5cea3d`. The saved `staged-parent-and-terminal-lambda-producers-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `bf9f5a5635e9876005265366485f4f31bad0d297b3478785aa453b778561c456`. The selected BEFORE environment of 2218 modules is separate from the complete pre-install snapshot of 5719 module rows.

The retained argument prefix keeps the callee's actual post and raw Source value typing before argument effects. Reflection then either returns the exact callee, first-gate or argument fault post, or keeps the successful application suffix with that callee evidence. Preservation constructs the callee and successful ordered arguments at their real successive states. Raw ordered argument typing follows the original successful Source traces.

For builtins, the actual codebook row and physical count recover the original signature and represented scalar arguments. The selected preservation and reflection proofs use the original primitive and application suffix once, constructing the whole parent and full caller post. Reflection dispatch handles accepted builtin application and physical-count rejection while retaining the actual user application prefix for later composition.

The strict child hypotheses are induction assumptions for the actual executed child: its Source trace grade is smaller for preservation, or its native evaluation grade is smaller for reflection. The shared numeric induction must still construct these hypotheses; the static compiler receipts do not contain a completed execution law.

The terminal closure route derives typing from the original return-some or singleton-tail body. Actual parameter installation constructs entry admission and stable histories. The retained Code and registry derive the child's Source scope; metadata and compiler receipts identify the genuine used child. Body and application preservation/reflection use strict expression hypotheses and restore the saved caller once. Source and native grades remain independent; the returned heap, store, pool, relation and PostAdmission are the actual reached ones. Semantic and stage failures keep their original tags and scopes.

The shared numeric induction for expressions and function bodies, general user and named application dispatch, full statement grammar and authentic compiler occurrence coverage remain open. Specialization, evidence and comptime composition, general failures/export errors and the final public all-pass theorem are unfinished. Finite proofs for literals and grouping, the separate closure argument-typing producer and the whole builtin preservation dispatcher are outside this checkpoint. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.

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

## Staged call parent dispatch bounds (2026-10-11; normally verified at `910e3e1d`)

`staged-call-parent-dispatch-bounds` is committed and normally verified at `910e3e1d`. Its seven proof Sources have 117 complete module-owned declarations and 19 selected interfaces. Every native and normal strict Source log is empty. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete 19-interface API logs are byte-identical. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews; the tooling has independent Root and Entry reviews.

The cumulative census is 19730 from 19614: 116 additions, one prior overlap and no removals. The overlapping generated helper, `ContextualCellOrigins.functions.congr_simp`, is literally unchanged. Build 5805 passes. The selected dependency BEFORE contains 2228 modules and the compiled native environment 2235; the complete normal snapshot changes from 5731 to 5738 rows. Seven new Source/olean/ilean triples are installed. Only the existing `CoreLowering` object pair changes, within the nine-module dependency cone and nine actual rebuilds. All 4985 protected artifacts remain unchanged.

The eleven original normal validation receipts are closed with exit code zero. Normal validation closed at `ce446f`; code commit `910e3e1d9f18c1fde867b7d56ef3321b5a0dd943` closed at `83f21b`. The saved `staged-call-parent-dispatch-bounds-checks.json` has SHA-256 `9360372c1f3e5abb9ab873e023f542f20bcfd58b301b46851ee5d9e7a108df4c`. Metadata finalization reuses the original eleven closed validation receipts without repeating their kernel checks.

The Source prefix dispatch constructs the real callee, first-gate and ordered argument failure parents, or retains the successful application prefix. Builtin preservation dispatch consumes the actual callee and ordered values once: an accepted physical count uses the original primitive parent, while a mismatch produces the authentic receiving semantic arity fault at the argument post. The user branch retains the same application prefix.

For closures, the successful argument producer derives original Source arity and contextual binder rows at the actual callee and argument heaps. Terminal application preservation and reflection use the genuine Code, support and selected body scope, consume their strict body child once, and restore the saved caller at the actual returned pool. Closure/global dispatch handles a closure's physical mismatch at the same reached argument state. It retains the global prefix for its independent named arity and application consumer.

Completed parent results keep the reached heap, store, map, world, relation and caller PostAdmission. A successful retained application prefix keeps reached Admission while its whole application remains open. First-gate stage failure and second-gate semantic arity failure retain different Source constructors, tags and scopes. Physical arity comes from the actual Source bindings and codebook row.

The strict child hypotheses describe the actual executed child: preservation uses a smaller Source trace grade, and reflection uses a smaller native evaluation grade. The shared numeric induction must still construct these hypotheses. Source and native grades are independent, and static compiler receipts retain authority rather than a completed execution law.

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


## Finite staged expressions and named call parents (2026-10-11; normally verified in two code commits)

`staged-finite-expressions-and-named-call-parents` is committed and normally verified in two logical code groups. The finite expression commit `5a5bdeffec4008cb4d6e972224b90b8a2df048db` contains four proof Sources, 102 module-owned declarations and 32 selected interfaces. The whole-call and named-call commit `ef75b2c3b86a2e2bc140ea274ae9ff55d86c99d2` contains seven Sources, 89 declarations and 18 interfaces. Together they add eleven Sources with 191 complete owned declarations and 50 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native strict logs and all eleven normal strict logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 191 declarations. The complete 50-interface API logs are byte-identical: 112327 bytes, SHA-256 `df758c72f09c97d7e7f17fee86fd94d67595c6adf117e6103b2bd158aa7f4058`. The independent selected BEFORE contains 2240 modules and the compiled native environment 2251.

The cumulative census grows from 19730 to 19921: 191 additions, no prior overlaps and no removals. Build 5816 passes. The complete normal snapshot grows from 5738 to 5749 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The original package tooling has independent Root and Entry reviews. The separate snapshot-copy successor was authored by Root and independently reviewed by Entry and Formal. Both code commits closed with exit code zero at actual receipt `0cb4aa`; normal validation records fifteen original CLOSED0 receipts. Its complete checks have SHA-256 `d48582c7b3291b9093a30b010b37f4805312f1b812e93c272b08ec96ed21d8cc`. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

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

## Finite reads and named body composition (2026-10-11; normally verified in two code commits)

`staged-finite-reads-and-named-body-composition` is committed and normally verified in two logical code groups. The finite read/body commit `6d4fcbd855b387845dba4ca511ea66d6dde0c020` contains six proof Sources, 64 module-owned declarations and fourteen selected interfaces. The closure/named commit `ed30cd3be8a2f9b11e5ff21387a19f8fcfdbde99` contains five Sources, 56 declarations and twenty-two interfaces. Together they add eleven Sources with 120 complete owned declarations and 36 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native and eleven normal strict Source logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 120 declarations. The complete 36-interface API logs are byte-identical: 108225 bytes, SHA-256 `79a0c159998685d6e97f3c1c1302f389d6ffcba81df469023faf1e62582b2e2c`. The independent selected BEFORE contains 2274 modules and the compiled native environment 2285.

The cumulative census grows from 19921 to 20041: 120 additions, no prior overlaps and no removals. Build 5827 passes. The complete normal snapshot grows from 5749 to 5760 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The selected tooling has independent Root and Entry reviews; the inherited snapshot-copy change retains its genuine Entry and Formal reviews. Both code commits and all fifteen original normal validation receipts are closed with exit code zero. The complete checks have SHA-256 `ce9c5751d088be73b668e9f76a8f64ce7f2c126d873dc8ae03102f7ccf498ed6`. Metadata finalization reuses the original fifteen closed normal validation receipts without repeating their kernel checks.

The finite fold now includes real-cell reads alongside literals, transparent grouping and ordered pairs. It builds the accepted compiler tree and literal-site certificate once, then constructs each child's meaning internally. A read uses its genuine lowered-read receipt and raw Source typing; generalized local reads remain outside this branch. The represented result, lazy mapping writes, full returned pool and reached caller post are retained. Preservation uses the independent Source trace grade. Reflection uses structural descent through a transparent group at the same native grade, and strict native descent only at actual evaluated bind children.

Named read diagnostics come from the actual prepared Header, diagnostic receipt and receiving issuer. The uninitialized-read interpretation is indexed by the certified read occurrence, including its binder, span and reason token; decoding does not manufacture a Source fault. The Header and accepted terminal receipt supply the real child typing and finite compiler tree. The finite named body producer calls this fold directly in both directions, removing its external child-expression meaning and arbitrary certificate callback. It keeps the actual parameter entry and selected body scope, and carries the returned heap, store, map, world, relation and PostAdmission.

The closure factories retain an exact accepted body child and its authentic static support. Their application consumers still require meaning for the actual selected child. Named invocation preservation constructs the real parameter allocation, uses the selected terminal body, and restores the caller at the returned pool. Named argument rows retain the original selected node and metadata, the Source argument types and the independent physical-count receipt. The literal named carrier supports both application directions at those exact endpoints. These generic invocation/application proofs still consume strict child hypotheses; they do not yet instantiate the new finite body producer.

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

## Finite call bodies and global joins (2026-10-11; normal verification complete)

The selected `staged-finite-call-bodies-and-global-joins` work contains nine proof Sources and 37 selected interfaces. The three generic parent/global joins expose seven interfaces; the two static closure-child producers expose twelve; the four finite call/body proofs expose eighteen. Each selected Source has an isolated author pass and two genuine nonauthor Source reviews. Normal verification passes for all nine Sources, 177 module-owned declarations and 37 selected interfaces. The generic joins contribute 68 declarations, the static closure-child producers 27, and the finite call/body proofs 82. The three code commits are `c37620a6`, `b568df64` and `ef72f57e`.

Preservation constructs native execution from an actual Source derivation. Reflection reconstructs a Source derivation from native completion with an independent Source grade. Both retain the actual reached heap, store, map, world, relation and returned pool. Completed application and parent results retain full caller PostAdmission, including the original tag and scope of nested stage failures.

Finite named invocation and application now call the finite named body producer directly at the actual parameter entry. Preservation retains every actual Source-selected body scope; reflection retains the authenticated Header/descriptor-selected scope. The proof runs the original parameter installation and body prefix once, uses the finite read/literal/group/pair body once, and restores the saved caller at the actual returned pool. It no longer takes an external child-expression meaning hypothesis or arbitrary certificate callback.

The finite named parent derives typed Source arguments and represented native parameters from the authentic ordered rows and independent physical-count receipt. Its accepted suffix uses that same finite application once. The finite global dispatcher recovers the real Header, dictionary, capture and Source frame from the positive named payload. It either runs the finite parent at the selected equal count or proves the actual Source semantic arity failure with the exact receiving diagnostic at the reached argument post. First-gate `Failure.stage` and second-gate semantic arity failure remain separate.

The finite closure body proof retains a fixed accepted BodyWith with both compiler-view and original-Source trees. Authentic frame typing and the selected Source scope provide the raw child type; the exact original child certificate feeds the finite evaluator. Its application proofs construct read/literal/group/pair child meaning internally and retain the restored caller post. Genuine finite-family compiler transport, terminal/read policy, certified read-fault interpretation, registry extension and runtime premises remain explicit.

The generic named parent/global joins and whole terminal indirect-call proof connect actual callee and ordered-argument prefixes to the original payload application and native suffix. They keep transient effects and the complete restored caller post. These generic ports still require authentic terminal factories and strict child induction hypotheses: those hypotheses assert child execution only below the enclosing numeric budget.

The static closure-child producers retain the exact accepted child in both original and compiler Sources, then restrict a requested child certificate to that literal occurrence. They do not infer raw typing from a metadata view or turn an arbitrary static certificate family into finite semantics.

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

## Finite closure dispatch and arbitrary tuple folds (2026-10-11)

`staged-finite-call-dispatch-and-tuple-folds` is normally verified in three code commits: `fb42f8c2` adds the finite closure parent, static transport and terminal packet (three modules, thirteen interfaces); `280557de` adds the arbitrary tuple fold and compiler issuer (two modules, six interfaces); `a48286e4` connects the whole-call and user dispatch branches (six modules, eight interfaces). The eleven modules expose 27 selected interfaces and 156 owned declarations. Each Source has two genuine nonauthor Source reviews.

All eleven fresh private and normal strict Source checks closed with empty output. Complete TYPE/AXIOMS and API audits passed, and the private and normal API logs are byte-identical (142486 bytes). The native import closure grew from 2319 to 2330 modules. The registered build completed 5847 jobs; normal Source/BOTH rows grew from 5769 to 5780. The only changed existing object was `CoreLowering`; all eleven new modules have regular objects, all thirteen modules in the reverse dependency cone were rebuilt, and 4985 protected artifacts stayed unchanged. The cumulative census grew from 20218 to 20374, with 156 additions, no overlap and no removals. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

The finite closure parent constructs application meaning from the actual contextual Association, parameter entry and accepted finite body. Public syntax and certificate transport cross only genuinely reached, unedited compiler-view occurrences; original child typing comes from the real parameter frame. The terminal packet is manufactured from that same accepted tree, its read policy, actual registry-selected body scope and certified read-fault interpretation. These proofs retain the returned callee pool and restore the saved caller. They do not require an external body-expression meaning hypothesis.

The arbitrary tuple fold supports nested finite tuples of any arity, including repeated child identifiers, in their original order. It internally constructs the read/literal/group/pair leaves and evaluates each next child at the actual intermediate caller state. Preservation uses the actual Source grades, including the legacy two-element pair rules. Reflection uses structural child descent when a singleton's native packer erases the tuple wrapper and keeps the same grade. The compiler issuer extracts this certificate from the actual accepted action and ordered child vector, with original raw typing and static policy inputs; no leaf execution law is supplied.

The finite closure user dispatch handles the physical-count mismatch at the real argument post or applies the retained finite closure at equal count. The whole-call preservation and reflection ports keep callee and ordered-argument effects, exact receiving faults and full restored caller PostAdmission; their global prefix feeds the existing finite named route. The final join combines those branches. Caller callee/argument induction hypotheses still remain explicit: these assert meaning only below the enclosing measured budget. Source and native grades remain independent, and first-gate `Failure.stage` keeps its original failing scope separately from semantic arity failures.

| Validation item | Current state |
| --- | --- |
| Proof selection | Eleven integrated modules, 156 owned declarations and 27 selected interfaces. |
| Native checks and literal audit | Eleven empty strict checks; complete TYPE/AXIOMS and byte-identical private/normal API logs; import closure 2319 → 2330. |
| Normal validation and build | Fifteen closed validation receipts; 5847 build jobs; normal Source/BOTH rows 5769 → 5780; thirteen affected modules rebuilt; 4985 protected artifacts unchanged. |
| Census and code commits | 20218 → 20374 (+156, no overlap or removals); `fb42f8c2`, `280557de`, `a48286e4`. |

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

The compiler issuer starts from the actual accepted lowering action and original Source typing. It recovers the original indirect-call node, raw callee type and ordered argument types before building the child certificate. The certificate retains groups, tuples and indirect calls recursively, including groups around new tuple or call nodes. Argument entries keep their original order and repeated identifiers.

Structural induction on that certificate proves both preservation and reflection at every actual reached state. Child execution hypotheses are constructed internally. Group reflection and erased singleton tuple packing can use the same native grade; induction follows the child certificate rather than assuming a smaller execution grade. An indirect call uses the actual callee entry and ordered argument tree, then the existing finite whole-call proof once. Results retain the reached heap, store, map and world, exact staged fault scope, returned pool, caller relation and PostAdmission. Source and native grades remain independent.

The compiler-facing wrapper constructs its root certificate internally. Its `CallsReady` premise refers only to call receipts reachable from that exact generated root. Actual preparation, Source view, sidecar, guard frame, selected Header or Association, receiver, registry extension, diagnostic interpretation, ledger and coverage remain static or runtime premises. Called bodies still use the existing finite read/literal/group/binary-pair family. No public child execution or arbitrary body meaning callback is supplied.

General recursive called bodies, the shared numeric expression/application/body family, other expression and statement forms, and specialization/evidence/comptime composition remain unfinished. The final public theorem across all compiler passes is incomplete. Estimates remain 100% for runtime unification, about 70% for meaning preservation and about 85% overall.

## Selected callers and recursive terminal body proofs (2026-10-11; normal verification complete)

The selected `staged-selected-callers-and-recursive-body-bounds` unit is normally verified in `7db7dd2c`, `dda78f9c`, `31549a17`: sixteen proof Sources, 376 owned declarations and 53 selected interfaces. Each Source has an isolated strict author pass and two independent nonauthor Source reviews, excluding contributing repair authors.

All sixteen native and normal strict Source checks have empty logs. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete API logs are byte-identical (215570 bytes, SHA-256 `40020d9c5a18129f8d398856d30533f3fbbb94a7d853a9d9bc783fc51eb820e9`). The selected native environment grows from 2317 to 2333 modules. Build 5869 passes; the normal Source/BOTH snapshot grows from 5786 to 5802 rows. The cumulative census grows from 20572 to 20948: 376 additions, no overlap and no removals. All 18 modules in the affected dependency cone are rebuilt and all 4985 protected artifacts remain unchanged.

Metadata finalization reuses the original twenty closed validation receipts without repeating their kernel checks.

The call chain selects one authentic terminal packet for the actual named Header or contextual closure Association. Its certificate is narrowed to that packet's original expression, scope and lowered child. Closure and named dispatch retain the real argument order, physical arity, staged rejection and selected scope. The accepted application keeps its actual returned pool and restores the saved caller, including caller relation and PostAdmission.

The selected caller fold constructs callee and argument preservation/reflection internally from the actual recursive certificate. Group reflection and erased singleton tuple packing may keep the same native grade; their induction follows the child certificate. Ordered argument entries retain repeated identifiers and use the actual intermediate state. Numeric strong induction then constructs meaning for supported selected terminal bodies at strictly smaller semantic budgets. The caller-from-bodies adapter consumes that constructed body family. These endpoints require no external child execution or body meaning callback. Source and native grades remain independent.

Static body support retains the original Source root, raw context, actual Header or Association body context and every genuinely selected child scope. The compiler support issues a certificate from the actual accepted original action and indexes call readiness by that exact proof. The compiler-view transport proves accepted lowering on the original Source from paired policies, reached unedited metadata and the real compiler action. Compiler callbacks, reason functions, original typing/declarations, receiver, registry extension, diagnostics, runtime ledger and coverage remain explicit authority inputs.

| Logical code group | Proof Sources | Selected interfaces |
| --- | --- | --- |
| Selected terminal dispatch | 9 | 14 |
| Caller and original Source authority | 5 | 27 |
| Numeric body induction and caller composition | 2 | 12 |

The three dependency-ordered code groups are committed at `7db7dd2c` (9 Sources / 14 interfaces); `dda78f9c` (5 Sources / 27 interfaces); `31549a17` (2 Sources / 12 interfaces).

This closes the supported selected terminal body/caller recursion. Constructing these authentic roots and authority packets for every compiler path remains unfinished. Wider expression and statement grammar, unrestricted function bodies, complete receiving-diagnostic coverage, specialization/evidence/comptime composition and the final public theorem across all passes are still open. Runtime unification remains 100%; meaning preservation remains about 70%, with an equally weighted overall estimate of about 85%. These estimates describe completed work, not interface counts or remaining time.
