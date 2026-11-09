import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCore.Internal.CallableIndexed
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.Test.SourceSemantics.CoreLowering.Callable.LambdaViews
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation

/-!
# Indexed lambda tests

Formation and runtime of indexed lambdas.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaCalls
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaInvocation CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
section Proof
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem completed_call [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Core.Value} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inRight .word result) finalStore) :
    ∃ sourceResult after finalMap finalWorld,
      Dynamic.CallableApplies program callerContext callerEvidence function.evidence before (.closure function) arguments sourceResult after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType sourceResult result code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | value payload =>
    cases execution with
    | value called => exact ⟨_, after, finalMap, finalWorld, called, payload, finalHeap, caller.read⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem failed_call [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {token : Word} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inLeft code.receipt.resultCore (.word token)) finalStore) :
    ∃ reason after finalMap finalWorld,
      Dynamic.CallableFaults program callerContext callerEvidence function.evidence before (.closure function) arguments reason after ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | fault represented =>
    cases execution with
    | fault failed => exact ⟨_, after, finalMap, finalWorld, failed, represented, finalHeap, caller.read⟩
end Proof

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function make(seed: Word) returns (F) { let unused: Word = 99; return lam(item: Word) -> Word { let converted = item + seed; { let nested = converted + wordFromInteger(0); nested; } if (converted < seed) { return seed; } return converted; }; }",
    "function fail(seed: Word) returns (F) { return lam(item: Word) -> Word { let table: mapping(Bool => Word); let loaded = table[item == seed]; let converted = item + seed; let gap: Word; return gap; }; }",
    "function two(seed: Word) returns (function(Word, Word) returns (Word)) { return lam(first: Word, second: Word) -> Word { return seed + first - second; }; }",
    "function zero(seed: Word) returns (function() returns (Word)) { return lam() -> Word { return seed + wordFromInteger(0); }; }",
    "function unitMaker() returns (function()) { return lam() { { let item = wordFromInteger(0); item; } }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"missing lambda call fixture {name}")

/-- Each resumed run starts from the actual suspended machine state. The
comparison includes the complete store, including parameters and body effects. -/
private def resumed (start : Core.State) : IO Core.StatefulRunResult := do
  let expected := runStateful 500000 start
  for spent in [0, 1, 17, 49, 111, 317] do
    let observed := match runStateful spent start with
      | .outOfFuel checkpoint => runStateful 500000 checkpoint
      | completed => completed
    SourceCompilerFeatureSupport.require (observed == expected) s!"lambda call resume changed value/store at {spent}"
  pure expected

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "lambda call checker" (checkProgram workspace)
  let names := ["make", "fail", "two", "zero", "unitMaker"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"lambda call worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "lambda call base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "lambda call indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let word := Word.ofNatModulo
  for (name, key) in names.zip keys do
    let inputs := if name == "unitMaker" then [] else [.word (word 3)]
    let completed ← SourceCompilerFeatureSupport.get "lambda maker" (prepared.runSource key inputs 500000)
    match completed.result.native.observation with
    | .succeeded native store =>
      let packed := if name == "two" then .pair (.word (word 10)) (.word (word 2))
        else if name == "zero" || name == "unitMaker" then .unit else .word (word 10)
      let result ← resumed (.initial CallableIndexedLambdaCalls.applyPayload [native, packed] store)
      match result with
      | .done value finalStore =>
        SourceCompilerFeatureSupport.require
          (finalStore[0]? == some (encode prepared.ancestry.layout.frame .empty))
          "lambda payload call did not restore the original caller frame"
        if name == "zero" then
          -- The call only makes the marked copy of its captured seed: the
          -- allocator's entry, the marker naming the copied snapshot cell, and
          -- the copied payload.
          let seed : Core.Value := .inRight .unit (.word (word 3))
          let copied := match finalStore.drop store.length with
            | [_, .constructed _ (.cellRef _ snapshot), payload] =>
              payload == seed && store[snapshot]? == some seed
            | _ => false
          SourceCompilerFeatureSupport.require (finalStore.take store.length == store && copied)
            "zero-parameter pure call did more than make the marked copy of its captured seed"
        else
          SourceCompilerFeatureSupport.require (finalStore.length > store.length)
            "lambda parameter/body allocations were lost"
        if name == "fail" then
          match value with
          | .inLeft .word (.word _) =>
            SourceCompilerFeatureSupport.require
              (finalStore.any (fun v => v == .inRight .unit (.word (word 13))))
              "lambda fault lost a completed body binding"
            SourceCompilerFeatureSupport.require (finalStore.any (fun v => v == .inLeft .word .unit))
              "lambda fault lost the uninitialized source cell"
          | other => throw (IO.userError s!"lambda fault result {reprStr other}")
        else
          let expected := if name == "unitMaker" then .unit else .word (word (if name == "make" then 13 else if name == "two" then 11 else 3))
          SourceCompilerFeatureSupport.require (value == .inRight .word expected) s!"lambda {name} result {reprStr value}"
      | other => throw (IO.userError s!"lambda {name} machine result {reprStr other}")
    | other => throw (IO.userError s!"lambda {name} creation {reprStr other}")
  IO.println "indexed lambda calls: source success/fault reflection, builtin lexical body, ordered parameters, exact caller restore and resumed store GREEN"
end Tests.SourceCoreCallableIndexedLambdaCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaGeneration
/-! The compiler-owned ordinary site constructs its history alignment instead
of receiving it. Runtime regressions inspect exact named source, saved lexical
state, evidence and capture order, without treating a scanner as a source trace. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration.Compilation.mk
#check_failure Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration.Site.mk
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaGeneration
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedHistory CallableIndexedNamedGeneration CallableIndexedLambdaValues CallableIndexedLambdaGeneration

theorem accepted_generation {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
      ∃ history : History site.code,
        history.metadata = state named ∧
        history.metadata.metadata.source = source named ∧
        history.metadata.metadata.owner = named.signature.key ∧
        history.metadata.nativeActive = [] := by
  obtain ⟨site, sameId, sameCode⟩ := of_contextual prepared compiled record sourceContext evidence captured profile
    viewOfSource sourceFound sourceForm found form owner requirements coercions ordinary read accepted typed
  obtain ⟨_, _, history, _, _, sameState⟩ := site.history compiled record
  refine ⟨site, sameId, sameCode, history, sameState, ?_, ?_, ?_⟩ <;> rw [sameState] <;> rfl

/-- The named compiler equation is recovered at the real cached global slot. -/
theorem actual_global_seed {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) {named : Named} {index : Nat}
    (selected : prepared.base.functions[index]? = some named)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    ∃ diagnostics code, prepared.secondPass.closures[index]? = some code ∧
      ∃ _compiled : Compilation prepared named diagnostics code,
        ∃ origin, prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
          Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
            (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)
            (.named origin) (some (state named)) := by
  obtain ⟨diagnostics, code, cached, ⟨compiled⟩⟩ := compiled_at prepared selected
  obtain ⟨origin, selected, carried, _⟩ := compiled.history record
  exact ⟨diagnostics, code, cached, compiled, origin, selected, carried⟩

/-- Source evidence and ordered abstract captures are the formation inputs,
including aliases. Native environment renaming never changes these values. -/
theorem closure_inputs (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty)
    (body : List StatementId) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (captured : Dynamic.Environment) :
    (closure named parameters result body context evidence captured).source = source named ∧
    (closure named parameters result body context evidence captured).context = context ∧
    (closure named parameters result body context evidence captured).evidence = evidence ∧
    (closure named parameters result body context evidence captured).captured = captured := ⟨rfl, rfl, rfl, rfl⟩

/-- A concrete administrative allocation is a genuine preserving prefix. The
completion consumer needs no separately supplied source/owner/active history.
The site's lambda copies its captures when it is created, so the completed
store is the formed one and the source closure captures the same copies. -/
theorem completed_after_administrative_allocation
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : Named} {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {capturedSource : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {mapping world actual}
    (captured : Captures prepared mapping world scope capturedSource actual)
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope captured.administrative)
    {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (program : SourceSemantics.Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions [])
    (coercions : site.code.sourceNode.coercions = [])
    {entryStore store after : Store} {location : Location} {saved temporary output : Core.Value}
    (allocated : store = (Store.allocate (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) temporary).1)
    (entryRead : entryStore.read? location = some saved) (unmapped : location ∉ mapping)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects
      prepared.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (referenceIndex : site.code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    (reference : captured.canonical[site.code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (completed : Evaluates actual store (site.code.lowered.expression.rename captured.embedding) output after) :
    ∃ formed : Formed model captured site.code (site.historyAt selected record) heap store location,
      after = formed.finalStore ∧
      Dynamic.ExpressionEvaluates program sourceContext evidence (source named) capturedSource heap site.code.id
        (.closure (closure named parameters result body sourceContext evidence formed.captured)) formed.finalHeap := by
  have preserved : GeneralHeap.AdministrativePreserved mapping
      (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) mapping store := by
    rw [allocated]
    exact GeneralHeap.AdministrativePreserved.allocate_administrative _ _ _
  obtain ⟨formed, _, sameStore, formedSource, _⟩ := site.reflects_after_prefix captured selected record program heap
    ordinary coercions entryRead unmapped preserved heaps site.snapshots referenceIndex reference completed
  exact ⟨formed, sameStore, formedSource⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function capture(seed: Word) returns (F) { let unused: Word = 9; return lam(item: Word) -> Word { seed += item; return seed; }; }",
    "function qualified<T>(seed: T) returns (function(T) returns (T)) where T: Mark { let unused: Word = 9; return lam(item: T) -> T { let ignored = seed; return keep(item); }; }",
    "function stopped(seed: Word) returns (Word) { let value: F = lam(item: Word) -> Word { seed += item; return seed; }; let written = value(4); let gap: Word; return gap; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) (arguments : List TypeSystem.Ty) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, arguments⟩
  | none => throw (IO.userError s!"missing generation fixture {name}")

private def audit {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (templates : SourceCoreCallableIndexedTemplates.Cache prepared)
    (headers : SourceCoreCallablePairedHeaders.Prepared prepared.ancestry.graph)
    (named : Named) {world : StoreTyping} {store : Store} {native : Core.Value}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (typed : RuntimeValueHasType world native (CallableContract.functionType .word .word) prepared.layouts.definitions)
    (expectedEvidence : Nat) : IO Unit := do
  let origin ← match prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) with
    | some origin => pure origin
    | none => throw (IO.userError "missing actual named origin")
  let frame := SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin
  SourceCompilerFeatureSupport.require (decide (SourceCoreCallableIndexedDispatch.lookup? prepared.ancestry.graph.table frame = some (some (state named))))
    "named seed lost exact source or native parent"
  let authenticated ← SourceCompilerFeatureSupport.get "generation authentic lambda"
    (SourceCoreCallableIndexedTemplates.authenticate templates stored native .word .word typed)
  let initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.bool, none⟩]
  let ledger ← SourceCompilerFeatureSupport.get "generation capture ledger"
    (SourceCoreAllocationLedger.scanTyped prepared.layouts initial world store stored)
  let restored ← SourceCompilerFeatureSupport.get "generation raw lambda"
    (SourceCoreCallableIndexedRestoration.restoreOrdinary headers authenticated ledger)
  SourceCompilerFeatureSupport.require (authenticated.snapshot.frame == frame)
    "lambda creation failed to retain its actual named state"
  SourceCompilerFeatureSupport.require (decide (restored.header.state = state named))
    "lambda header selected a different full source state"
  SourceCompilerFeatureSupport.require (restored.header.context.context.evidence.length == expectedEvidence)
    "generation changed qualified lexical evidence"
  SourceCompilerFeatureSupport.require (decide (restored.captures.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst))
    "generation changed lexical capture order"
  SourceCompilerFeatureSupport.require (restored.captures.environment.length == 2 &&
      restored.captures.environment.all (fun item => item.2.index ≥ initial.length))
    "generation lost the unused capture or opaque source prefix"
  SourceCompilerFeatureSupport.require (authenticated.current.frame == .empty)
    "generation named entry failed to restore the caller"

/-- The snapshot cell of `stopped`'s lambda: after the input `seed` and the
copy of `seed` made when the lambda was created. -/
private def storedLambda : Nat := 2

/-- The stored lambda was created with `seed = 3` and already called with `4`.
Its call copies its creation-time copy of `seed` again, so with `2` it returns
`3 + 2`, not the value the earlier call left in that call's own copy. -/
private def callSnapshot {artifact : SourceCoreExecution.Artifact}
    (snapshot : SourceCoreExecution.Snapshot artifact) : IO SourceCoreExecution.Handle := do
  let handle ← match (snapshot.cells[storedLambda]?).bind (fun (cell : SourceCoreHeapSnapshot.Cell) => cell.value) with
    | some (.data (.function handle)) => pure handle
    | _ => throw (IO.userError "generation snapshot lost its stored lambda")
  let session ← match snapshot.restore with
    | .ready session => pure session
    | .suspended _ => throw (IO.userError "completed generation snapshot remained suspended")
  let called ← SourceCompilerFeatureSupport.get "invoke stored generation"
    (← session.invokePacked handle (SourceCompilerFeatureSupport.scalar 2) SourceCompilerFeatureSupport.executionOptions)
  match called with
  | .succeeded done =>
    SourceCompilerFeatureSupport.require (done.value == SourceCompilerFeatureSupport.scalar 5)
      "stored generation did not restart from its creation-time capture"
  | _ => throw (IO.userError "stored generation invocation failed")
  pure handle

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "generation checker" (checkProgram workspace)
  let captureKey ← key program "capture" []
  let qualifiedKey ← key program "qualified" [.word]
  let qualifiedParameters ← match program.signatures.functions.find? (·.name == "qualified") with
    | some signature => pure signature.scheme.parameters
    | none => throw (IO.userError "missing qualified signature")
  let plan ← match SourceSpecializationWorklist.run program
      [⟨captureKey.declaration, []⟩, ⟨qualifiedKey.declaration, qualifiedParameters.zip [.word]⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"generation worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "generation base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "generation indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let templates ← SourceCompilerFeatureSupport.get "generation templates" (SourceCoreCallableIndexedTemplates.prepare prepared)
  let headers ← SourceCompilerFeatureSupport.get "generation headers" (SourceCoreCallablePairedHeaders.prepare prepared.ancestry.graph)
  for (selectedKey, expectedEvidence) in [(captureKey, 0), (qualifiedKey, 1)] do
    let named ← match prepared.base.functions.find? (fun named => decide (named.signature.key = selectedKey)) with
      | some named => pure named
      | none => throw (IO.userError "missing compiled named generation")
    for fuel in [0, 19, 300000] do
      let started ← SourceCompilerFeatureSupport.get "generation start" (prepared.runSource selectedKey [.word (Word.ofNatModulo 3)] fuel)
      let completion := started.resume 300000
      if same : completion.entry.native.resultType = CallableContract.functionType .word .word then
        match done : completion.result.native.observation with
        | .succeeded native store =>
          have typed : RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
              RuntimeValueHasType (store.map Core.Value.type) native (CallableContract.functionType .word .word) prepared.layouts.definitions := by
            obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed done
            have worlds := stored.world_eq
            subst world
            rw [same] at typed
            exact ⟨stored, typed⟩
          audit prepared templates headers named typed.1 typed.2 expectedEvidence
        | other => throw (IO.userError s!"generation completion {reprStr other}")
      else throw (IO.userError "generation native header changed")
  let stopped ← SourceCompilerFeatureSupport.compileNamed program "stopped"
  let argument := SourceCompilerFeatureSupport.scalar 3
  let baseline ← stopped.invoke [argument]
  let (token, finalSession) ← match baseline.outcome with
    | .failed token session => pure (token, session)
    | _ => throw (IO.userError "generation first fault unexpectedly succeeded")
  let snapshot ← SourceCompilerFeatureSupport.get "generation failed snapshot" (← finalSession.snapshot 2048)
  let baselineHandle ← callSnapshot snapshot
  for fuel in [0, 11, 53] do
    let started ← SourceCompilerFeatureSupport.get "generation suspension"
      (← baseline.initial.run baseline.key [argument] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let final ← SourceCompilerFeatureSupport.get "generation resumed snapshot" (← session.snapshot 2048)
      let resumedHandle ← callSnapshot final
      SourceCompilerFeatureSupport.require (actual == token && resumedHandle.sourceType == baselineHandle.sourceType &&
          reprStr (final.cells.eraseIdx storedLambda) == reprStr (snapshot.cells.eraseIdx storedLambda))
        "generation resume changed captures, writes or first fault"
    | _ => throw (IO.userError "generation resume changed its stopping point")
  IO.println "indexed named-to-lambda generation: real callbacks, full source seed, lexical evidence/captures and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaGeneration
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaImperativeNativeTyping
/-! The consumer creates Code and real named history without a Code or native
HasType premise. Static native callback laws and exact body equations remain visible. IO checks heterogeneous packed parameters, lexical captures, lazy faults
and suspension on the actual indexed execution path. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaImperativeNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedParameterNativeTyping CallableIndexedLambdaCertificates
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaImperativeNativeTyping

theorem accepted_imperative_generation {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (receipt : Certificate policy lowerBody fuel (context prepared named) view scope id node
      parameters result body reported reasonAt lowered)
    (bodyProfile : BodyProfile receipt prepared.layouts.definitions administrative)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      (representation prepared) prepared.base.locals named.signature.key [])
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = [])
    (ordinaryParameters : ∀ binder ∈ parameters, view.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
      ∃ history : CallableIndexedLambdaValues.History site.code,
        history.metadata = state named ∧ history.metadata.metadata.source = source named ∧
        history.metadata.metadata.owner = named.signature.key ∧ history.metadata.nativeActive = [] := by
  obtain ⟨site, sameId, sameCode⟩ := CallableIndexedLambdaImperativeNativeTyping.of_contextual prepared compiled record
    sourceContext evidence captured profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted receipt bodyProfile projector allocation manifest expressionHook callables binderPolicy
    monomorphic ordinaryParameters scopeWF current
  obtain ⟨_, _, history, _, _, sameState⟩ := site.history compiled record
  refine ⟨site, sameId, sameCode, history, sameState, ?_, ?_, ?_⟩ <;> rw [sameState] <;> rfl

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function step(value: Word) returns (Word) { return value + 1; }",
    "function factory(seed: Word) returns (function() returns (Word)) { return lam() -> Word { let value: Word = seed; for (let i: Word = 0; i < 3; i += 1) { if (i == 1) { continue; } value = step(value); } while (value < 12) { value = step(value); } return value; }; }",
    "function pair(seed: Word) returns (function(Word, Bool) returns (Word)) { return lam(delta: Word, choose: Bool) -> Word { let value: Word = seed; if (choose) { for (let i: Word = 0; i < 2; i += 1) { value += delta; } } else { value += 1; } return value; }; }",
    "function failed(seed: Word) returns (function(Bool) returns (Word)) { let missing: Word; return lam(flag: Bool) -> Word { seed += 1; return flag ? seed : missing; }; }"
  ]}] }

private def exercise (program : CheckedProgram) (name : String)
    (argument expected : SourceCoreExecution.Value) : IO Unit := do
  let entry ← SourceCompilerFeatureSupport.compileNamed program name
  let created ← entry.invoke [SourceCompilerFeatureSupport.scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done
    | _ => throw (IO.userError s!"{name}: lambda formation failed")
  let handle ← match done.value with
    | .function handle => pure handle
    | _ => throw (IO.userError s!"{name}: lambda handle missing")
  let complete ← SourceCompilerFeatureSupport.get "imperative lambda invoke"
    (← done.session.invokePacked handle argument SourceCompilerFeatureSupport.executionOptions)
  let final ← match complete with
    | .succeeded final => pure final
    | _ => throw (IO.userError s!"{name}: imperative invocation failed")
  SourceCompilerFeatureSupport.require (final.value == expected) s!"{name}: parameter order or capture changed"
  let baseline ← SourceCompilerFeatureSupport.get "imperative final snapshot" (← final.session.snapshot 2048)
  for spent in [0, 7, 43] do
    let started ← SourceCompilerFeatureSupport.get "imperative pending invocation"
      (← done.session.invokePacked handle argument {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel pending => pending.resume 300000 2048
      | complete => pure complete
    match resumed with
    | .succeeded actual =>
      let observed ← SourceCompilerFeatureSupport.get "imperative resumed snapshot" (← actual.session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual.value == expected && reprStr observed.cells == reprStr baseline.cells)
        s!"{name}: resume changed parameter allocation or captured state"
    | _ => throw (IO.userError s!"{name}: imperative resume failed")

private def failure (program : CheckedProgram) : IO Unit := do
  let entry ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let created ← entry.invoke [SourceCompilerFeatureSupport.scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done
    | _ => throw (IO.userError "fault lambda formation failed")
  let handle ← match done.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "fault lambda handle missing")
  let complete ← SourceCompilerFeatureSupport.get "imperative lambda fault"
    (← done.session.invokePacked handle (.bool false) SourceCompilerFeatureSupport.executionOptions)
  let (reason, session) ← match complete with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "selected missing capture did not fail")
  let baseline ← SourceCompilerFeatureSupport.get "fault snapshot" (← session.snapshot 2048)
  for spent in [0, 11, 59] do
    let started ← SourceCompilerFeatureSupport.get "imperative pending fault"
      (← done.session.invokePacked handle (.bool false) {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel pending => pending.resume 300000 2048
      | complete => pure complete
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "fault resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr baseline.cells)
        "imperative lambda fault/resume changed first failure or allocation prefix"
    | _ => throw (IO.userError "imperative lambda fault/resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "imperative lambda checker" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  exercise program "factory" .unit (w 12)
  exercise program "pair" (.product (w 4) (.bool true)) (w 15)
  exercise program "pair" (.product (w 4) (.bool false)) (w 8)
  exercise program "failed" (.bool true) (w 8)
  failure program
  IO.println "indexed imperative lambda native typing: actual body callback, parameter fold/history, loops/named calls, fault writes and resume GREEN"

end Tests.SourceCoreCallableIndexedLambdaImperativeNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaNestedStageOrigins
/-! The actual nested model carries both body receipts and stage origins.
These consumers keep the original model and its invocation conditions. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaNestedStageOrigins
open Solcore
open Core Frontend SourceSemantics
open SourceInference SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaNestedRuntimeCertificates CallableIndexedLambdaNestedRuntimeBodyMeaning
open RecursiveNamedCatalog

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
  {locations : Locations (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (program := program)}
local notation "F" => CallableIndexedLambdaNestedRuntimeCertificates.model
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) headers locations registry faults

section Actual

theorem header_source
    (header : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      header.named.signature.key [] header.function.source ∧ NodeOccurrencesUnique header.function.source :=
  CallableIndexedActualNamedSourceReceipts.header_source compiled header

/-- Recapture uses the actual source environment, including its unused tail. -/
theorem recaptured_source
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {rank : Nat} {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank source context evidence scope id lowered)
    (environment : Dynamic.Environment) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      (actualCode head environment).compilation.owner (actualCode head environment).active
      (formed head environment).source ∧ NodeOccurrencesUnique (formed head environment).source :=
  CallableIndexedLambdaNestedStageOrigins.support_provenance compiled (actualSupport head environment)

/-- The same formation evaluation and ValueRep, over the copies of the captured
cells, also supply its stage origin. -/
theorem formed_origin
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {rank : Nat} {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = compiled.indexed.base.plan)
    (sameTable : site.table = compiled.indexed.ancestry.graph.inputs.callable.table)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical actual : Environment} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {ξ : Renaming}
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (F profile))
      mapping world heap store) :
    ∃ value captured finalHeap finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (formed head captured)) finalHeap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) finalStore ∧
      ValueRep compiled.compatible.checked registry (F profile) finalMap finalWorld head.code.sourceNode.type
        (.closure (formed head captured)) value lowered.type ∧
      CallableLedger.OriginRep sidecar.plan site.table (.closure (formed head captured)) value := by
  obtain ⟨value, captured, finalHeap, finalStore, finalMap, finalWorld, sourceValue, _copy, nativeValue, represented,
      _heaps, _maps, _worlds, _frame, _metadata⟩ :=
    formation head profile complete globals slots entry related agrees typed heaps
  exact ⟨value, captured, finalHeap, finalStore, finalMap, finalWorld, sourceValue, nativeValue, represented,
    CompatibleAmbientStageOrigins.related_origin
      (CallableIndexedLambdaNestedStageOrigins.function_origins compiled profile samePlan sameTable)
      represented (.closure _)⟩

theorem actual_guards
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreCallableContracts.prepareCallsite compiled.indexed.ancestry.graph.inputs.callable.table context.owner node.id
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (F profile))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type :=
  CallableIndexedLambdaNestedStageOrigins.actual_compiled_coverage compiled profile issued caller contains form sourceType type

end Actual

section Boundaries
/-- The original ordered capture condition remains available after attribution. -/
abbrev actual_closure_receipt := @CallableIndexedLambdaNestedStageOrigins.closure_receipt

/-- Invocation still consumes independently supplied catalog authority. -/
def caller_catalog
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {location : Location}
    {capturePrefix callerPrefix : Nat} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (captures : CallableIndexedLambdaCatalogEntries.CaptureGlobals
      (values := .initial compiled.compatible.checked) headers locations callerPrefix scope canonical location)
    (authority : Authority headers locations capturePrefix mapping world heap store) :
    Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical :=
  captures.catalog authority

/-- Retained builtin/data values do not acquire an arbitrary lambda history. -/
theorem scalar_not_callable (number : Int) : ¬ Staging.CallBoundary.UserCallable (.integer number) := by
  intro impossible
  cases impossible

/-- These existing body interfaces use F, its full heap and separate original
source/native grades. Stage coverage adds no body execution hypothesis. -/
abbrev same_model_body_preserves := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.preserves_sized
abbrev same_model_body_reflects := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.reflects_sized
abbrev same_model_entry := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.entry_of_source
abbrev actual_lambda_permission := @CallableIndexedLambdaRuntimeEntry.reflects_original_nested_for
end Boundaries
end Tests.SourceCoreCallableIndexedLambdaNestedStageOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaScalarNativeTyping
/-! The consumer creates Code and real named history without a Code or native
HasType premise. Static scalar syntax/typing and exact callback equations remain
visible. IO checks heterogeneous packed parameters, lexical captures, lazy faults
and suspension on the actual indexed execution path. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaScalarNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedParameterNativeTyping CallableIndexedLambdaCertificates
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaScalarNativeTyping

theorem accepted_scalar_generation {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (receipt : Certificate policy lowerBody fuel (context prepared named) view scope id node
      parameters result body reported reasonAt lowered)
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    (scalar : ScalarBody values sameChecked receipt)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      (representation prepared) prepared.base.locals named.signature.key [])
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = [])
    (ordinaryParameters : ∀ binder ∈ parameters, view.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
      ∃ history : CallableIndexedLambdaValues.History site.code,
        history.metadata = state named ∧ history.metadata.metadata.source = source named ∧
        history.metadata.metadata.owner = named.signature.key ∧ history.metadata.nativeActive = [] := by
  obtain ⟨site, sameId, sameCode⟩ := CallableIndexedLambdaScalarNativeTyping.of_contextual prepared compiled record
    sourceContext evidence captured profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted receipt values sameChecked scalar projector allocation manifest expressionHook callables binderPolicy
    monomorphic ordinaryParameters scopeWF current
  obtain ⟨_, _, history, _, _, sameState⟩ := site.history compiled record
  refine ⟨site, sameId, sameCode, history, sameState, ?_, ?_, ?_⟩ <;> rw [sameState] <;> rfl

/-- The third heterogeneous argument uses two right projections, preserving
actual packed order instead of assigning each parameter the bundle type. -/
theorem third_projection (definitions : DataEnvironment) (administrative : Core.Context) :
    HasType (.product .word (.product .bool .integer) :: administrative)
      (SourceCoreFunctions.argumentProjection 2 3 (.var 0)) .integer definitions :=
  projection_typed (types := [.word, .bool, .integer]) rfl (.var rfl)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(seed: Word) returns (function(Word, Bool) returns (Word)) { let unused: Bool = true; return lam(item: Word, choose: Bool) -> Word { return choose ? seed + item : item; }; }",
    "function single(seed: Word) returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return seed + item; }; }",
    "function pair(seed: Word) returns (function(Bool, Word) returns ((Bool, Word))) { return lam(flag: Bool, item: Word) -> (Bool, Word) { return (flag, seed + item); }; }",
    "function zero(seed: Word) returns (function() returns (Word)) { return lam() -> Word { return seed; }; }",
    "function three(seed: Word) returns (function(Word, Bool, Word) returns (Word)) { return lam(first: Word, branch: Bool, last: Word) -> Word { return branch ? seed + first : last; }; }",
    "function failed(seed: Word) returns (function(Bool) returns (Word)) { let missing: Word; return lam(flag: Bool) -> Word { return flag ? seed : missing; }; }"
  ]}] }

private def exercise (program : CheckedProgram) (name : String)
    (argument expected : SourceCoreExecution.Value) : IO Unit := do
  let entry ← SourceCompilerFeatureSupport.compileNamed program name
  let created ← entry.invoke [SourceCompilerFeatureSupport.scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done
    | _ => throw (IO.userError s!"{name}: lambda formation failed")
  let handle ← match done.value with
    | .function handle => pure handle
    | _ => throw (IO.userError s!"{name}: lambda handle missing")
  let complete ← SourceCompilerFeatureSupport.get "scalar lambda invoke"
    (← done.session.invokePacked handle argument SourceCompilerFeatureSupport.executionOptions)
  let final ← match complete with
    | .succeeded final => pure final
    | _ => throw (IO.userError s!"{name}: scalar invocation failed")
  SourceCompilerFeatureSupport.require (final.value == expected) s!"{name}: parameter order or capture changed"
  let baseline ← SourceCompilerFeatureSupport.get "scalar final snapshot" (← final.session.snapshot 2048)
  for spent in [0, 7, 43] do
    let started ← SourceCompilerFeatureSupport.get "scalar pending invocation"
      (← done.session.invokePacked handle argument {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel pending => pending.resume 300000 2048
      | complete => pure complete
    match resumed with
    | .succeeded actual =>
      let observed ← SourceCompilerFeatureSupport.get "scalar resumed snapshot" (← actual.session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual.value == expected && reprStr observed.cells == reprStr baseline.cells)
        s!"{name}: resume changed parameter allocation or captured state"
    | _ => throw (IO.userError s!"{name}: scalar resume failed")

private def failure (program : CheckedProgram) : IO Unit := do
  let entry ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let created ← entry.invoke [SourceCompilerFeatureSupport.scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done
    | _ => throw (IO.userError "fault lambda formation failed")
  let handle ← match done.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "fault lambda handle missing")
  let complete ← SourceCompilerFeatureSupport.get "scalar lambda fault"
    (← done.session.invokePacked handle (.bool false) SourceCompilerFeatureSupport.executionOptions)
  let (reason, session) ← match complete with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "selected missing capture did not fail")
  let baseline ← SourceCompilerFeatureSupport.get "fault snapshot" (← session.snapshot 2048)
  for spent in [0, 11, 59] do
    let started ← SourceCompilerFeatureSupport.get "scalar pending fault"
      (← done.session.invokePacked handle (.bool false) {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel pending => pending.resume 300000 2048
      | complete => pure complete
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "fault resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr baseline.cells)
        "scalar lambda fault/resume changed first failure or allocation prefix"
    | _ => throw (IO.userError "scalar lambda fault/resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "scalar lambda checker" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  exercise program "make" (.product (w 4) (.bool true)) (w 11)
  exercise program "make" (.product (w 4) (.bool false)) (w 4)
  exercise program "single" (w 4) (w 11)
  exercise program "pair" (.product (.bool true) (w 4)) (.product (.bool true) (w 11))
  exercise program "zero" .unit (w 7)
  exercise program "three" (.product (w 4) (.product (.bool false) (w 29))) (w 29)
  exercise program "failed" (.bool true) (w 7)
  failure program
  IO.println "indexed scalar lambda native typing: actual parameter fold, captures, lazy branch/fault and resume GREEN"

end Tests.SourceCoreCallableIndexedLambdaScalarNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaSemanticCalls
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation.ViewBody.mk
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaSemanticCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaSemanticInvocation CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
section Proof
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} (profile : values.checked.catalog.callableContracts = true)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code)
  (sourceFrame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
  (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy)
  {changed : List ExpressionId}
  (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
  (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
  (unique : NodeOccurrencesUnique function.source)
  (valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements inputs.context function.evidence)
  (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
  (syntaxTree : BuiltinLexicalStatements.Syntax code.view inputs.context true function.body function.resultType)
  {flow : Expr}
  (emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason)
  (tree : BuiltinLexicalStatements.Tree prepared.layouts code.compilation.owner code.active prepared.ancestry.layout.frame
    prepared.base.globals.length code.allocationError readFuel values code.view code.compilation.solvedRequirements code.reasonAt
    inputs.context (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    true function.body function.resultType code.receipt.resultCore flow)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem completed_call [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Core.Value} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaSemanticCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inRight .word result) finalStore) :
    ∃ sourceResult after finalMap finalWorld,
      Dynamic.CallableApplies program callerContext callerEvidence function.evidence before (.closure function) arguments sourceResult after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType sourceResult result code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨viewBody⟩ := ViewBody.of_tree code inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaSemanticCalls.reflects captured code history viewBody.body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | value payload =>
    cases execution with
    | value called => exact ⟨_, after, finalMap, finalWorld, called, payload, finalHeap, caller.read⟩

include inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem failed_call [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {token : Word} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaSemanticCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inLeft code.receipt.resultCore (.word token)) finalStore) :
    ∃ reason after finalMap finalWorld,
      Dynamic.CallableFaults program callerContext callerEvidence function.evidence before (.closure function) arguments reason after ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨viewBody⟩ := ViewBody.of_tree code inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaSemanticCalls.reflects captured code history viewBody.body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | fault represented =>
    cases execution with
    | fault failed => exact ⟨_, after, finalMap, finalWorld, failed, represented, finalHeap, caller.read⟩
/- Independent source success or fault runs the same actual closure code.
Every body semantic input is constructed from static evidence at the compiler
view and its actual callback equation. -/
include inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem source_call [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaSemanticCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨viewBody⟩ := ViewBody.of_tree code inputs sourceFrame readFuel policy callback edited avoids unique valid projection syntaxTree emitted tree
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, heaps, _, _, _, _, restored⟩ :=
    CallableIndexedLambdaSemanticCalls.preserves captured code history viewBody.body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing executed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, heaps, restored.read⟩

/- The body action retained by the lambda compiler uses the exact ordered
parameter scope; acceptance is at the actual view, never the canonical source. -/
include callback in
theorem actual_body_receipt :
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope ∧
    SourceCoreLoops.lowerStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body :=
  ⟨body_scope code, loops_accepted code policy callback⟩

end Proof


def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaCalls.run
  Tests.SourceCoreCallableLambdaViewBuiltinBodyTree.run
  IO.println "indexed semantic lambda calls: actual view callback/parameter receipt, canonical source call/fault, caller restore and resumed heap GREEN"

end Tests.SourceCoreCallableIndexedLambdaSemanticCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaValues
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedLambdaValues GeneralHeap CompatiblePayload

theorem anonymous_comparison {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Core.Value}
    (related : (model prepared profile).Represents registry mapping world sourceType (.closure function) native comparator.type)
    (store : Store) :
    Evaluates [native, native] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool false)
      (CompatibleEquality.preparedStore comparator [native, native] store) := by
  obtain ⟨result, equivalent, evaluated⟩ := CompatibleEquality.prepared_compare_preserves comparator
    (identity_faithful prepared) (observations prepared profile related) (observations prepared profile related)
    [native, native] store (.var 0) (.var 1) (.var rfl) (.var rfl)
  cases result with
  | false => exact evaluated
  | true => have impossible := (equivalent.mp rfl).2; cases impossible

/-- The completion is consumed after the actual renamed formation code, which
first copies the captured cells of the creation environment, with source
captures and both full worlds retained. The completed store is the formed one,
and the source lambda forms the same closure over the same copies. No body
execution is supplied. -/
theorem completed_source {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap}
    {world : StoreTyping} {actual : Core.Environment} {environment : Dynamic.Environment}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects
      prepared.layouts.definitions}
    (captured : Captures prepared mapping world scope environment actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (copied : code.policy.snapshotLambda code.id = true)
    (referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    (program : SourceSemantics.Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = [])
    {before after : Store} {location : Location} {result : Core.Value}
    (heaps : GenericHeap.HeapRepresents model mapping world heap before)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native))
    (completed : Evaluates actual before (code.lowered.expression.rename captured.embedding) result after) :
    ∃ formed : Formed model captured code history heap before location,
      after = formed.finalStore ∧ Dynamic.ExpressionEvaluates program function.context function.evidence
        function.source environment heap code.id (.closure formed.closure) formed.finalHeap := by
  obtain ⟨formed⟩ := formation captured code history copied referenceIndex heaps reference read
  exact ⟨formed, (formed.reflects completed).2, formed.source program ordinary coercions⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function pair(seed: Word) returns (F, F) { let unused: Word = 9; let f: F = lam(item: Word) -> Word { seed += item; return seed; }; return (f, f); }",
    "function qualified<T>(seed: T) returns (function(T) returns (T)) where T: Mark { return lam(item: T) -> T { return keep(item); }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) (arguments : List TypeSystem.Ty) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, arguments⟩
  | none => throw (IO.userError s!"missing lambda fixture {name}")

private def capture {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    (templates : SourceCoreCallableIndexedTemplates.Cache prepared)
    (headers : SourceCoreCallablePairedHeaders.Prepared prepared.ancestry.graph)
    {world : StoreTyping} {store : Store} {native : Core.Value}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (typed : RuntimeValueHasType world native (CallableContract.functionType .word .word) prepared.layouts.definitions)
    (expectedEvidence : Nat) : IO SourceTypedRuntime.Environment := do
  let authenticated ← SourceCompilerFeatureSupport.get "owned indexed lambda"
    (SourceCoreCallableIndexedTemplates.authenticate templates stored native .word .word typed)
  let initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.bool, none⟩]
  let ledger ← SourceCompilerFeatureSupport.get "lambda capture ledger"
    (SourceCoreAllocationLedger.scanTyped prepared.layouts initial world store stored)
  let restored ← SourceCompilerFeatureSupport.get "lambda raw header"
    (SourceCoreCallableIndexedRestoration.restoreOrdinary headers authenticated ledger)
  SourceCompilerFeatureSupport.require (restored.header.context.context.evidence.length == expectedEvidence)
    "lambda lexical dictionary was changed or inferred from its type"
  SourceCompilerFeatureSupport.require (authenticated.current.frame == .empty) "lambda formation failed to restore the caller frame"
  SourceCompilerFeatureSupport.require (restored.captures.environment.all (fun item => item.2.index ≥ initial.length))
    "lambda capture lost the opaque source prefix"
  SourceCompilerFeatureSupport.require (decide (restored.captures.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst))
    "lambda lexical capture order changed"
  pure restored.captures.environment

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "lambda value checker" (checkProgram workspace)
  let pairKey ← key program "pair" []
  let qualifiedKey ← key program "qualified" [.word]
  let qualifiedParameters ← match program.signatures.functions.find? (·.name == "qualified") with
    | some signature => pure signature.scheme.parameters
    | none => throw (IO.userError "missing qualified signature")
  let plan ← match SourceSpecializationWorklist.run program
      [⟨pairKey.declaration, []⟩, ⟨qualifiedKey.declaration, qualifiedParameters.zip [.word]⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"lambda value worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "lambda base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "lambda indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let templates ← SourceCompilerFeatureSupport.get "lambda templates" (SourceCoreCallableIndexedTemplates.prepare prepared)
  let headers ← SourceCompilerFeatureSupport.get "lambda headers" (SourceCoreCallablePairedHeaders.prepare prepared.ancestry.graph)
  let word := Word.ofNatModulo
  for spent in [0, 21, 300000] do
    let started ← SourceCompilerFeatureSupport.get "lambda pair start" (prepared.runSource pairKey [.word (word 3)] spent)
    let completion := started.resume 300000
    if same : completion.entry.native.resultType = .product (CallableContract.functionType .word .word) (CallableContract.functionType .word .word) then
      match done : completion.result.native.observation with
      | .succeeded (.pair left right) store =>
          have typed : RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
              RuntimeValueHasType (store.map Core.Value.type) left (CallableContract.functionType .word .word) prepared.layouts.definitions ∧
              RuntimeValueHasType (store.map Core.Value.type) right (CallableContract.functionType .word .word) prepared.layouts.definitions := by
            obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed done
            have worlds := stored.world_eq
            subst world
            rw [same] at typed
            cases typed with | pair first second => exact ⟨stored, first, second⟩
          let first ← capture templates headers typed.1 typed.2.1 0
          let second ← capture templates headers typed.1 typed.2.2 0
          SourceCompilerFeatureSupport.require (first == second && first.length == 2) "shared lambda captures or unused lexical slot changed"
          let comparator ← SourceCompilerFeatureSupport.get "lambda comparison" (SourceCoreCompatibleDataEquality.prepare 500 automatic.checked (.function .word .word))
          SourceCompilerFeatureSupport.require (runStateful 100000 (.initial (CompatibleEquality.comparison comparator (.var 0) (.var 1)) [left, right] store) ==
            .done (.bool false) (CompatibleEquality.preparedStore comparator [left, right] store))
            "anonymous lambdas were assigned a named identity"
          let applyTwice := LocalSequence.pair .word .word
            (.apply (.second (.first (.var 1))) (.word (word 10)))
            (.apply (.second (.first (.var 0))) (.word (word 20)))
          match runStateful 100000 (.initial applyTwice [right, left] store) with
          | .done (.inRight .word (.pair (.word first) (.word second))) finalStore =>
            SourceCompilerFeatureSupport.require (first == word 13 && second == word 23)
              "a call of the returned lambda did not restart from its creation-time seed"
            SourceCompilerFeatureSupport.require (finalStore[0]? == some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame .empty))
              "lambda invocation did not restore its caller"
          | other => throw (IO.userError s!"lambda native reuse {reprStr other}")
      | other => throw (IO.userError s!"lambda pair completion {reprStr other}")
    else throw (IO.userError "lambda pair projected type changed")
  let qualified ← SourceCompilerFeatureSupport.get "qualified lambda" (prepared.runSource qualifiedKey [.word (word 7)] 300000)
  if same : qualified.entry.native.resultType = CallableContract.functionType .word .word then
    match done : qualified.result.native.observation with
    | .succeeded native store =>
      have typed : RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
          RuntimeValueHasType (store.map Core.Value.type) native (CallableContract.functionType .word .word) prepared.layouts.definitions := by
        obtain ⟨world, stored, typed⟩ := qualified.result.native.success_typed done
        have worlds := stored.world_eq
        subst world
        rw [same] at typed
        exact ⟨stored, typed⟩
      let _ ← capture templates headers typed.1 typed.2 1
      pure ()
    | other => throw (IO.userError s!"qualified lambda completion {reprStr other}")
  else throw (IO.userError "qualified lambda projected type changed")
  IO.println "indexed lambda leaves: actual templates, ordered shared captures, retained dictionary, anonymous equality and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaValues
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaViewCalls
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation.Body.source
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaViewCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaViewInvocation CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
section Proof
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem completed_call [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Core.Value} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaViewCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inRight .word result) finalStore) :
    ∃ sourceResult after finalMap finalWorld,
      Dynamic.CallableApplies program callerContext callerEvidence function.evidence before (.closure function) arguments sourceResult after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType sourceResult result code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaViewCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | value payload =>
    cases execution with
    | value called => exact ⟨_, after, finalMap, finalWorld, called, payload, finalHeap, caller.read⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem failed_call [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {token : Word} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaViewCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inLeft code.receipt.resultCore (.word token)) finalStore) :
    ∃ reason after finalMap finalWorld,
      Dynamic.CallableFaults program callerContext callerEvidence function.evidence before (.closure function) arguments reason after ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaViewCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | fault represented =>
    cases execution with
    | fault failed => exact ⟨_, after, finalMap, finalWorld, failed, represented, finalHeap, caller.read⟩
end Proof

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return seed + item; }; }" }] }

/-- The view changes the enclosing expression header, while the actual
parameter site and allocator still use the same complete binder metadata.
This checks allocation authentication only; it does not assert that arbitrary
header replacement preserves the source body semantics. -/
private def allocationView : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "lambda view checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "make") with
    | some signature => pure signature
    | none => throw (IO.userError "lambda view signature missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"lambda view worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "lambda view base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "lambda view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let lambda ← match prepared.ancestry.templates.lambdas with
    | lambda :: _ => pure lambda
    | [] => throw (IO.userError "lambda view template missing")
  let parameter ← match lambda.node.form with
    | .lambda (parameter :: _) _ _ => pure parameter
    | _ => throw (IO.userError "lambda view parameter missing")
  let site ← match prepared.layouts.entries.find? (fun site => decide
      (site.key.owner = lambda.owner ∧ site.key.active = lambda.active ∧ site.key.binder = parameter ∧ site.key.initialized = true)) with
    | some site => pure site
    | none => throw (IO.userError "lambda view actual parameter site missing")
  let source := lambda.context.inventory.source
  let view := SourceCoreEvidence.withNode source { lambda.node with type := .bool }
  SourceCompilerFeatureSupport.require (decide (source ≠ view)) "view fixture failed to change its full source"
  SourceCompilerFeatureSupport.require
    (decide (SourceCoreAllocationCodebook.sourceView source = SourceCoreAllocationCodebook.sourceView view))
    "lambda metadata view changed authenticated source shape"
  let request : SourceCoreSourceCells.Request :=
    ⟨source, site.key.scope, Renaming.id, parameter, site.key.payloadType, some (.var 0)⟩
  let original ← SourceCompilerFeatureSupport.get "lambda original allocation"
    (SourceCoreAllocationLayouts.allocateWithReceipt prepared.layouts lambda.owner lambda.active request)
  let viewed ← SourceCompilerFeatureSupport.get "lambda metadata-view allocation"
    (SourceCoreAllocationLayouts.allocateWithReceipt prepared.layouts lambda.owner lambda.active {request with source := view})
  SourceCompilerFeatureSupport.require (original.expression == viewed.expression)
    "metadata view changed actual parameter captures or payload allocation"
  SourceCompilerFeatureSupport.require (decide (original.entry.key = viewed.entry.key))
    "metadata view selected a different allocation layout"

def run : IO Unit := do
  allocationView
  Tests.SourceCoreCallableIndexedLambdaCalls.run
  IO.println "indexed lambda metadata views: unequal source tables preserve actual parameter allocation and canonical-source call receipts GREEN"
end Tests.SourceCoreCallableIndexedLambdaViewCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaEntryBounds
/-! Original indexed lambda completions expose a strict body witness and the
actual typed allocation state, including the copies of the complete captures
and frame restore. The empty argument case keeps the frame/manifest boundary. Runtime regressions
reuse real ordered-parameter, capture, fault and resume fixtures. No old Entry
identity or source body meaning is inferred from the reached prefix. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaEntryBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames SourceCoreLambdaTemplates CallableIndexedLambdaEntryBounds

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
/-- The consumer keeps the body subderivation of the supplied application,
and reads the ordered lexical prefix from its reached state: the parameters
over the copies of the captured scope, with every slot past the scope kept. -/
theorem original_application {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
          reached.canonical = added ++ copied ∧
          ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]? := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored, reached.spine⟩

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
/-- Zero arguments retain the original strict body edge; the canonical
lexical spine has no added parameter values. The scope slots hold the copies,
and every administrative slot past the scope keeps its index and value. -/
theorem empty_arguments_strict {size : Nat} {result : Value} {finalStore : Store}
    (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ∀ slot, scope.length ≤ slot → reached.canonical[slot]? = captured.canonical[slot]? := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨added, copied, length, spine, slots⟩ := reached.spine
  have parameters : code.receipt.loweredParameters.length = 0 := by
    simpa [empty] using represented.length.2
  have noValues : added = [] := List.eq_nil_of_length_eq_zero (length.trans parameters)
  rw [noValues, List.nil_append] at spine
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored, fun slot outside => spine ▸ slots slot outside⟩

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
/-- This consumer erases only the extracted child witness. It never chooses a
new grade for the original completion. -/
theorem original_body {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        Evaluates reached.actual reached.store (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    body_prefix captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, evaluated.sound, restored⟩
end Entry

/-- Actual manifest captures and their type survive stripping the original
let witness, even if the marked parameter prefix is empty. -/
theorem original_manifest {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {source : Dynamic.Environment} {canonical actual : Environment}
    {argument : Value} {ξ : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical definitions)
    (agrees : EnvironmentsAgree ξ (argument :: canonical) actual)
    (descriptor : Word) (fields : List (Word × Ty)) (body : Expr) (store : Store)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((manifestBody descriptor fields (SourceCoreSourceCells.captures id scope) body).rename ξ) result finalStore) :
    ∃ manifest child,
      RuntimeValueHasType world manifest
        (.product .word (.product (scopeManifestType fields) (SourceCoreSourceCells.captureType scope))) definitions ∧
      child < size ∧ EvaluationSize child (manifest :: actual) store
        (body.rename (Renaming.comp (Renaming.insertion 0) ξ)) result finalStore := by
  obtain ⟨manifest, typed, sized⟩ := manifest_prefix related agrees descriptor fields body store
  obtain ⟨child, smaller, evaluated⟩ := sized.remaining completed
  exact ⟨manifest, child, typed, smaller, evaluated⟩

theorem empty_prefix_same_size {size : Nat} {environment : Environment} {store after : Store}
    {code : Expr} {value : Value} (original : EvaluationSize size environment store code value after) :
    ∃ child, child = size ∧ EvaluationSize child environment store code value after :=
  ⟨size, rfl, original⟩

theorem agreement_does_not_force_strict :
    ContinuationAgreement [] [] .unit [] [] .unit ∧ ¬ ContinuationSize true [] [] .unit [] [] .unit := by
  refine ⟨.refl _ _ _, ?_⟩
  intro strict
  obtain ⟨child, smaller, original⟩ := strict.remaining EvaluationSize.unit
  cases original
  simp at smaller

/-- This is the actual empty capture/field manifest initializer. Its let
is strict while the remaining unit body keeps its own size one witness. -/
theorem empty_manifest_actual :
    ∃ child, child < 7 ∧ EvaluationSize child
      [.pair (.word Word.zero) (.pair .unit .unit)] [] .unit .unit [] := by
  have initializer : EvaluationSize 5 [] []
      (.pair (.word Word.zero) (.pair .unit .unit))
      (.pair (.word Word.zero) (.pair .unit .unit)) [] :=
    .pair EvaluationSize.word (.pair EvaluationSize.unit EvaluationSize.unit)
  have original : EvaluationSize 7 [] []
      (manifestBody Word.zero [] (SourceCoreSourceCells.captures id []) .unit) .unit [] := by
    simpa [manifestBody, scopeManifest, SourceCoreSourceCells.captures, Expr.weakenAt, Expr.rename]
      using EvaluationSize.letE initializer (EvaluationSize.unit (environment :=
        [.pair (.word Word.zero) (.pair .unit .unit)]) (store := []))
  have lowered : manifestBody Word.zero [] (SourceCoreSourceCells.captures id []) .unit =
      .letE (.pair (.word Word.zero) (.pair .unit .unit)) .unit := by
    simp [manifestBody, scopeManifest, SourceCoreSourceCells.captures, Expr.weakenAt]
  rw [lowered] at original
  exact (ContinuationSize.letE initializer.sound).remaining original

def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaViewCalls.run
  Tests.SourceCoreCallableIndexedLambdaValues.run
  IO.println "indexed lambda sized entry: original frame/manifest/parameter children, empty arity and complete typed captures GREEN"
end Tests.SourceCoreCallableIndexedLambdaEntryBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody
/-! Formal consumers retain actual view acceptance, ordered parameters,
canonical full match trees, runtime ledger and entry context independently.
The runtime fixture audits real captured lambdas; this stage does not provide
a combined named/anonymous recursive meaning theorem. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimeBody
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaRuntimeBody
open GeneralHeap ReadOnly CompatiblePayload

/-- The factory's existential retains the exact supplied context, fuel,
policy, emitted flow and actual view tree. No whole-body runtime law is input. -/
abbrev actual_body := @CallableIndexedLambdaRuntimeBody.Body.of_tree
abbrev actual_prefix := @CallableIndexedLambdaRuntimeBody.entry_exists
abbrev actual_full_match_transport := @CallableLambdaViewMatchRuntimeCertificates.original

section Body
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code prepared function scope administrative} {program : SourceSemantics.Program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body code program registry faults)

include body in
theorem actual_view_accepted :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body := body.accepted

include body in
theorem original_code_and_tree :
    code.receipt.body = CompatibleStatements.finish code.receipt.resultCore body.flow
      code.compilation.internalReason code.compilation.internalReason ∧
    body.tree.CatalogSites .reachable registry faults ∧ body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.emitted, body.sites, body.actualSites⟩

include body in
theorem complete_context :
    body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.context ∧ function.evidence.Covers body.context :=
  ⟨body.valid.ledger, body.valid.runtime, body.valid.covers⟩

include body in
theorem ordered_parameters :
    MonoBindersExtend function.source.owner function.context function.parameters body.types body.context ∧
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope :=
  ⟨body.extended, body_scope code⟩
end Body

section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime validity cannot supply the old ordinary premise for an unused row. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] := by
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup; decide
    · intro item evidence member implementation
      have same : item = row := by simpa [context, Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · constructor
    · intro predicate evidence found; cases found
    · intro predicate member; cases member
  · intro ordinary
    have valid := ordinary.valid.entriesValid row (by simp [context, Context.withSolvedRequirements])
    cases valid with
    | intro retained =>
      cases retained with
      | intro represents valid =>
        cases represents
        cases valid with
        | assumption member => cases member
end Boundary

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function loops(seed: Word) returns(F) { let unused: Word = 99; return lam(item: Word) -> Word { let sum = seed; for(let i: Word = 0; i < item; i += 1) { if(i == 1) { continue; } sum += i; } while(sum < seed + 10) { sum += 1; if(sum > seed + 5) { break; } } return sum; }; }",
    "function selected(seed: Word) returns(F) { return lam(item: Word) -> Word { match((item, seed)) { case (0, chosen) { return chosen; } case (left, right) { return left + right; } default { return 77; } } }; }",
    "function first(seed: Word) returns(F) { return lam(item: Word) -> Word { match((item, seed)) { case (0, chosen) { return chosen; } case (left, right) { return left + right; } default { return 77; } } }; }",
    "function defaulted(seed: Word) returns(F) { return lam(item: Word) -> Word { match(item) { case 0 { return seed; } default { let extra = seed + item; return extra; } } }; }",
    "function failed(seed: Word) returns(F) { return lam(item: Word) -> Word { match(item) { case 0 { return seed; } default { let prior = seed + item; let missing: Word; return missing; } } }; }",
    "function scrutinee(seed: Word) returns(F) { return lam(item: Word) -> Word { let missing: Word; match(missing) { case 0 { return seed; } default { return item; } } }; }",
    "function zero(seed: Word) returns(function() returns(Word)) { return lam() -> Word { { return seed; } }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"runtime lambda missing fixture {name}")

private def containsLambda : Nat → Core.Expr → Core.Expr → Bool
  | 0, _, _ => false
  | fuel + 1, expected, code =>
    let recurse := containsLambda fuel expected
    match code with
    | .lambda _ _ body => body == expected || recurse body
    | .pair a b | .apply a b | .storeCell a b | .letE a b | .binary _ a b => recurse a || recurse b
    | .first a | .second a | .inLeft _ a | .inRight _ a | .newCell _ a | .loadCell a
    | .construct _ a | .unary _ a => recurse a
    | .caseE a b c | .ifE a b c | .ternary _ a b c => recurse a || recurse b || recurse c
    | .matchData _ _ a branches => recurse a || branches.any recurse
    | _ => false

/-- Each call first copies the lambda's captures, most recent binding first,
from the values they had when the lambda was created; the parameter and the
body's binders follow. -/
private def expectedRows (name : String) : List (String × TypeSystem.Ty × Option Core.Value) :=
  let w := fun n => some (Core.Value.word (Word.ofNatModulo n))
  match name with
  | "loops" => [("unused", .word, w 99), ("seed", .word, w 3), ("item", .word, w 4), ("sum", .word, w 9), ("i", .word, w 4)]
  | "first" => [("seed", .word, w 3), ("item", .word, w 0), ("", .product .word .word, some (.pair (.word (Word.ofNatModulo 0)) (.word (Word.ofNatModulo 3)))), ("chosen", .word, w 3)]
  | "selected" => [("seed", .word, w 3), ("item", .word, w 4), ("", .product .word .word, some (.pair (.word (Word.ofNatModulo 4)) (.word (Word.ofNatModulo 3)))), ("left", .word, w 4), ("right", .word, w 3)]
  | "defaulted" => [("seed", .word, w 3), ("item", .word, w 4), ("", .word, w 4), ("extra", .word, w 7)]
  | "failed" => [("seed", .word, w 3), ("item", .word, w 4), ("", .word, w 4), ("prior", .word, w 7), ("missing", .word, none)]
  | "scrutinee" => [("seed", .word, w 3), ("item", .word, w 4), ("missing", .word, none)]
  | "zero" => [("seed", .word, w 3)]
  | _ => []

private def native_bodies : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "runtime lambda checker" (checkProgram workspace)
  let names := ["loops", "first", "selected", "defaulted", "failed", "scrutinee", "zero"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"runtime lambda worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "runtime lambda base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "runtime lambda indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let word := Word.ofNatModulo
  for (name, selectedKey) in names.zip keys do
    let created ← SourceCompilerFeatureSupport.get "runtime lambda maker" (prepared.runSource selectedKey [.word (word 3)] 500000)
    match created.result.native.observation with
    | .succeeded native original =>
      let inert := Core.Value.closure .unit .unit (.var 0) [.word (word 991), .bool true]
      let before := original ++ [inert]
      let arguments := if name == "zero" then .unit else .word (word (if name == "first" then 0 else 4))
      let state := Core.State.initial CallableIndexedLambdaCalls.applyPayload [native, arguments] before
      let expected := Core.runStateful 500000 state
      for fuel in [0, 1, 31, 500000] do
        let actual := match Core.runStateful fuel state with
          | .outOfFuel checkpoint => Core.runStateful 500000 checkpoint
          | finished => finished
        SourceCompilerFeatureSupport.require (actual == expected) s!"runtime lambda full resume {name}/{fuel}"
      match expected with
      | .done value after =>
        SourceCompilerFeatureSupport.require (after.take before.length == before) s!"runtime lambda prefix/captures {name}"
        let ledger ← SourceCompilerFeatureSupport.get "runtime lambda ordered allocations" (SourceCoreAllocationLedger.scan prepared.layouts [] after)
        let rows := ledger.rows.filter (fun row => row.markerIndex ≥ before.length)
        let expected := expectedRows name
        SourceCompilerFeatureSupport.require
          (decide (rows.map (fun row => (row.entry.key.binder.name, row.entry.key.binder.scheme.body, row.payload)) = expected))
          s!"runtime lambda full ordered raw bindings {name}"
        let (executable, snapshot) ← match native with
          | .pair (.pair _ (.closure _ _ executable (lexical :: _))) (.word origin) =>
            match SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame lexical with
            | some frame => pure (executable, SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
                (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table origin frame .empty))
            | none => throw (IO.userError "runtime lambda lexical frame decode")
          | _ => throw (IO.userError "runtime lambda actual closure shape")
        let administrativeCount := if name == "loops" then 2 else 0
        SourceCompilerFeatureSupport.require
          (ledger.pending.isNone && after.length == before.length + 3 * rows.length + administrativeCount)
          s!"runtime lambda unaccounted native cells {name}"
        for (row, index) in rows.zipIdx do
          SourceCompilerFeatureSupport.require
            (row.markerIndex == before.length + 3 * index + 1 && after[row.markerIndex - 1]? == some snapshot)
            "runtime lambda exact snapshot/marker/payload order"
        for index in List.range administrativeCount do
          let location := before.length + 3 * rows.length + index
          match after[location]? with
          | some (.inRight .unit (.closure .unit resultType body captures)) =>
            SourceCompilerFeatureSupport.require
              (resultType == LocalLoop.resultType .word && containsLambda 2000 body executable &&
               captures.head? == some (.cellRef (OptionalCell.cellType (LocalLoop.functionType .word)) location) &&
               Core.infer? (.unit :: captures.map Core.Value.type) body prepared.layouts.definitions == some resultType)
              "runtime lambda full loop closure code/self/capture types"
          | _ => throw (IO.userError "runtime lambda loop administrative cell")
        if name == "failed" || name == "scrutinee" then
          match value with
          | .inLeft .word (.word token) =>
            match created.result.diagnostics.diagnostic? token, rows.getLast? with
            | some diagnostic, some missing =>
              SourceCompilerFeatureSupport.require
                (diagnostic.error == .uninitializedLocal missing.entry.key.binder.id && missing.payload.isNone)
                "runtime lambda exact first missing binder"
            | _, _ => throw (IO.userError "runtime lambda missing fault receipt")
          | _ => throw (IO.userError "runtime lambda expected failure")
        else
          let result := if name == "loops" then 9 else if name == "first" || name == "zero" then 3 else 7
          SourceCompilerFeatureSupport.require (value == .inRight .word (.word (word result)))
            s!"runtime lambda result {name}"

      | other => throw (IO.userError s!"runtime lambda incomplete {name}: {reprStr other}")
    | other => throw (IO.userError s!"runtime lambda creation {name}: {reprStr other}")

def run : IO Unit := do
  native_bodies
  IO.println "runtime lambda static bodies: actual view / full imperative tree / captured frame / ordered capture copies, parameters and match binders / complete ledger / caller restore and full resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaRuntimeBody
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaCatalogEntries
/-! The actual lambda allocator and its retained spine, the parameters over
the copies of the captured scope, supply a catalog entry with the full lambda
history. Initial capture coherence and catalog authority
are explicit observations, independent of native typing. The source entry
stays distinct from a named entry. Lambda body meaning remains the existing
builtin fragment; this unit supplies the catalog boundary needed by a later
named-body extension. The runner reuses the registered actual lambda suite. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaCatalogEntries
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedLambdaCatalogEntries

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed initial sameFrame in
/-- The same actual unsized prefix supplies the source state, full heap and
ordered globals. Its existing agreement is not converted into a grade. -/
theorem actual_source_entry :
    ∃ entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry
      arguments nativeArguments before store location current currentGhost,
      ∃ sourceEntry : SourceEntry code history headers locations capturePrefix callerPrefix
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical,
        sourceEntry.catalog.authority.frameLocation = location ∧
        sourceEntry.catalog.authority.current = entry.next ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions
          entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := by
  obtain ⟨entry, added, copied, length, spine, slots⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
    captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed
  exact ⟨entry, source_entry entry initial sameFrame length spine slots, sameFrame, rfl, entry.entry.heaps⟩

include captured code inputs initial reference in
/-- Capture coherence observes the actual canonical slots. The separate
initial catalog supplies authority; the frame lookup comes from the receipt. -/
theorem actual_capture_globals : CaptureGlobals headers locations callerPrefix scope captured.canonical location :=
  ⟨initial.globals, by simpa only [inputs.referenceIndex] using reference⟩

variable (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry
    arguments nativeArguments before store location current currentGhost)
  {added copied : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ copied)
  (slots : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)

include initial sameFrame length spine slots in
theorem reached_ordered_global
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    entry.entry.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      callerPrefix + header.slot]? = some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  (source_entry entry initial sameFrame length spine slots).catalog.globals header member

include initial sameFrame length spine slots in
theorem full_carried_history :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (source_entry entry initial sameFrame length spine slots).catalog.authority.current
      (.lambda code.descriptor.id history.ghost) (some history.metadata) :=
  (source_entry entry initial sameFrame length spine slots).carried

variable (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history inputs functions registry arguments before store location current)

include reached initial sameFrame in
/-- Sized completions supply the same catalog boundary without changing the
original body witness or either grade. -/
theorem sized_catalog_is_legacy :
    (source_entry_sized reached initial sameFrame).catalog =
      CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame := rfl

include reached initial sameFrame in
theorem sized_frame_reference :
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type (source_entry_sized reached initial sameFrame).catalog.authority.frameLocation) :=
  (source_entry_sized reached initial sameFrame).reference

end Entry

section Boundaries
/-- Native typing has no role in this constructor distinction. The actual
lambda ghost cannot be substituted for a named source-entry ghost. -/
theorem lambda_not_named (id origin : Word) (parent : GhostFrame) :
    ((.lambda id parent) : GhostFrame) ≠ .named origin := by intro same; cases same

/-- Two ordered globals and a physical frame survive finite capture retention
and one real added slot. The arbitrary unused suffix is kept independently. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let canonical : Environment := [.cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let finite := canonical.take 3
    let reached : Environment := [.bool true] ++ canonical
    finite[0]? = some (.cellRef .word 3) ∧ finite[1]? = some (.cellRef .bool 4) ∧
      finite[2]? = some (.cellRef .unit 5) ∧
      reached[1]? = some (.cellRef .word 3) ∧ reached[2]? = some (.cellRef .bool 4) ∧
      reached[3]? = some (.cellRef .unit 5) ∧ reached.drop 4 = unused := by simp

end Boundaries

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaCatalogEntries
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaEntrySpines
/-! The actual parameter allocator supplies the canonical spine. The reached
entry retains its original function model, full heap, typed environment and
caller/lexical histories. The entry first copies the captured scope slots, so
the spine is the parameters over those copies; it shifts the existing global
and frame slots past the scope unchanged. Neither a continuation agreement nor
native typing supplies source history. The runner reuses the registered actual
indexed lambda suite. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaEntrySpines
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedLambdaEntryPrefix

abbrev actual_view_prefix := @CallableIndexedLambdaViewPrefix.entry_of_accepted_with_spine

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)


include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- The actual accepted prefix returns the allocated spine over the copies of
the captured scope and the original complete heap relation in the same entry.
No body completion is required. -/
theorem actual_entry :
    ∃ entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost,
      ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions
          entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := by
  obtain ⟨entry, added, copied, length, spine, slots⟩ := entry_exists_for_with_spine captured code history inputs
    functions represented heaps locals reference read currentCarried unmapped allowed
  exact ⟨entry, added, copied, length, spine, slots, entry.entry.heaps⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- Empty arity adds no canonical values: the scope slots hold the copies and
every administrative slot past the scope keeps its index and value. Heaps and
both histories remain in the original entry. -/
theorem empty_parameters (empty : nativeArguments = []) :
    ∃ entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost,
      ∀ slot, scope.length ≤ slot → entry.entry.canonical[slot]? = captured.canonical[slot]? := by
  obtain ⟨entry, added, copied, length, spine, slots⟩ := entry_exists_for_with_spine captured code history inputs
    functions represented heaps locals reference read currentCarried unmapped allowed
  have zero : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  have nil : added = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
  refine ⟨entry, fun slot outside => ?_⟩
  rw [spine, nil, List.nil_append]
  exact slots slot outside

variable (entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
  {added copied : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ copied)
  (slots : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)

include length spine slots in
/-- Every old slot past the scope is shifted by the actual number of allocated
parameters; the scope slots before it hold the entry's copies. -/
theorem shifted_lookup {index : Nat} {value : Value} (outside : scope.length ≤ index)
    (found : captured.canonical[index]? = some value) :
    entry.entry.canonical[code.receipt.loweredParameters.length + index]? = some value := by
  rw [spine, ← length, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, slots index outside]
  exact found

include length spine slots reference in
/-- The surviving frame slot is the same physical reference; no type-tag
argument invents a carried frame or history. -/
theorem shifted_reference :
    entry.entry.canonical[code.receipt.loweredParameters.length + code.referenceIndex]? =
      some (.cellRef prepared.ancestry.layout.frame.type location) :=
  shifted_lookup captured code history inputs functions entry length spine slots
    (by rw [inputs.referenceIndex]; omega) reference

include entry in
theorem same_full_heap :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := entry.entry.heaps

include entry in
theorem same_frame_history :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table entry.next
      (.lambda code.descriptor.id history.ghost) (some history.metadata) := entry.nextHistory

variable {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)

include length spine slots initial in
/-- A real catalog entry supplies the ordered global slot. The allocator's
spine preserves that slot independently of arbitrary unused administrative data. -/
theorem ordered_global
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    entry.entry.canonical[code.receipt.loweredParameters.length + (scope.length + callerPrefix + header.slot)]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  shifted_lookup captured code history inputs functions entry length spine slots (by omega)
    (initial.globals header member)
end Entry

section Concrete
/-- This finite example has two global slots and an arbitrary untouched
administrative suffix. Only the actual one-value prefix shifts the lookups. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let canonical : Environment := [.cellRef .word 3, .cellRef .bool 4, .unit] ++ unused
    let reached : Environment := [.bool true] ++ canonical
    reached[1]? = some (.cellRef .word 3) ∧
      reached[2]? = some (.cellRef .bool 4) ∧ reached.drop 4 = unused := by
  simp
end Concrete

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaEntrySpines
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaModelEntryBounds
/-! The supplied function relation stays unchanged from the original application
through its strict body child and full restored store. Static observations and
runtime views concern represented function values; they are separate from body
execution. No unsized entry agreement supplies a size or an arbitrary stronger
model. The runtime runner reuses the existing actual indexed lambda suite. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaModelEntryBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedLambdaEntryBounds

abbrev actual_reached_reflection := @CallableIndexedLambdaRuntimeEntry.reached_reflects_for
abbrev original_reflection := @CallableIndexedLambdaRuntimeEntry.reflects_original_for
abbrev independent_source_outcome := @CallableIndexedLambdaRuntimeEntry.reflects_for

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- The consumer keeps the body subderivation of the supplied application,
and reads the ordered lexical prefix from its reached state: the parameters
over the copies of the captured scope, with every slot past the scope kept. -/
theorem original_application {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
          reached.canonical = added ++ copied ∧
          (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions reached.mapping reached.world reached.heap reached.store := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed completed
  refine ⟨reached, child, bodyStore, smaller, evaluated, restored, ?_⟩
  obtain ⟨added, copied, length, spine, slots⟩ := reached.spine
  exact ⟨added, copied, length, spine, slots, reached.heaps⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- Zero arguments retain the original strict body edge; the canonical
lexical spine has no added parameter values. The scope slots hold the copies,
and every administrative slot past the scope keeps its index and value. -/
theorem empty_arguments_strict {size : Nat} {result : Value} {finalStore : Store}
    (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ∀ slot, scope.length ≤ slot → reached.canonical[slot]? = captured.canonical[slot]? := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed completed
  obtain ⟨added, copied, length, spine, slots⟩ := reached.spine
  have parameters : code.receipt.loweredParameters.length = 0 := by
    simpa [empty] using represented.length.2
  have noValues : added = [] := List.eq_nil_of_length_eq_zero (length.trans parameters)
  rw [noValues, List.nil_append] at spine
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored, fun slot outside => spine ▸ slots slot outside⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- This consumer erases only the extracted child witness. It never chooses a
new grade for the original completion. -/
theorem original_body {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        Evaluates reached.actual reached.store (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    body_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, evaluated.sound, restored⟩
end Entry

section Actual
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  (functionObservations : CompatibleEquality.FunctionObservations values.checked.catalog functions (Identity prepared))
  (functionViews : FunctionRuntimeViews functions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)


include initial sameFrame in
/-- Global row order comes from the original Entry and the actual native
parameter spine. The same physical slots are retained at the reached state. -/
theorem ordered_globals
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current)
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      callerPrefix + header.slot]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).globals header member

include initial sameFrame in
theorem actual_frame
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current) :
    (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).authority.frameLocation = location ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).authority.current = reached.next ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame).authority.ghost =
      .lambda code.descriptor.id history.ghost :=
  ⟨CallableIndexedLambdaRuntimeEntry.catalog_frame_for reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_current_for reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_ghost_for reached initial sameFrame⟩

variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)


include body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- Empty arity keeps the original strict native witness. The scope slots hold
the copies of the captures and every administrative slot past the scope keeps
its index and value. The same source copies, allocation and caller restoration
follow from the concrete runtime body. -/
theorem empty_arguments [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store} (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history body.toContext functions registry arguments before store location current,
      ∃ child bodyStore outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      (∀ slot, scope.length ≤ slot → reached.canonical[slot]? = captured.canonical[slot]?) ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨reached, child, bodyStore, _, outcome, after, finalMap, finalWorld, smaller, evaluated, _, _, source, _, heaps,
    _, _, _, _, callerEntry, caller⟩ :=
    CallableIndexedLambdaRuntimeEntry.reflects_original_for captured code history body functions functionObservations functionViews extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  obtain ⟨added, copied, length, spine, slots⟩ := reached.spine
  have zero : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  have nil : added = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
  rw [nil, List.nil_append] at spine
  exact ⟨reached, child, bodyStore, outcome, after, finalMap, finalWorld, smaller, evaluated,
    fun slot outside => spine ▸ slots slot outside, source, heaps, callerEntry, caller⟩

end Actual

section StrongerModel
private def SourceFrame (program : SourceSemantics.Program) (source : Dynamic.Value) : Prop :=
  match source with
  | .closure function => Dynamic.ClosureFrame program function
  | _ => True

private def framed {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (base : FunctionModel checked.catalog ambient) (program : SourceSemantics.Program) :
    FunctionModel checked.catalog ambient where
  Represents := fun registry mapping world type source native nativeType =>
    base.Represents registry mapping world type source native nativeType ∧ SourceFrame program source
  projection := fun related => base.projection related.1
  runtime_hasType := fun related => base.runtime_hasType related.1
  source_function := fun related => base.source_function related.1
  extend := fun related registries maps worlds =>
    ⟨base.extend related.1 registries maps worlds, related.2⟩

/-- The independent closure frame is carried in the model itself. -/
theorem frame_from_stronger_relation {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : (framed base program).Represents registry mapping world type (.closure function) native nativeType) :
    Dynamic.ClosureFrame program function := related.2

/-- Observations of represented values survive strengthening. This supplies no
body semantics or missing closure frame to an older value representation. -/
theorem framed_observations {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {identities : Dynamic.Value → Word → Prop}
    (observed : CompatibleEquality.FunctionObservations checked.catalog base identities) :
    CompatibleEquality.FunctionObservations checked.catalog (framed base program) identities :=
  fun related => observed related.1

theorem framed_runtime_views {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    (views : FunctionRuntimeViews base) : FunctionRuntimeViews (framed base program) :=
  fun related => views related.1

/-- The weak relation cannot supply the missing independent source frame. -/
theorem missing_frame_blocks_reverse_inclusion {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : base.Represents registry mapping world type (.closure function) native nativeType)
    (missing : ¬ Dynamic.ClosureFrame program function) :
    ¬ base.Includes (framed base program) := by
  intro includes
  exact missing (frame_from_stronger_relation (includes related))
end StrongerModel

abbrev unsized_agreement_boundary := Tests.SourceCoreCallableIndexedLambdaEntryBounds.agreement_does_not_force_strict
abbrev actual_empty_manifest := Tests.SourceCoreCallableIndexedLambdaEntryBounds.empty_manifest_actual

/-- Actual lambda, capture, fault and resume regressions are reused once.
Generic model preservation and reflection are formal consumers above. -/
def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
  IO.println "lambda model entry bounds: same function relation, original strict children, full heap and caller restore GREEN"
end Tests.SourceCoreCallableIndexedLambdaModelEntryBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaModelPrefix
/-! A function relation can carry an independent source closure frame. The real
entry prefix keeps that stronger relation in its complete allocated heap. A
weaker representation supplies no missing frame. Runtime regressions reuse the
actual indexed lambda roots, including captures, faults and checkpoint resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaModelPrefix
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload CallableIndexedLambdaValues
open CallableIndexedHistory CallableIndexedLambdaEntryPrefix

private def SourceFrame (program : SourceSemantics.Program) (source : Dynamic.Value) : Prop :=
  match source with
  | .closure function => Dynamic.ClosureFrame program function
  | _ => True

private def framed {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (base : FunctionModel checked.catalog ambient) (program : SourceSemantics.Program) :
    FunctionModel checked.catalog ambient where
  Represents := fun registry mapping world type source native nativeType =>
    base.Represents registry mapping world type source native nativeType ∧ SourceFrame program source
  projection := fun related => base.projection related.1
  runtime_hasType := fun related => base.runtime_hasType related.1
  source_function := fun related => base.source_function related.1
  extend := fun related registries maps worlds =>
    ⟨base.extend related.1 registries maps worlds, related.2⟩

/-- This static witness travels with a function value; native typing does not
construct it. -/
theorem frame_from_stronger_relation {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : (framed base program).Represents registry mapping world type (.closure function) native nativeType) :
    Dynamic.ClosureFrame program function := related.2

/-- A representation of the same native closure in the older relation cannot
justify the stronger model when its independent source frame is absent. -/
theorem missing_frame_prevents_reverse_inclusion {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : base.Represents registry mapping world type (.closure function) native nativeType)
    (missing : ¬ Dynamic.ClosureFrame program function) :
    ¬ base.Includes (framed base program) := by
  intro includes
  exact missing (frame_from_stronger_relation (includes related))

/-- Parameter allocation retains the stronger relation in every cell of the
actual reached heap, including old cells outside the parameter prefix. -/
theorem entry_preserves_full_model {values : SourceCoreCompatibleValues.Context}
    {prepared : Prepared values.checked} {function : Dynamic.Closure}
    {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Core.Environment}
    {captured : Captures prepared mapping world scope function.captured capturedActual}
    {code : Code prepared function scope captured.administrative} {history : History code}
    {inputs : Context code} {program : SourceSemantics.Program}
    {base : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    {before : Dynamic.Heap} {store : Store} {location : Core.Location}
    {current : NativeFrame} {currentGhost : GhostFrame}
    (entry : EntryFor captured code history inputs (framed base program) registry arguments nativeArguments
      before store location current currentGhost) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry (framed base program)
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := entry.entry.heaps

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaModelPrefix
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaModelPreservation
/-! A stronger function model carries independent source frames. Its value
observations and runtime views follow from the original representation. These
are representation properties; neither executes or assumes a callable body.
The generic preservation endpoints keep this model in results and all cells. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaModelPreservation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload CompatibleEquality

private def Frame (program : SourceSemantics.Program) (source : Dynamic.Value) : Prop :=
  match source with
  | .closure function => Dynamic.ClosureFrame program function
  | _ => True

private def framed {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (base : FunctionModel checked.catalog ambient) (program : SourceSemantics.Program) :
    FunctionModel checked.catalog ambient where
  Represents := fun registry mapping world type source native nativeType =>
    base.Represents registry mapping world type source native nativeType ∧ Frame program source
  projection := fun related => base.projection related.1
  runtime_hasType := fun related => base.runtime_hasType related.1
  source_function := fun related => base.source_function related.1
  extend := fun related registries maps worlds =>
    ⟨base.extend related.1 registries maps worlds, related.2⟩

theorem observations {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {identity : Dynamic.Value → Word → Prop}
    (observed : FunctionObservations checked.catalog base identity) :
    FunctionObservations checked.catalog (framed base program) identity :=
  fun related => observed related.1

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    (viewed : FunctionRuntimeViews base) : FunctionRuntimeViews (framed base program) :=
  fun related => viewed related.1

/-- Independent closure provenance remains available after allocation, without
reconstructing it from a native closure or a compatibility-erased type. -/
theorem frame_survives_extension {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry futureRegistry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : (framed base program).Represents registry mapping world type (.closure function) native nativeType)
    (registries : SourceCoreRawMetadata.Extends registry futureRegistry)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    (framed base program).Represents futureRegistry futureMapping futureWorld type (.closure function) native nativeType ∧
      Dynamic.ClosureFrame program function :=
  ⟨(framed base program).extend related registries maps worlds, related.2⟩

abbrev entry_preserves := @CallableIndexedLambdaRuntimePreservation.entry_preserves_for
abbrev preserves := @CallableIndexedLambdaRuntimePreservation.preserves_for

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaModelPreservation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaNamedRuntimeBodyMeaning
/-! The actual compiler view supplies named/direct receipts at the closure's
same complete dictionary. Source and native bodies consume their original grades.
Catalog authority, captures and history are separate static inputs. This cut
closes named recursion inside lambda bodies; nested lambda formation, indirect
apply, general methods and comptime remain separate grammar boundaries. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaNamedRuntimeBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaNamedRuntimeBodyMeaning

abbrev actual_body := @of_tree
abbrev original_source_child := @CallableIndexedLambdaRuntimePreservation.preserves_named_sized_for
abbrev original_native_child := @CallableIndexedLambdaRuntimeEntry.reflects_original_named_for
abbrev closed_body_preserves := @Body.preserves_sized
abbrev closed_body_reflects := @Body.reflects_sized

section Receipt
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code prepared function scope administrative} {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body headers code program registry faults)

include body in
theorem same_actual_finish :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body ∧
    body.toKernel.emitted = body.emitted := ⟨body.accepted, rfl⟩

include body in
theorem complete_dictionary :
    body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.context ∧ function.evidence.Covers body.context ∧
    body.tree.CatalogSites .reachable registry faults ∧ body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.valid.ledger, body.valid.runtime, body.valid.covers, body.sites, body.actualSites⟩

include body in
theorem ordered_parameter_context :
    MonoBindersExtend function.source.owner function.context function.parameters body.types body.context ∧
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope :=
  ⟨body.extended, CallableIndexedLambdaSemanticInvocation.body_scope code⟩
end Receipt

section Ordinary
open CallableAncestryPairedLookup RecursiveNamedCatalog CallableLambdaViewNamedRuntimeCertificates
variable {checked : Checked} {base : Base checked} {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program} {headers : Inventory prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
  (receipt : Ordinary headers compilation source context children scope id output)

include receipt in
theorem actual_emission_kept :
    output.expression = SourceCoreCalls.call receipt.header.named.signature
      (scope.length + compilation.administrativePrefix + receipt.emission.index)
      (SourceCoreCalls.packArguments receipt.codes).expression compilation.internalReason ∧
    compilation.globals[receipt.emission.index]? = some receipt.header.named.signature := by
  obtain ⟨code, _, _, selected⟩ := receipt.emission.equation
  exact ⟨code, selected⟩

end Ordinary

section Boundaries
/-- Runtime ledger validity retains an unused assumption row; it does not
turn the body into the old ordinary literal context. -/
abbrev unused_ledger := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.runtime_not_ordinary

/-- The source child grade has no equality premise with a native body grade. -/
theorem independent_grades (source native budget : Nat) (sourceWithin : source ≤ budget)
    (nativeWithin : native < budget) : source ≤ budget ∧ native < budget := ⟨sourceWithin, nativeWithin⟩

/-- Actual emitted code may be typed with an arbitrary unused suffix. The
canonical dictionary/global prefix and history are not inferred from it. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let captured : Environment := [.cellRef .word 11, .cellRef .bool 12, .cellRef .unit 13] ++ unused
    captured[0]? = some (.cellRef .word 11) ∧ captured[1]? = some (.cellRef .bool 12) ∧
      captured[2]? = some (.cellRef .unit 13) ∧ captured.drop 3 = unused := by simp
end Boundaries

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "trait Mark<T> {}", "trait Stamp<T> {}", "impl Mark<Word> {}", "impl Stamp<Word> {}",
    "function keep(value: Word) returns(Word) { return value + 1; }",
    "function recurse(value: Word) returns(Word) { if(value == 0) { return 0; } return recurse(value - 1) + 1; }",
    "function marked<T>(value: T) returns(T) where T: Mark, T: Stamp, T: Mark { return value; }",
    "function missing(value: Word) returns(Word) { let gap: Word; return gap; }",
    "function named(seed: Word) returns(F) { let unused: Word = 99; return lam(item: Word) -> Word { let prior = seed + item; return keep(prior); }; }",
    "function nested(seed: Word) returns(F) { return lam(item: Word) -> Word { return keep(keep(item + seed)); }; }",
    "function recursive(seed: Word) returns(F) { return lam(item: Word) -> Word { return recurse(item) + seed; }; }",
    "function direct(seed: Word) returns(F) { return lam(item: Word) -> Word { return marked(seed + item); }; }",
    "function firstfault(seed: Word) returns(F) { return lam(item: Word) -> Word { let gap: Word; return keep(gap) + keep(seed); }; }",
    "function laterfault(seed: Word) returns(F) { return lam(item: Word) -> Word { let written = keep(seed); let gap: Word; return keep(gap); }; }",
    "function bodyfault(seed: Word) returns(F) { return lam(item: Word) -> Word { return missing(item); }; }",
    "function zero(seed: Word) returns(function() returns(Word)) { return lam() -> Word { return keep(seed); }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"runtime lambda missing fixture {name}")

private def containsLambda : Nat → Core.Expr → Core.Expr → Bool
  | 0, _, _ => false
  | fuel + 1, expected, code =>
    let recurse := containsLambda fuel expected
    match code with
    | .lambda _ _ body => body == expected || recurse body
    | .pair a b | .apply a b | .storeCell a b | .letE a b | .binary _ a b => recurse a || recurse b
    | .first a | .second a | .inLeft _ a | .inRight _ a | .newCell _ a | .loadCell a
    | .construct _ a | .unary _ a => recurse a
    | .caseE a b c | .ifE a b c | .ternary _ a b c => recurse a || recurse b || recurse c
    | .matchData _ _ a branches => recurse a || branches.any recurse
    | _ => false

/-- Each lambda call first copies the lambda's captures, most recent binding
first, from their creation-time values; the parameter, the body's binders and
the named callees' cells follow. -/
private def expectedRows (name : String) : List (String × TypeSystem.Ty × Option Core.Value) :=
  let w := fun n => some (Core.Value.word (Word.ofNatModulo n))
  match name with
  | "named" => [("unused", .word, w 99), ("seed", .word, w 3), ("item", .word, w 4), ("prior", .word, w 7), ("value", .word, w 7)]
  | "nested" => [("seed", .word, w 3), ("item", .word, w 4), ("value", .word, w 7), ("value", .word, w 8)]
  | "recursive" => [("seed", .word, w 3), ("item", .word, w 4), ("value", .word, w 4), ("value", .word, w 3), ("value", .word, w 2), ("value", .word, w 1), ("value", .word, w 0)]
  | "direct" => [("seed", .word, w 3), ("item", .word, w 4), ("value", .word, w 7)]
  | "firstfault" => [("seed", .word, w 3), ("item", .word, w 4), ("gap", .word, none)]
  | "laterfault" => [("seed", .word, w 3), ("item", .word, w 4), ("value", .word, w 3), ("written", .word, w 4), ("gap", .word, none)]
  | "bodyfault" => [("seed", .word, w 3), ("item", .word, w 4), ("value", .word, w 4), ("gap", .word, none)]
  | "zero" => [("seed", .word, w 3), ("value", .word, w 3)]
  | _ => []

private def native_bodies : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "runtime lambda checker" (checkProgram workspace)
  let names := ["named", "nested", "recursive", "direct", "firstfault", "laterfault", "bodyfault", "zero"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"runtime lambda worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "runtime lambda base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "runtime lambda indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let word := Word.ofNatModulo
  for (name, selectedKey) in names.zip keys do
    let created ← SourceCompilerFeatureSupport.get "runtime lambda maker" (prepared.runSource selectedKey [.word (word 3)] 500000)
    match created.result.native.observation with
    | .succeeded native original =>
      let inert := Core.Value.closure .unit .unit (.var 0) [.word (word 991), .bool true]
      let before := original ++ [inert]
      let arguments := if name == "zero" then .unit else .word (word (4))
      let state := Core.State.initial CallableIndexedLambdaCalls.applyPayload [native, arguments] before
      let expected := Core.runStateful 500000 state
      let (richer, actualCaptured) ← match native with
        | .pair (.pair manifest (.closure parameter result body captures)) origin =>
          let extended := captures ++ [.bool true, .unit, inert]
          pure (.pair (.pair manifest (.closure parameter result body extended)) origin, extended)
        | _ => throw (IO.userError "named lambda actual captured closure missing")
      let richerState := Core.State.initial CallableIndexedLambdaCalls.applyPayload [richer, arguments] before
      SourceCompilerFeatureSupport.require (Core.runStateful 500000 richerState == expected)
        s!"named lambda nonempty globals and unused native capture suffix {name}"
      SourceCompilerFeatureSupport.require (actualCaptured.drop (actualCaptured.length - 3) == [.bool true, .unit, inert])
        "named lambda full arbitrary capture suffix retained"
      for fuel in [0, 1, 31, 500000] do
        let actual := match Core.runStateful fuel state with
          | .outOfFuel checkpoint => Core.runStateful 500000 checkpoint
          | finished => finished
        SourceCompilerFeatureSupport.require (actual == expected) s!"runtime lambda full resume {name}/{fuel}"
      match expected with
      | .done value after =>
        SourceCompilerFeatureSupport.require (after.take before.length == before) s!"runtime lambda prefix/captures {name}"
        let ledger ← SourceCompilerFeatureSupport.get "runtime lambda ordered allocations" (SourceCoreAllocationLedger.scan prepared.layouts [] after)
        let rows := ledger.rows.filter (fun row => row.markerIndex ≥ before.length)
        let expected := expectedRows name
        SourceCompilerFeatureSupport.require
          (decide (rows.map (fun row => (row.entry.key.binder.name, row.entry.key.binder.scheme.body, row.payload)) = expected))
          s!"runtime lambda full ordered raw bindings {name}"
        let (executable, snapshot) ← match native with
          | .pair (.pair _ (.closure _ _ executable (lexical :: _))) (.word origin) =>
            match SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame lexical with
            | some frame => pure (executable, SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
                (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table origin frame .empty))
            | none => throw (IO.userError "runtime lambda lexical frame decode")
          | _ => throw (IO.userError "runtime lambda actual closure shape")
        let administrativeCount := 0
        SourceCompilerFeatureSupport.require
          (ledger.pending.isNone && after.length == before.length + 3 * rows.length + administrativeCount)
          s!"runtime lambda unaccounted native cells {name}"
        for (row, index) in rows.zipIdx do
          let expectedSnapshot ← if row.entry.key.owner == selectedKey then pure snapshot else do
            let origin ← match prepared.ancestry.graph.inputs.callable.table.idAt? (.named row.entry.key.owner) with
              | some origin => pure origin
              | none => throw (IO.userError "named lambda actual callee descriptor missing")
            pure (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
              (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))
          SourceCompilerFeatureSupport.require
            (row.markerIndex == before.length + 3 * index + 1 && after[row.markerIndex - 1]? == some expectedSnapshot)
            "runtime lambda exact snapshot/marker/payload order"
        for index in List.range administrativeCount do
          let location := before.length + 3 * rows.length + index
          match after[location]? with
          | some (.inRight .unit (.closure .unit resultType body captures)) =>
            SourceCompilerFeatureSupport.require
              (resultType == LocalLoop.resultType .word && containsLambda 2000 body executable &&
               captures.head? == some (.cellRef (OptionalCell.cellType (LocalLoop.functionType .word)) location) &&
               Core.infer? (.unit :: captures.map Core.Value.type) body prepared.layouts.definitions == some resultType)
              "runtime lambda full loop closure code/self/capture types"
          | _ => throw (IO.userError "runtime lambda loop administrative cell")
        if name == "firstfault" || name == "laterfault" || name == "bodyfault" then
          match value with
          | .inLeft .word (.word token) =>
            match created.result.diagnostics.diagnostic? token, rows.getLast? with
            | some diagnostic, some missing =>
              SourceCompilerFeatureSupport.require
                (diagnostic.error == .uninitializedLocal missing.entry.key.binder.id && missing.payload.isNone)
                "runtime lambda exact first missing binder"
            | _, _ => throw (IO.userError "runtime lambda missing fault receipt")
          | _ => throw (IO.userError "runtime lambda expected failure")
        else
          let result := if name == "named" then 8 else if name == "nested" then 9 else if name == "zero" then 4 else 7
          SourceCompilerFeatureSupport.require (value == .inRight .word (.word (word result)))
            s!"runtime lambda result {name}"

      | other => throw (IO.userError s!"runtime lambda incomplete {name}: {reprStr other}")
    | other => throw (IO.userError s!"runtime lambda creation {name}: {reprStr other}")

def run : IO Unit := do
  native_bodies
  IO.println "named lambda bodies: actual ordinary/direct receipts, recursion, ordered argument cells, first/later/body faults, full captures/store and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaNamedRuntimeBodyMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaNestedRuntimeBodyMeaning
/-! Actual public compilation and native observations audit nested formation.
The runtime harness retains full captures and stores. Static Code/History and
catalog authority remain formal receipts, rather than inferred observations. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaNestedRuntimeBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableIndexedHistory CallableIndexedLambdaValues

open SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
open CallableIndexedLambdaNestedRuntimeCertificates CallableIndexedLambdaNestedRuntimeBodyMeaning

abbrev actual_body := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.of_tree
abbrev original_source_child := @CallableIndexedLambdaRuntimePreservation.preserves_nested_sized_for
abbrev original_native_child := @CallableIndexedLambdaRuntimeEntry.reflects_original_nested_for

variable {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : Locations (prepared := indexed.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {rank : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

section Execution
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code indexed function outerScope administrative)
  (body : Body headers caller registry faults rank code)
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0
    (model headers locations registry faults profile) registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
local notation "F" => model headers locations registry faults profile
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1
include body complete globals slots extension family uninitialized missing escaped owners in
theorem closed_body_preserves [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical :=
  CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.preserves_sized code body profile complete globals slots extension family owners uninitialized missing escaped budget size within environments heaps locals agrees typed reference read unmapped installed trace

include body complete globals slots extension family uninitialized missing escaped in
theorem closed_body_reflects [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.body.context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical :=
  CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.reflects_sized code body profile complete globals slots extension family uninitialized missing escaped budget size within environments heaps locals agrees typed reference read unmapped installed evaluated

end Execution

section Receipts
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code indexed function outerScope administrative}
  (body : Body headers caller registry faults rank code)

include body in
theorem same_actual_finish :
    SourceCoreLoops.lowerStatementsWithPolicy body.body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body ∧ body.toKernel.emitted = body.body.emitted := ⟨body.body.accepted, rfl⟩

include body in
theorem complete_dictionary :
    body.body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.body.context ∧ function.evidence.Covers body.body.context ∧
    body.body.tree.CatalogSites .reachable registry faults ∧ body.body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.body.valid.ledger, body.body.valid.runtime, body.body.valid.covers, body.body.sites, body.body.actualSites⟩

include body in
theorem actual_source_compilation :
    function.source = CallableIndexedNamedGeneration.source caller.named ∧
    code.compilation = CallableIndexedNamedGeneration.context indexed caller.named ∧ code.active = [] :=
  ⟨body.source, body.compilation, body.active⟩
end Receipts

section Captures
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures indexed mapping world outerScope function.captured actual)
  (code : Code indexed function outerScope captured.administrative) (history : History code)
  (supportedBody : Support headers registry faults code)
  (supported : Condition (registry := registry) (faults := faults) headers locations captured code history supportedBody)

include supported in
theorem actual_capture_globals :
    history.metadata = CallableIndexedNamedGeneration.state supportedBody.1.named ∧
    ∃ location, CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 outerScope captured.canonical location :=
  supported
end Captures

section Boundaries
variable {support : RankedSupport (indexed := indexed)} {children : GenericExpressionMeaning.Certificate}
  {compilation : SourceCoreFunctions.Context}

theorem literal_rank_zero
    (head : Lambda support 0 caller source context evidence scope id lowered) : False :=
  Nat.not_lt_zero _ head.smaller

/-- Named recursion has no static rank decrease requirement. -/
theorem named_at_rank_zero
    (head : CallableLambdaViewNamedRuntimeCertificates.Head (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
      headers compilation source context evidence children scope id lowered) :
    Head support 0 caller headers compilation source context evidence children scope id lowered := .existing head

/-- A native cell tag does not identify its physical location. -/
theorem same_type_different_reference (type : Core.Ty) :
    (Value.cellRef type 0).type = (Value.cellRef type 1).type ∧ Value.cellRef type 0 ≠ Value.cellRef type 1 := by
  constructor
  · rfl
  · intro equal
    cases equal

/-- Full source metadata does not replace the actual lambda ghost by a named one. -/
theorem lambda_history_is_not_named
    {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code indexed function outerScope administrative} {history : History code}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (entry : CallableIndexedLambdaCatalogEntries.SourceEntry code history headers locations 0 1 scope mapping world heap store canonical)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state caller.named) (origin : Word) :
    history.metadata = CallableIndexedNamedGeneration.state caller.named ∧ entry.catalog.authority.ghost ≠ .named origin := by
  refine ⟨metadata, ?_⟩
  rw [entry.ghost]
  intro same
  cases same

/-- The actual source entry and its physical frame are supplied independently. -/
abbrev reached_entry := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.entry_of_source
end Boundaries

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "type Maker = function(Word) returns(F);",
    "trait Mark<T> {}", "trait Stamp<T> {}", "impl Mark<Word> {}", "impl Stamp<Word> {}",
    "function keep(value: Word) returns(Word) { return value + 1; }",
    "function recurse(value: Word) returns(Word) { if(value == 0) { return 0; } return recurse(value - 1) + 1; }",
    "function marked<T>(value: T) returns(T) where T: Mark, T: Stamp, T: Mark { return value; }",
    "function nested(seed: Word) returns(Maker) { return lam(item: Word) -> F { let prior = keep(seed + item); return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function direct(seed: Word) returns(Maker) { return lam(item: Word) -> F { let prior = marked(seed + item); return lam(last: Word) -> Word { return marked(prior + last); }; }; }",
    "function recursive(seed: Word) returns(Maker) { return lam(item: Word) -> F { let prior = recurse(item) + seed; return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function emptyouter(seed: Word) returns(function() returns(F)) { return lam() -> F { return lam(last: Word) -> Word { return keep(seed + last); }; }; }",
    "function emptyinner(seed: Word) returns(function(Word) returns(function() returns(Word))) { return lam(item: Word) -> function() returns(Word) { return lam() -> Word { return keep(seed + item); }; }; }",
    "function firstfault(seed: Word) returns(Maker) { return lam(item: Word) -> F { let gap: Word; let prior = keep(gap); return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function laterfault(seed: Word) returns(Maker) { return lam(item: Word) -> F { let written = keep(seed); let gap: Word; let prior = keep(gap); return lam(last: Word) -> Word { return keep(prior + last); }; }; }",
    "function parallel(seed: Word) returns(Maker) { return lam(item: Word) -> F { let first = lam(last: Word) -> Word { return keep(seed + last); }; return lam(last: Word) -> Word { return keep(item + last); }; }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"nested lambda missing fixture {name}")

private def containsLambda : Nat → Core.Expr → Core.Expr → Bool
  | 0, _, _ => false
  | fuel + 1, expected, code =>
    let recurse := containsLambda fuel expected
    match code with
    | .lambda _ _ body => body == expected || recurse body
    | .pair a b | .apply a b | .storeCell a b | .letE a b | .binary _ a b => recurse a || recurse b
    | .first a | .second a | .inLeft _ a | .inRight _ a | .newCell _ a | .loadCell a | .construct _ a | .unary _ a => recurse a
    | .caseE a b c | .ifE a b c | .ternary _ a b c => recurse a || recurse b || recurse c
    | .matchData _ _ a branches => recurse a || branches.any recurse
    | _ => false

private def closureSuffix (native : Core.Value) (inert : Core.Value) : IO (Core.Value × Core.Expr) := do
  match native with
  | .pair (.pair manifest (.closure parameter result body captures)) origin =>
    pure (.pair (.pair manifest (.closure parameter result body (captures ++ [.bool true, .unit, inert]))) origin, body)
  | _ => throw (IO.userError "nested lambda actual closure carrier")

/-- The only admitted difference is this exact appended unused capture tail.
Every code, annotation, origin, used capture, cell and store position is compared. -/
private def suffixValue : Nat → Core.Value → Core.Value → Core.Value → Bool
  | 0, expected, actual, _ => expected == actual
  | fuel + 1, expected, actual, inert =>
    let recur := fun expected actual => suffixValue fuel expected actual inert
    match expected, actual with
    | .pair a b, .pair c d => recur a c && recur b d
    | .inLeft t a, .inLeft u b | .inRight t a, .inRight u b => t == u && recur a b
    | .closure p r body captures, .closure ap ar abody acaptures =>
      p == ap && r == ar && body == abody && acaptures.length ≥ captures.length &&
      (captures.zip (acaptures.take captures.length)).all (fun (a,b) => recur a b) &&
      (acaptures.drop captures.length == [] || acaptures.drop captures.length == [.bool true, .unit, inert])
    | _, _ => expected == actual

private def complete (state : Core.State) : IO Core.StatefulRunResult := do
  let expected := Core.runStateful 500000 state
  for fuel in [0, 1, 31, 500000] do
    let actual := match Core.runStateful fuel state with
      | .outOfFuel checkpoint => Core.runStateful 500000 checkpoint
      | done => done
    SourceCompilerFeatureSupport.require (actual == expected) s!"nested lambda full resume {fuel}"
  pure expected

/-- Closures capture by value: each call first copies its captures, and
creating an inner lambda copies the bindings in scope, most recent first. The
outer call copies `seed`; an inner lambda copies its scope when it is created
and again when it is called. -/
private def expectedNames (name : String) : List String :=
  match name with
  | "nested" | "direct" => ["seed", "item", "value", "prior", "prior", "item", "seed", "prior", "item", "seed", "last", "value"]
  | "recursive" => ["seed", "item", "value", "value", "value", "value", "value", "prior", "prior", "item", "seed",
      "prior", "item", "seed", "last", "value"]
  | "emptyouter" => ["seed", "seed", "seed", "last", "value"]
  | "emptyinner" => ["seed", "item", "item", "seed", "item", "seed", "value"]
  | "firstfault" => ["seed", "item", "gap"]
  | "laterfault" => ["seed", "item", "value", "written", "gap"]
  | "parallel" => ["seed", "item", "item", "seed", "first", "first", "item", "seed", "first", "item", "seed", "last", "value"]
  | _ => []

private def native_bodies : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "nested lambda checker" (checkProgram workspace)
  let names := ["nested", "direct", "recursive", "emptyouter", "emptyinner", "firstfault", "laterfault", "parallel"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"nested lambda worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "nested lambda base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "nested lambda indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let word := Word.ofNatModulo
  for (name, selectedKey) in names.zip keys do
    let created ← SourceCompilerFeatureSupport.get "nested lambda maker" (prepared.runSource selectedKey [.word (word 3)] 500000)
    match created.result.native.observation with
    | .succeeded native original =>
      let inert := Core.Value.closure .unit .unit (.var 0) [.word (word 991), .bool true]
      let before := original ++ [inert]
      let arguments := if name == "emptyouter" then .unit else .word (word 4)
      let state := Core.State.initial CallableIndexedLambdaCalls.applyPayload [native, arguments] before
      let expected ← complete state
      let (richer, outerBody) ← closureSuffix native inert
      let withSuffix := Core.runStateful 500000 (Core.State.initial CallableIndexedLambdaCalls.applyPayload [richer, arguments] before)
      match expected, withSuffix with
      | .done (.inRight resultType (.pair (.pair manifest (.closure parameter result body captures)) origin)) after,
        .done (.inRight actualType (.pair (.pair actualManifest (.closure actualParameter actualResult actualBody actualCaptures)) actualOrigin)) actualAfter =>
        SourceCompilerFeatureSupport.require
          (actualType == resultType && actualManifest == manifest && actualParameter == parameter && actualResult == result &&
           actualBody == body && actualOrigin == origin && actualAfter.length == after.length &&
           (after.zip actualAfter).all (fun (a,b) => suffixValue 3000 a b inert) &&
           (captures.zip (actualCaptures.take captures.length)).all (fun (a,b) => suffixValue 3000 a b inert) && actualCaptures.drop captures.length == [.bool true, .unit, inert])
          s!"nested lambda full actual returned captures with unused outer suffix {name}: types={actualType == resultType}, manifest={actualManifest == manifest}, code={actualBody == body}, origin={actualOrigin == origin}, storelen={actualAfter.length == after.length}, store={(after.zip actualAfter).all (fun (a,b) => suffixValue 3000 a b inert)}, prefix={actualCaptures.take captures.length == captures}, lengths={captures.length}/{actualCaptures.length}, tail={actualCaptures.drop captures.length == [.bool true, .unit, inert]}"
      | _, _ => SourceCompilerFeatureSupport.require (withSuffix == expected) s!"nested lambda original fault suffix {name}"
      let (result, finalStore) ← match expected with
        | .done (.inRight _ inner) after =>
          let (richerInner, innerBody) ← closureSuffix inner inert
          SourceCompilerFeatureSupport.require (containsLambda 3000 innerBody outerBody) "nested lambda actual emitted child body"
          let last := if name == "emptyinner" then .unit else .word (word 5)
          let second := Core.State.initial CallableIndexedLambdaCalls.applyPayload [inner, last] after
          let finished ← complete second
          SourceCompilerFeatureSupport.require (Core.runStateful 500000 (Core.State.initial CallableIndexedLambdaCalls.applyPayload [richerInner, last] after) == finished)
            s!"nested lambda arbitrary unused inner suffix {name}"
          match finished with
          | .done value store => pure (value, store)
          | other => throw (IO.userError s!"nested lambda inner completion {name}: {reprStr other}")
        | .done value after => pure (value, after)
        | other => throw (IO.userError s!"nested lambda original completion {name}: {reprStr other}")
      SourceCompilerFeatureSupport.require (finalStore.take before.length == before) "nested lambda full original store prefix"
      let ledger ← SourceCompilerFeatureSupport.get "nested lambda full allocations" (SourceCoreAllocationLedger.scan prepared.layouts [] finalStore)
      let rows := ledger.rows.filter (fun row => row.markerIndex ≥ before.length)
      SourceCompilerFeatureSupport.require (rows.map (fun row => row.entry.key.binder.name) == expectedNames name)
        s!"nested lambda exact ordered allocation names {name}: {reprStr (rows.map (fun row => row.entry.key.binder.name))}"
      SourceCompilerFeatureSupport.require (ledger.pending.isNone && finalStore.length == before.length + 3 * rows.length)
        "nested lambda all administrative/source cells accounted"
      for (row, index) in rows.zipIdx do
        SourceCompilerFeatureSupport.require (row.markerIndex == before.length + 3 * index + 1)
          "nested lambda exact snapshot/marker/payload order"
        SourceCompilerFeatureSupport.require (row.payload.isSome || row.entry.key.binder.name == "gap")
          "nested lambda every reached nonfault cell initialized"
      if name == "firstfault" || name == "laterfault" then
        match result, rows.getLast? with
        | .inLeft _ (.word token), some missing =>
          match created.result.diagnostics.diagnostic? token with
          | some diagnostic =>
            SourceCompilerFeatureSupport.require
              (diagnostic.error == .uninitializedLocal missing.entry.key.binder.id && missing.payload.isNone)
              "nested lambda exact first missing ID"
          | none => throw (IO.userError "nested lambda fault token")
        | _, _ => throw (IO.userError "nested lambda expected original fault")
      else
        let n := if name == "nested" then 14 else if name == "direct" then 12 else if name == "recursive" then 13
          else if name == "emptyouter" then 9 else if name == "emptyinner" then 8 else 10
        SourceCompilerFeatureSupport.require (result == .inRight .word (.word (word n))) s!"nested lambda final result {name}"
    | other => throw (IO.userError s!"nested lambda creation {name}: {reprStr other}")

def run : IO Unit := do
  native_bodies
  IO.println "nested lambda bodies: actual nested formation, ordinary/direct/recursive children, empty arities, ordered cells, first/later faults, full captures/store and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaNestedRuntimeBodyMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeEntry
/-! The actual canonical body receipt closes reflection from the supplied
original application. The consumers retain its strict native body child,
independent source body grade, ordered globals and the restored caller Entry.
Runtime regression delegates to existing capture/call suites; it does not
assert identity with an arbitrary unsized older lambda Entry or closure of
named/indirect recursive body syntax. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimeEntry
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames

abbrev actual_reached_body := @CallableIndexedLambdaRuntimeEntry.reached_reflects
abbrev original_strict_state := @CallableIndexedLambdaRuntimeEntry.reflects_original
abbrev original_source_outcome := @CallableIndexedLambdaRuntimeEntry.reflects
abbrev finish_without_recompilation := @RecursiveNamedFunctionFinishBounds.reflects_at_emitted

section Actual
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)


include initial sameFrame in
/-- Global row order comes from the original Entry and the actual native
parameter spine. The same physical slots are retained at the reached state. -/
theorem ordered_globals
    (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current)
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      callerPrefix + header.slot]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).globals header member

include initial sameFrame in
theorem actual_frame
    (reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current) :
    (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).authority.frameLocation = location ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).authority.current = reached.next ∧
    (CallableIndexedLambdaRuntimeEntry.catalog_entry reached initial sameFrame).authority.ghost =
      .lambda code.descriptor.id history.ghost :=
  ⟨CallableIndexedLambdaRuntimeEntry.catalog_frame reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_current reached initial sameFrame,
    CallableIndexedLambdaRuntimeEntry.catalog_ghost reached initial sameFrame⟩

variable {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)


include body profile extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
/-- Empty arity keeps the original strict native witness. The scope slots hold
the copies of the captures and every administrative slot past the scope keeps
its index and value. The same source copies, allocation and caller restoration
follow from the concrete runtime body. -/
theorem empty_arguments [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {result : Value} {finalStore : Store} (empty : nativeArguments = [])
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.Prefix captured code history body.toContext profile registry arguments before store location current,
      ∃ child bodyStore outcome after finalMap finalWorld,
      child < size ∧ EvaluationSize child reached.actual reached.store
        (code.receipt.body.rename reached.embedding) result bodyStore ∧
      (∀ slot, scope.length ≤ slot → reached.canonical[slot]? = captured.canonical[slot]?) ∧
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨reached, child, bodyStore, _, outcome, after, finalMap, finalWorld, smaller, evaluated, _, _, source, _, heaps,
    _, _, _, _, callerEntry, caller⟩ :=
    CallableIndexedLambdaRuntimeEntry.reflects_original captured code history body profile extension uninitialized missing escaped initial sameFrame
      represented heaps locals reference read currentCarried allowed completed
  obtain ⟨added, copied, length, spine, slots⟩ := reached.spine
  have zero : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  have nil : added = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
  rw [nil, List.nil_append] at spine
  exact ⟨reached, child, bodyStore, outcome, after, finalMap, finalWorld, smaller, evaluated,
    fun slot outside => spine ▸ slots slot outside, source, heaps, callerEntry, caller⟩

end Actual

/-- Existing whole capture and callable regressions are reused once. New
reflection itself is checked above through its original sized completion. -/
def run : IO Unit := do
  Tests.SourceCoreCallableIndexedLambdaViewCalls.run
  Tests.SourceCoreCallableIndexedLambdaValues.run

end Tests.SourceCoreCallableIndexedLambdaRuntimeEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaRuntimePreservation
/-! The independent source success/fault consumers retain the full real heap
and caller catalog restored by the actual payload application. The source
copies of the captures and the parameter allocation are matched to the
generated prefix, without an old Entry identity.
The native regression reuses the seven actual builtin-body lambda cases. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimePreservation
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev actual_prefix_preserves := @CallableIndexedLambdaRuntimePreservation.entry_preserves
abbrev independent_call_preserves := @CallableIndexedLambdaRuntimePreservation.preserves

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap}
  {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

variable {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  {currentMetadata : Option MetadataState}
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include body extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
theorem source_value_completes [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {payload : Dynamic.Value} {after : Dynamic.Heap}
    (executed : Dynamic.CallableApplies program callerContext callerEvidence function.evidence before
      (.closure function) arguments payload after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload (.inRight .word value) finalStore ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType payload value code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, rest⟩ :=
    CallableIndexedLambdaRuntimePreservation.preserves captured code history body profile extension uninitialized missing escaped
      initial sameFrame represented heaps locals reference read currentCarried allowed (.value executed)
  cases related with
  | value related => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, related, rest⟩

include body extension uninitialized missing escaped initial sameFrame represented heaps locals reference read currentCarried allowed in
theorem source_fault_completes [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (executed : Dynamic.CallableFaults program callerContext callerEvidence function.evidence before
      (.closure function) arguments reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store CallableIndexedLambdaCalls.applyPayload (.inLeft code.receipt.resultCore (.word token)) finalStore ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore captured.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, related, rest⟩ :=
    CallableIndexedLambdaRuntimePreservation.preserves captured code history body profile extension uninitialized missing escaped
      initial sameFrame represented heaps locals reference read currentCarried allowed (.fault executed)
  cases related with
  | fault related => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, related, rest⟩

include represented in
/-- Empty native arity is linked to the actual ordered source parameters. -/
theorem empty_parameters (empty : nativeArguments = []) : function.parameters = [] := by
  have count : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  rw [CallableIndexedLambdaEntryPrefix.parameters code, List.eq_nil_of_length_eq_zero count]
  rfl

/-- Two independent copies of the captures and allocations for the actual
closure inputs give the same copies, source environment and full heap. No
equality of native prefix receipts follows. -/
theorem actual_allocation
    (entry : CallableIndexedLambdaRuntimeBody.Entry captured code history body profile arguments nativeArguments before store location current currentGhost)
    {copies environment : Dynamic.Environment} {copiedHeap bound : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap)
    (allocated : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment bound) :
    entry.entry.copies = copies ∧ entry.entry.copiedHeap = copiedHeap ∧
      entry.entry.environment = environment ∧ entry.entry.heap = bound := by
  obtain ⟨sameCopies, sameHeap⟩ := entry.entry.copy.functional copy
  subst sameCopies sameHeap
  exact ⟨rfl, rfl, FunctionCallBody.allocations_same entry.entry.allocation allocated⟩

/-- Reuse the actual whole for/while/match/default/fault/empty-arity bodies. -/
def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run

end Tests.SourceCoreCallableIndexedLambdaRuntimePreservation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeValues
/-! Static consumers keep the body for the actual generated lambda, including
its source frame and full ledger. Registry extension changes the ghost value
parameter while the runtime model's body registry remains fixed. The existing
actual lambda runtime suite is reused once at whole registration. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaRuntimeValues
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedLambdaValues CallableIndexedLambdaRuntimeValues

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {program : SourceSemantics.Program} {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : values.checked.catalog.callableContracts = true)

theorem actual_observations :
    FunctionObservations values.checked.catalog
      (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile) (Identity prepared) :=
  CallableIndexedLambdaRuntimeValues.observations prepared program bodyRegistry faults profile

theorem actual_runtime_views :
    FunctionRuntimeViews (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile) :=
  CallableIndexedLambdaRuntimeValues.runtime_views prepared program bodyRegistry faults profile

/-- Independent source validity is carried by the body itself. -/
theorem actual_source_frame {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      registry mapping world sourceType (.closure function) native type) :
    Dynamic.ClosureFrame program function :=
  CallableIndexedLambdaRuntimeValues.Represents.closure_frame prepared program bodyRegistry faults related

/-- The fixed body registry is still the one named in the receipt, even when
FunctionModel.extend changes its independent ghost registry argument. -/
theorem receipt_after_extension {registry futureRegistry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      registry mapping world sourceType (.closure function) native type)
    (registries : SourceCoreRawMetadata.Extends registry futureRegistry)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      futureRegistry futureMapping futureWorld sourceType (.closure function) native type ∧
    ∃ scope actual, ∃ (captured : Captures prepared futureMapping futureWorld scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code),
      Nonempty (CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults) ∧
      sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  have extended := (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).extend related registries maps worlds
  exact ⟨extended, CallableIndexedLambdaRuntimeValues.Represents.closure_inv prepared program bodyRegistry faults extended⟩

/-- A weak value receipt alone cannot discharge the independent body premise. -/
theorem absent_body_forbids_strong_value {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (missing : ∀ scope actual (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative),
      ¬ Nonempty (CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults)) :
    ¬ (CallableIndexedLambdaRuntimeValues.model prepared program bodyRegistry faults profile).Represents
      registry mapping world sourceType (.closure function) native type := by
  intro related
  obtain ⟨scope, actual, captured, code, _, body, _⟩ :=
    CallableIndexedLambdaRuntimeValues.Represents.closure_inv prepared program bodyRegistry faults related
  exact missing scope actual captured code body

abbrev actual_formation := @CallableIndexedLambdaRuntimeValues.formation
abbrev actual_reflection := @CallableIndexedLambdaRuntimeValues.reflects
abbrev accepted_site_formation := @CallableIndexedLambdaRuntimeValues.accepted_site_formation
abbrev accepted_site_reflection := @CallableIndexedLambdaRuntimeValues.accepted_site_reflection
abbrev same_model_preservation := @CallableIndexedLambdaRuntimePreservation.preserves_for
abbrev same_model_reflection := @CallableIndexedLambdaRuntimeEntry.reflects_for

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaRuntimeValues
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaStaticBodySupport
/-! These consumers retain the actual compiler view, canonical static body,
complete runtime ledger, captures and history under one support family.
Named calls have no static rank decrease. Only literal nested-lambda tokens
use rank, independently of all source and native execution grades. This unit
does not close named lambda-body execution, indirect apply or method bodies.
The runtime runner reuses the registered seven actual lambda cases once. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaStaticBodySupport
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaStaticBodySupport

abbrev actual_body := @BodyWith.of_tree
abbrev actual_entry := @CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
abbrev actual_lambda_site := @RecursiveNamedLambdaFormationHeads.LambdaWith.of_site

section Body
variable {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code prepared function scope administrative} {program : SourceSemantics.Program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : BodyWith expressionSyntax certificates code program registry faults)

include body in
theorem original_view_and_static_body :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body ∧
    code.receipt.body = CompatibleStatements.finish code.receipt.resultCore body.flow
      code.compilation.internalReason code.compilation.internalReason ∧
    body.tree.CatalogSites .reachable registry faults ∧ body.actualTree.CatalogSites .reachable registry faults :=
  ⟨body.accepted, body.emitted, body.sites, body.actualSites⟩

include body in
theorem full_context_and_origin_shape :
    body.context.solvedRequirements = code.compilation.solvedRequirements ∧
    RuntimeRequirementLedgerValid body.context ∧ function.evidence.Covers body.context ∧
    NodeOccurrencesUnique function.source :=
  ⟨body.valid.ledger, body.valid.runtime, body.valid.covers, body.unique⟩

theorem legacy_body_roundtrip
    (legacy : CallableIndexedLambdaRuntimeBody.Body code program registry faults) :
    CallableIndexedLambdaRuntimeBody.Body.fromWith legacy.toWith = legacy := by
  cases legacy
  rfl
end Body

section Values
open CallableIndexedLambdaRuntimeValues
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {support : SupportFamily prepared} {P : SupportCondition prepared support}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  {environment : Dynamic.Environment} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog values.checked.catalog) projects
    prepared.layouts.definitions}
  {current : Captures prepared mapping world scope environment actual}
  {code : Code prepared function scope current.administrative} {history : History code}
  {heap : Dynamic.Heap} {store : Store} {location : Location}
  (formed : Formed model current code history heap store location)
  (body : support formed.closureCode)
  (supported : P (function := formed.closure) formed.captures formed.closureCode formed.closureHistory body)
  (profile : values.checked.catalog.callableContracts = true)
  (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)

include formed body supported profile stored in
/-- The formed closure over the copies of the creation environment keeps the
support receipt and condition of its code. -/
theorem actual_formation {program : SourceSemantics.Program}
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    Evaluates actual store (code.lowered.expression.rename current.embedding)
      (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
    RepresentsWith prepared support P formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  formation_with prepared program formed body supported profile stored ordinary coercions

include formed body supported profile stored in
theorem actual_reflection {program : SourceSemantics.Program}
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) {result : Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename current.embedding) result after) :
    result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
    after = formed.finalStore ∧
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    RepresentsWith prepared support P formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  reflects_with prepared program formed body supported profile stored ordinary coercions completed

theorem retained_code_history_and_condition
    {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
    (related : RepresentsWith prepared support P mapping world sourceType (.closure function) native type) :
    ∃ scope actual, ∃ (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code) (body : support code),
      P captured code history body ∧ sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore :=
  RepresentsWith.closure_inv prepared related
end Values

section Capture
open CallableIndexedLambdaRuntimeValues
variable {values : SourceCoreCompatibleValues.Context} (prepared : Prepared values.checked) (program : SourceSemantics.Program)
  (support : SupportFamily prepared)
  (origin : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code prepared function scope administrative) → History code → Prop)
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  (callerPrefix : Nat)

theorem actual_same_capture_condition {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code) (body : support code)
    (supported : captureCondition prepared program support origin (headers := headers) (locations := locations)
      callerPrefix captured code history body)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    captureCondition prepared program support origin (headers := headers) (locations := locations)
      callerPrefix (captured.extend maps worlds) code history body :=
  captureCondition_stable prepared program support origin callerPrefix captured code history body supported maps worlds

abbrev actual_capture := @RecursiveNamedLambdaFormationHeads.capture_globals
abbrev actual_capture_condition := @RecursiveNamedLambdaFormationHeads.LambdaWith.capture_condition
abbrev actual_cached_slots := @RecursiveNamedLambdaFormationHeads.cached_capture_slots
end Capture

section Boundaries
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {support : Nat → {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → Code prepared function scope administrative → Type}
  {calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate}
  {source : TypedSource} {context : SourceSemantics.Context} {children : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

theorem named_rank_unrestricted (rank : Nat) (head : calls children scope id lowered) :
    CallsWith prepared support rank calls source context children scope id lowered := .existing head

theorem no_nested_lambda_at_zero
    (head : NestedLambda prepared support 0 source context scope id lowered) : False :=
  Nat.not_lt_zero head.childRank head.smaller

/-- Two real globals, their independent frame and an arbitrary unused native
suffix survive the finite used-prefix retention; the full actual env stays. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let canonical : Environment := [.word (Word.ofNatModulo 7), .cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let finite := canonical.take 4
    finite[0]? = some (.word (Word.ofNatModulo 7)) ∧
      finite[1]? = some (.cellRef .word 3) ∧ finite[2]? = some (.cellRef .bool 4) ∧
      finite[3]? = some (.cellRef .unit 5) ∧ canonical.drop 4 = unused := by simp

end Boundaries

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaStaticBodySupport
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedLambdaTemplatePermission
/-! Formal consumers of actual template preparation and actual retained code.
Dispatch permission is separate from call-time catalogue authority and from
execution of any lambda body. This module adds no runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaTemplatePermission
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedLambdaValues CallableIndexedHistory CallableAppliedViewProvenance

abbrev actual_prepare := @CallableAppliedViewProvenance.prepared_template
abbrev actual_template := @CallableIndexedLambdaTemplatePermission.selected
abbrev old_header := @CallableAppliedViewProvenance.header_of_prepared
abbrev old_body := @CallableIndexedLambdaRuntimeBody.Body.of_tree

section ActualCode
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code prepared function scope administrative) (history : History code)

theorem actual_permission :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs
      history.metadata code.descriptor.id = true :=
  CallableIndexedLambdaTemplatePermission.lambda_allowed code history

theorem actual_caller {currentNative : NativeFrame} {currentGhost : GhostFrame}
    {current : Option CallableIndexedHistory.MetadataState}
    (carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      currentNative currentGhost current) :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id
        history.native currentNative)
      (.lambda code.descriptor.id history.ghost) (some history.metadata) :=
  CallableIndexedLambdaTemplatePermission.ordinary_history code history carried

/-- The selected first-match template keeps the complete ordered source header. -/
theorem actual_ordered_header :
    ∃ template, prepared.ancestry.graph.inputs.templates.lambdaAt? code.descriptor.id = some template ∧
      PreparedTemplate prepared.base template ∧
      template.owner = code.compilation.owner ∧ template.id = code.id ∧ template.active = code.active ∧
      template.node.form = .lambda function.parameters function.resultType function.body :=
  CallableIndexedLambdaTemplatePermission.selected code

/-- Permission does not alter the value's ordered captures, including unused
and shadowed suffix slots, or either retained active substitution. -/
theorem same_value_and_history {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {actual : Core.Environment} (captured : Captures prepared mapping world scope function.captured actual) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs
      history.metadata code.descriptor.id = true ∧
    CallableIndexedLambdaValues.value code captured.embedding history.native actual =
      .pair (.pair (.inLeft .word .unit)
        (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
          (code.body.rename captured.embedding.lift.lift)
          (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native :: actual)))
        (.word code.descriptor.id) ∧
    history.metadata.metadata.source = function.source ∧ history.metadata.metadata.owner = code.compilation.owner ∧
    history.metadata.nativeActive = code.active :=
  ⟨actual_permission code history, rfl, history.source, history.owner, history.active⟩
end ActualCode

section Prepared
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
  {inventory : SourceCoreLambdaTemplates.Inventory checked} {template : SourceCoreLambdaTemplates.Lambda}

/-- Successful preparation retains the entire original source and the exact
ordered inherited witness list, even when rows repeat. -/
theorem ordered_principal_source
    (accepted : SourceCoreLambdaTemplates.prepare base = .ok inventory)
    (member : template ∈ inventory.lambdas) :
    template.principalSource = SourceTypedRuntime.rewriteLocalRequirements
      (((base.contexts.find? (fun parent => decide
        (parent.caller.key = template.owner ∧ parent.substitution = template.active))).map
          (·.witnesses)).getD [])
      (template.originalSource.applySubstitution template.active) := by
  obtain ⟨_, _, _, _, original, _, _, _, _, _, _, _, _, _, _, _, _, source, principal, _⟩ :=
    prepared_template accepted member
  rw [source]
  exact principal

theorem actual_table_uniqueness (inputs : SourceCoreCallableAncestryPreparation.Inputs base) :
    (inputs.callable.table.entries.map (·.id)).Nodup ∧
    (inputs.callable.table.entries.map (·.origin)).Nodup :=
  ⟨inputs.callable.table.idsUnique, inputs.callable.table.originsUnique⟩
end Prepared

section Boundaries
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
  (inputs : SourceCoreCallableAncestryPreparation.Inputs base) (state : CallableIndexedHistory.MetadataState) (id : Word)

theorem missing_template (missing : inputs.templates.lambdaAt? id = none) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = false := by
  simp [SourceCoreCallableAncestryPairedPreparation.lambdaAllowed, missing]

/-- The guard reads the native context; it does not equate it with the
semantic substitution retained by an applied source view. -/
theorem semantic_active_separate (active : TypeSystem.Substitution) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs
      {state with metadata := {state.metadata with active := active}} id =
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id := rfl

end Boundaries
end Tests.SourceCoreCallableIndexedLambdaTemplatePermission
end
