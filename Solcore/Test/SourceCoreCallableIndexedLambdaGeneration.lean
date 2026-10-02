import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.Frontend.SourceCoreCallableIndexedRestoration
import Solcore.Test.SourceCompilerFeatureSupport

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
completion consumer needs no separately supplied source/owner/active history. -/
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
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[site.code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (completed : Evaluates actual store (site.code.lowered.expression.rename captured.embedding) output after) :
    after = store ∧
    Dynamic.ExpressionEvaluates program sourceContext evidence (source named) capturedSource heap site.code.id
      (.closure (closure named parameters result body sourceContext evidence capturedSource)) heap := by
  have preserved : GeneralHeap.AdministrativePreserved mapping
      (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) mapping store := by
    rw [allocated]
    exact GeneralHeap.AdministrativePreserved.allocate_administrative _ _ _
  have reflected := site.reflects_after_prefix captured selected record program heap ordinary coercions
    entryRead unmapped preserved stored reference completed
  exact ⟨reflected.2.1, reflected.2.2.1⟩

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

private def callSnapshot {artifact : SourceCoreExecution.Artifact}
    (snapshot : SourceCoreExecution.Snapshot artifact) : IO SourceCoreExecution.Handle := do
  let handle ← match (snapshot.cells[1]?).bind (fun (cell : SourceCoreHeapSnapshot.Cell) => cell.value) with
    | some (.data (.function handle)) => pure handle
    | _ => throw (IO.userError "generation snapshot lost its stored lambda")
  let session ← match snapshot.restore with
    | .ready session => pure session
    | .suspended _ => throw (IO.userError "completed generation snapshot remained suspended")
  let called ← SourceCompilerFeatureSupport.get "invoke stored generation"
    (← session.invokePacked handle (SourceCompilerFeatureSupport.scalar 2) SourceCompilerFeatureSupport.executionOptions)
  match called with
  | .succeeded done =>
    SourceCompilerFeatureSupport.require (done.value == SourceCompilerFeatureSupport.scalar 9)
      "stored generation lost the mutated shared capture"
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
          reprStr (final.cells.eraseIdx 1) == reprStr (snapshot.cells.eraseIdx 1))
        "generation resume changed captures, writes or first fault"
    | _ => throw (IO.userError "generation resume changed its stopping point")
  IO.println "indexed named-to-lambda generation: real callbacks, full source seed, lexical evidence/captures and resume GREEN"
end Tests.SourceCoreCallableIndexedLambdaGeneration
