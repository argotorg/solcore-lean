import Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning

/-! Independent source-body correspondence through the actual indexed named
entry callback. The universal body theorem supplies child execution under the
real inserted binders. Installation and restoration are derived native steps,
including their effects on the represented heap and protected snapshots.

This composes a certified source body with an accepted instrumentation hook.
It does not extract that body certificate from the whole function compiler:
the production parameter prefix, named-source attribution and staged recursive
body correspondence remain separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

private theorem agree_body {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_body (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects}
  {program : Program} {sourceFunction : Dynamic.Closure} {certificate : FunctionCode.BodyCertificate}
  {faults : FunctionCalls.FaultRep}

/-- The accepted callback supplies the named origin and installed history.
Source finiteness and the universal body theorem supply all child execution;
the caller's current token and original administrative values are restored. -/
theorem preserves (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {scope : SourceCoreLocalCell.Scope}
    {type : Ty} {body code : Expr} {ξ : Renaming}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared named (body.rename ξ) = .ok code)
    (bodyCertificate : certificate sourceFunction.source scope sourceFunction.body type body)
    (bodyMeaning : FunctionCalls.BodyPreserves model program sourceFunction certificate faults)
    {context staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (bodyTyped : StatementsHaveType sourceFunction.source
      {returnType := sourceFunction.resultType, loopDepth := 0} context sourceFunction.body staticFinal facts)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {outcome : Dynamic.ExpressionOutcome}
    {records : List CallableIndexedSnapshots.Record}
    (registered : prepared.layout.frame.Registered catalog.definitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
    (reference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)
    (trace : FunctionCallBody.Trace program sourceFunction context environment before outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store code value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceFunction.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared accepted
  obtain ⟨installedHeaps, _⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    bodyMeaning bodyCertificate bodyTyped environments installedHeaps locals
      (agree_body agrees (encode prepared.layout.frame current)) trace
  rw [rename_body] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    emitted.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

/-- A completed actual wrapper supplies the child native trace for the
universal reflection theorem. No finite source body trace is required. -/
theorem reflects (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {scope : SourceCoreLocalCell.Scope}
    {type : Ty} {body code : Expr} {ξ : Renaming}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared named (body.rename ξ) = .ok code)
    (bodyCertificate : certificate sourceFunction.source scope sourceFunction.body type body)
    (bodyMeaning : FunctionCalls.BodyReflects model program sourceFunction certificate faults)
    {context staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (bodyTyped : StatementsHaveType sourceFunction.source
      {returnType := sourceFunction.resultType, loopDepth := 0} context sourceFunction.body staticFinal facts)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {value : Value}
    {records : List CallableIndexedSnapshots.Record}
    (registered : prepared.layout.frame.Registered catalog.definitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
    (reference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)
    (evaluation : Evaluates actual store code value finalStore) :
    ∃ origin index metadata outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      FunctionCallBody.Trace program sourceFunction context environment before outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceFunction.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared accepted
  obtain ⟨installedHeaps, _⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  rw [emitted] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var reference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_body] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    bodyMeaning bodyCertificate bodyTyped environments installedHeaps locals
      (agree_body agrees (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history,
    trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedBodyMeaning
