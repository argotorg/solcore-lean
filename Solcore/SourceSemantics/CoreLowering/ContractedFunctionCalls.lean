import Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues
import Solcore.SourceSemantics.CoreLowering.FunctionCalls

/-! Ordinary source closure calls beneath accepted callable-contract gates.
The generated argument-cell prefix and complete body composition preserve the
generic heap. Callee/argument Core evaluations in the gate-prefix theorem are
explicit compositional premises, not fields of code authentication. Rejected
runtime stage gates are intentionally not claimed to be existing Dynamic faults. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments FunctionCallBody FunctionCalls

private theorem parameters_scope {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Ty)}
    (tree : FunctionCode.Parameters policy source scope parameters lowered finalScope) :
    lowered.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope = finalScope := by
  induction tree with
  | nil => rfl
  | cons _ _ ih => exact ih

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}
  {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
  {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {actual : Environment} {faults : FunctionCalls.FaultRep}

/-- Contract wrappers do not change closure parameter allocation. All source
metadata and mapped lexical references are constructed by the real prefix. -/
structure Entry
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (before : Dynamic.Heap) (initialStore : Store) (context : SourceSemantics.Context)
    (arguments : List Dynamic.Value) (values : List Value) where
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  bodyEnvironment : Environment
  store : Store
  finalMap : LocationMap
  finalWorld : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents catalog finalMap finalWorld layout.administrativeContext
    code.artifact.raw.bodyScope environment canonical
  heaps : GenericHeap.HeapRepresents model finalMap finalWorld heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping initialStore finalMap store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical bodyEnvironment
  agreement : ContinuationAgreement (DataPatternValues.packValues values :: actual) initialStore
    (code.artifact.raw.rawBody.rename layout.embedding.lift) bodyEnvironment store
      (code.artifact.raw.bodyCode.rename embedding)

theorem entry_exists
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store : Store} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {arguments : List Dynamic.Value} {values : List Value}
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured) :
    Nonempty (Entry (model := model) layout code before store context arguments values) := by
  obtain ⟨environment, heap, canonical, bodyEnvironment, finalStore, finalMap, finalWorld, embedding,
      allocation, environments, finalHeaps, maps, worlds, frame, lookups, agreement⟩ :=
    parameters_prefix represented (body := code.artifact.raw.bodyCode) (outputType := code.artifact.raw.resultCore)
      layout.represented heaps (EnvironmentsAgree.lift (mapping := layout.embedding) layout.lookups
        (DataPatternValues.packValues values))
  rw [code.artifact.raw.parametersTree.binders] at allocation
  rw [parameters_scope code.artifact.raw.parametersTree] at environments
  have mono := mono_binders extension
  exact ⟨⟨environment, heap, canonical, bodyEnvironment, finalStore, finalMap, finalWorld, embedding,
    allocation, environments, finalHeaps, GenericLexicalContext.binders_agree mono.1 mono.2 locals allocation,
    maps, worlds, frame, GenericLexicalContext.binders_metadata allocation, lookups, agreement⟩⟩

theorem preserves
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (bodyMeaning : BodyPreserves model program function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have arity : function.parameters.length = arguments.length := by
    rw [← code.artifact.raw.parametersTree.binders, List.length_map]
    exact represented.length.1
  obtain ⟨types, callContext, environment, bound, extension, allocated, trace⟩ := execution.trace arity
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨rfl, rfl⟩ := allocations_same allocated entry.allocation
  obtain ⟨_, _, typed, _⟩ := frame_body_at code.frame extension
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, result, finalHeaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

theorem reflects
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (bodyMeaning : BodyReflects model program function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, callContext, _, _, extension, typed, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
      (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace.call code.frame extension entry.allocation,
    result, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
    entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- Once both actual gate decisions accept, the call prefix enters precisely
the real closure body. Callee and argument effects occur once and in order;
reflection recovers the same body evaluation from any completed whole call. -/
theorem accepted_call_agreement {environment captured : Environment} {before middle applied : Store}
    {parameter result : Ty} {callee arguments body : Expr} {identity argument : Value} {contract : Word}
    (gates : List CallableContract.Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
        (.word contract))) middle)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit ::
      .pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) applied)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown contract = none) :
    ContinuationAgreement environment before (CallableContract.call gates unknown result callee arguments)
      (argument :: captured) applied body := by
  constructor
  · intro value finalStore evaluated
    exact CallableContract.call_success gates unknown calleeEvaluation stageAccepted argumentsEvaluation arityAccepted evaluated
  · intro value finalStore evaluated
    obtain ⟨_, sized⟩ := evaluation_has_size evaluated
    obtain ⟨_, _, afterCallee⟩ := sized.bind_success calleeEvaluation
    have beforeArguments := CallableContract.dispatch_evaluates gates .beforeArguments unknown contract
      (show Evaluates (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
        (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle from .second (.var rfl))
    rw [stageAccepted] at beforeArguments
    obtain ⟨_, _, afterGuard⟩ := afterCallee.bind_success beforeArguments
    obtain ⟨_, _, afterArguments⟩ := afterGuard.bind_success argumentsEvaluation
    have beforeApplication := CallableContract.dispatch_evaluates gates .beforeApplication unknown contract
      (show Evaluates (argument :: .unit :: .pair (.pair identity
        (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
        applied (.second (.var 2)) (.word contract) applied from .second (.var rfl))
    rw [arityAccepted] at beforeApplication
    obtain ⟨_, _, application⟩ := afterArguments.bind_success beforeApplication
    obtain ⟨_, _, bodyEvaluation⟩ := application.apply_body
      (show Evaluates (.unit :: argument :: .unit :: .pair (.pair identity
        (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
        applied (.second (.first (.var 3))) (.closure parameter (LanguageResult.resultType result) body captured) applied
        from .second (.first (.var rfl))) (.var rfl)
    exact bodyEvaluation.sound

end Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls
