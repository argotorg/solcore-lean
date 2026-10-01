import Solcore.SourceSemantics.CoreLowering.BuiltinNamedBodyCertificates
import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyMeaning

/-! The concrete recursive builtin statement tree supplies the named body
beneath its actual finish helper. Raw source return typing fixes true-mode
fallthrough; lexical allocations and stopping contexts remain observable.
Neither source execution nor a universal body meaning is stored in a receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes source_view)
open CompatibleNamedBody (trace_control body_result)
open GenericLexicalStatements (true_fallthrough_unit control_not_fault)

private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ = CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

private theorem finish_from_flow
    {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {source : TypedSource} {context actualContext finalContext : SourceSemantics.Context}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {sourceBefore sourceAfter : Dynamic.Heap}
    {statements : List StatementId} {environment : Environment} {before after : Store}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (unique : NodeOccurrencesUnique source)
    (trace : Executes true program actualContext evidence source sourceEnvironment sourceBefore statements finalContext outcome sourceAfter)
    (projection : values.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word)
    (represented : TypedScopedStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough nextEnvironment =>
    have raw := true_fallthrough_unit syntaxTree unique trace
    subst expected
    have native : type = .unit := by
      change Except.ok (.unit : Ty) = .ok type at projection
      exact Except.ok.inj projection.symm
    subst type
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated)
      (by simpa [LanguageResult.success, Expr.weakenAt] using
        (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)),
      .fallthrough nextEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include definitions registered extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.preserves
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.preserves functions definitions registered extension faithful functionLeaves functionTypes program function.evidence uninitialized missing
      unique contextValid environments heaps locals agrees actualTyped reference read unmapped sourceTrace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions certificate.syntaxTree unique sourceTrace
    certificate.projection fellThrough escaped represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [certificate.emitted, finish_rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, body_result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩⟩

include definitions registered extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.reflects
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  rw [certificate.emitted, finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEval⟩ := finish_input evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.reflects functions definitions registered extension faithful functionLeaves functionTypes program function.evidence uninitialized missing
      contextValid environments heaps locals agrees actualTyped reference read unmapped flowEval
  obtain ⟨result, completed, related⟩ := finish_from_flow functions certificate.syntaxTree unique trace
    certificate.projection fellThrough escaped represented flowEval
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (control_not_fault certificate.syntaxTree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩⟩


end Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
