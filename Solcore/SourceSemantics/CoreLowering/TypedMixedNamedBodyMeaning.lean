import Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyCertificates
import Solcore.SourceSemantics.CoreLowering.TypedStatementMixedMeaning
import Solcore.SourceSemantics.CoreLowering.TypedNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyMeaning

/-! The concrete mixed tree closes body meaning at the actual call context and
ambient definitions. Its result retains the lexical context where execution
stopped. Initial environment typing is explicit; every child expression's
meaning, including nested scalar-key indices, is derived from the tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleNamedBody (trace_control body_result)

/-- The actual lexical stopping context is retained with the represented exit.
An initializer fault stops before its declaration enters the source context. -/
def ReachedExit (checked : SourceCoreCompatibleCatalog.Checked) (definitions : DataEnvironment)
    (mapping : LocationMap) (world : StoreTyping) (administrative : Core.Context)
    (program : Program) (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (environment : Dynamic.Environment)
    (before after : Dynamic.Heap) (outcome : Dynamic.ExpressionOutcome) : Prop :=
  ∃ (resultContext : SourceSemantics.Context) (control : Dynamic.ControlOutcome),
    Dynamic.FunctionStatementsExecuteOutcome program context function.evidence function.source
      environment before function.body resultContext control after ∧
    CompatibleNamedBody.Exit function.resultType control outcome ∧
    TypedStatementMixed.LexicalResult checked definitions mapping world administrative function.source.owner
      context scope environment resultContext after

/-- Successful source control through the ordinary binding spine cannot be a
fault. The initialized head can fault only through its separate fault relation. -/
theorem tree_control_not_fault
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : TypedStatementMixed.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type flow)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : Dynamic.FunctionStatementsExecute program actualContext evidence source environment before
      statements finalContext (.fault reason) after) : False := by
  induction tree generalizing actualContext finalContext environment before after with
  | body body => exact TypedNamedBody.tree_control_not_fault body unique executed
  | @uninitialized context nextContext scope id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨_, _, same, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases same
      exact ih tail
    · obtain ⟨_, _, same, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases same
  | @initialized context nextContext scope id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same
      exact ih tail
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same

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

include definitions registered extension contextValid unique uninitialized missing in
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
      ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.body_preserves functions definitions registered extension program function.evidence uninitialized missing
      contextValid fellThrough escaped unique environments heaps locals agrees actualTyped reference read unmapped sourceTrace
  rw [← certificate.emitted] at evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, body_result represented exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩⟩

include definitions registered extension contextValid unique uninitialized missing in
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
      ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  rw [certificate.emitted] at evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.body_reflects functions definitions registered extension program function.evidence uninitialized missing
      contextValid fellThrough escaped environments heaps locals agrees actualTyped reference read unmapped evaluated
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at represented
    cases represented with
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
      | control executed => exact False.elim (tree_control_not_fault certificate.tree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩⟩


end Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBody
