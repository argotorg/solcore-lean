import Solcore.SourceSemantics.CoreLowering.GenericImperativeForReflection
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForEndpoint

/-! Actual for installation composes generic condition, post and recursive body
certificates. Administrative self cells are preserved by the common heap frame;
all helper captures use the actual ambient environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep Preserves Reflects)
open TypedImperativeFor (LoopPreserves LoopReflects initial_state PostPreserves PostFaults PostReflects)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
variable {scope : Scope} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include extension meaning unique definitions registered faithful observations in
theorem loop_preserves {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (correct : Preserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    LoopPreserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have postCorrect : PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode := by
    intro mapping world before after store finalContext finalEnvironment state continued trace
    exact post_preserves functions definitions registered extension program evidence meaning faithful observations postTree
      valid unique agrees reference state continued trace
  have postFailed : PostFaults functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode := by
    intro mapping world before after store finalContext reason state continued trace
    exact post_fault functions definitions registered extension program evidence meaning faithful observations postTree postErrors
      valid unique agrees reference state continued trace
  cases trace with
  | control sourceTrace =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_success sourceTrace (meaning context valid) conditionTree conditionFound valid unique agrees reference correct postCorrect state
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) state.selfRead nativeTrace,
      represented, installedProgress.trans progress⟩
  | fault failed =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_fault failed (meaning context valid) conditionTree conditionFound valid unique agrees reference correct postCorrect postFailed state
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) state.selfRead nativeTrace,
      represented, installedProgress.trans progress⟩

include extension meaning reflection unique definitions registered faithful observations in
theorem loop_reflects (functionTypes : FunctionRuntimeViews functions)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    LoopReflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have postCorrect : PostReflects functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode := by
    intro mapping world before store finalStore value state continued trace
    exact post_reflects functions definitions registered extension program evidence meaning reflection faithful observations functionTypes postTree postErrors
      valid unique agrees reference state continued trace
  rw [LoopRenaming.iterate] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, entry⟩ := sized.iterate_entry
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, progress⟩ :=
    iterations_reflect functions program evidence (reflection context valid) conditionTree conditionFound valid agrees reference correct
      postCorrect bodyCannotFault entrySize state entry
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, installedProgress.trans progress⟩

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
