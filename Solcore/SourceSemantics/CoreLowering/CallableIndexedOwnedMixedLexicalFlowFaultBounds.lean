import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyFaultBounds

/-! The original lexical Tree consumes genuine strict expression members at
its actual current context. Callable children keep their causal fault post,
while allocations retain the same ordered pool and stable frame receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalFlowFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open NamedLexicalFlowFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} (evidence : Dynamic.EvidenceEnvironment)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (post : ExpressionFailurePostContracts.ExpressionFaultPost)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)

section Flows
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (condition : Location → NativeFrame → Prop)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (acquire : ∀ location native, condition location native → ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext)

include definitions registered producer bindings acquire unique extend in
theorem flow_preserves (outer budget size : Nat) (within : budget < outer) (bounded : size ≤ budget)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) callerProtocol (readiness bridge)
        program evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
        (context := context) (source := source) (faults := faults) child)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.PreservesAtFor
      (post := FlowPost (post))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.preserves_at_for_with_post
    (expressionPost := post)
    (headPost := HeadPost (post))
    (flowPost := FlowPost (post))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child bounded context valid => children child (Nat.lt_of_le_of_lt bounded within) context valid)
    tree valid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

include definitions registered producer bindings acquire unique extend in
theorem flow_reflects (outer budget size : Nat) (within : budget < outer) (bounded : size ≤ budget)
    (children : ∀ child, child < outer → ∀ context, validity context →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) callerProtocol (readiness bridge)
        program evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts source) (certificates context)
        (context := context) (source := source) (faults := faults) child)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      source certificates context scope mode statements expected type code) :
    NamedLexicalFlowFaultPostContracts.ReflectsAtFor
      (post := FlowPost (post))
      callerProtocol (readiness bridge) condition (GenericLexicalStatements.Syntax source expressionSyntax)
      (values := .initial compiled.compatible.checked) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.reflects_at_for_with_post
    (expressionPost := post)
    (headPost := HeadPost (post))
    (flowPost := FlowPost (post))
    (joins := origin_joins _ program evidence source)
    (protocol := callerProtocol) (condition := condition) (producer := producer) (stateBindings := bindings) (acquire := acquire)
    (readiness := readiness bridge) (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child bounded context valid => children child (Nat.lt_of_le_of_lt bounded within) context valid)
    tree valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted evaluated

end Flows

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalFlowFaultBounds
