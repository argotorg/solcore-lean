import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPhysical
import Solcore.SourceSemantics.CoreLowering.CellAwareMatchSelectedPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchPrefixAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts

/-! Selected match children retain their actual Source grades and reached
caller states. Restoring lexical bindings preserves captured heap cells and
both semantic and staging failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves BranchReflects)
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix DataMatchBranchPrefix
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (parent : SourceSemantics.Context) (control : ControlContext) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty) (budget : Nat)

def ArmPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge armContext
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

def ArmReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge armContext
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

def DefaultPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge parent
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

def DefaultReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge parent
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions) index producer
      stages invocation faults administrative finalScope false statements expected type body budget

private theorem selected_pattern {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {raw : TypeSystem.Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Dynamic.Value} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (typed : MatchCasesHaveType source control context raw cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm statements bindings)) :
    ∃ arm ∈ cases, ∃ binders arity,
      TypedMatchPatternHasType context arm.pattern raw binders arity ∧ bindings.map Prod.fst = binders := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head _ =>
      cases head with
      | intro pattern _ _ =>
        exact ⟨_, List.mem_cons_self, _, _, pattern, DataMatchSourceScopes.PatternMatches.binders pattern matched⟩
  | tail _ selected =>
    cases typed with
    | cons _ tail =>
      obtain ⟨arm, member, binders, arity, pattern, same⟩ := selected_pattern tail selected
      exact ⟨arm, List.mem_cons_of_mem _ member, binders, arity, pattern, same⟩
termination_by cases.length
decreasing_by simp_all

theorem selected_members {source : TypedSource} {control : ControlContext} {context : SourceSemantics.Context}
    {site : StatementId} {statement : StatementNode} {resolution : MatchResolution}
    {raw : TypeSystem.Ty} {caseFacts : List BodyFacts}
    {value : Dynamic.Value} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (found : source.lookupStatement? site = some statement) (form : statement.form = .matchWith resolution)
    (typed : MatchCasesHaveType source control context raw resolution.cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings)) :
    ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  obtain ⟨arm, member, binders, arity, pattern, same⟩ := selected_pattern typed selected
  rw [same]
  exact CompatibleMatchArmScopes.pattern_declarations found form member pattern

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchHeads
