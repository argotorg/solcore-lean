import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceInferenceSelectedForItemTransport

/-! Header items use their actual result and the same selected final source.
Their local bindings and expression references remain attached to that source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure ForItemBoundary (selected : Selected compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context) (item : Syntax.ForItem)
    (expectedReturn : Ty) (initial : State) (inferred : ForItemForm) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferForItemFuel childFuel inferenceContext item initial = .ok (inferred, final)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends final.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawReferences : ∀ reference ∈ inferred.references,
    RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) reference
  integerPatterns : final.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : final.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : final.requirements ⊆ selected.body.returned.requirements
  owner : selected.body.finalized.typedSource.owner = initial.owner
  covered : ForItemReferencesCovered selected.body.finalized.typedSource
    selected.body.finalized.substitution target inferred
  bindingsRetained : ForItemBindingRetained (evidenceSource selected) inferred
  actualCovered : ∀ reference ∈ inferred.references,
    ActualContext.Covers selected.body.finalized frames reference
  actualBindings : ActualForItemBindings selected.body.finalized frames inferred

def ForItemConclusion (selected : Selected compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (inferred : ForItemForm) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized final finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant final (evidenceSource selected) ∧
    ForItemHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target (inferred.applySubstitution selected.body.finalized.substitution) finalContext

structure ForItemsBoundary (selected : Selected compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context) (items : List Syntax.ForItem)
    (expectedReturn : Ty) (initial : State) (result : Detail.InferredForItems)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferForItemsFuel childFuel inferenceContext items initial = .ok result
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawReferences : ∀ item ∈ result.items, ∀ reference ∈ item.references,
    RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected) reference
  integerPatterns : result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.state.requirements ⊆ selected.body.returned.requirements
  owner : selected.body.finalized.typedSource.owner = initial.owner
  covered : ForItemsReferencesCovered selected.body.finalized.typedSource
    selected.body.finalized.substitution target result.items
  bindingsRetained : ForItemsBindingsRetained (evidenceSource selected) result.items
  actualCovered : ∀ item ∈ result.items, ∀ reference ∈ item.references,
    ActualContext.Covers selected.body.finalized frames reference
  actualBindings : ActualForItemsBindings selected.body.finalized frames result.items

def ForItemsConclusion (selected : Selected compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (result : Detail.InferredForItems)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
    ForItemsHaveType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target (result.items.map (ForItemForm.applySubstitution selected.body.finalized.substitution)) finalContext

def ForItemRootedSoundness (selected : Selected compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expectedReturn : Ty}
    {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    ForItemBoundary selected childFuel inferenceContext item expectedReturn initial inferred final frames target →
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target

def ForItemsRootedSoundness (selected : Selected compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {items : List Syntax.ForItem} {expectedReturn : Ty}
    {initial : State} {result : Detail.InferredForItems}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    ForItemsBoundary selected childFuel inferenceContext items expectedReturn initial result frames target →
    ForItemsConclusion selected inferenceContext expectedReturn result frames target

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
