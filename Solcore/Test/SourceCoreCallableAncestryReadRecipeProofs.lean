import Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Universal consumers of the paired metadata receipts. They need neither a
source execution nor equality of caller/lexical contexts. Independent dynamic
evidence is supplied explicitly, not inferred from native closure typing. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryReadRecipeProofs
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CallableAncestryReadRecipes CallableAncestryMetadata CallableAncestryProfiles

example {leftCaller rightCaller : SourceSpecialization.SpecializedFunction}
    {leftAvailable rightAvailable : SourceCompilationPlan.EvidenceEnvironment}
    {leftBinder rightBinder : TypedBinder} {leftNode rightNode : ExpressionNode}
    {leftSubstitution rightSubstitution : Substitution} {leftWitnesses rightWitnesses : List Witness}
    (left : SourceCompilationPlan.localRequirementWitnesses leftCaller leftAvailable leftBinder leftNode =
      .ok (leftSubstitution, leftWitnesses))
    (right : SourceCompilationPlan.localRequirementWitnesses rightCaller rightAvailable rightBinder rightNode =
      .ok (rightSubstitution, rightWitnesses))
    (scheme : leftBinder.scheme = rightBinder.scheme) (rawType : leftNode.rawType = rightNode.rawType) :
    leftSubstitution = rightSubstitution := factory_substitution_eq left right scheme rawType

section
variable {checked : SourceCoreCallableAncestryReadRecipes.Checked}
  {base : SourceCoreCallableAncestryReadRecipes.Base checked}
  {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
  {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
  (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)

example
    (scheme : read.binder.scheme =
      (read.entry.view.principal.binder.applySubstitution read.entry.view.parentActive).scheme)
    (rawType : read.node.rawType = read.entry.view.rawRead.rawType) :
    read.substitution ∈ CallableAncestrySourceActive.generators inputs.views :=
  read_generator_from_metadata read scheme rawType

example {callerIds lexicalIds : List RequirementId}
    (callerBounded : Bounded callerIds caller.metadata.source)
    (lexicalBounded : Bounded lexicalIds lexical.metadata.source) :
    Bounded (callerIds ++ lexicalIds) (read.after lexical).metadata.source :=
  after_bounded_union read lexical callerBounded lexicalBounded

example (reachable : CallableAncestrySourceActive.Reachable
    (CallableAncestrySourceActive.generators inputs.views) lexical.metadata.active) :
    (read.after lexical).metadata.active ∈
      CallableAncestrySourceActive.keySpace (CallableAncestrySourceActive.generators inputs.views) :=
  (after_finite read lexical reachable).2.2.2

example : (read.after lexical).metadata.active = read.substitution.compose lexical.metadata.active ∧
    (read.after lexical).nativeActive = read.entry.view.cumulative := (after_contexts read lexical).2

variable (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)

example (context : SourceSemantics.Context) (binder : TypedBinder) (captured : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) :
    let result := (principal applied context binder captured).instantiate read.substitution evidence
    eraseRequirements (read.after lexical).metadata.source = eraseRequirements result.source ∧
      ExpressionForm.lambda result.parameters result.resultType result.body = read.template.node.form ∧
      result.captured = captured ∧ result.evidence = evidence :=
  instantiated_metadata applied context binder captured evidence

example (binding : Resolved.LocalId × SourceTypedRuntime.Location)
    (tail : SourceTypedRuntime.Environment) (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    applied.sourceValue (binding :: binding :: tail) evidence =
      .instantiated read.substitution read.witnesses
        (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
          (binding :: binding :: tail) evidence) := export_original applied _ _

example {left right : SourceTypedRuntime.Environment}
    {leftEvidence rightEvidence : SourceCompilationPlan.EvidenceEnvironment}
    (same : applied.sourceValue left leftEvidence = applied.sourceValue right rightEvidence) :
    left = right ∧ leftEvidence = rightEvidence := export_captures_injective applied same

end
end Tests.SourceCoreCallableAncestryReadRecipeProofs
