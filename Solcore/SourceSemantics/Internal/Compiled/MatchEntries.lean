import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.SourceInferenceGeneralizedPatternState
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedMatchState
import Solcore.SourceSemantics.Internal.Compiled.InitializerOccurrences
import Solcore.SourceSemantics.Internal.Compiled.PrivateDescent
import Solcore.Frontend.SourceInference.Internal.Continuations
import Solcore.SourceSemantics.SourceInferenceStatementsSoundness
import Solcore.SourceSemantics.Internal.Prepared.CallEdges

/-!
# Entries of match statements

An accepted pattern call provides its typing, the arm context and both privacy continuations, and
every scrutinee shape enters its first pattern with privacy. Open template emitters close their plan
premises at the same height.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedPatternEntry
/-! An accepted pattern call provides its declarative pattern typing, the
actual arm context, and both recursive invariants for entering that arm. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open ProtectedVariables

private theorem binder_context_fields {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder}
    (extension : BindersExtend owner before binders after) :
    after.signatures = before.signatures ∧ after.typeParameters = before.typeParameters ∧
      after.currentDeclaration = before.currentDeclaration ∧
      after.residualTypeVariables = before.residualTypeVariables ∧
      after.solvedRequirements = before.solvedRequirements ∧ after.assumptions = before.assumptions := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    cases head
    simpa only [SourceSemantics.Context.withLocal] using ih

theorem patternEntered
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {patternSource : Syntax.Pattern}
    {expected : Ty} {initial resultState : State} {inferred : TypedMatchPattern}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context} {occurrence : NodeId}
    (scope : CheckingScope selected inferenceContext)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (owner : initial.owner = (checkingContext selected).scope.genericOwner)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (expectedAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expected))
    (expectedSafe : Safe (activeSchemeQuantifiers initial) initial expected)
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (occurs : ∀ requirement ∈ inferred.requirements,
      PrimaryRequirementOccursAt selected.body.finalized.typedSource occurrence requirement)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target occurrence)
    (accepted : Detail.inferMatchPatternFuel childFuel inferenceContext patternSource expected initial =
      .ok (inferred, resultState)) :
    ∃ certificate : MatchPatternInferenceCertificate selected.body.finalized.typedSource target
        selected.body.finalized.substitution expected inferred resultState,
      RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized
        resultState certificate.armContext ∧
      ActualContext (checkingContext selected) selected.body.finalized frames certificate.armContext ∧
      GeneralizedActualStateInvariant resultState (evidenceSource selected) := by
  have formation := scope.formation checked
  have catalog := scope.catalog checked
  have semanticSignatures : target.signatures = inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans scope.signatures.symm
  have finalOwner : selected.body.finalized.typedSource.owner =
      (checkingContext selected).scope.genericOwner := by
    rw [selected.body.resources.source_eq]
    change selected.body.returned.owner = selected.body.declaration.id
    exact (congrArg State.Header.owner (Detail.unify_state_header selected.body.unified)).trans
      (Detail.inferStatementsFuel_preserves_owner selected.body.inferred)
  have evidence := selected.body.resources.integerPatternEvidenceAt
    invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered
  obtain ⟨certificate⟩ := inferMatchPatternFuel_success_sound_at formation
    (by simpa only [semanticSignatures] using catalog) semanticSignatures evidence
    invariant.ready expectedBelow invariant.bindersBelow (finalOwner.trans owner.symm)
    (invariant.declarationEq.trans (congrArg some finalOwner.symm)) expectedAdmissible invariant.active
    extension integerPatterns requirements occurs accepted
  have properties := Detail.inferMatchPatternFuel_inferenceProperties invariant.ready expectedBelow
    formation accepted
  have isolated := inferMatchPatternFuel_active_isolation invariant.ready expectedBelow formation
    operational.quantifiersBelow invariant.schemeIsolation operational.privacy expectedSafe accepted
  obtain ⟨signatures, parameters, declaration, residual, solved, assumptions⟩ :=
    binder_context_fields certificate.binders_extend
  refine ⟨certificate, ?_, actual.binders certificate.binders_extend,
    operational.ofPattern invariant.ready formation expectedBelow expectedSafe accepted⟩
  exact {
    active := certificate.pattern_invariant
    ready := properties.2.1
    bindersBelow := certificate.pattern_below
    nodesBelow := (Detail.inferMatchPatternFuel_occurrenceBoundExtends accepted).nodesBelowNextOccurrence
      invariant.nodesBelow
    schemeIsolation := isolated.1
    substitutionExtension := extension
    signaturesEq := signatures.trans invariant.signaturesEq
    typeParametersEq := parameters.trans invariant.typeParametersEq
    declarationEq := declaration.trans invariant.declarationEq
    residual := residual.trans invariant.residual
    solvedRequirementsEq := solved.trans invariant.solvedRequirementsEq
    assumptionsMono := by simpa only [assumptions] using invariant.assumptionsMono }

/-- The single-scrutinee branch enters its first pattern using privacy from the
actual scrutinee call. Reserving the hidden local changes no lexical scheme. -/
theorem patternEntered_after_expression
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel expressionFuel patternFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {patternSource : Syntax.Pattern} {entry scrutineeState initial resultState : State}
    {scrutinee : InferredExpression} {inferred : TypedMatchPattern}
    {hidden : Resolved.LocalId} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (scope : CheckingScope selected inferenceContext)
    (entryReady : entry.InferenceReady)
    (entryOperational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (expressionAccepted : Detail.inferExprFuel expressionFuel inferenceContext expression none entry =
      .ok (scrutinee, scrutineeState))
    (allocation : scrutineeState.allocateHiddenLocal = (hidden, initial))
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (owner : initial.owner = (checkingContext selected).scope.genericOwner)
    (expectedAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply scrutinee.type))
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (occurs : ∀ requirement ∈ inferred.requirements,
      PrimaryRequirementOccursAt selected.body.finalized.typedSource occurrence requirement)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target occurrence)
    (accepted : Detail.inferMatchPatternFuel patternFuel inferenceContext patternSource scrutinee.type initial =
      .ok (inferred, resultState)) :
    ∃ certificate : MatchPatternInferenceCertificate selected.body.finalized.typedSource target
        selected.body.finalized.substitution scrutinee.type inferred resultState,
      RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized
        resultState certificate.armContext ∧
      ActualContext (checkingContext selected) selected.body.finalized frames certificate.armContext ∧
      GeneralizedActualStateInvariant resultState (evidenceSource selected) := by
  have formation := scope.formation checked
  have catalog := scope.catalog checked
  have canonical := scope.functionsCanonical checked
  have properties := Detail.inferExprFuel_inferenceProperties entryReady formation canonical
    (by simp) expressionAccepted
  have privacy := entryOperational.expression_result_private entryReady catalog formation canonical expressionAccepted
  have operational := (entryOperational.ofExpression entryReady catalog formation canonical
    (by simp) (by simp) expressionAccepted).allocateHiddenLocal
  have initialEq := congrArg Prod.snd allocation
  simp only at initialEq
  subst initial
  exact patternEntered checked scope invariant actual operational owner properties.2.2
    expectedAdmissible privacy extension integerPatterns requirements occurs covered accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedMatchContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure MatchCasesBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (cases : List Syntax.MatchCase) (scrutinee expectedReturn : Ty)
    (initial : State) (outerScope : LexicalScope) (result : Detail.MatchCasesResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) (occurrence : NodeId) : Prop where
  accepted : Detail.inferMatchCasesFuel childFuel inferenceContext scrutinee expectedReturn
    outerScope cases initial = .ok result
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  owner : initial.owner = (checkingContext selected).scope.genericOwner
  lexicalScope : initial.lexicalScope = outerScope
  scrutineeBelow : scrutinee.VariablesBelow initial.inference.next
  scrutineeAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply scrutinee)
  scrutineeSafe : Safe (activeSchemeQuantifiers initial) initial scrutinee
  integerPatterns : result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.state.requirements ⊆ selected.body.returned.requirements
  patternCovered : TemplateScopeCovered selected.body.finalized.typedSource target occurrence
  patternOccurs : ∀ arm ∈ result.cases, ∀ requirement ∈ arm.pattern.requirements,
    PrimaryRequirementOccursAt selected.body.finalized.typedSource occurrence requirement
  rawSubtrees : ∀ arm ∈ result.cases, ∀ child ∈ arm.body,
    RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.statement child)
  covered : ∀ arm ∈ result.cases, ∀ child ∈ arm.body,
    TemplateScopeCovered selected.body.finalized.typedSource target (.statement child)
  actualCovered : ∀ arm ∈ result.cases, ∀ child ∈ arm.body,
    ActualContext.Covers selected.body.finalized frames (.statement child)

def MatchCasesConclusion (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) (scrutinee expectedReturn : Ty)
    (result : Detail.MatchCasesResult) (frames : List InitializedLetBinding)
    (target : SourceSemantics.Context) : Prop :=
  RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized result.state target ∧
  ActualContext (checkingContext selected) selected.body.finalized frames target ∧
  GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
  ∃ facts, MatchCasesHaveType selected.body.finalized.typedSource
    {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
    target (selected.body.finalized.substitution.apply scrutinee)
    (result.cases.map (TypedMatchCase.applySubstitution selected.body.finalized.substitution)) facts ∧
    allBodiesSawReturn facts = result.allReturn

theorem MatchCasesBoundary.resultInvariant
    {raw : Workspace.RawWorkspace} {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {inferenceContext : SourceInference.Context} {cases : List Syntax.MatchCase}
    {scrutinee expectedReturn : Ty} {initial : State} {outerScope : LexicalScope}
    {result : Detail.MatchCasesResult} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (boundary : MatchCasesBoundary selected childFuel inferenceContext cases scrutinee expectedReturn
      initial outerScope result frames target occurrence) :
    RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized result.state target := by
  have properties := Detail.inferMatchCasesFuel_inferenceProperties boundary.invariant.ready
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    boundary.scrutineeBelow boundary.invariant.returnBelow boundary.lexicalScope boundary.accepted
  have binders : result.state.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders ((Detail.inferMatchCasesFuel_success_lexicalScope_eq
      boundary.lexicalScope boundary.accepted).trans boundary.lexicalScope.symm)
  exact {
    active := boundary.invariant.active.congr_localBinders binders
    ready := properties.2.1
    returnBelow := boundary.invariant.returnBelow.weaken properties.1.next_le
    bindersBelow := boundary.invariant.bindersBelow.transport binders
      (Detail.inferMatchCasesFuel_nextLocal_le boundary.accepted)
    nodesBelow := (Detail.inferMatchCasesFuel_occurrenceBoundExtends boundary.accepted).nodesBelowNextOccurrence
      boundary.invariant.nodesBelow
    schemeIsolation := activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation binders
    substitutionExtension := boundary.extension
    signaturesEq := boundary.invariant.signaturesEq
    typeParametersEq := boundary.invariant.typeParametersEq
    declarationEq := boundary.invariant.declarationEq
    residual := boundary.invariant.residual
    solvedRequirementsEq := boundary.invariant.solvedRequirementsEq
    assumptionsMono := boundary.invariant.assumptionsMono }

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedScrutineeEntry
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization ProtectedVariables

/-- Every actual scrutinee shape enters its first pattern with privacy derived
from that scrutinee computation, including the synthetic tuple branch. -/
theorem patternEntered_after_scrutinees
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel expressionFuel patternFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr}
    {patternSource : Syntax.Pattern} {entry scrutineeState initial resultState : State}
    {scrutinee : InferredExpression} {inferred : TypedMatchPattern}
    {hidden : Resolved.LocalId} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (scope : CheckingScope selected inferenceContext)
    (entryReady : entry.InferenceReady)
    (entryOperational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (expressionAccepted : inferMatchScrutineesFuel expressionFuel inferenceContext span sources entry =
      .ok (scrutinee, scrutineeState))
    (allocation : scrutineeState.allocateHiddenLocal = (hidden, initial))
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (owner : initial.owner = (checkingContext selected).scope.genericOwner)
    (expectedAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply scrutinee.type))
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (occurs : ∀ requirement ∈ inferred.requirements,
      PrimaryRequirementOccursAt selected.body.finalized.typedSource occurrence requirement)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target occurrence)
    (accepted : Detail.inferMatchPatternFuel patternFuel inferenceContext patternSource scrutinee.type initial =
      .ok (inferred, resultState)) :
    ∃ certificate : MatchPatternInferenceCertificate selected.body.finalized.typedSource target
        selected.body.finalized.substitution scrutinee.type inferred resultState,
      RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized
        resultState certificate.armContext ∧
      ActualContext (checkingContext selected) selected.body.finalized frames certificate.armContext ∧
      GeneralizedActualStateInvariant resultState (evidenceSource selected) := by
  have formation := scope.formation checked
  have catalog := scope.catalog checked
  have canonical := scope.functionsCanonical checked
  have properties := inferMatchScrutineesFuel_inferenceProperties entryReady formation canonical
    expressionAccepted
  have actualScrutinees := entryOperational.ofMatchScrutinees entryReady catalog formation canonical expressionAccepted
  have privacy := actualScrutinees.2
  have operational := actualScrutinees.1.allocateHiddenLocal
  have initialEq := congrArg Prod.snd allocation
  simp only at initialEq
  subst initial
  exact patternEntered checked scope invariant actual operational owner properties.2.2
    expectedAdmissible privacy extension integerPatterns requirements occurs covered accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedScrutineeTyping
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure ScrutineeBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context) (span : Syntax.SourceSpan)
    (sources : List Syntax.Expr) (initial : State) (inferred : InferredExpression) (result : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : inferMatchScrutineesFuel childFuel inferenceContext span sources initial = .ok (inferred, result)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
    selected.body.finalized.solvedRequirements selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends result.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawSubtree : RawSubtreePreserved (result.toTypedSource (bodyRoots selected))
    (evidenceSource selected) (.expression inferred.id)
  integerPatterns : result.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id)
  actualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)

private theorem syntheticScrutinee_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial elementsState : State} {elements : List InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expressions childFuel inferenceContext sources initial elements elementsState))
    (accepted : Detail.inferExprsFuel childFuel inferenceContext sources initial = .ok (elements, elementsState))
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource)
    (extension : selected.body.finalized.substitution.SemanticallyExtends elementsState.inference.substitution)
    (scope : CheckingScope selected inferenceContext)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (rawSubtree : RawSubtreePreserved
      ((elementsState.allocateExpressionId.2.recordNode (.expression {
        id := elementsState.allocateExpressionId.1, span,
        type := Ty.productMany (elements.map (·.type)), form := .tuple (elements.map (·.id))
      })).toTypedSource (bodyRoots selected)) (evidenceSource selected)
      (.expression elementsState.allocateExpressionId.1))
    (integerPatterns : elementsState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (integerLiterals : elementsState.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : elementsState.requirements ⊆ selected.body.returned.requirements)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression elementsState.allocateExpressionId.1))
    (actualCovered : ActualContext.Covers selected.body.finalized frames (.expression elementsState.allocateExpressionId.1)) :
    ExpressionHasType selected.body.finalized.typedSource target elementsState.allocateExpressionId.1
      (selected.body.finalized.substitution.apply (Ty.productMany (elements.map (·.type)))) := by
  let node : ExpressionNode := {
    id := elementsState.allocateExpressionId.1, span,
    type := Ty.productMany (elements.map (·.type)), form := .tuple (elements.map (·.id)) }
  let final := elementsState.allocateExpressionId.2.recordNode (.expression node)
  have contains : ContainsExpression (final.toTypedSource (bodyRoots selected)) node.id node :=
    recordNode_containsExpression _ node
  have sourceExtension : TypingSourceExtends (elementsState.toTypedSource (bodyRoots selected))
      (final.toTypedSource (bodyRoots selected)) := by
    exact ⟨rfl, List.prefix_append _ _⟩
  have edge : ∀ element ∈ elements, DirectChild (final.toTypedSource (bodyRoots selected))
      (.expression node.id) (.expression element.id) := by
    intro element member
    refine ⟨.expression node, ⟨contains.1, rfl⟩, ?_⟩
    simpa [node, nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩ :
        NodeId.expression element.id ∈ (elements.map (·.id)).map NodeId.expression)
  have typed := expressionsRooted_for checked descend childFuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
    here accepted interfaces extension scope invariant actual operational
    (fun element member => (rawSubtree.child (edge element member)).monoBefore sourceExtension)
    integerPatterns integerLiterals requirements
    (fun element member => covered.expressionChild selected.body.resources.graph_closed
      ((rawSubtree.finalized selected.body.resources).directChild (edge element member)))
    (fun element member => actualCovered.directChild
      ((rawSubtree.finalized selected.body.resources).directChild (edge element member)))
  have binders := invariant.typeParameterBinders (by
    simpa [scope.owner, scope.parameters] using scope.canonical checked)
  have finalContains : ContainsExpression selected.body.finalized.typedSource node.id
      (node.applySubstitution selected.body.finalized.substitution) :=
    ⟨(rawSubtree.finalized selected.body.resources).nodes (.expression node) contains.1 (.inl rfl), rfl⟩
  have formTyping : ExpressionFormHasRawType selected.body.finalized.typedSource target
      (node.applySubstitution selected.body.finalized.substitution).form
      (selected.body.finalized.substitution.apply node.type) (.ordinary []) := by
    simpa [node, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
      FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using ExpressionFormHasRawType.tuple typed
  have admissible : TypeAdmissible target (selected.body.finalized.substitution.apply node.type) := by
    simpa [node, FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
      typed.product_type_admissible binders
  exact ExpressionHasType.ofOrdinary (owned := [])
    (rawType := selected.body.finalized.substitution.apply node.type) finalContains formTyping admissible admissible
    (by intro requirement member; simp at member)
    (.nil _) (by simp [node, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, coercionRequirementIds])

theorem scrutineeRooted_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial result : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (singleHere : ∀ expression, sources = [expression] →
      callProvenance (.expression childFuel inferenceContext expression none initial inferred result))
    (manyHere : ∀ elements elementsState, (∀ expression, sources ≠ [expression]) →
      Detail.inferExprsFuel childFuel inferenceContext sources initial = .ok (elements, elementsState) →
      callProvenance (.expressions childFuel inferenceContext sources initial elements elementsState))
    (boundary : ScrutineeBoundary selected childFuel inferenceContext span sources initial inferred result frames target) :
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type) := by
  have accepted := boundary.accepted
  have tupleCase : ∀ (manySources : List Syntax.Expr), sources = manySources →
      (∀ expression, manySources ≠ [expression]) →
      inferMatchScrutineesFuel childFuel inferenceContext span manySources initial = .ok (inferred, result) →
      ExpressionHasType selected.body.finalized.typedSource target inferred.id
        (selected.body.finalized.substitution.apply inferred.type) := by
    intro manySources sourceEq nonsingle accepted
    subst sources
    unfold inferMatchScrutineesFuel at accepted
    split at accepted
    next => exact False.elim (nonsingle _ rfl)
    next _ _ =>
      cases elementsAccepted : Detail.inferExprsFuel childFuel inferenceContext manySources initial with
      | error error => simp [elementsAccepted, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨elements, elementsState⟩
        simp only [elementsAccepted, bind, Except.bind] at accepted
        simp only [pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact syntheticScrutinee_for descend checked recursive
          (manyHere elements elementsState nonsingle elementsAccepted) elementsAccepted boundary.interfaces
          boundary.extension boundary.scope boundary.invariant boundary.actual boundary.operational
          boundary.rawSubtree boundary.integerPatterns boundary.integerLiterals boundary.requirements
          boundary.covered boundary.actualCovered
  cases sources with
  | nil => exact tupleCase [] rfl (by simp) accepted
  | cons source rest =>
    cases rest with
    | nil =>
      exact expressionRooted_of_retained_for checked (recursive childFuel (Nat.lt_succ_self _))
        (singleHere source rfl) ({
        accepted := by simpa [inferMatchScrutineesFuel] using accepted
        interfaces := boundary.interfaces, extension := boundary.extension, scope := boundary.scope
        invariant := boundary.invariant, actual := boundary.actual, operational := boundary.operational
        expectedBelow := by simp
        expectedAdmissible := by simp
        expectedSafe := by simp
        integerPatterns := boundary.integerPatterns, integerLiterals := boundary.integerLiterals
        requirements := boundary.requirements, covered := boundary.covered, actualCovered := boundary.actualCovered
        rawSubtree := boundary.rawSubtree } : RootedExpressionBoundary selected childFuel inferenceContext
          source none initial inferred result frames target)
    | cons second tail => exact tupleCase (source :: second :: tail) rfl (by simp) accepted

theorem scrutineeRooted
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial result : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ScrutineeBoundary selected childFuel inferenceContext span sources initial inferred result frames target) :
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type) := by
  exact scrutineeRooted_for (callProvenance := fun _ => True) true_childClosed checked
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    (fun _ _ => True.intro) (fun _ _ _ _ => True.intro) boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledMatchContinuations
/-! Match bodies inherit the actual pattern state and all later arm/default
calls before the selected finalizer. No semantic body premise is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure CasesContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) where
  checkingFuel : Nat
  inferenceContext : SourceInference.Context
  sources : List Syntax.MatchCase
  scrutinee : Ty
  expected : Ty
  entry : State
  result : Detail.MatchCasesResult
  signatures : inferenceContext.signatures = compiled.program.signatures
  accepted : Detail.inferMatchCasesFuel checkingFuel inferenceContext scrutinee expected entry.lexicalScope sources entry = .ok result
  ready : entry.InferenceReady
  nodesBelow : entry.NodesBelowNextOccurrence
  scrutineeBelow : scrutinee.VariablesBelow entry.inference.next
  expectedBelow : expected.VariablesBelow entry.inference.next
  continuation : result.state.InferenceProgress selected.body.body.state
  retained : result.state.nodes <+: selected.body.body.state.nodes

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem CasesContinuation.arm (cases : CasesContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.MatchCase} (position : cases.sources[index]? = some source) :
    ∃ child : BlockContinuation selected, child.sources = source.value.body.value ∧
      child.inferenceContext = cases.inferenceContext := by
  have formation : ProgramSignatureFormationValidated cases.inferenceContext.signatures :=
    cases.signatures.symm ▸ Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ cases.inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes) := by
    intro signature member
    rw [cases.signatures] at member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := MatchCaseInferenceContinuation.of_position cases.ready cases.nodesBelow
    formation canonical cases.scrutineeBelow cases.expectedBelow cases.accepted position
  exact ⟨{
    checkingFuel := occurrence.fuel, inferenceContext := cases.inferenceContext,
    sources := source.value.body.value, expected := cases.expected, entry := occurrence.entry,
    result := occurrence.result, signatures := cases.signatures, accepted := occurrence.accepted,
    ready := occurrence.ready, nodesBelow := occurrence.nodesBelow, expectedBelow := occurrence.expectedBelow,
    continuation := occurrence.continuation.trans cases.continuation,
    retained := occurrence.retained.trans cases.retained
  }, rfl, rfl⟩

namespace BlockContinuation

theorem match_without_default (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    (form : source.value = .matchWith scrutinees arms) (default : arms.value.defaultBody = none) :
    ∃ cases : CasesContinuation selected, cases.sources = arms.value.cases ∧
      cases.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨scrutinee, scrutineeState, hidden, hiddenState, cases, scrutineeRun,
        hiddenAllocation, casesRun, _, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_matchWithoutDefault_facts form default rfl accepted
      have properties := SourceInferenceSoundness.inferMatchScrutineesFuel_inferenceProperties
        occurrence.ready.allocateStatementId (block.formation checked) (block.canonical checked) scrutineeRun
      have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
      have hiddenReady : hiddenState.InferenceReady := hiddenEq ▸ properties.2.1.allocateHiddenLocal
      have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact properties.2.2
      have expectedBelow : block.expected.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact (block.expectedBelow.weaken occurrence.before.next_le).weaken properties.1.next_le
      have scrutineeNodes := SourceInferenceStatementsSoundness.inferMatchScrutineesFuel_success_nodesBelow
        scrutineeRun (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)
      have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
        rw [← hiddenEq]; exact scrutineeNodes
      have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady
        (block.formation checked) (block.canonical checked) scrutineeBelow expectedBelow rfl casesRun
      have unchanged : occurrence.result.state.inference = cases.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have retained : cases.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]; exact List.prefix_append _ _
      exact ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := arms.value.cases, scrutinee := scrutinee.type, expected := block.expected,
        entry := hiddenState, result := cases, signatures := block.signatures, accepted := casesRun,
        ready := hiddenReady, nodesBelow := hiddenNodes, scrutineeBelow := scrutineeBelow,
        expectedBelow := expectedBelow,
        continuation := (State.InferenceProgress.of_inference_eq casesProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := retained.trans (occurrence.retained.trans block.retained)
      }, rfl, rfl⟩

theorem match_with_default (block : BlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms} {body : Syntax.Block}
    (form : source.value = .matchWith scrutinees arms) (default : arms.value.defaultBody = some body) :
    ∃ cases : CasesContinuation selected, ∃ child : BlockContinuation selected,
      cases.sources = arms.value.cases ∧ cases.inferenceContext = block.inferenceContext ∧
      child.sources = body.value ∧ child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence, occurrenceBelow⟩ := StatementInferenceContinuation.of_position_with_bounds
    block.ready block.nodesBelow (block.formation checked) (block.canonical checked)
    block.expectedBelow block.accepted position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨scrutinee, scrutineeState, hidden, hiddenState, cases, defaultResult, scrutineeRun,
        hiddenAllocation, casesRun, defaultRun, _, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_matchWithDefault_facts form default rfl accepted
      have properties := SourceInferenceSoundness.inferMatchScrutineesFuel_inferenceProperties
        occurrence.ready.allocateStatementId (block.formation checked) (block.canonical checked) scrutineeRun
      have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
      have hiddenReady : hiddenState.InferenceReady := hiddenEq ▸ properties.2.1.allocateHiddenLocal
      have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact properties.2.2
      have expectedBelow : block.expected.VariablesBelow hiddenState.inference.next := by
        rw [← hiddenEq]; exact (block.expectedBelow.weaken occurrence.before.next_le).weaken properties.1.next_le
      have scrutineeNodes := SourceInferenceStatementsSoundness.inferMatchScrutineesFuel_success_nodesBelow
        scrutineeRun (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)
      have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
        rw [← hiddenEq]; exact scrutineeNodes
      have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady
        (block.formation checked) (block.canonical checked) scrutineeBelow expectedBelow rfl casesRun
      have expectedAtDefault := expectedBelow.weaken casesProperties.1.next_le
      have defaultProperties := Detail.inferStatementsFuel_inferenceProperties casesProperties.2.1
        (block.formation checked) (block.canonical checked) expectedAtDefault defaultRun
      have casesNodes := (Detail.inferMatchCasesFuel_occurrenceBoundExtends casesRun).nodesBelowNextOccurrence hiddenNodes
      have toDefault : cases.state.nodes <+: defaultResult.state.nodes :=
        Detail.inferStatementsFuel_preserves_nodesPrefix defaultRun (List.prefix_refl _) casesNodes (Nat.le_refl _)
      have unchanged : occurrence.result.state.inference = defaultResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have retained : defaultResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]; exact List.prefix_append _ _
      have continuation := (State.InferenceProgress.of_inference_eq defaultProperties.2.1.solved unchanged).trans
        (occurrence.continuation.trans block.continuation)
      have nodeContinuation := retained.trans (occurrence.retained.trans block.retained)
      exact ⟨{
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := arms.value.cases, scrutinee := scrutinee.type, expected := block.expected,
        entry := hiddenState, result := cases, signatures := block.signatures, accepted := casesRun,
        ready := hiddenReady, nodesBelow := hiddenNodes, scrutineeBelow := scrutineeBelow,
        expectedBelow := expectedBelow, continuation := defaultProperties.1.trans continuation,
        retained := toDefault.trans nodeContinuation
      }, {
        checkingFuel := childFuel, inferenceContext := block.inferenceContext,
        sources := body.value, expected := block.expected, entry := cases.state, result := defaultResult,
        signatures := block.signatures, accepted := defaultRun, ready := casesProperties.2.1,
        nodesBelow := casesNodes, expectedBelow := expectedAtDefault,
        continuation := continuation, retained := nodeContinuation
      }, rfl, rfl, rfl, rfl⟩

end BlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledTemplateCallOwner
/-! Raw selected compilation closes the plan and graph premises for real open
template emitters, yielding an actual contextual instance of the same row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledTemplateCallOwner
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourcePreparedOpenCallEdges
open CoreLowering.CallableCoercionPreparationSteps (Specialized)

private theorem member_filter {entries : List Specialized} {row : Specialized}
    (unique : (entries.map (·.key)).Nodup) (member : row ∈ entries) :
    entries.filter (fun other => decide (other.key = row.key)) = [row] := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · have empty : rest.filter (fun other => decide (other.key = row.key)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro other present matched
          exact absent (List.mem_map.mpr ⟨other, present, of_decide_eq_true matched⟩)
        simp only [List.filter_cons, decide_true, if_true, empty]
      · have different : first.key ≠ row.key := by
          intro same
          exact absent (List.mem_map.mpr ⟨row, member, same.symm⟩)
        simpa only [List.filter_cons, decide_eq_false different, Bool.false_eq_true, if_false] using ih unique member

/-- Actual worklist uniqueness supplies exact selection for every source row,
not only the named root vector. -/
theorem selected_exact {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations) :
    SourceCompilationPlan.exactSpecialization compiled.plan row.key = .ok row := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  have unique := run_complete_specializationKeys_nodup _ _ _ _ ran
  have found := member_filter unique member
  simp only [SourceCompilationPlan.exactSpecialization, found]

/-- Parameter substitution preserves the original checker's unique occurrence
identities; no body-typing proof is required. -/
theorem selected_unique {compiled : SourceCoreCompiler.Compiled} {row : Specialized} {fuel : Nat}
    (receipt : Selected compiled row fuel) : NodeOccurrencesUnique row.function.typedBody := by
  have unique := receipt.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [receipt.source]
  change (nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource)).Nodup
  have occurrences : nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource) =
      nodeOccurrenceIds receipt.body.finalized.typedSource := by
    simp only [nodeOccurrenceIds, SourceSpecialization.applyTypedSource, List.map_map]
    congr 1
    funext node
    cases node <;> rfl
  rw [occurrences]
  exact unique

structure PreparedContextual (compiled : SourceCoreCompiler.Compiled) (caller : Specialized)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) where
  prepared : Plan
  accepted : SourceCompilationPlan.prepareExecutablePlanEvidence compiled.program compiled.plan = .ok prepared
  edge : EdgeAt caller node instantiation prepared
  contextual : SourcePreparedOpenCallOwner.Contextual compiled.program caller.key caller.function.typedBody node edge.edge
  bodyNodes : List Node
  bodyAccepted : localLambdaBodyNodes caller.function.typedBody contextual.localInstance = .ok bodyNodes
  nodeInBody : .expression node ∈ bodyNodes
  templates : LocalTemplateUses (localLambdaBindings caller.function.typedBody) contextual.localInstance bodyNodes

/-- Actual public compilation and an actual original open call provide the
complete discovered owner, substitution, and original-node correspondence.
There is no contextual-origin, ownership, or plan-uniqueness assumption. -/
theorem open_call_owner {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} (present : .expression node ∈ caller.function.typedBody.nodes)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (cataloged : instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id))
    (opened : InstantiationClosed instantiation = false) :
    Nonempty (PreparedContextual compiled caller node instantiation) := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  have catalog := SignatureCatalogWellFormed.ofCheckProgram (SourceCoreCompiler.compile_checked_source accepted)
  obtain ⟨prepared, preparedAccepted, growth, _origins, covered⟩ :=
    SourcePreparedFinalCallEdgeOrigins.compiled_selected compiled
  obtain ⟨edge, origin⟩ := covered caller member node present callee arguments instantiation form opened
  have source := SourcePreparedCatalogedCallOrigin.source_origin catalog growth
    (selected_exact accepted member) origin edge.callerEq
    (edge.declarationEq.symm ▸ cataloged)
  obtain ⟨contextual⟩ := SourcePreparedOpenCallOwner.contextual_of_open
    (selected_unique selected) present form opened source edge.occurrenceEq
  obtain ⟨bodyNodes, bodyAccepted, nodeInBody, templates⟩ :=
    contextual.body (selected_unique selected) present
  exact ⟨⟨prepared, preparedAccepted, edge, contextual, bodyNodes, bodyAccepted, nodeInBody, templates⟩⟩

/-- Every finalized template has a cataloged emitter. If that original call
is open, the same successful compilation also supplies its actual discovered
local instance. The closed alternative remains explicit for predicate joining. -/
theorem template_owner {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {id : RequirementId} (template : id ∈ sourceLocalSchemeTemplateIds caller.function.typedBody) :
    ∃ node, .expression node ∈ caller.function.typedBody.nodes ∧
      ∃ callee arguments instantiation,
        node.form = .call callee arguments (.declaration instantiation) ∧
        id ∈ node.requirements ∧
        instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id) ∧
        (InstantiationClosed instantiation = true ∨
          Nonempty (PreparedContextual compiled caller node instantiation)) := by
  obtain ⟨node, present, callee, arguments, instantiation, form, issued, cataloged⟩ :=
    SourceCompiledCatalogedCallOrigins.compile_template_emitters accepted member id template
  refine ⟨node, present, callee, arguments, instantiation, form, issued, cataloged, ?_⟩
  cases closed : InstantiationClosed instantiation with
  | true => exact .inl rfl
  | false => exact .inr (open_call_owner accepted member present form cataloged closed)

end Solcore.SourceSemantics.SourceCompiledTemplateCallOwner
end
