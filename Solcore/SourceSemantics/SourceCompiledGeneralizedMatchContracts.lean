import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceGeneralizedMatchState
import Solcore.SourceSemantics.SourceCompiledGeneralizedPatternEntry
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementsContracts

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
