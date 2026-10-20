import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerState
import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

/-! Recursive expression contracts use one selected body and its actual
finalizer. Their boundaries retain the concrete inference call and source
records; generalized locals use the operational invariant without a
monomorphism restriction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

abbrev checkingContext (selected : BodySelection compiled row fuel) : SourceInference.Context :=
  context compiled.program.environment compiled.program.signatures
    selected.signature selected.body.declaration

abbrev bodyRoots (selected : BodySelection compiled row fuel) : List NodeId :=
  selected.body.body.statements.map NodeId.statement

abbrev evidenceSource (selected : BodySelection compiled row fuel) : TypedSource :=
  selected.body.returned.toTypedSource (bodyRoots selected)

/-- Lexical descent may change loop depth while preserving the actual
declaration's static type environment. -/
structure CheckingScope (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) : Prop where
  signatures : inferenceContext.signatures = (checkingContext selected).signatures
  owner : inferenceContext.scope.genericOwner = (checkingContext selected).scope.genericOwner
  parameters : inferenceContext.typeParameters = (checkingContext selected).typeParameters
  assumptions : inferenceContext.assumptions = (checkingContext selected).assumptions

theorem CheckingScope.refl (selected : BodySelection compiled row fuel) :
    CheckingScope selected (checkingContext selected) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem CheckingScope.withLoopDepth {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} (scope : CheckingScope selected inferenceContext)
    (depth : Nat) :
    CheckingScope selected { inferenceContext with loopDepth := depth } :=
  ⟨scope.signatures, scope.owner, scope.parameters, scope.assumptions⟩

theorem CheckingScope.formation {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ProgramSignatureFormationValidated inferenceContext.signatures :=
  scope.signatures.symm ▸ Frontend.checkProgram_success_signature_formation checked

theorem CheckingScope.catalog {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    SignatureCatalogWellFormed inferenceContext.signatures :=
  scope.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked

theorem CheckingScope.functionsCanonical {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes) := by
  intro candidate member
  rw [scope.signatures] at member
  exact (Frontend.checkProgram_success_function_signature_shape checked member).2

theorem CheckingScope.canonical {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters := by
  have canonical := selected.canonical checked
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  rw [scope.owner, scope.parameters]
  simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq] using canonical

structure ExpressionCallBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (expected : Option Ty)
    (initial : State) (inferred : InferredExpression) (resultState : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferExprFuel childFuel inferenceContext expression expected initial =
    .ok (inferred, resultState)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends
    resultState.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected)
    selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next
  expectedAdmissible : ∀ type ∈ expected,
    TypeAdmissible target (selected.body.finalized.substitution.apply type)
  expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
    ProtectedVariables.Safe binder.scheme.quantified initial type
  integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : resultState.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : resultState.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id)
  actualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)

structure RetainedExpressionBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (expected : Option Ty)
    (initial : State) (inferred : InferredExpression) (resultState : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop
    extends ExpressionCallBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target where
  proper : ProperDescendantsPreserved selected.body.finalized.substitution
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
    (.expression inferred.id)
  rawProper : RawProperDescendantsPreserved
    (resultState.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression inferred.id)
  expressionRequirements : ExpressionRequirementsRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id
  coercionPrimaries : ExpressionCoercionPrimariesRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id
  operatorSite : ExpressionOperatorSiteRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id
  directChildren : ExpressionDirectChildrenRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id

structure RootedExpressionBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (expected : Option Ty)
    (initial : State) (inferred : InferredExpression) (resultState : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop
    extends ExpressionCallBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target where
  rawSubtree : RawSubtreePreserved (resultState.toTypedSource (bodyRoots selected))
    (evidenceSource selected) (.expression inferred.id)

def ExpressionRetainedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    RetainedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred

def ExpressionRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
