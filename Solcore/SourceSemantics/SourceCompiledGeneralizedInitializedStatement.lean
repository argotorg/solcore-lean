import Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerRecursion

/-! A generalized initialized statement is indexed by the actual selected
receipt. Its barrier concerns that one allocation; it is not a law over
arbitrary checker calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure InitializedStatementBoundary (selected : BodySelection compiled row fuel)
    (source : Syntax.Statement) (expectedReturn : Ty)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) where
  continuation : RetainedInitializer selected source
  scope : CheckingScope selected continuation.inferenceContext
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
    selected.body.finalized continuation.entry target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant continuation.entry (evidenceSource selected)
  rawSubtree : RawSubtreePreserved
    (continuation.result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected)
    (.statement continuation.result.id)
  patterns : continuation.result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  literals : continuation.result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : continuation.result.state.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target
    (.statement continuation.entry.allocateStatementId.1)
  actualCovered : ActualContext.Covers selected.body.finalized frames
    (.statement continuation.entry.allocateStatementId.1)
  barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
    continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
    selected.body.finalized.substitution target (localSchemeTemplateIds continuation.initializerBinding.binder)

def InitializedStatementConclusion {selected : BodySelection compiled row fuel}
    {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedStatementBoundary selected source expectedReturn frames target) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized boundary.continuation.result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant boundary.continuation.result.state (evidenceSource selected) ∧
    StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := boundary.continuation.inferenceContext.loopDepth }
      target boundary.continuation.result.id finalContext
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
    StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution boundary.continuation.result
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }

theorem InitializedStatementBoundary.sound {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedStatementBoundary selected source expectedReturn frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (childSound : ExpressionRootedSoundness selected boundary.continuation.childFuel) :
    InitializedStatementConclusion boundary :=
  boundary.continuation.statement_of_expressionSoundness checked boundary.scope boundary.interfaces
    boundary.invariant boundary.actual boundary.operational boundary.rawSubtree
    boundary.patterns boundary.literals boundary.requirements boundary.covered boundary.actualCovered
    boundary.barrier childSound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
