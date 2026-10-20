import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceRecursion
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceProducer

/-! A generalized initialized statement is indexed by the actual selected
receipt. Its barrier concerns that allocation and remains an explicit
premise until the actual call reachability is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure InitializedOccurrenceBoundary (selected : BodySelection compiled row fuel)
    (source : Syntax.Statement) (expectedReturn : Ty)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) where
  occurrence : BodyInitializerOccurrence selected source
  scope : CheckingScope selected occurrence.inferenceContext
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
    selected.body.finalized occurrence.entry target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected)
  rawSubtree : RawSubtreePreserved
    (occurrence.result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected)
    (.statement occurrence.result.id)
  patterns : occurrence.result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  literals : occurrence.result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : occurrence.result.state.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target
    (.statement occurrence.entry.allocateStatementId.1)
  actualCovered : ActualContext.Covers selected.body.finalized frames
    (.statement occurrence.entry.allocateStatementId.1)
  barrier : GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
    occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
    selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)

def InitializerOccurrenceConclusion {selected : BodySelection compiled row fuel}
    {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedOccurrenceBoundary selected source expectedReturn frames target) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized boundary.occurrence.result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant boundary.occurrence.result.state (evidenceSource selected) ∧
    StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := boundary.occurrence.inferenceContext.loopDepth }
      target boundary.occurrence.result.id finalContext
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
    StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution boundary.occurrence.result
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }

theorem InitializedOccurrenceBoundary.sound {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedOccurrenceBoundary selected source expectedReturn frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (childSound : ExpressionRootedSoundness selected boundary.occurrence.childFuel) :
    InitializerOccurrenceConclusion boundary :=
  boundary.occurrence.statement_of_expressionSoundness checked boundary.scope boundary.interfaces
    boundary.invariant boundary.actual boundary.operational boundary.rawSubtree
    boundary.patterns boundary.literals boundary.requirements boundary.covered boundary.actualCovered
    boundary.barrier childSound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
