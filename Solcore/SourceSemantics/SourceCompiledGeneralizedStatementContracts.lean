import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementInvariant
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted

/-! Ordinary statements retain their actual call and the same selected final
source. Initialized statements supply their own concrete allocation barrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure StatementBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (statement : Syntax.Statement) (expectedReturn : Ty)
    (initial : State) (result : Detail.StatementResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferStatementFuel childFuel inferenceContext statement expectedReturn initial =
    .ok result
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends
    result.state.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
    selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawSubtree : RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected))
    (evidenceSource selected) (.statement result.id)
  integerPatterns : result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.state.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target (.statement result.id)
  actualCovered : ActualContext.Covers selected.body.finalized frames (.statement result.id)

def StatementConclusion (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (result : Detail.StatementResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext facts,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
    StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target result.id finalContext facts ∧
    StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
