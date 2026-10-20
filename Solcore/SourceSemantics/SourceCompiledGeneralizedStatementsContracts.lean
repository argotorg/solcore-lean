import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure StatementsBoundary (selected : Selected compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (statements : List Syntax.Statement) (expectedReturn : Ty)
    (initial : State) (result : Detail.BlockResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferStatementsFuel childFuel inferenceContext statements expectedReturn initial =
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
  rawSubtrees : ∀ child ∈ result.statements,
    RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.statement child)
  integerPatterns : result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.state.requirements ⊆ selected.body.returned.requirements
  covered : ∀ child ∈ result.statements,
    TemplateScopeCovered selected.body.finalized.typedSource target (.statement child)
  actualCovered : ∀ child ∈ result.statements,
    ActualContext.Covers selected.body.finalized frames (.statement child)

def StatementsConclusion (selected : Selected compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (result : Detail.BlockResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext facts,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
    StatementsHaveType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target result.statements finalContext facts ∧
    BlockResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
