import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity

/-! A method port retains the genuine selected method, its full dictionary and
its actual cached slot. Runtime capture authority and body meaning are separate
inputs at the reached call state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)

/-- The actual source operator fixes its trait method names. -/
def Dispatch (traitName methodName : String) : Prop :=
  (∃ operator operand, receipt.node.form = .unary operator operand ∧
    UnaryTraitDispatch operator traitName methodName) ∨
  (∃ operator left right, receipt.node.form = .binary left operator right ∧
    BinaryTraitDispatch operator traitName methodName)

/-- Static formation of the actual selected method. The closed initial profile
has empty method assumptions; its caller may retain a nonempty dictionary. -/
structure SelectionSupport
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator) : Prop where
  formed : CallableCoercionMethodInstantiation.Formation
    selected.certificate.selected.implementation selected.certificate.selected.declaration
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures receipt.program.signatures)
    receipt.method.specialized.parameterSubstitution
  covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method
  unique : NodeOccurrencesUnique
    (CallableCoercionMethodInstantiation.bodyInstance receipt.program receipt.method).source
  empty : (CallableCoercionMethodInstantiation.bodyInstance receipt.program receipt.method).context.assumptions = []

structure Port (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment)
    (stages : Staging.Recursive.Registry) where
  actual : Receipt policy body fuel compilation values source scope id reasonAt lowered
  program : actual.program = compiled.sourceProgram
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled actual.method
  signature : principal.named.signature = receipt.signature
  slot : principal.cached.index = receipt.index
  dispatch : Dispatch receipt principal.traitName principal.methodName
  selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    context caller principal.traitName principal.methodName receipt.node.requirements
    principal.sourceBody principal.dictionary
  agrees : ∀ sourceBody dictionary,
    Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context caller principal.traitName principal.methodName receipt.node.requirements
      sourceBody dictionary → sourceBody = principal.sourceBody ∧ dictionary = principal.dictionary
  child : Staging.Recursive.Scope
  staged : stages.Closure principal.sourceFunction child
  diagnostics : ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
    compiled.indexed.base.diagnostics = some diagnostics ∧
    principal.cached.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}
  sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
    (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
