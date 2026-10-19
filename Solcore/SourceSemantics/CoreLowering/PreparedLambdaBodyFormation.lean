import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
import Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries

/-! Genuine unrestricted ordinary support forms a closure at its actual
nested Header packet. Source attribution and the full carried seed stay original.
Forward inclusion transfers only the new closure, with one function model for
all actual input/output heaps and the unchanged reached packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open PreparedLambdaBodySupport CallableIndexedOwnedSourceAdmission

section Seed
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- The actual chosen contextual seed carries its prepared body before any
capture value exists. No execution law or old body package is a field. -/
structure Formation (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  produced : Produced (compiled := compiled) caller.named parameters result statements context evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  issued : CallableIndexedOwnedContextualLambdaSourceDiagnostics.IssuedSource compiled produced.site.code.compilation.owner
    (CallableIndexedNamedGeneration.source caller.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : PreparedLambdaBodySupport.Body produced.compilation produced.site.code
    (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
  bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code
  bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named
  declarations : CompatibleExpressionReads.ScopeDeclarations
    (CallableIndexedNamedGeneration.source caller.named) scope context
  sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements produced.site.code.sourceNode.coercions []
  coercions : produced.site.code.sourceNode.coercions = []
  callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence

variable {caller context evidence}

def Formation.function {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements context evidence environment

def Formation.code {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Code compiled.indexed (head.function environment) scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) :=
  RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
    head.produced.site.code environment

def Formation.support {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Support (head.code environment) :=
  (Support.of_site caller head.produced.compilation head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body).recapture environment

theorem Formation.prepared {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : PreparedAt (head.code environment) (head.support environment) :=
  .recaptured caller head.produced.compilation head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body head.produced.binderPolicy head.produced.compilerPolicy head.produced.issuedRecipe head.bodyView head.bodyReasons head.declarations environment
end Seed

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
