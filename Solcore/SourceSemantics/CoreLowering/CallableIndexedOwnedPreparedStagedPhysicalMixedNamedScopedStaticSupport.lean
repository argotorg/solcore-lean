import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads

/-! Each named scoped child retains its actual physical mixed root and compiler
prefix. The authentic named receipt supplies the complete collected statement
tree and its catalog sites; execution is supplied by the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Certificate
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ root : RootAt compiled headers stages context invocation scope id lowered semanticFaults,
    root.compilation.administrativePrefix = 1

structure Support
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (receipt : Receipt header)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    header.function.source invalidProjection missingDefault)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults)
      header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source expressionSyntax
      (TypedCertificate child.source (fun context => Certificate headers stages semanticFaults context child))
      compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body)
      header.function.resultType header.output receipt.flow

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport
