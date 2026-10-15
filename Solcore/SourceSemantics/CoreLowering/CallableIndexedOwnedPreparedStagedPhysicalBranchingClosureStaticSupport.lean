import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport

/-! Actual scoped closure compilation retains the original flow and mixed
expression roots at each reached lexical context. No execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching parameterScope)

structure SelectedBody {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Branching code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  readFuel : Nat
  «prefix» : code.compilation.administrativePrefix = 1
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    function.source invalidProjection missingDefault)
  collected : ∀ child, stages.Closure function child →
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) compiled.indexed.layouts packet.allocationOwner packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length packet.onError
      (.initial compiled.compatible.checked) child.source (fun _ => True)
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
        (fun context scope id lowered => Nonempty (Σ rawType,
          CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.Root compiled headers stages
            code.policy code.lowerBody code.compilation readFuel context child code.reasonAt
            scope id lowered rawType semanticFaults)))
      compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore packet.flow

abbrev SelectedBody.tree {compiled function scope administrative headers code inputs stages packet semanticFaults}
    (support : @SelectedBody compiled function scope administrative headers code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :=
  (support.collected child selected).tree

theorem SelectedBody.sites {compiled function scope administrative headers code inputs stages packet semanticFaults}
    (support : @SelectedBody compiled function scope administrative headers code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (registry : SourceCoreRawMetadata.Registry) :
    PreparedBranchingCatalogSites.CatalogSites support.invalidProjection support.missingDefault registry semanticFaults
      (support.tree child selected) :=
  (support.collected child selected).sites registry

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport
