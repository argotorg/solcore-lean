import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates

/-! Actual ordinary closure reads construct the expression Roots needed by
conditional branches, bare assignments and lexical statements. The retained compiler chooses one
branching packet; no Source execution or whole-body law is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaReadRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots (Read)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (original : MetadataFor compiled.indexed support.caller.named function.source)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include provenance receiver wellFormed original in
/-- Every original read is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_reads
    (syntaxTree : GenericImperativeMatch.Syntax function.source (Read function.source)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.BranchingSupport
      code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  refine ⟨support.body.frame, support.body.projection, ?_⟩
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport.tree
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures support.body.projection syntaxTree
    (certificates := fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered faults))
    (fun context fields current fuel id node lowered declarations read reached found typed accepted _nativeType _native => by
      obtain ⟨readNode, name, binder, readFound, form⟩ := read
      have same := Option.some.inj (readFound.symm.trans found)
      subst readNode
      apply CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.of_child
        code support provenance receiver wellFormed original selected fields declarations reached found form typed
      simpa only [choice.callback, choice.reason, FunctionCode.children] using accepted)
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  simpa only [stages.source selected] using weakened

include provenance receiver wellFormed original in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_reads
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (Read function.source)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code stages,
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support
        code support.body.toContext stages packet faults) := by
  obtain ⟨choice⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose
    code support.caller.named provenance.policy_recipe.body_recipe shape child selected
  exact ⟨⟨.branching choice.packet,
    support_reads code support provenance receiver wellFormed original choice syntaxTree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaReadRoots
