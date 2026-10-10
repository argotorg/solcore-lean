import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedExpressionNativeChildren

/-! The actual raw compiler head supplies native witnesses only for its used
child slots. Ordinary and evidence calls retain their selected Header and exact
argument pack. Indirect calls retain the authentic prepared callsite and physical
callee-first entries. Lambda heads use no expression children. The same original
head is strengthened; no Source authority or body execution is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedRawCompilerHeads
open CallableIndexedOwnedPreparedExpressionNativeChildren
open CallableIndexedOwnedPreparedNativeAssignmentChildren (packed_children)

section Named
variable {checked : CallableAncestryPairedLookup.Checked}
  {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {nativeContext : Core.Context} {definitions : DataEnvironment} {nativeType : Ty}

/-- The original ordinary Emission identifies the literal named call pack. -/
theorem ordinary_with_raw {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : RecursiveNamedCatalog.Head headers compilation source context children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    RecursiveNamedCatalog.Head headers compilation source context
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | named member metadata sourceType form calleeFound calleeForm calleeRequirements calleeCoercions
      valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
    rw [emission.equation.1] at typed
    obtain ⟨packType, packTyped⟩ := named_call_arguments typed
    exact .named member metadata sourceType form calleeFound calleeForm calleeRequirements calleeCoercions
      valid predicates evidence arity emission selectedSlot
      (sequence_with_raw sequence (packed_children packTyped)) nativeTypes

/-- The full RawCall preserves the real caller dictionary and selected row. -/
theorem evidence_with_raw {evidence : Dynamic.EvidenceEnvironment}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | ordinary actual => exact .ordinary (ordinary_with_raw actual typed)
  | direct receipt certified metadata =>
    have emitted := congrArg (fun code : SourceCoreBasic.LoweredExpr => code.expression)
      (certified.emitted receipt metadata.coercions)
    rw [emitted] at typed
    obtain ⟨packType, packTyped⟩ := named_call_arguments typed
    exact .direct receipt
      ⟨certified.selected, certified.sourceType, certified.calleeNode, certified.name,
        certified.calleeFound, certified.calleeForm, certified.calleeRequirements, certified.calleeCoercions,
        certified.valid, certified.dictionary,
        sequence_with_raw certified.sequence (packed_children packTyped), certified.nativeTypes⟩ metadata

/-- Both genuine optional-evidence alternatives use their actual emission. -/
theorem named_with_raw {callerEvidence : Option Dynamic.EvidenceEnvironment}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context
      children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases callerEvidence with
  | none => exact ordinary_with_raw head typed
  | some evidence => exact evidence_with_raw head typed

end Named

section Raw
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {children : GenericExpressionMeaning.Certificate}
  {nativeContext : Core.Context} {definitions : DataEnvironment} {nativeType : Ty}

/-- Only actual used slots are strengthened. An arbitrary Entries list may
contain unused children; no native witness for those entries is requested. -/
theorem raw_children {childScope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      children childScope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      (WithRaw nativeContext definitions children) childScope id lowered := by
  cases head with
  | named actual => exact .named (named_with_raw actual typed)
  | lambda allowed found form certificate accepted sourceTyped metadata =>
    exact .lambda allowed found form certificate accepted sourceTyped metadata
  | indirect found form receipt ordered =>
    have emitted := congrArg (fun code : SourceCoreBasic.LoweredExpr => code.expression) receipt.compiler.output
    rw [emitted, receipt.prepared.emitted] at typed
    obtain ⟨calleeRaw, packRaw⟩ := contracted_call_children typed
    obtain ⟨packType, packTyped⟩ := packRaw
    have argumentsRaw := packed_children packTyped
    refine .indirect found form receipt ?_
    intro child code member
    refine ⟨ordered child code member, ?_⟩
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact calleeRaw
    · exact argumentsRaw code (List.of_mem_zip remaining).2

/-- This discharges the original static call slot for the same raw compiler
family. Primitive/data/call heads all retain their original Source receipts. -/
theorem expression_head_with_raw {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : CompatibleExpressionCalls.Head
      (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
      (.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    CompatibleExpressionCalls.Head
      (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
      (.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt
      (WithRaw nativeContext definitions children) scope id lowered := by
  exact CallableIndexedOwnedPreparedExpressionNativeChildren.head_with_raw
    (fun actual _nativeType actualTyped => raw_children root expressionSyntax callerEvidence headers actual actualTyped) head typed

end Raw
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren
