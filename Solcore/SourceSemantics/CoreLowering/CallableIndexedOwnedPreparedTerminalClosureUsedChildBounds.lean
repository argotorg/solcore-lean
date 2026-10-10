import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation

/-! The accepted same-Code compiler factory exposes its exact used body child.
A singleton certificate keeps that scope, expression and lowered child through
the original terminal application producers. The numeric child hypotheses and
every actual Source-selected scope remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedTerminalClosureFactories
universe u

private abbrev preparedStages (compiled : SourceCoreUnifiedCompilation.Compiled) :=
  RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
    compiled.indexed.ancestry.graph.inputs.callable.table

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- A static certificate for one physical compiler child. -/
def Point (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current id code => current = scope ∧ id = expression ∧ code = lowered

private abbrev bodyScope {closure : Dynamic.Closure}
    {localScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed closure localScope administrative) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope

/-- The accepted lowering action determines the packet's exact child. All
compiler fields and the selected staged scope stay at that same packet. -/
def narrow {closure : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed closure localScope administrative}
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages :=
  { packet with
    certificate := Point (bodyScope code) packet.expression packet.receipt.child
    certifies := by
      intro lowered generated
      have same : packet.receipt.child = lowered :=
        Except.ok.inj (packet.receipt.generated.symm.trans generated)
      exact ⟨rfl, rfl, same.symm⟩ }

/-- Both contextual association forms retain their real Code and receipt. -/
def narrowFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (packet : TerminalFor association stages) :
    TerminalFor association stages :=
  match association, packet with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _, packet => narrow packet
  | .principal _ _ _ _ _ _ _ _ _ _ _, packet => narrow packet

/-- Reflection is requested only at a used child certified by the actual
BodyWith family, with an independent strict native budget. -/
def ReflectsUsedChildBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget

/-- Preservation uses the same exact static child and the Source trace budget.
It still covers every scope genuinely selected by that Source application. -/
def PreservesUsedChildBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget

private theorem reflects_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : ReflectsUsedChildBelow (registry := registry) (faults := faults) (stages := stages)
      association expression functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor
      (registry := registry) (faults := faults) association (narrowFor association packet) functions budget := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [ReflectsUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified packet.child packet.selected)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [ReflectsUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified packet.child packet.selected)

private theorem preserves_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : PreservesUsedChildBelow (registry := registry) (faults := faults) (stages := stages)
      association expression functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor
      (registry := registry) (faults := faults) association (narrowFor association packet) functions budget := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [PreservesUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [PreservesUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified)

section ContextualApplication
variable (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {sources : List Dynamic.Value} {values : List Value}
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)

include raw represented heaps stable runtime in
/-- The actual used child certificate supplies the singleton numeric hypothesis
before the original application reflection port runs once. -/
theorem application_reflects
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat) (children : ReflectsUsedChildBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association expression functions budget)
    {invocation : Staging.Recursive.Scope} {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) (preparedStages compiled) sourceSize
        invocation context before (.closure function) sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression shape reader
  exact CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.application_reflects
    association (narrowFor association packet) functions caller raw represented heaps stable runtime valid budget
    (reflects_at_packet association expression packet actualChild functions budget children) completed within

include raw represented heaps stable runtime in
/-- The original Source-selected application consumes its exact static child
through the singleton hypothesis and restores the full reached caller state. -/
theorem application_preserves
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (budget : Nat)
    (children : PreservesUsedChildBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association expression functions budget)
    {invocation : Staging.Recursive.Scope} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) (preparedStages compiled) size
      invocation context before (.closure function) sources outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [native, DataPatternValues.packValues values] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression shape reader
  exact CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.application_preserves
    association (narrowFor association packet) functions caller raw represented heaps stable runtime budget
    (preserves_at_packet association expression packet actualChild functions budget children) trace within
end ContextualApplication

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
