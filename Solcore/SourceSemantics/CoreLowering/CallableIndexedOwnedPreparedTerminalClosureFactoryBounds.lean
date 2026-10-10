import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation

/-! Actual body certificates feed strict staged children and the original
closure application producers. The accepted compiler Tree supplies TerminalFor
internally. Smaller child meaning stays at the real BodyWith certificate and
actual selected Source scope; no arbitrary terminal or whole body law is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactoryBounds
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

/-- The reflection hypothesis ranges over actual selected scopes and the
literal static certificate stored by this association's BodyWith. -/
def ReflectsActualBodyBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget

/-- Preservation covers the Source-selected scope at the same real certificate
and independent Source trace budget. -/
def PreservesActualBodyBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget

private theorem reflects_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : ReflectsActualBodyBelow (registry := registry) (faults := faults) (stages := stages) association functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor
      (registry := registry) (faults := faults) association packet functions budget := by
  have same : HasBodyCertificate association packet := actualChild.1
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [ReflectsActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor]
    rw [same]
    exact children packet.child packet.selected
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [ReflectsActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor]
    rw [same]
    exact children packet.child packet.selected

private theorem preserves_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : PreservesActualBodyBelow (registry := registry) (faults := faults) (stages := stages) association functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor
      (registry := registry) (faults := faults) association packet functions budget := by
  have same : HasBodyCertificate association packet := actualChild.1
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [PreservesActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor]
    rw [same]
    exact children
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [PreservesActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor]
    rw [same]
    exact children

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
/-- The accepted body factory constructs its packet before the original
application reflection port runs once at the literal native completion. -/
theorem application_reflects
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat) (children : ReflectsActualBodyBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association functions budget)
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
    association packet functions caller raw represented heaps stable runtime valid budget
    (reflects_at_packet association expression packet actualChild functions budget children) completed within

include raw represented heaps stable runtime in
/-- The same static packet supports the actual Source-selected application;
no completed body meaning or prebuilt TerminalFor is an input. -/
theorem application_preserves
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (budget : Nat)
    (children : PreservesActualBodyBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association functions budget)
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
    association packet functions caller raw represented heaps stable runtime budget
    (preserves_at_packet association expression packet actualChild functions budget children) trace within
end ContextualApplication

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactoryBounds
