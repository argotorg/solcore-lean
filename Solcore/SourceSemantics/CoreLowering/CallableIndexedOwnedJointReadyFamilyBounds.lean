import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyInputs
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! This finite connection uses the existing measured Ready Family for the
three authentic joint indices. Its expression selectors receive only the
strictly smaller dependent body meanings and must be supplied by the actual
expression dispatcher. The module does not close that mixed dispatcher. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedJointReadyFamilyInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- The actual source expression dispatcher receives strictly smaller joint
body meanings at each callee's own protocol, full origin and genuine facts. -/
abbrev PreservingExpressions : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    ∀ context, (origin index).validity context → ∀ budget child, child ≤ budget →
      (∀ callee : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (certificates := certificates) (expressionSyntax := expressionSyntax), RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol callee) (readiness (bridge callee))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed callee).facts
          functions (Program.ofChecked compiled.sourceProgram) (origin callee))) →
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt (protocol index) (readiness (bridge index))
        (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (inputs wellFormed index).exprFacts ((origin index).certificates context)
        (context := context) (source := (origin index).function.source) (faults := faults) child

/-- Native expression children retain the original strict dependent callee
bounds and independently reconstructed Source grades at the actual post. -/
abbrev ReflectingExpressions : Prop :=
  ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    ∀ context, (origin index).validity context → ∀ budget child, child ≤ budget →
      (∀ callee : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (certificates := certificates) (expressionSyntax := expressionSyntax), RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol callee) (readiness (bridge callee))
          (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed callee).facts
          functions (Program.ofChecked compiled.sourceProgram) (origin callee))) →
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt (protocol index) (readiness (bridge index))
        (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (inputs wellFormed index).exprFacts ((origin index).certificates context)
        (context := context) (source := (origin index).function.source) (faults := faults) child

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

include extension faithful observations sameLayouts in
/-- The sole existing measured Family composes genuine finite catalog kits
with this source dispatcher; all actual reached entry fields remain intact. -/
theorem preserves_at
    (expressions : PreservingExpressions (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed)
    (size : Nat) : ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    CallableRuntimeBodyReadyOrigins.PreservesAt (protocol index) (readiness (bridge index))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
      functions (Program.ofChecked compiled.sourceProgram) (origin index) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.preserves_at (registry := registry) (faults := faults)
    origin functions (Program.ofChecked compiled.sourceProgram) observations
    protocol (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts) (acquire functions sameLayouts) transport bindings
    (fun index => readiness (bridge index)) (inputs wellFormed) expressions
    (fun index budget children => preserving_kits functions sameLayouts wellFormed extension faithful observations
      index budget children) size

include extension faithful observations sameLayouts in
/-- The same Family consumes original native completions and preserves the
independent Source grade and each branch's actual returned protocol witness. -/
theorem reflects_at (functionTypes : FunctionRuntimeViews functions)
    (expressions : ReflectingExpressions (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed)
    (size : Nat) : ∀ index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax),
    CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol index) (readiness (bridge index))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index).facts
      functions (Program.ofChecked compiled.sourceProgram) (origin index) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.reflects_at (registry := registry) (faults := faults)
    origin functions (Program.ofChecked compiled.sourceProgram) observations
    protocol (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts) (acquire functions sameLayouts) transport bindings
    (fun index => readiness (bridge index)) (inputs wellFormed) expressions
    (fun index budget children => reflecting_kits functions sameLayouts wellFormed extension faithful observations
      functionTypes index budget children) size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyBounds
