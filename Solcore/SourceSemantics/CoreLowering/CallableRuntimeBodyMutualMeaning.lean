import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyInputs

/-! One source induction and one native induction close a family of actual
static bodies. The expression interface is internal to the enclosing mutual
proof and receives only strictly smaller original body obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins

private theorem close_sized {ι : Type} (family : ι → Nat → Prop)
    (step : ∀ size, (∀ callee, RecursiveNamedBoundedContracts.Below size (family callee)) →
      ∀ i, family i size) (size : Nat) : ∀ i, family i size := by
  induction size using Nat.strongRecOn with
  | ind size ih => exact step size (fun callee smaller strict => ih smaller strict callee)
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} (origins : ι → Origin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension faithful observations in
/-- Source children may use the current budget; callee bodies are strict. -/
theorem preserves_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget (PreservesAt functions program (origins callee))) →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults (origins i).protectedEntry)
    (size : Nat) : ∀ i, PreservesAt functions program (origins i) size := by
  apply close_sized (fun i => PreservesAt functions program (origins i))
  intro size below i entry outcome after trace
  have children : ∀ context, (origins i).validity context → RecursiveNamedHeaderContracts.AtMost size
      (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context
        (origins i).function.evidence (origins i).function.source ((origins i).certificates context)
        faults (origins i).protectedEntry) := by
    intro context valid child within
    exact expressionMeaning i context valid size child within below
  exact (origins i).body.preserves_sized functions (origins i).definitions (origins i).registered extension
    program faithful observations (origins i).escapedFault (origins i).transport (origins i).binders
    (origins i).extend (origins i).runtimeOf size size (Nat.le_refl size) children
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.installed trace

include extension faithful observations functionTypes in
/-- Native finish inversion selects original strict children. Reflection
returns the source grade without a preservation or source-trace premise. -/
theorem reflects_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget (ReflectsAt functions program (origins callee))) →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults (origins i).protectedEntry)
    (size : Nat) : ∀ i, ReflectsAt functions program (origins i) size := by
  apply close_sized (fun i => ReflectsAt functions program (origins i))
  intro size below i entry value finalStore completed
  have children : ∀ context, (origins i).validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context
        (origins i).function.evidence (origins i).function.source ((origins i).certificates context)
        faults (origins i).protectedEntry) := by
    intro context valid child smaller
    exact expressionMeaning i context valid size child (Nat.le_of_lt smaller)
      below
  exact (origins i).body.reflects_sized functions (origins i).definitions (origins i).registered extension
    program faithful observations functionTypes (origins i).escapedFault (origins i).transport (origins i).binders
    (origins i).extend (origins i).runtimeOf size size (Nat.le_refl size) children
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.installed completed

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
open CallableRuntimeBodyReadyInputs
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} {Records : ι → Type v}
  (origins : ι → StaticOrigin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (protocols : ∀ i, ProtectedStateTransition.Protocol.{u, v} (Records i))
  (conditionGate : ι → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ i, ProtectedStateTransition.MarkedAllocation.Producer (protocols i)
    (origins i).layouts (origins i).frameLayout (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ i location native, conditionGate i location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers i).toOrdinary location native)
  (stateTransport : ∀ i, ProtectedStateTransition.AdministrativeTransport (protocols i))
  (stateBindings : ∀ i, ProtectedStateTransition.Bindings (protocols i))

  (readinesses : ∀ i, Readiness (protocols i))
  (inputs : ∀ i, Inputs (protocols i) (readinesses i) (stateBindings i) program (origins i))

include observations producers acquire stateTransport stateBindings inputs in
/-- The original measured family closes actual ready entries through the same kernel. -/
theorem preserves_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (protocols callee) (readinesses callee) (conditionGate callee) (inputs callee).facts functions program (origins callee))) →
      ExpressionPreservesAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child)
    (kitsFor : ∀ i budget,
      (∀ context, (origins i).validity context → RecursiveNamedHeaderContracts.AtMost budget (fun child =>
        ExpressionPreservesAt (protocols i) (readinesses i) program (origins i).function.evidence
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
          (context := context) (source := (origins i).function.source) (faults := faults) child)) →
      PreservingKits (protocols i) (readinesses i) (stateBindings i) program (origins i) functions (conditionGate i) (inputs i) budget)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyReadyOrigins.PreservesAt (protocols i) (readinesses i) (conditionGate i) (inputs i).facts functions program (origins i) size := by
  apply close_sized (fun i => CallableRuntimeBodyReadyOrigins.PreservesAt (protocols i) (readinesses i)
    (conditionGate i) (inputs i).facts functions program (origins i))
  intro size below i entry outcome after trace
  have children : ∀ context, (origins i).validity context → RecursiveNamedHeaderContracts.AtMost size
      (fun child => ExpressionPreservesAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child) := by
    intro context valid child within
    exact expressionMeaning i context valid size child within below
  have kit := kitsFor i size children
  exact CallableRuntimeBodyKernel.Stateful.WithReady.BodyFor.preserves_sized
    (body := (origins i).body) (functions := functions) (definitions := (origins i).definitions)
    (registered := (origins i).registered) (program := program)
    (observations := observations) (escapedFault := (origins i).escapedFault) (extend := (origins i).extend)
    (protocol := protocols i) (producer := producers i) (conditionGate := conditionGate i)
    (acquire := acquire i) (stateTransport := stateTransport i) (stateBindings := stateBindings i)
    (readiness := readinesses i) (facts := (inputs i).facts) (headFacts := (inputs i).headFacts)
    (exprFacts := (inputs i).exprFacts) (loopFacts := (inputs i).loopFacts) (initializerFacts := (inputs i).initializerFacts)
    (assignmentFacts := (inputs i).assignmentFacts) (snapshotFacts := (inputs i).snapshotFacts)
    (sites := (inputs i).sites) (initializerSites := (inputs i).initializerSites) (assignmentSites := (inputs i).assignmentSites)
    (transfers := (inputs i).transfers) (snapshots := (inputs i).snapshots)
    size size (Nat.le_refl size) kit.assignments kit.assignmentFaults kit.headFor kit.loopFor children entry.bodyFacts
    entry.original.environments entry.original.heaps entry.original.locals entry.original.lookups entry.original.actualTyped
    entry.original.reference entry.original.read entry.original.unmapped entry.original.initial entry.original.gate entry.ready trace

include observations producers acquire stateTransport stateBindings inputs in
/-- The original measured family closes actual ready entries through the same kernel. -/
theorem reflects_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocols callee) (readinesses callee) (conditionGate callee) (inputs callee).facts functions program (origins callee))) →
      ExpressionReflectsAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child)
    (kitsFor : ∀ i budget,
      (∀ context, (origins i).validity context → RecursiveNamedBoundedContracts.Below budget (fun child =>
        ExpressionReflectsAt (protocols i) (readinesses i) program (origins i).function.evidence
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
          (context := context) (source := (origins i).function.source) (faults := faults) child)) →
      ReflectingKits (protocols i) (readinesses i) (stateBindings i) program (origins i) functions (conditionGate i) (inputs i) budget)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyReadyOrigins.ReflectsAt (protocols i) (readinesses i) (conditionGate i) (inputs i).facts functions program (origins i) size := by
  apply close_sized (fun i => CallableRuntimeBodyReadyOrigins.ReflectsAt (protocols i) (readinesses i)
    (conditionGate i) (inputs i).facts functions program (origins i))
  intro size below i entry value finalStore completed
  have children : ∀ context, (origins i).validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => ExpressionReflectsAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child) := by
    intro context valid child smaller
    exact expressionMeaning i context valid size child (Nat.le_of_lt smaller) below
  have kit := kitsFor i size children
  exact CallableRuntimeBodyKernel.Stateful.WithReady.BodyFor.reflects_sized
    (body := (origins i).body) (functions := functions) (definitions := (origins i).definitions)
    (registered := (origins i).registered) (program := program)
    (observations := observations) (escapedFault := (origins i).escapedFault) (extend := (origins i).extend)
    (protocol := protocols i) (producer := producers i) (conditionGate := conditionGate i)
    (acquire := acquire i) (stateTransport := stateTransport i) (stateBindings := stateBindings i)
    (readiness := readinesses i) (facts := (inputs i).facts) (headFacts := (inputs i).headFacts)
    (exprFacts := (inputs i).exprFacts) (loopFacts := (inputs i).loopFacts) (initializerFacts := (inputs i).initializerFacts)
    (assignmentFacts := (inputs i).assignmentFacts) (snapshotFacts := (inputs i).snapshotFacts)
    (sites := (inputs i).sites) (initializerSites := (inputs i).initializerSites) (assignmentSites := (inputs i).assignmentSites)
    (transfers := (inputs i).transfers) (snapshots := (inputs i).snapshots)
    size size (Nat.le_refl size) kit.assignments kit.headFor kit.loopFor children entry.bodyFacts
    entry.original.environments entry.original.heaps entry.original.locals entry.original.lookups entry.original.actualTyped
    entry.original.reference entry.original.read entry.original.unmapped entry.original.initial entry.original.gate entry.ready completed

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family

namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.Family
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} {Records : ι → Type v}
  (origins : ι → StaticOrigin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (protocols : ∀ i, ProtectedStateTransition.Protocol.{u, v} (Records i))
  (conditionGate : ι → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ i, ProtectedStateTransition.MarkedAllocation.Producer (protocols i)
    (origins i).layouts (origins i).frameLayout (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ i location native, conditionGate i location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers i).toOrdinary location native)
  (stateTransport : ∀ i, ProtectedStateTransition.AdministrativeTransport (protocols i))
  (stateBindings : ∀ i, ProtectedStateTransition.Bindings (protocols i))

include extension faithful observations producers acquire stateTransport stateBindings in
/-- Each genuine origin uses its own state protocol and record observation.
The same measured fold supplies only strictly smaller actual callee meanings. -/
theorem preserves_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocols callee) (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.PreservesAt (protocols i) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocols i) (conditionGate i) functions program (origins i) size := by
  have closed := WithReady.Family.preserves_at
    (origins := origins) (functions := functions) (program := program) (observations := observations)
    (protocols := protocols) (conditionGate := conditionGate) (producers := producers) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readinesses := fun i => RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial (protocols i))
    (inputs := fun i => CallableRuntimeBodyReadyInputs.Inputs.trivial (protocols i) (stateBindings i) program (origins i))
    (expressionMeaning := fun i context valid budget child within below =>
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
        (protocol := protocols i) (program := program) (evidence := (origins i).function.evidence)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context)
        (expressionMeaning i context valid budget child within (fun callee smaller strict =>
          CallableRuntimeBodyReadyOrigins.PreservesAt.forget_trivial (below callee smaller strict))))
    (kitsFor := fun i budget children => CallableRuntimeBodyReadyInputs.PreservingKits.trivial
      (protocol := protocols i) (stateBindings := stateBindings i) (program := program) (origin := origins i)
      (functions := functions) (conditionGate := conditionGate i) (budget := budget)
      (extension := extension) (faithful := faithful) (observations := observations)
      (producer := producers i) (acquire := acquire i) (stateTransport := stateTransport i)
      (fun context valid child within => CallableRuntimeBodyReadyInputs.expression_preserves_forget_true
        (protocol := protocols i) (program := program)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context) (children context valid child within))) size
  intro i
  exact CallableRuntimeBodyReadyOrigins.PreservesAt.forget_trivial (closed i)

include extension faithful observations functionTypes producers acquire stateTransport stateBindings in
/-- Original native completions choose strict callees at their own protocols.
The same measured closer returns independent source grades and actual posts. -/
theorem reflects_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocols callee) (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.ReflectsAt (protocols i) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocols i) (conditionGate i) functions program (origins i) size := by
  have closed := WithReady.Family.reflects_at
    (origins := origins) (functions := functions) (program := program) (observations := observations)
    (protocols := protocols) (conditionGate := conditionGate) (producers := producers) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readinesses := fun i => RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial (protocols i))
    (inputs := fun i => CallableRuntimeBodyReadyInputs.Inputs.trivial (protocols i) (stateBindings i) program (origins i))
    (expressionMeaning := fun i context valid budget child within below =>
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true
        (protocol := protocols i) (program := program) (evidence := (origins i).function.evidence)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context)
        (expressionMeaning i context valid budget child within (fun callee smaller strict =>
          CallableRuntimeBodyReadyOrigins.ReflectsAt.forget_trivial (below callee smaller strict))))
    (kitsFor := fun i budget children => CallableRuntimeBodyReadyInputs.ReflectingKits.trivial
      (protocol := protocols i) (stateBindings := stateBindings i) (program := program) (origin := origins i)
      (functions := functions) (conditionGate := conditionGate i) (budget := budget)
      (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes)
      (producer := producers i) (acquire := acquire i) (stateTransport := stateTransport i)
      (fun context valid child within => CallableRuntimeBodyReadyInputs.expression_reflects_forget_true
        (protocol := protocols i) (program := program)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context) (children context valid child within))) size
  intro i
  exact CallableRuntimeBodyReadyOrigins.ReflectsAt.forget_trivial (closed i)

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.Family

namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} {Records : Type v}
  (origins : ι → StaticOrigin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : ι → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ i, ProtectedStateTransition.MarkedAllocation.Producer protocol
    (origins i).layouts (origins i).frameLayout (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ i location native, conditionGate i location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers i).toOrdinary location native)
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)

include extension faithful observations producers acquire stateTransport stateBindings in
/-- The actual source family closes through the shared measured fold. Its
expression interface receives only strictly smaller actual callee meanings. -/
theorem preserves_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.PreservesAt protocol (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.PreservesAt protocol (conditionGate i) functions program (origins i) size := by
  exact Family.preserves_at origins functions extension program faithful observations
    (fun _ => protocol) conditionGate producers acquire
    (fun _ => stateTransport) (fun _ => stateBindings) expressionMeaning size

include extension faithful observations functionTypes producers acquire stateTransport stateBindings in
/-- The actual native family consumes original completions and returns
independently graded source traces through the same measured closer. -/
theorem reflects_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.ReflectsAt protocol (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt protocol (conditionGate i) functions program (origins i) size := by
  exact Family.reflects_at origins functions extension program faithful observations functionTypes
    (fun _ => protocol) conditionGate producers acquire
    (fun _ => stateTransport) (fun _ => stateBindings) expressionMeaning size

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful
