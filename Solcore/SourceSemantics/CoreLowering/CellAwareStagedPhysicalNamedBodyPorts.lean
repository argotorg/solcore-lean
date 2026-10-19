import Solcore.SourceSemantics.CoreLowering.GenericCellHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures

/-! Internal body ports separate authentic named parameter entry and caller
restoration from statement shape. Reflection keeps the actual final Source
context, including locals introduced while evaluating the body. Static compiler
packets and strict child induction supply these ports. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedPhysicalNamedBodyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedNamedChildBounds (poolBridge)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (cells : GenericHeap.CellModel definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (budget : Nat)

/-- Full Source-to-native body meaning at the real reached parameter state. -/
def PreservesBelow : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (_environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
    (_heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : State headers keys
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
    (_admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context initial)
    (owner : OwnedKey keys)
    (_packet : owner.key.capturePrefix = 0 → header.globals = compiled.indexed.base.globals.length →
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial)
    (_keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    (_physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (_slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) canonical),
    ∀ {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (_trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (_matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (_within : size ≤ budget),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached

/-- Native-to-Source body meaning with its actual final lexical context. -/
def ReflectsBelow : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (_environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
    (_heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : State headers keys
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
    (_admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context initial)
    (owner : OwnedKey keys)
    (_packet : owner.key.capturePrefix = 0 → header.globals = compiled.indexed.base.globals.length →
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial)
    (_keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    (_physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (_slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) canonical),
    ∀ {size : Nat} {value : Value} {finalStore : Store}
    (_completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (_within : size ≤ budget),
    ∃ sourceSize finalContext bodyOutcome outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult header.function.resultType
        bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached

theorem preservesBelow_ordinary_iff :
    PreservesBelow (headers := headers) (keys := keys) header model (GenericHeap.CellModel.ordinary model)
      stages child faults budget ↔
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys) header model
      stages child faults budget := by
  simp only [PreservesBelow, CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow, GenericHeap.ordinaryHeap_iff]

theorem reflectsBelow_ordinary_iff :
    ReflectsBelow (headers := headers) (keys := keys) header model (GenericHeap.CellModel.ordinary model)
      stages child faults budget ↔
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys) header model
      stages child faults budget := by
  simp only [ReflectsBelow, CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow, GenericHeap.ordinaryHeap_iff]

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedPhysicalNamedBodyPorts
