import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderControl
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts

/-! Measured stopping receipts for existing protected headers. The source
prefix and the original Core continuation have independent sizes. Empty
headers can retain the entire Core derivation, so continuation contracts use
an inclusive fixed bound; expression and body callbacks remain strictly below
that bound. The actual Tail and result receipts share one context predicate;
ordinary entry points specialize it without changing the static Tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open ProtectedForHeader (Tail TailFor Scope ValuesContext)

/-- A continuation may use the outer size itself when the prefix is empty. -/
def AtMost (budget : Nat) (contract : Nat → Prop) : Prop :=
  ∀ size, size ≤ budget → contract size

theorem AtMost.restrict {contract : Nat → Prop} {small large : Nat}
    (meaning : AtMost large contract) (bounded : small ≤ large) : AtMost small contract :=
  fun size smaller => meaning size (Nat.le_trans smaller bounded)

theorem AtMost.below {contract : Nat → Prop} {budget : Nat}
    (meaning : AtMost budget contract) : RecursiveNamedBoundedContracts.Below budget contract :=
  fun size smaller => meaning size (Nat.le_of_lt smaller)

def ContinuationWithin (budget : Nat)
    (meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (scope : Scope) (code : Expr) : Prop :=
  AtMost budget (fun size => meaning size context scope code)

inductive ResultAtFor (validity : SourceSemantics.Context → Prop) (headerSize : Nat) {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop where
  | continues {sourceSize remainingSize finalContext finalEnvironment after}
      (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after)
      (trace : SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after)
      (maps : LocationMap.Extends mapping tail.mapping) (worlds : WorldExtends world tail.world)
      (preservation : AdministrativePreserved mapping store tail.mapping tail.store)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (remaining : EvaluationSize remainingSize tail.actual tail.store (tail.code.rename tail.embedding) value finalStore)
      (bounded : remainingSize ≤ headerSize) :
      ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore
  | fault {sourceSize finalContext reason token after finalMap finalWorld}
      (trace : SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after)
      (same : value = .inLeft (LocalLoop.controlType type) (.word token)) (matched : faults reason token)
      (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (preservation : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after) :
      ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore

abbrev ResultAt (headerSize : Nat) {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop :=
  ResultAtFor (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) headerSize
    (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
    context environment before items mapping world store value finalStore

variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Ty} {faults : FunctionCalls.FaultRep}
  {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}

/-- Forget bounds only in the safe direction. The source prefix, tail,
heap effects, and actual environment are retained field for field. -/
theorem ResultAtFor.erase {validity : SourceSemantics.Context → Prop} {headerSize : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {items : List ForItemForm}
    {mapping : LocationMap} {world : StoreTyping} {store finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (result : ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore) :
    ProtectedForHeader.ResultFor validity (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore := by
  cases result with
  | continues tail trace maps worlds preservation metadata remaining _ =>
    exact .continues tail trace.sound maps worlds preservation metadata remaining.sound
  | fault trace same matched heaps maps worlds preservation metadata =>
    exact .fault trace.sound same matched heaps maps worlds preservation metadata

theorem ResultAt.erase {headerSize : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {items : List ForItemForm}
    {mapping : LocationMap} {world : StoreTyping} {store finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (result : ResultAt headerSize (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore) :
    ProtectedForHeader.Result (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment before items
      mapping world store value finalStore :=
  ResultAtFor.erase result

theorem ResultAtFor.prepend {validity : SourceSemantics.Context → Prop} {headerSize childSize headSize : Nat} {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (bounded : childSize ≤ headerSize)
    (tail : ResultAtFor validity childSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata remaining remainingBound =>
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) remaining (Nat.le_trans remainingBound bounded)
  | fault trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata =>
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata)

theorem ResultAt.prepend {headerSize childSize headSize : Nat} {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (bounded : childSize ≤ headerSize)
    (tail : ResultAt childSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    ResultAt headerSize (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore :=
  ResultAtFor.prepend head maps worlds preservation metadata bounded tail

/-- The empty prefix retains the original derivation, including equal size. -/
theorem ResultAtFor.nil {validity : SourceSemantics.Context → Prop} {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame} {value : Value} {finalStore : Store}
    (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    ResultAtFor validity size (entry := entry) registry functions program source solved evidence administrative frame globals
      contextLocation native type faults continuation context environment heap [] tail.mapping tail.world tail.store value finalStore :=
  .continues tail .nil (.refl _) (.refl _) (.refl _ _) (.refl _) evaluated (Nat.le_refl _)

theorem ResultAt.nil {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame} {value : Value} {finalStore : Store}
    (tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    ResultAt size (entry := entry) registry functions program source solved evidence administrative frame globals
      contextLocation native type faults continuation context environment heap [] tail.mapping tail.world tail.store value finalStore :=
  ResultAtFor.nil tail evaluated

/-- Instantiate an inclusive continuation with the actual remaining size. -/
theorem tail_at_remaining_for {validity : SourceSemantics.Context → Prop} {budget headerSize remainingSize : Nat}
    {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame}
    (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native (ContinuationWithin budget meaning) context environment heap)
    (remainingBound : remainingSize ≤ headerSize) (headerBound : headerSize ≤ budget) :
    meaning remainingSize context tail.scope tail.code :=
  tail.certificate remainingSize (Nat.le_trans remainingBound headerBound)

theorem tail_at_remaining {budget headerSize remainingSize : Nat}
    {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {contextLocation : Location} {native : NativeFrame}
    (tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native (ContinuationWithin budget meaning) context environment heap)
    (remainingBound : remainingSize ≤ headerSize) (headerBound : headerSize ≤ budget) :
    meaning remainingSize context tail.scope tail.code :=
  tail_at_remaining_for tail remainingBound headerBound

/-- Retain the two actual source children, including the reached lexical scope. -/
theorem source_cons_children {program : Program} {size : Nat}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment finalEnvironment : Dynamic.Environment}
    {before after : Dynamic.Heap} {item : ForItemForm} {items : List ForItemForm}
    (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before
      (item :: items) finalContext finalEnvironment after) :
    ∃ headSize tailSize middleContext nextEnvironment middle,
      SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before
        item middleContext nextEnvironment middle ∧
      SourceExecutionSize.ForItemsExecute program tailSize middleContext evidence source nextEnvironment middle
        items finalContext finalEnvironment after ∧
      headSize < size ∧ tailSize < size := by
  cases trace with
  | cons head tail =>
    exact ⟨_, _, _, _, _, head, tail,
      SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- A first-item fault keeps the entry context. A later fault retains the
successful source prefix and its actual intermediate environment and heap. -/
theorem source_fault_children {program : Program} {size : Nat}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {item : ForItemForm} {items : List ForItemForm}
    {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before
      (item :: items) finalContext reason after) :
    (finalContext = context ∧ ∃ childSize,
      SourceExecutionSize.ForItemFaults program childSize context evidence source environment before item reason after ∧
      childSize < size) ∨
    (∃ headSize tailSize middleContext nextEnvironment middle,
      SourceExecutionSize.ForItemExecutes program headSize context evidence source environment before
        item middleContext nextEnvironment middle ∧
      SourceExecutionSize.ForItemsFault program tailSize middleContext evidence source nextEnvironment middle
        items finalContext reason after ∧
      headSize < size ∧ tailSize < size) := by
  cases trace with
  | head failed =>
    exact .inl ⟨rfl, _, failed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | tail head failed =>
    exact .inr ⟨_, _, _, _, _, head, failed,
      SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
