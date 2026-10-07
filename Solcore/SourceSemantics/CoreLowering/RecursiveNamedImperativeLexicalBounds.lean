import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate

/-! Lexical bodies embed into the five-way imperative contract without changing
an execution, heap, lexical context, caller entry or size. The only converted
field is the established three-way flow representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep)

variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} {scope : Scope} {mode : Bool}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {size : Nat}

theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.PreservesAtFor (validity := validity) functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
       (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical⟩

theorem preserves_at
    (correct : RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  exact preserves_at_for (functions := functions) (program := program) (evidence := evidence)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) correct

theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.ReflectsAtFor (validity := validity) functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
       (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical⟩

theorem reflects_at
    (correct : RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  exact reflects_at_for (functions := functions) (program := program) (evidence := evidence)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) correct

namespace Stateful
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol condition functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped initial gate trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped initial gate trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩

theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (correct : RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol condition functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial gate evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped initial gate evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical, transition⟩

end Stateful

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
