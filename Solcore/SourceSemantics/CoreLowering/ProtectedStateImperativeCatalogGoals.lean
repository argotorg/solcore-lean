import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderContinuationMap
import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts

/-! One static CatalogSites goal family. Statement goals carry the actual
reached state; initializer goals retain the same ordered header tree with an
actual loop continuation. Source and native grades remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedImperativeFor (Position)
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)

abbrev PreservingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservesAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol conditionGate (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderWith protocol conditionGate (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol conditionGate (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderWith protocol conditionGate (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.CatalogCompatibility
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  {entry : ProtectedExpressionMeaning.Entry} {validity : SourceSemantics.Context → Prop}
  {size : Nat} {scope : Scope} {mode : Bool} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {condition : ExpressionId} {post : List ForItemForm}

/-- The legacy flow observes the actual producer's result. -/
theorem preserves
    (actual : ProtectedStateTransition.Lexical.Gated.PreservesAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _post⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

/-- Reflection retains its independent source grade. -/
theorem reflects
    (actual : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped installed evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _post⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

/-- Header continuation observation uses the actual reached loop entry. -/
theorem loop_preserves
    (actual : ProtectedFor.Body.Stateful.LoopPreservesAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) condition post statements expected type code) :
    RecursiveNamedForContracts.LoopPreservesAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before after store ξ contextLocation native outcome
    environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, _related⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached.down⟩

/-- The reached observer is extracted from the actual native loop result. -/
theorem loop_reflects
    (actual : ProtectedFor.Body.Stateful.LoopReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) condition post statements expected type code) :
    RecursiveNamedForContracts.LoopReflectsAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, _related⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached.down⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.CatalogCompatibility
