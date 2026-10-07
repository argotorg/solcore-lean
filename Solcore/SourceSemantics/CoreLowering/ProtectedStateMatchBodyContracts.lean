import Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchPrefix

/-! The bounded match child interfaces keep the actual selected-arm state and
fixed frame gate. Source selection and typing stay independent static receipts;
these callbacks are discharged by the surrounding body induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource}
  (program : Program) (parent : SourceSemantics.Context) (control : ControlContext)
  (evidence : Dynamic.EvidenceEnvironment) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty)
  {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : FunctionCalls.FaultRep} (budget : Nat)

def ArmPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def ArmPreservesBelow (outerScope : Scope) : Prop :=
  ArmPreservesBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def ArmReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def ArmReflectsBelow (outerScope : Scope) : Prop :=
  ArmReflectsBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def DefaultPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultPreservesBelow (outerScope : Scope) : Prop :=
  DefaultPreservesBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def DefaultReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultReflectsBelow (outerScope : Scope) : Prop :=
  DefaultReflectsBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)


/-- The match head uses the same actual five-way head interface as control. -/
abbrev Head.HeadPreservesAtFor := @RecursiveNamedImperativeFor.Control.Stateful.HeadPreservesAtWith
abbrev Head.HeadReflectsAtFor := @RecursiveNamedImperativeFor.Control.Stateful.HeadReflectsAtWith


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds.Stateful

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ProtectedStateTransition

/-- The old entry receipt has both concrete binder operations. -/
def legacyBindings {guarded : ProtectedExpressionMeaning.Entry}
    (bindings : ProtectedExpressionMeaning.Binds guarded) : Bindings (Lexical.legacyProtocol guarded) where
  prepend state _ _ _ := ⟨bindings.prepend state.down⟩
  prepend_related _ _ _ _ := trivial
  prepend_records _ _ _ _ := rfl
  restore state := ⟨bindings.restore state.down⟩
  restore_related _ := trivial
  restore_records _ := rfl

section ExpressionAdapters
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {size : Nat} {guarded : ProtectedExpressionMeaning.Entry}

/-- The compatibility post observes the effects proved by the child. -/
theorem legacy_expression_preserves (transport : ProtectedExpressionMeaning.Transport guarded)
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults guarded) :
    ProtectedStateTransition.PreservesAt (Lexical.legacyProtocol guarded) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

/-- Reflection keeps its independent Source grade and actual effects. -/
theorem legacy_expression_reflects (transport : ProtectedExpressionMeaning.Transport guarded)
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults guarded) :
    ProtectedStateTransition.ReflectsAt (Lexical.legacyProtocol guarded) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩
end ExpressionAdapters

end Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts
