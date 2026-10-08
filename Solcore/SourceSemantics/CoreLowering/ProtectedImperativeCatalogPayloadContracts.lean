import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeMatchStructuralElimination
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady

/-! Payload-aware initializer results keep the actual emitted code. A result
family is assembled by the six existing header constructors; statement meaning
and all Ready witnesses retain the original contract. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)

abbrev HeaderReceiptFamily := Ty → (SourceSemantics.Context → Scope → Expr → Prop) →
  SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop

section HeaderReceipts
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

abbrev LegacyHeaderReceipt (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : HeaderReceiptFamily :=
  fun type continuation context scope items code =>
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates definitions administrative
      type continuation context scope items code, GenericForHeader.Tree.ErrorsFor policy registry faults tree

abbrev StructuralHeaderReceipt
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload) : HeaderReceiptFamily :=
  fun type continuation context scope items code =>
    GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation) AP UP context scope items code

/-- The result builder supplies only the six static header constructor rules. -/
def HeaderReceiptAlgebra (R : HeaderReceiptFamily)
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload) : Prop :=
  ∀ (type : Ty) (continuation : SourceSemantics.Context → Scope → Expr → Prop),
    GenericForHeader.Structural.BranchAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation) AP UP
      (fun context scope items code => R type continuation context scope items code)

theorem legacy_header_algebra (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) :
  HeaderReceiptAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) policy registry faults)
    (fun head => head.ErrorsFor policy registry faults) (fun head => head.Errors faults) := by
  intro type continuation
  constructor
  · intro context scope code next
    exact ⟨.nil next, GenericForHeader.Tree.ErrorsFor.nil (policy := policy) (next := next)⟩
  · intro context next scope binder rest body payload mono extended ordinary projected allocation annotation same child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same tree,
      .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (projected := projected)
        (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  · intro context next scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.initialized mono extended ordinary found sourceType initial allocation annotation same tree,
      .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary) (initializerFound := found)
        (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) errors⟩
  · intro context scope expression expressionNode rest lowered body found value child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.discard found value tree, .discard (found := found) (value := value) errors⟩
  · intro context scope assignment operator rhs rest body head receipt child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.assign head tree, .assign (head := head) errors receipt⟩
  · intro context scope assignment rest body head receipt child
    obtain ⟨tree, errors⟩ := child
    exact ⟨.bitNot head tree, .bitNot (head := head) errors receipt⟩


theorem structural_header_algebra
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload) :
  HeaderReceiptAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (StructuralHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) AP UP) AP UP := by
  intro type continuation
  constructor
  · intro context scope code next M algebra
    exact algebra.nil next
  · intro context next scope binder rest body payload mono extended ordinary projected allocation annotation same child M algebra
    exact algebra.uninitialized mono extended ordinary projected allocation annotation same (child M algebra)
  · intro context next scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same child M algebra
    exact algebra.initialized mono extended ordinary found sourceType initial allocation annotation same (child M algebra)
  · intro context scope expression expressionNode rest lowered body found value child M algebra
    exact algebra.discard found value (child M algebra)
  · intro context scope assignment operator rhs rest body head receipt child M algebra
    exact algebra.assign head receipt (child M algebra)
  · intro context scope assignment rest body head receipt child M algebra
    exact algebra.bitNot head receipt (child M algebra)

end HeaderReceipts

universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)


abbrev PreservingHeaderWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  R type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code

abbrev ReflectingHeaderWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  R type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code

abbrev PreservesAtWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderWithReceipt protocol readiness conditionGate loopFacts initializerFacts (validity := validity) functions program evidence budget R
      (source := source) (frame := frame) (globals := globals)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtWithReceipt (R : HeaderReceiptFamily) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderWithReceipt protocol readiness conditionGate loopFacts initializerFacts (validity := validity) functions program evidence budget R
      (source := source) (frame := frame) (globals := globals)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A completed initializer keeps the original condition, body, and ordered
post-header compiler receipts. Its body premise is the strict recursive goal;
the pending loop Source facts are supplied at its actual normalized context. -/
inductive LoopRecipeWithPayload (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner)
    (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
    (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative))
    (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop) :
    SourceSemantics.Context → Scope → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | mk {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
        context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (postErrors : HP postTree)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
      (child : goal context scope (.statements false statements) expected type bodyCode) :
      LoopRecipeWithPayload HP goal context scope condition post statements expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason)
/-- Forget only the parameterized post-header facet in the legacy instance. -/
theorem LoopRecipeWithPayload.to_legacy (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop}
    {context scope condition post statements expected type code}
    (recipe : LoopRecipeWithPayload (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient)
      (fun postTree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
      goal context scope condition post statements expected type code) :
    ProtectedStateImperativeCatalogReady.LoopRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) diagnosticPolicy goal context scope condition post statements expected type code := by
  cases recipe with
  | mk conditionFound conditionType conditionTree loopBody postTree postErrors nativeTyped child =>
    exact .mk conditionFound conditionType conditionTree loopBody postTree postErrors nativeTyped child

universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (validity : SourceSemantics.Context → Prop) (budget : Nat)
  (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop)

/-- The loop callback keeps its original actual-state preservation contract. -/
def PreservingLoopsWithPayload
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipeWithPayload (administrative := administrative) (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient)
      HP goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    RecursiveNamedHeaderContracts.AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor
      protocol readiness conditionGate (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)

/-- The loop callback keeps its original actual-state reflection contract. -/
def ReflectingLoopsWithPayload
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipeWithPayload (administrative := administrative) (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (ambient := ambient)
      HP goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    RecursiveNamedHeaderContracts.AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor
      protocol readiness conditionGate (validity := validity) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogPayload
