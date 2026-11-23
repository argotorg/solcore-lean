import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ElementWrites
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ElementSourceInversion

/-!
# Cell-aware invocations: writes to an element of a local array

The pieces the heads of `a[i] = v`, `a[i] op= v` and `a[i] ~=;` take, at one element of a local `a`: the
root's Core cell, an option holding the array's reference or nothing yet, as its Source cell stands for it
(`CellAwareElementWriteRoots.cell_at`, `initialized`, `uninitialized`), and the compiled write's bundle
(`CellAwareElementWriteHeads.Head`), whose code is the receipt's (`CompatibleElementWrites.code`).
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteRoots
open Core Frontend SourceInference GeneralHeap

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {ordinary : GenericHeap.PayloadModel catalog projects definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store}
  {ξ : Renaming} {root : Resolved.LocalId} {slot : Nat} {rootType : Ty} {location : Dynamic.Location}
  {cell : Dynamic.Cell}

/-- The root's Core cell, at the actual slot's reference, and how it stands for the root's Source cell. -/
theorem cell_at
    (environments : DataHeap.EnvRepresents (definitions := definitions) catalog mapping world administrative scope
      environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel ordinary instances) mapping
      world heap store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slotEq : SourceCoreLocalCell.lookup? scope root = some (slot, rootType))
    (lookup : Dynamic.Environment.LooksUp environment root location)
    (read : Dynamic.Heap.Reads heap location cell) (absent : cell.generalized = none) :
    ∃ target coreValue, actual[ξ slot]? = some (.cellRef (OptionalCell.cellType rootType) target) ∧
      store.read? target = some coreValue ∧
      GenericHeap.CellRepresents ordinary mapping world cell coreValue rootType := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slotEq
  obtain ⟨other, coreValue, sourceRead, coreRead, stands⟩ := heaps.cells reference.mapped
  cases read.functional sourceRead
  cases stands with
  | array typed arrayed =>
    obtain ⟨_, _, _, _, _, _, _, _, typeEq, _⟩ := arrayed
    rw [typeEq] at typed
    have impossible := reference.typed.symm.trans typed
    simp [OptionalCell.cellType] at impossible
  | optional typed represented =>
    have samePayload := Option.some.inj (typed.symm.trans reference.typed)
    simp only [OptionalCell.cellType, Ty.sum.injEq, true_and] at samePayload
    subst samePayload
    exact ⟨target, coreValue, agrees selected, coreRead,
      GeneralizedLocalDescriptorHeap.ordinary_cell represented absent⟩

/-- A root that holds an array: its Core cell holds the option's right, with the array's representation. -/
theorem initialized {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (definitions := definitions) catalog mapping world administrative scope
      environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel ordinary instances) mapping
      world heap store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slotEq : SourceCoreLocalCell.lookup? scope root = some (slot, rootType))
    (lookup : Dynamic.Environment.LooksUp environment root location)
    (read : Dynamic.Heap.Reads heap location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation))) :
    ∃ target native, actual[ξ slot]? = some (.cellRef (OptionalCell.cellType rootType) target) ∧
      store.read? target = some (.inRight .unit native) ∧
      ordinary.Represents mapping world cell.type (.arrayRef element arrayLocation) native rootType := by
  cases initialValue with
  | initialized =>
    obtain ⟨target, coreValue, reference, coreRead, represented⟩ :=
      cell_at environments heaps agrees slotEq lookup read rfl
    cases represented with
    | initialized represented => exact ⟨target, _, reference, coreRead, represented⟩

/-- A root not yet initialized: its Core cell holds the option's left. -/
theorem uninitialized
    (environments : DataHeap.EnvRepresents (definitions := definitions) catalog mapping world administrative scope
      environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel ordinary instances) mapping
      world heap store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slotEq : SourceCoreLocalCell.lookup? scope root = some (slot, rootType))
    (lookup : Dynamic.Environment.LooksUp environment root location)
    (read : Dynamic.Heap.Reads heap location cell) (initialValue : Dynamic.RootInitialValue cell none) :
    ∃ target, actual[ξ slot]? = some (.cellRef (OptionalCell.cellType rootType) target) ∧
      store.read? target = some (.inLeft rootType .unit) := by
  cases initialValue with
  | uninitialized _ =>
    obtain ⟨target, coreValue, reference, coreRead, represented⟩ :=
      cell_at environments heaps agrees slotEq lookup read rfl
    cases represented with
    | uninitialized _ => exact ⟨target, reference, coreRead⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteRoots

namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload SourceCoreCompatibleDataPlaces

/-- A write to one element of a local array as the compiler emitted it: the receipt's pieces at the
statement's scope, the index's and the right side's code under the certificate, and the views and the
profile that relate the right side's value to the element's. -/
structure Head (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (rhs : ExpressionId) where
  key : ExpressionId
  single : assignment.target.projections = [.element key]
  slot : Nat
  elementType : Ty
  identity : DataTypeId
  slotEq : SourceCoreLocalCell.lookup? scope assignment.target.root =
    some (slot, .cell (.product .word (.product elementType (.namedData identity))))
  writable : WritableLocal context assignment.target.root (TypeSystem.Ty.array assignment.target.type)
  fuel : Nat
  comparison : SourceCoreCompatibleDataEquality.Prepared values.checked
  prepared : SourceCoreCompatibleDataEquality.prepare fuel values.checked (.constructor (.builtin .word)) =
    .ok comparison
  site : SourceCoreElaboration.ErrorSite
  leaf : project values.checked site assignment.target.type = .ok elementType
  keyNode : ExpressionNode
  keyFound : source.lookupExpression? key = some keyNode
  keyCode : SourceCoreBasic.LoweredExpr
  keyChild : certificate scope key keyCode
  keyType : keyCode.type = .word
  node : ExpressionNode
  found : source.lookupExpression? rhs = some node
  lowered : SourceCoreBasic.LoweredExpr
  right : certificate scope rhs lowered
  rightType : lowered.type = elementType
  rightView : AssignedRhsView operator assignment.target.type node.type
  profile : WideAssignmentProfile operator assignment.target.type
  invalidProjection : Word
  invalid : Word

namespace Head
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

/-- The array's mapping layout. -/
def layout (head : Head values source context certificate scope assignment operator rhs) :
    OrderedMapping.Layout :=
  ⟨.word, head.elementType, head.identity⟩

/-- The root's Core type: a reference to the array's cell. -/
def rootType (head : Head values source context certificate scope assignment operator rhs) : Ty :=
  .cell (.product .word (.product head.elementType (.namedData head.identity)))

/-- The element's modifier: none for a plain write. -/
def modifier (head : Head values source context certificate scope assignment operator rhs) :
    Option ElementModifier :=
  CompatibleElementWrites.modifierOf assignment operator false head.elementType head.invalid

/-- The code the compiler emitted, before `next`. -/
def emit (head : Head values source context certificate scope assignment operator rhs) (next : Expr)
    (output : Ty) : Expr :=
  CompatibleElementWrites.code head.slot head.rootType output head.invalidProjection head.comparison.expression
    head.lowered.expression next head.modifier head.layout head.keyCode.expression

end Head
end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
