import Solcore.Frontend.RustHull.StatementCorrespondence
import Solcore.Frontend.RustHull.LoweringStructure

/-! Product-place assignment reads the current root after RHS evaluation,
updates one selected component, and writes the root back to its original cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence

def fieldType : List Bool → Core.Ty → Option Core.Ty
  | [], type => some type
  | direction :: rest, .product left right => fieldType rest (if direction then right else left)
  | _ :: _, _ => none

theorem fieldType_append (path suffix : List Bool) (type : Core.Ty) :
    fieldType (path ++ suffix) type = (fieldType path type).bind (fieldType suffix) := by
  induction path generalizing type with
  | nil => rfl
  | cons direction rest ih =>
      cases type <;> simp only [List.cons_append, fieldType]
      all_goals first | rfl | exact ih _

theorem place_correspondence {fuel : Nat} {expression : Expr} {name : String} {path : List Bool}
    (compiled : place fuel expression = .ok (name, path)) :
    Semantics.place? expression = some (name, path) := by
  induction fuel generalizing expression name path with
  | zero => simp [place, fail] at compiled
  | succ fuel ih =>
      cases expression with | mk type kind span =>
      cases kind <;> simp only [place] at compiled
      all_goals try { simp [fail] at compiled }
      case var localName => cases compiled; simp only [Semantics.place?]
      case fst operand =>
        obtain ⟨⟨root, route⟩, inner, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        simp only [Semantics.place?, ih inner, Bind.bind, Option.bind, Pure.pure]
      case snd operand =>
        obtain ⟨⟨root, route⟩, inner, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        simp only [Semantics.place?, ih inner, Bind.bind, Option.bind, Pure.pure]

/-- Checking the actual left expression determines the type at the selected
root path; the RHS type is therefore checked at the component being replaced. -/
theorem place_type {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {lowered : Lowered} {name : String} {path : List Bool}
    {binding : Binding} {index : Nat}
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (placed : place fuel expression = .ok (name, path))
    (looked : scope.lookup name = .ok (binding, index)) :
    fieldType path binding.type = some lowered.type := by
  induction fuel generalizing expression lowered name path with
  | zero => simp [place, fail] at placed
  | succ fuel ih =>
      cases expression with | mk type kind span =>
      cases kind <;> simp only [place] at placed
      all_goals try { simp [fail] at placed }
      case var localName =>
        cases placed
        exact congrArg some (variable_type compiled looked).symm
      case fst operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
          lowerExpression_projection_components false compiled
        have selected := ih operandCompiled innerPlace looked
        rw [operandType] at selected
        rw [fieldType_append, selected]
        rfl
      case snd operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
          lowerExpression_projection_components true compiled
        have selected := ih operandCompiled innerPlace looked
        rw [operandType] at selected
        rw [fieldType_append, selected]
        rfl

/-- Updating a checked path changes only that product component. The two
operands are already computed values, so rebuilding the product is store-free. -/
theorem updateProduct_evaluates {path : List Bool} {type selectedType : Core.Ty}
    {old value expression : Core.Expr}
    (compiled : updateProduct path type old value = .ok expression)
    (selected : fieldType path type = some selectedType)
    {sourceOld sourceValue sourceUpdated : Semantics.Value}
    {targetOld targetValue : Core.Value}
    (oldRelated : ValueRel type sourceOld targetOld)
    (valueRelated : ValueRel selectedType sourceValue targetValue)
    (updated : Semantics.updateProduct? path sourceOld sourceValue = some sourceUpdated)
    {environment : Core.Environment} {store : Core.Store}
    (oldEvaluated : Core.Evaluates environment store old targetOld store)
    (valueEvaluated : Core.Evaluates environment store value targetValue store) :
    ∃ targetUpdated, ValueRel type sourceUpdated targetUpdated ∧
      Core.Evaluates environment store expression targetUpdated store := by
  induction path generalizing type sourceOld sourceUpdated targetOld old expression with
  | nil =>
      cases compiled
      cases selected
      cases updated
      exact ⟨targetValue, valueRelated, valueEvaluated⟩
  | cons direction rest ih =>
      cases type <;> simp only [fieldType] at selected
      all_goals try contradiction
      case product leftType rightType =>
        cases oldRelated with
        | pair leftRelated rightRelated =>
            rename_i sourceLeft sourceRight targetLeft targetRight
            cases direction
            · simp only [updateProduct, Bool.false_eq_true, ↓reduceIte] at compiled
              obtain ⟨component, componentCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
              cases returned
              cases inner : Semantics.updateProduct? rest sourceLeft sourceValue with
              | none => simp [Semantics.updateProduct?, inner] at updated
              | some sourceComponent =>
                  simp only [Semantics.updateProduct?, Bool.false_eq_true, ↓reduceIte, inner,
                    Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at updated
                  cases updated
                  obtain ⟨targetComponent, related, evaluated⟩ :=
                    ih componentCompiled selected leftRelated inner (.first oldEvaluated)
                  exact ⟨.pair targetComponent targetRight, .pair related rightRelated,
                    .pair evaluated (.second oldEvaluated)⟩
            · simp only [updateProduct, ↓reduceIte] at compiled
              obtain ⟨component, componentCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
              cases returned
              cases inner : Semantics.updateProduct? rest sourceRight sourceValue with
              | none => simp [Semantics.updateProduct?, inner] at updated
              | some sourceComponent =>
                  simp only [Semantics.updateProduct?, ↓reduceIte, inner,
                    Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at updated
                  cases updated
                  obtain ⟨targetComponent, related, evaluated⟩ :=
                    ih componentCompiled selected rightRelated inner (.second oldEvaluated)
                  exact ⟨.pair targetLeft targetComponent, .pair leftRelated related,
                    .pair (.first oldEvaluated) evaluated⟩

theorem updateProduct_rename {path : List Bool} {type : Core.Ty} {old value expression : Core.Expr}
    (compiled : updateProduct path type old value = .ok expression) (mapping : Core.Renaming) :
    updateProduct path type (old.rename mapping) (value.rename mapping) = .ok (expression.rename mapping) := by
  induction path generalizing type old expression with
  | nil => cases compiled; rfl
  | cons direction rest ih =>
      cases type <;> simp only [updateProduct] at compiled
      all_goals try { simp [fail] at compiled }
      case product left right =>
        cases direction <;> simp only [Bool.false_eq_true, ↓reduceIte] at compiled
        all_goals
          obtain ⟨component, componentCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
          cases returned
          have renamed := ih componentCompiled
          simp only [Core.Expr.rename] at renamed
          simp only [updateProduct, Bool.false_eq_true, ↓reduceIte, Core.Expr.rename,
            renamed, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem assignment_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {lhs rhs : Expr} {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression) :
    ∃ right name path binding index updated,
      lowerExpression fuel signatures scope rhs = .ok right ∧
      Semantics.place? lhs = some (name, path) ∧
      scope.lookup name = .ok (binding, index) ∧ binding.reference = true ∧
      fieldType path binding.type = some right.type ∧
      updateProduct path binding.type (.var 0) (.var 1) = .ok updated ∧
      expression = Core.LanguageResult.bind (Core.LocalLoop.controlType result) right.expression
        (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
          (Core.OptionalCell.read binding.type (.var (index + 1)) (Core.Word.ofNatModulo 1))
          (.letE (.storeCell (.var (index + 2)) (.inRight .unit updated))
            (Core.LocalLoop.fallthrough result))) := by
  simp only [lowerStatement] at compiled
  obtain ⟨left, leftCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨right, rightCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, matched, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨⟨name, path⟩, placed, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  have reference : binding.reference = true := by
    cases yes : binding.reference
    · simp [yes, fail, Bind.bind, Except.bind] at compiled
    · rfl
  simp only [reference, ↓reduceIte] at compiled
  obtain ⟨updated, updatedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  have selected := place_type leftCompiled placed looked
  rw [expectType_eq_of_ok matched] at selected
  exact ⟨right, name, path, binding, index, updated, rightCompiled,
    place_correspondence placed, looked, reference, selected, updatedCompiled, rfl⟩

theorem assignment_source {σ : Type} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {lhs : Expr} {name : String} {path : List Bool}
    {value : Semantics.Value} (placed : Semantics.place? lhs = some (name, path))
    (assigned : Semantics.assignResult sourceEnvironment initial lhs value = .value final) :
    ∃ location old updated,
      Semantics.lookupLocation sourceEnvironment name = some location ∧
      initial.heap[location]? = some old ∧
      Semantics.updateProduct? path old value = some updated ∧
      final = {initial with heap := initial.heap.set location updated} := by
  simp only [Semantics.assignResult, placed] at assigned
  cases found : Semantics.lookupLocation sourceEnvironment name with
  | none => simp only [found] at assigned; contradiction
  | some location =>
      cases read : initial.heap[location]? with
      | none => simp only [found, read] at assigned; contradiction
      | some old =>
          cases updated : Semantics.updateProduct? path old value with
          | none => simp only [found, read, updated] at assigned; contradiction
          | some newValue =>
              have bound := (List.getElem?_eq_some_iff.mp read).1
              simp only [found, read, updated, Semantics.write?, bound,
                ↓reduceIte, Semantics.Result.value.injEq] at assigned
              exact ⟨location, old, newValue, rfl, read, updated, assigned.symm⟩

theorem assignment_core {result type : Core.Ty} {rhs updated : Core.Expr} {index : Nat}
    {mapping : Core.Renaming} {environment : Core.Environment}
    {initial middle final : Core.Store} {value old newValue : Core.Value} {location : Nat}
    (evaluated : Core.Evaluates environment initial (rhs.rename mapping)
      (.inRight .word value) middle)
    (found : environment[mapping index]? =
      some (.cellRef (Core.OptionalCell.cellType type) location))
    (read : middle.read? location = some (.inRight .unit old))
    (updatedEvaluated : Core.Evaluates (old :: value :: environment) middle
      (updated.rename mapping.lift.lift) newValue middle)
    (written : middle.write? location (.inRight .unit newValue) = some final) :
    Core.Evaluates environment initial
      ((Core.LanguageResult.bind (Core.LocalLoop.controlType result) rhs
        (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
          (Core.OptionalCell.read type (.var (index + 1)) (Core.Word.ofNatModulo 1))
          (.letE (.storeCell (.var (index + 2)) (.inRight .unit updated))
            (Core.LocalLoop.fallthrough result)))).rename mapping)
      (Core.LocalLoop.fallthroughValue result) final := by
  change Core.Evaluates environment initial
    (Core.LanguageResult.bind (Core.LocalLoop.controlType result) (rhs.rename mapping)
      (Core.LanguageResult.bind (Core.LocalLoop.controlType result)
        (Core.OptionalCell.read type (.var (mapping index + 1)) (Core.Word.ofNatModulo 1))
        (.letE (.storeCell (.var (mapping index + 2)) (.inRight .unit (updated.rename mapping.lift.lift)))
          (Core.LocalLoop.fallthrough result)))) _ _
  apply Core.LanguageResult.bind_success _ evaluated
  have foundOne : (value :: environment)[mapping index + 1]? =
      some (.cellRef (Core.OptionalCell.cellType type) location) := found
  apply Core.LanguageResult.bind_success _
    (Core.OptionalCell.read_success _ (.var foundOne) read)
  have foundTwo : (old :: value :: environment)[mapping index + 2]? =
      some (.cellRef (Core.OptionalCell.cellType type) location) := found
  exact .letE (.storeCell (.var foundTwo) read (.inRight updatedEvaluated) written)
    (Core.LocalLoop.fallthrough_evaluates _ _ _)

/-- Every accepted local/product-path assignment preserves the source update.
The source and Core both select and read the root after the RHS effects. -/
theorem assignment {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {lhs rhs : Expr} (rightPreserves : NormalExprPreserves functions effects signatures external rhs)
    {sourceEnvironment : Semantics.Environment} {initial middle final : Semantics.State σ}
    {sourceValue : Semantics.Value} {span : Option Span}
    (sourceEvaluated : Semantics.EvalExpr functions effects sourceEnvironment rhs initial
      (.value sourceValue) middle)
    (assigned : Semantics.assignResult sourceEnvironment middle lhs sourceValue = .value final)
    {fuel : Nat} {scope : Scope} {result : Core.Ty} {loops : Nat} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension finalStore,
      Core.Evaluates environment store (expression.rename mapping)
        (Core.LocalLoop.fallthroughValue result) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  obtain ⟨right, name, path, binding, index, updated, rightCompiled, placed,
      looked, _, selected, updatedCompiled, rfl⟩ := assignment_components compiled
  obtain ⟨extension, value, middleStore, valueRelated, evaluated, middleHeap, middleExternal⟩ :=
    rightPreserves sourceEvaluated rightCompiled environmentRelated heapRelated externalRelated
  obtain ⟨sourceLocation, sourceOld, sourceUpdated, found, read, updateSource, rfl⟩ :=
    assignment_source placed assigned
  obtain ⟨location, entry, _, targetFound⟩ :=
    (environmentRelated.extendWorld extension) name sourceLocation binding index found looked
  obtain ⟨oldValue, targetRead, oldRelated⟩ := middleHeap.read entry read
  have updatedRenamed : updateProduct path binding.type (.var 0) (.var 1) =
      .ok (updated.rename mapping.lift.lift) :=
    updateProduct_rename updatedCompiled mapping.lift.lift
  have oldEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
      (.var 0) oldValue middleStore := .var rfl
  have valueEvaluated : Core.Evaluates (oldValue :: value :: environment) middleStore
      (.var 1) value middleStore := .var rfl
  obtain ⟨newValue, newRelated, updatedEvaluated⟩ :=
    updateProduct_evaluates updatedRenamed selected oldRelated valueRelated updateSource oldEvaluated valueEvaluated
  have written : middleStore.write? location (.inRight .unit newValue) =
      some (middleStore.set location (.inRight .unit newValue)) :=
    Core.Store.write?_eq_some_iff.mpr ⟨middleHeap.location_bound entry, rfl⟩
  exact ⟨extension, _, assignment_core evaluated targetFound targetRead updatedEvaluated written,
    middleHeap.write entry newRelated written, frame.write middleExternal middleHeap entry written⟩

end Solcore.Frontend.RustHull.StatementCorrespondence
