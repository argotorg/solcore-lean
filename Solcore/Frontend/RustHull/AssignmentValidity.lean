import Solcore.Frontend.RustHull.ProductAssignmentCorrespondence
import Solcore.Frontend.RustHull.ScopeCoverage

/-! Accepted assignment paths and covered source locals exclude malformed
source updates. The source root is read after the RHS has finished. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence

private theorem place_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {lowered : Lowered} {name : String} {path : List Bool}
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (placed : place fuel expression = .ok (name, path)) :
    name.startsWith Effects.reservedPrefix = false := by
  induction fuel generalizing expression lowered name path with
  | zero => simp [place, fail] at placed
  | succ fuel ih =>
      cases expression with | mk type kind span =>
      cases kind <;> simp only [place] at placed
      all_goals try { simp [fail] at placed }
      case var localName =>
        cases placed
        simp only [lowerExpression] at compiled
        obtain ⟨expected, _, compiled⟩ := lower_bind_eq_ok.mp compiled
        cases allowed : name.startsWith Effects.reservedPrefix
        · rfl
        · simp [allowed, fail, Bind.bind, Except.bind] at compiled
      case fst operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, _, _, operandCompiled, _, _⟩ :=
          lowerExpression_projection_components false compiled
        exact ih operandCompiled innerPlace
      case snd operand =>
        obtain ⟨⟨root, route⟩, innerPlace, returned⟩ := lower_bind_eq_ok.mp placed
        cases returned
        obtain ⟨operandCode, _, _, operandCompiled, _, _⟩ :=
          lowerExpression_projection_components true compiled
        exact ih operandCompiled innerPlace

private theorem assignment_root_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {lhs rhs : Expr} {span : Option Span} {expression : Core.Expr}
    {name : String} {path : List Bool}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression)
    (placed : Semantics.place? lhs = some (name, path)) :
    name.startsWith Effects.reservedPrefix = false := by
  simp only [lowerStatement] at compiled
  obtain ⟨left, leftCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨right, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨⟨root, route⟩, placeCompiled, _⟩ := lower_bind_eq_ok.mp compiled
  have same := Option.some.inj ((place_correspondence placeCompiled).symm.trans placed)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact place_allowed leftCompiled placeCompiled

/-- A checked product path has a source update whenever the root has its
represented type. This also covers replacing the whole local at the empty path. -/
theorem updateProduct_exists {path : List Bool} {type selectedType : Core.Ty}
    {sourceOld sourceValue : Semantics.Value} {targetOld : Core.Value}
    (selected : fieldType path type = some selectedType)
    (related : ValueRel type sourceOld targetOld) :
    ∃ sourceUpdated, Semantics.updateProduct? path sourceOld sourceValue = some sourceUpdated := by
  induction path generalizing type sourceOld targetOld with
  | nil => exact ⟨sourceValue, rfl⟩
  | cons direction rest ih =>
      cases type <;> simp only [fieldType] at selected
      all_goals try contradiction
      case product leftType rightType =>
        cases related with
        | pair left right =>
            rename_i sourceLeft sourceRight targetLeft targetRight
            cases direction
            · obtain ⟨updated, found⟩ := ih selected left
              exact ⟨.pair updated sourceRight, by simp [Semantics.updateProduct?, found]⟩
            · obtain ⟨updated, found⟩ := ih selected right
              exact ⟨.pair sourceLeft updated, by simp [Semantics.updateProduct?, found]⟩

/-- Compilation checks the path, coverage supplies its source name, and HeapRel
supplies the initialized root and its type, so source assignment cannot be malformed. -/
theorem assignment_valid {σ : Type} {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {lhs rhs : Expr} {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.assign lhs rhs, span⟩ = .ok expression)
    {sourceEnvironment : Semantics.Environment} (covered : ScopeCoverage sourceEnvironment scope)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    {state : Semantics.State σ} {value : Semantics.Value}
    (locals : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heap : HeapRel world state.heap store) :
    ∃ finalState, Semantics.assignResult sourceEnvironment state lhs value = .value finalState := by
  obtain ⟨right, name, path, binding, index, updated, _, placed, looked, _, selected, _, _⟩ :=
    assignment_components compiled
  have allowed := assignment_root_allowed compiled placed
  obtain ⟨sourceLocation, found⟩ := covered name binding index allowed looked
  obtain ⟨location, entry, _, _⟩ := locals name sourceLocation binding index found looked
  obtain ⟨sourceOld, targetOld, read, _, related⟩ := heap.cell sourceLocation binding.type location entry
  obtain ⟨sourceUpdated, updated⟩ := updateProduct_exists (sourceValue := value) selected related
  have bound := (List.getElem?_eq_some_iff.mp read).1
  exact ⟨{state with heap := state.heap.set sourceLocation sourceUpdated}, by
    simp only [Semantics.assignResult, placed, found, read, updated, Semantics.write?, bound, ↓reduceIte]⟩

end Solcore.Frontend.RustHull.StatementCorrespondence
