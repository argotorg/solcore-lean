import Solcore.Syntax.Term
import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalReference

/-! Local-name avoidance and renaming support. -/

/-!
## Consolidated module: `Solcore.Frontend.LocalNameAvoidance`
-/

/-! A spelling-avoidance condition for the local-expression shapes. Every literal
payload avoids all names, even if malformed, overflowing, or a string. This is
not a free-name analysis for other canonical syntax forms. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- No identifier in this expression has the specified spelling. Literal validity
is not required, since literal payloads do not perform name lookup.
All conditional children, binary operands and original tuple elements are checked, including
children that a particular runtime environment might skip. -/
inductive AvoidsLocalName (name : String) : Syntax.Expr → Prop where
  | identifier {span : Syntax.SourceSpan} {identifier : Syntax.Identifier}
      (different : name ≠ identifier.value) :
      AvoidsLocalName name { span, value := .identifier identifier }
  | literal {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteral} :
      AvoidsLocalName name { span, value := .literal literal }
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      (child : AvoidsLocalName name inner) :
      AvoidsLocalName name { span, value := .group inner }
  | unit {span tupleSpan : Syntax.SourceSpan} :
      AvoidsLocalName name { span, value := .tuple ⟨tupleSpan, []⟩ }
  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .tuple ⟨tupleSpan, [left, right]⟩ }
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr} (headAvoids : AvoidsLocalName name first)
      (tailAvoids : AvoidsLocalName name ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩) :
      AvoidsLocalName name ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : AvoidsLocalName name operand) :
      AvoidsLocalName name { span, value := .unary ⟨operatorSpan, .logicalNot⟩ operand }
  | bitNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : AvoidsLocalName name operand) :
      AvoidsLocalName name { span, value := .unary ⟨operatorSpan, .bitNot⟩ operand }
  | add {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .add⟩ right }
  | subtract {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .subtract⟩ right }
  | multiply {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .multiply⟩ right }
  | divide {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .divide⟩ right }
  | modulo {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .modulo⟩ right }
  | greater {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .greater⟩ right }
  | equal {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .equal⟩ right }
  | notEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .notEqual⟩ right }
  | lessEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .lessEqual⟩ right }
  | less {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .less⟩ right }
  | greaterEqual {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .greaterEqual⟩ right }
  | bitAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .bitAnd⟩ right }
  | bitOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .bitOr⟩ right }
  | bitXor {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .bitXor⟩ right }
  | logicalAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .logicalAnd⟩ right }
  | logicalOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftAvoids : AvoidsLocalName name left) (rightAvoids : AvoidsLocalName name right) :
      AvoidsLocalName name { span, value := .binary left ⟨operatorSpan, .logicalOr⟩ right }
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr}
      (conditionAvoids : AvoidsLocalName name condition)
      (thenAvoids : AvoidsLocalName name thenBranch)
      (elseAvoids : AvoidsLocalName name elseBranch) :
      AvoidsLocalName name
        { span, value := .conditional condition question thenBranch colon elseBranch }

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalNameAvoidanceProperties`
-/

/-! Adding an unused spelling preserves exact structural resolution. No
freshness of the supplied ID, table uniqueness, or successful resolution is
required; using the added spelling is deliberately outside these laws. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalNameTable.lookup_cons_iff_of_ne {table : LocalNameTable}
    {name spelling : String} {newId id : Resolved.LocalId} (different : name ≠ spelling) :
    LocalNameTable.Lookup ((name, newId) :: table) spelling id ↔
      LocalNameTable.Lookup table spelling id := by
  constructor
  · intro found
    cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => exact found
  · exact LocalNameTable.Lookup.tail different

theorem AvoidsLocalName.resolves_cons_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) {table : LocalNameTable}
    {id : Resolved.LocalId} {resolved : Resolved.Expr} :
    ResolvesLocalExpression ((name, id) :: table) source resolved ↔
      ResolvesLocalExpression table source resolved := by
  induction avoids generalizing resolved with
  | unit =>
      constructor <;> intro resolution <;> cases resolution <;> exact .unit
  | identifier different =>
      constructor
      · intro resolution
        cases resolution with
        | identifier found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mp found)
      · intro resolution
        cases resolution with
        | identifier found =>
            exact .identifier ((LocalNameTable.lookup_cons_iff_of_ne different).mpr found)
  | literal =>
      constructor <;> intro resolution <;> cases resolution with
      | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih =>
      constructor
      · intro resolution
        cases resolution with
        | group child => exact .group (ih.mp child)
      · intro resolution
        cases resolution with
        | group child => exact .group (ih.mpr child)
  | pair _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | pair left right => exact .pair (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | pair left right => exact .pair (leftIH.mpr left) (rightIH.mpr right)
  | many _ _ headIH tailIH =>
      constructor
      · intro resolution
        cases resolution with
        | many head tail => exact .many (headIH.mp head) (tailIH.mp tail)
      · intro resolution
        cases resolution with
        | many head tail => exact .many (headIH.mpr head) (tailIH.mpr tail)
  | logicalNot _ ih =>
      constructor
      · intro resolution
        cases resolution with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro resolution
        cases resolution with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro resolution
        cases resolution with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro resolution
        cases resolution with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | divide _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | divide left right => exact .divide (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | divide left right => exact .divide (leftIH.mpr left) (rightIH.mpr right)
  | modulo _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | modulo left right => exact .modulo (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | modulo left right => exact .modulo (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | lessEqual _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | lessEqual left right => exact .lessEqual (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | lessEqual left right => exact .lessEqual (leftIH.mpr left) (rightIH.mpr right)
  | less _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | less left right => exact .less (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | less left right => exact .less (leftIH.mpr left) (rightIH.mpr right)
  | greaterEqual _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | greaterEqual left right => exact .greaterEqual (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | greaterEqual left right => exact .greaterEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | logicalAnd left right => exact .logicalAnd (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | logicalAnd left right => exact .logicalAnd (leftIH.mpr left) (rightIH.mpr right)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro resolution
        cases resolution with
        | logicalOr left right => exact .logicalOr (leftIH.mp left) (rightIH.mp right)
      · intro resolution
        cases resolution with
        | logicalOr left right => exact .logicalOr (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro resolution
        cases resolution with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mp condition) (thenIH.mp thenBranch) (elseIH.mp elseBranch)
      · intro resolution
        cases resolution with
        | conditional condition thenBranch elseBranch =>
            exact .conditional (conditionIH.mpr condition) (thenIH.mpr thenBranch) (elseIH.mpr elseBranch)

/-- Exact executable agreement includes unresolved expressions returning `none`. -/
theorem AvoidsLocalName.resolve_cons_eq {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (table : LocalNameTable) (id : Resolved.LocalId) :
    resolveLocalExpression? ((name, id) :: table) source = resolveLocalExpression? table source := by
  cases old : resolveLocalExpression? table source with
  | none =>
      cases extended : resolveLocalExpression? ((name, id) :: table) source with
      | none => rfl
      | some resolved =>
          have accepted := (avoids.resolves_cons_iff.mp (resolveLocalExpression?_sound extended)).complete
          rw [old] at accepted
          cases accepted
  | some resolved =>
      exact (avoids.resolves_cons_iff.mpr (resolveLocalExpression?_sound old)).complete

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalNameRenaming`
-/

/-! Relabel only the IDs in an explicit ordered name table. Spellings, row
order, and first-name-match behavior are unchanged, even for noninjective maps.
This is not source spelling renaming or a fresh-identity allocation policy. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalNameTable

def mapIds (mapping : Resolved.LocalId → Resolved.LocalId) (table : LocalNameTable) :
    LocalNameTable :=
  table.map (fun entry => (entry.1, mapping entry.2))

@[simp] theorem mapIds_id (table : LocalNameTable) : mapIds id table = table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, id⟩
      simp only [mapIds, List.map_cons] at ih ⊢
      exact congrArg (List.cons (name, id)) ih

theorem mapIds_comp (table : LocalNameTable)
    (first second : Resolved.LocalId → Resolved.LocalId) :
    mapIds second (mapIds first table) = mapIds (second ∘ first) table := by
  simp only [mapIds, List.map_map, Function.comp_def]

/-- Name lookup selects the same row; no injectivity premise is necessary. -/
theorem lookup?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (table : LocalNameTable) (spelling : String) :
    lookup? (mapIds mapping table) spelling = (lookup? table spelling).map mapping := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, id⟩
      by_cases same : candidate = spelling
      · simp only [mapIds, List.map_cons, lookup?, if_pos same, Option.map_some]
      · simpa only [mapIds, List.map_cons, lookup?, if_neg same] using ih

theorem lookup_mapIds_iff_exists (mapping : Resolved.LocalId → Resolved.LocalId)
    {table : LocalNameTable} {spelling : String} {renamed : Resolved.LocalId} :
    Lookup (mapIds mapping table) spelling renamed ↔
      ∃ original, Lookup table spelling original ∧ mapping original = renamed := by
  simp only [← lookup?_iff, lookup?_mapIds, Option.map_eq_some_iff]

theorem lookup_mapIds_iff (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping)
    {table : LocalNameTable} {spelling : String} {id : Resolved.LocalId} :
    Lookup (mapIds mapping table) spelling (mapping id) ↔ Lookup table spelling id := by
  rw [lookup_mapIds_iff_exists]
  constructor
  · rintro ⟨original, found, same⟩
    cases injective same
    exact found
  · intro found
    exact ⟨id, found, rfl⟩

end Solcore.Frontend.LocalNameTable
