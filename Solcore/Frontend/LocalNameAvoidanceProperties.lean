import Solcore.Frontend.LocalNameAvoidance
import Solcore.Frontend.LocalExpressionResolutionProperties

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
