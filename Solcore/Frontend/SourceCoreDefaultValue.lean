import Solcore.Frontend.SourceCoreDataEquality

/-! Optional source defaults, generated as ordinary Core values. Absence is
returned to the caller so its own language-failure policy remains explicit. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDefaultValue

open Core
abbrev Error := SourceCoreDataEquality.Error
abbrev Catalog := SourceCoreDataCatalog.Catalog

def defaultExpression (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty) :
    Except Error (Option Expr) :=
  match fuel with
  | 0 => throw .exhausted
  | fuel + 1 => match type with
    | .constructor (.builtin .unit) => pure (some .unit)
    | .constructor (.builtin .bool) => pure (some (.bool false))
    | .constructor (.builtin .word) => pure (some (.word Word.zero))
    | .constructor (.builtin .integer) => pure (some (.integer 0))
    | .product left right => do
        let left ← defaultExpression fuel catalog left
        let right ← defaultExpression fuel catalog right
        pure (do pure (.pair (← left) (← right)))
    | .proxy _ | .mapping _ _ =>
        match catalog.identity? type with
        | some id => pure (some (.construct ⟨id, 0⟩ .unit))
        | none => throw (.catalog (.missingRepresentation type))
    | .comptime inner => defaultExpression fuel catalog inner
    | _ => pure none

def wrap (type : Core.Ty) : Option Expr → Expr
  | none => .inLeft type .unit
  | some value => .inRight .unit value

structure Prepared (checked : SourceCoreDataCatalog.Checked) where
  sourceType : TypeSystem.Ty
  type : Core.Ty
  projection : checked.catalog.project sourceType = .ok type
  compilationFuel : Nat
  default : Option Expr
  generated : defaultExpression compilationFuel checked.catalog sourceType = .ok default
  expression : Expr
  expression_eq : expression = wrap type default
  typed : HasType [] expression (.sum .unit type) checked.catalog.definitions
  deriving Repr

def prepare (fuel : Nat) (checked : SourceCoreDataCatalog.Checked)
    (sourceType : TypeSystem.Ty) : Except Error (Prepared checked) := do
  match projected : checked.catalog.project sourceType with
  | .error error => throw (.catalog error)
  | .ok type =>
    match generated : defaultExpression fuel checked.catalog sourceType with
    | .error error => throw error
    | .ok default =>
      let expression := wrap type default
      if accepted : infer? [] expression checked.catalog.definitions = some (.sum .unit type) then
        pure {
          sourceType, type, projection := projected, compilationFuel := fuel,
          default, generated, expression, expression_eq := rfl, typed := infer_sound accepted
        }
      else throw (.checkFailed (.sum .unit type) (infer? [] expression checked.catalog.definitions))

end Solcore.Frontend.SourceCoreDefaultValue
