import Solcore.Frontend.SourceCoreCompatibleCatalog
import Solcore.Frontend.SourceCoreDataEquality

/-! Comparators for the separate source-compatible representation. Proxy
payloads and nominal payload prefixes retain raw metadata words. Mapping
values compare false, as do anonymous functions; named callable comparison
observes identity independently of its call descriptor.

Preparation uses general optional cells for mutually recursive comparators.
The native checker validates these actual compatible definitions. This module
makes no unconditional termination claim and does not reuse strict receipts. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCompatibleDataEquality
open Core
abbrev Catalog := SourceCoreCompatibleCatalog.Catalog
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev comparatorType := SourceCoreDataEquality.comparatorType

inductive Error where
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | exhausted
  | unsupportedCarrier (type : Core.Ty)
  | missingEntry (id : DataTypeId)
  | missingDefinition (id : DataTypeId)
  | checkFailed (expected : Core.Ty) (actual : Option Core.Ty)
  deriving Repr, DecidableEq

def referenceIndex (catalog : Catalog) (depth : Nat) (id : DataTypeId) : Nat :=
  depth + (catalog.entries.length - 1 - id.index)

/-- The mapping's public carrier contains its metadata and transported
default. Those fields do not make source mapping equality reflexive. -/
def isMappingCarrier (catalog : Catalog) (type : Core.Ty) : Bool :=
  match type with
  | .product .word (.product (.sum .unit _) (.namedData id)) =>
      match catalog.entries[id.index]? with
      | some entry => match entry.sourceType with
          | .mapping _ _ => match catalog.project entry.sourceType with
              | .ok projected => projected == type
              | .error _ => false
          | _ => false
      | none => false
  | _ => false

def compareType (fuel : Nat) (catalog : Catalog) (depth : Nat)
    (type : Core.Ty) (left right : Expr) : Except Error Expr :=
  match fuel with
  | 0 => throw .exhausted
  | fuel + 1 =>
    if isMappingCarrier catalog type then pure (.bool false)
    else match type with
    | .unit => pure (.bool true)
    | .bool => pure (.ifE left right (.unary .boolNot right))
    | .word => pure (.binary .wordEq left right)
    | .integer => pure (.binary .integerEq left right)
    | .product (.sum .unit .word) (.function _ (.sum .word _)) =>
        pure (SourceCoreDataEquality.functionEqual left right)
    | .product first second => do
        if catalog.callableContracts && SourceCoreDataEquality.isCallableContractType type then
          pure (SourceCoreDataEquality.functionEqual (.first left) (.first right))
        else
          pure (.ifE
            (← compareType fuel catalog depth first (.first left) (.first right))
            (← compareType fuel catalog depth second (.second left) (.second right))
            (.bool false))
    | .namedData id => do
        let entry ← match catalog.entries[id.index]? with
          | some entry => pure entry
          | none => throw (.missingEntry id)
        match entry.sourceType with
        | .mapping _ _ => pure (.bool false)
        | _ => pure (SourceCoreDataEquality.invoke (.var (referenceIndex catalog depth id)) left right)
    | _ => throw (.unsupportedCarrier type)

def nominalBody (fuel : Nat) (catalog : Catalog) (id : DataTypeId)
    (payloads : List Core.Ty) : Except Error Expr := do
  let branches ← payloads.zipIdx.mapM fun (payload, leftIndex) => do
    let inner ← payloads.zipIdx.mapM fun (_, rightIndex) => do
      if leftIndex = rightIndex then compareType fuel catalog 3 payload (.var 1) (.var 0)
      else pure (.bool false)
    pure (.matchData id .bool (.second (.var 1)) inner)
  pure (.matchData id .bool (.first (.var 0)) branches)

def helperBody (fuel : Nat) (catalog : Catalog) (id : DataTypeId) : Except Error Expr := do
  let entry ← match catalog.entries[id.index]? with
    | some entry => pure entry | none => throw (.missingEntry id)
  match entry.sourceType with
  | .mapping _ _ => pure (.bool false)
  | _ =>
      let definition ← match entry.definition with
        | some definition => pure definition | none => throw (.missingDefinition id)
      nominalBody fuel catalog id definition.constructorPayloadTypes

def allocate (catalog : Catalog) (next : Expr) : Expr :=
  (catalog.entries.zipIdx).foldr (fun (_, index) next =>
    .letE (OptionalCell.allocate (comparatorType (.namedData ⟨index⟩))) next) next

def install (catalog : Catalog) (bodies : List Expr) (next : Expr) : Expr :=
  (bodies.zipIdx).foldr (fun (body, index) next =>
    .letE (.storeCell (.var (referenceIndex catalog 0 ⟨index⟩))
      (.inRight .unit (.lambda (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool body)))
      (next.weakenAt 0)) next

def helperBodies (fuel : Nat) (catalog : Catalog) : Except Error (List Expr) :=
  catalog.entries.zipIdx.mapM fun (_, index) => helperBody fuel catalog ⟨index⟩

structure Prepared (checked : Checked) where
  sourceType : TypeSystem.Ty
  type : Core.Ty
  projection : checked.catalog.project sourceType = .ok type
  compilationFuel : Nat
  bodies : List Expr
  bodiesGenerated : helperBodies compilationFuel checked.catalog = .ok bodies
  body : Expr
  bodyGenerated : compareType compilationFuel checked.catalog 1 type (.first (.var 0)) (.second (.var 0)) = .ok body
  expression : Expr
  expression_eq : expression = allocate checked.catalog
    (install checked.catalog bodies (.lambda (.product type type) .bool body))
  typed : HasType [] expression (comparatorType type) checked.catalog.definitions

def prepare (fuel : Nat) (checked : Checked) (sourceType : TypeSystem.Ty) : Except Error (Prepared checked) := do
  match projected : checked.catalog.project sourceType with
  | .error error => throw (.catalog error)
  | .ok type =>
      match generated : helperBodies fuel checked.catalog with
      | .error error => throw error
      | .ok bodies =>
          match bodyGenerated : compareType fuel checked.catalog 1 type (.first (.var 0)) (.second (.var 0)) with
          | .error error => throw error
          | .ok body =>
              let expression := allocate checked.catalog (install checked.catalog bodies
                (.lambda (.product type type) .bool body))
              if accepted : infer? [] expression checked.catalog.definitions = some (comparatorType type) then
                pure ⟨sourceType, type, projected, fuel, bodies, generated, body, bodyGenerated,
                  expression, rfl, infer_sound accepted⟩
              else throw (.checkFailed (comparatorType type) (infer? [] expression checked.catalog.definitions))

end Solcore.Frontend.SourceCoreCompatibleDataEquality
