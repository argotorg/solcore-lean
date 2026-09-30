import Solcore.Frontend.SourceCoreDataCatalog
import Solcore.Core.OrderedMapping

/-! Equality is ordinary Core code. A preparation expression allocates all
catalog comparator cells once, installs mutually recursive closures, then
returns the requested comparator. Its invocation bodies contain no allocation
or write. Source metadata authenticity is a separate representation premise. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataEquality

open Core

inductive Error where
  | catalog (error : SourceCoreDataCatalog.Error)
  | exhausted
  | unsupportedCarrier (type : Core.Ty)
  | missingEntry (id : DataTypeId)
  | missingDefinition (id : DataTypeId)
  | checkFailed (expected : Core.Ty) (actual : Option Core.Ty)
  deriving Repr, DecidableEq

abbrev Catalog := SourceCoreDataCatalog.Catalog

def comparatorType (type : Core.Ty) : Core.Ty := .function (.product type type) .bool

def referenceIndex (catalog : Catalog) (depth : Nat) (id : DataTypeId) : Nat :=
  depth + (catalog.entries.length - 1 - id.index)

/-- The absent branch is unreachable after installation. It remains a total
ordinary sum elimination and introduces no language or machine failure. -/
def invoke (reference left right : Expr) : Expr :=
  .caseE (.loadCell reference) (.bool false)
    (.apply (.var 0) (.pair (left.weakenAt 0) (right.weakenAt 0)))

/-- Raw tagged-function equality; only the identity tags are observed. -/
def functionEqual (left right : Expr) : Expr :=
  .letE left (.letE (right.weakenAt 0) TaggedFunction.equalBody)

/-- The descriptor is a call contract, while source equality observes only
the tagged function's identity. This shape is special only in that profile. -/
def isCallableContractType : Core.Ty → Bool
  | .product (.product (.sum .unit .word) (.function _ (.sum .word _))) .word => true
  | _ => false

/-- Function patterns are selected according to the catalog profile. A source
product containing a function therefore retains its ordinary product fields. -/
def compareType (fuel : Nat) (catalog : Catalog) (depth : Nat)
    (type : Core.Ty) (left right : Expr) : Except Error Expr :=
  match fuel with
  | 0 => throw .exhausted
  | fuel + 1 => match type with
    | .unit => pure (.bool true)
    | .bool => pure (.ifE left right (.unary .boolNot right))
    | .word => pure (.binary .wordEq left right)
    | .integer => pure (.binary .integerEq left right)
    | .product (.sum .unit .word) (.function _ (.sum .word _)) =>
        pure (functionEqual left right)
    | .product first second => do
        if catalog.callableContracts && isCallableContractType type then
          pure (functionEqual (.first left) (.first right))
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
        | .proxy _ => pure (.bool true)
        | _ => pure (invoke (.var (referenceIndex catalog depth id)) left right)
    | _ => throw (.unsupportedCarrier type)

def nominalBody (fuel : Nat) (catalog : Catalog) (id : DataTypeId)
    (payloads : List Core.Ty) : Except Error Expr := do
  let branches ← payloads.zipIdx.mapM fun (payload, leftIndex) => do
    let inner ← payloads.zipIdx.mapM fun (_, rightIndex) => do
      if leftIndex = rightIndex then
        compareType fuel catalog 3 payload (.var 1) (.var 0)
      else pure (.bool false)
    pure (.matchData id .bool (.second (.var 1)) inner)
  pure (.matchData id .bool (.first (.var 0)) branches)

def helperBody (fuel : Nat) (catalog : Catalog) (id : DataTypeId) : Except Error Expr := do
  let entry ← match catalog.entries[id.index]? with
    | some entry => pure entry
    | none => throw (.missingEntry id)
  match entry.sourceType with
  | .mapping _ _ => pure (.bool false)
  | .proxy _ => pure (.bool true)
  | _ =>
    let definition ← match entry.definition with
      | some definition => pure definition
      | none => throw (.missingDefinition id)
    nominalBody fuel catalog id definition.constructorPayloadTypes

/-- Bodies are prepared in catalog order, while the captured cell environment
is newest first. A write's temporary Unit binder is removed by weakening the
remaining installation code. -/
def install (catalog : Catalog) (bodies : List Expr) (next : Expr) : Expr :=
  (bodies.zipIdx).foldr (fun (body, index) next =>
    .letE (.storeCell (.var (referenceIndex catalog 0 ⟨index⟩))
      (.inRight .unit (.lambda (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool body)))
      (next.weakenAt 0)) next

def allocate (catalog : Catalog) (next : Expr) : Expr :=
  (catalog.entries.zipIdx).foldr (fun (_, index) next =>
    .letE (OptionalCell.allocate (comparatorType (.namedData ⟨index⟩))) next) next

def helperBodies (fuel : Nat) (catalog : Catalog) : Except Error (List Expr) :=
  catalog.entries.zipIdx.mapM fun (_, index) => helperBody fuel catalog ⟨index⟩

structure Prepared (checked : SourceCoreDataCatalog.Checked) where
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
  deriving Repr

/-- All preparation effects precede every comparison, including comparisons
performed later by OrderedMapping in an extended store. -/
def prepare (fuel : Nat) (checked : SourceCoreDataCatalog.Checked)
    (sourceType : TypeSystem.Ty) : Except Error (Prepared checked) := do
  match projected : checked.catalog.project sourceType with
  | .error error => throw (.catalog error)
  | .ok type =>
    match bodiesGenerated : helperBodies fuel checked.catalog with
    | .error error => throw error
    | .ok bodies =>
      match bodyGenerated : compareType fuel checked.catalog 1 type (.first (.var 0)) (.second (.var 0)) with
      | .error error => throw error
      | .ok body =>
        let expression := allocate checked.catalog
          (install checked.catalog bodies (.lambda (.product type type) .bool body))
        if accepted : infer? [] expression checked.catalog.definitions = some (comparatorType type) then
          pure {
            sourceType, type, projection := projected, compilationFuel := fuel, bodies,
            bodiesGenerated, body, bodyGenerated, expression, expression_eq := rfl, typed := infer_sound accepted
          }
        else throw (.checkFailed (comparatorType type) (infer? [] expression checked.catalog.definitions))

/- Syntactic read-only audit. This does not imply termination: the finite
comparison theorem additionally follows the related values' constructor tree. -/
mutual
  def ReadOnly : Expr → Prop
    | .newCell _ _ | .storeCell _ _ => False
    | .pair a b | .apply a b | .binary _ a b | .letE a b => ReadOnly a ∧ ReadOnly b
    | .first a | .second a | .lambda _ _ a | .inLeft _ a | .inRight _ a
    | .loadCell a | .construct _ a | .unary _ a => ReadOnly a
    | .caseE a b c | .ternary _ a b c | .ifE a b c => ReadOnly a ∧ ReadOnly b ∧ ReadOnly c
    | .matchData _ _ a branches => ReadOnly a ∧ ReadOnlyList branches
    | _ => True
  def ReadOnlyList : List Expr → Prop
    | [] => True
    | x :: xs => ReadOnly x ∧ ReadOnlyList xs
end

end Solcore.Frontend.SourceCoreDataEquality
