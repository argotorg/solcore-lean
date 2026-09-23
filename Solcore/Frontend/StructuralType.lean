import Solcore.Frontend.TypeName

/-! Structural type meanings over original canonical syntax, shared by entry annotations.
The separate named-only interpreter and its whole-result membership law stay unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Exact named leaves, Unit, singleton identity, right-associated products and unary
function annotations. Original child nesting and source parameter arity are retained. -/
def interpretStructuralType? (table : TypeNameTable) (source : Syntax.TypeExpr) : Option Core.Ty :=
  match source with
  | ⟨_, .named name none⟩ => table.lookup? (qualifiedTypeNameKey name)
  | ⟨_, .tuple []⟩ => some .unit
  | ⟨_, .tuple [child]⟩ => interpretStructuralType? table child
  | ⟨_, .tuple [left, right]⟩ => do
      let first ← interpretStructuralType? table left
      let second ← interpretStructuralType? table right
      return .product first second
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ => do
      let headType ← interpretStructuralType? table first
      let tailType ← interpretStructuralType? table ⟨span, .tuple (second :: third :: rest)⟩
      return .product headType tailType
  | ⟨_, .function _ ⟨_, [parameter]⟩ none⟩ => do
      let parameterType ← interpretStructuralType? table parameter
      return .function parameterType .unit
  | ⟨_, .function _ ⟨_, [parameter]⟩ (some ⟨returnsSpan, results⟩)⟩ => do
      let parameterType ← interpretStructuralType? table parameter
      let returnType ← interpretStructuralType? table ⟨returnsSpan, .tuple results⟩
      return .function parameterType returnType
  | _ => none
termination_by sizeOf source

/-- Source meaning is specified independently of the executable interpreter.
Every child keeps the same table, including duplicate first-match priorities. -/
inductive StructuralTypeDenotes (table : TypeNameTable) : Syntax.TypeExpr → Core.Ty → Prop where
  | named {span : Syntax.SourceSpan} {name : Syntax.QualifiedName} {type : Core.Ty}
      (found : TypeNameTable.Lookup table (qualifiedTypeNameKey name) type) :
      StructuralTypeDenotes table ⟨span, .named name none⟩ type
  | unit {span : Syntax.SourceSpan} : StructuralTypeDenotes table ⟨span, .tuple []⟩ .unit
  | single {span : Syntax.SourceSpan} {child : Syntax.TypeExpr} {type : Core.Ty}
      (meaning : StructuralTypeDenotes table child type) :
      StructuralTypeDenotes table ⟨span, .tuple [child]⟩ type
  | pair {span : Syntax.SourceSpan} {left right : Syntax.TypeExpr} {leftType rightType : Core.Ty}
      (first : StructuralTypeDenotes table left leftType)
      (second : StructuralTypeDenotes table right rightType) :
      StructuralTypeDenotes table ⟨span, .tuple [left, right]⟩ (.product leftType rightType)
  | many {span : Syntax.SourceSpan} {first second third : Syntax.TypeExpr}
      {rest : List Syntax.TypeExpr} {firstType tailType : Core.Ty}
      (headMeaning : StructuralTypeDenotes table first firstType)
      (tailMeaning : StructuralTypeDenotes table ⟨span, .tuple (second :: third :: rest)⟩ tailType) :
      StructuralTypeDenotes table ⟨span, .tuple (first :: second :: third :: rest)⟩ (.product firstType tailType)
  | functionDefault {span keyword parametersSpan : Syntax.SourceSpan}
      {parameter : Syntax.TypeExpr} {parameterType : Core.Ty}
      (parameterMeaning : StructuralTypeDenotes table parameter parameterType) :
      StructuralTypeDenotes table ⟨span, .function keyword ⟨parametersSpan, [parameter]⟩ none⟩
        (.function parameterType .unit)
  | functionReturns {span keyword parametersSpan returnsSpan : Syntax.SourceSpan}
      {parameter : Syntax.TypeExpr} {results : List Syntax.TypeExpr} {parameterType returnType : Core.Ty}
      (parameterMeaning : StructuralTypeDenotes table parameter parameterType)
      (returnMeaning : StructuralTypeDenotes table ⟨returnsSpan, .tuple results⟩ returnType) :
      StructuralTypeDenotes table
        ⟨span, .function keyword ⟨parametersSpan, [parameter]⟩ (some ⟨returnsSpan, results⟩)⟩
        (.function parameterType returnType)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.StructuralTypeProperties`
-/

/-! Exact correspondence for the independent structural type fragment.
Named-only interpretation and its whole-result table membership law remain unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem StructuralTypeDenotes.complete {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (meaning : StructuralTypeDenotes table source type) :
    interpretStructuralType? table source = some type := by
  induction meaning with
  | named found =>
      simpa only [interpretStructuralType?] using TypeNameTable.lookup?_iff.mpr found
  | unit => simp only [interpretStructuralType?]
  | single _ ih => simpa only [interpretStructuralType?] using ih
  | pair _ _ leftIH rightIH =>
      simp only [interpretStructuralType?, leftIH, rightIH, bind, Option.bind_some, pure]
  | many _ _ headIH tailIH =>
      rw [interpretStructuralType?]
      simp only [headIH, tailIH, bind, Option.bind_some, pure]
  | functionDefault _ parameterIH =>
      simp only [interpretStructuralType?, parameterIH, bind, Option.bind_some, pure]
  | functionReturns _ _ parameterIH returnIH =>
      simp only [interpretStructuralType?, parameterIH, returnIH, bind, Option.bind_some, pure]

theorem interpretStructuralType?_sound {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (result : interpretStructuralType? table source = some type) :
    StructuralTypeDenotes table source type := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [interpretStructuralType?, reduceCtorEq] at result
      case named name arguments =>
        cases arguments with
        | none =>
            exact .named (TypeNameTable.lookup?_iff.mp
              (by simpa only [interpretStructuralType?] using result))
        | some arguments => simp only [interpretStructuralType?, reduceCtorEq] at result
      case function keyword parameters returns =>
        cases parameters with
        | mk parametersSpan parameters =>
          cases parameters with
          | nil => simp only [interpretStructuralType?, reduceCtorEq] at result
          | cons parameter rest =>
              cases rest with
              | cons next rest => simp only [interpretStructuralType?, reduceCtorEq] at result
              | nil =>
                  cases returns with
                  | none =>
                      simp only [interpretStructuralType?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq] at result
                      obtain ⟨parameterType, parameterResult, rfl⟩ := result
                      exact .functionDefault (interpretStructuralType?_sound parameterResult)
                  | some returns =>
                      cases returns with
                      | mk returnsSpan results =>
                        rw [interpretStructuralType?] at result
                        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at result
                        obtain ⟨parameterType, parameterResult, returnType, returnResult, rfl⟩ := result
                        exact .functionReturns (interpretStructuralType?_sound parameterResult)
                          (interpretStructuralType?_sound returnResult)
      case tuple elements =>
        cases elements with
        | nil =>
            simp only [interpretStructuralType?, Option.some.injEq] at result
            cases result
            exact .unit
        | cons left remaining =>
            cases remaining with
            | nil =>
                exact .single (interpretStructuralType?_sound
                  (by simpa only [interpretStructuralType?] using result))
            | cons right tail =>
                cases tail with
                | cons third rest =>
                    rw [interpretStructuralType?] at result
                    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at result
                    obtain ⟨firstType, firstResult, tailType, tailResult, rfl⟩ := result
                    exact .many (interpretStructuralType?_sound firstResult)
                      (interpretStructuralType?_sound tailResult)
                | nil =>
                    simp only [interpretStructuralType?, bind, Option.bind_eq_some_iff,
                      pure, Option.some.injEq] at result
                    obtain ⟨leftType, leftResult, rightType, rightResult, rfl⟩ := result
                    exact .pair (interpretStructuralType?_sound leftResult)
                      (interpretStructuralType?_sound rightResult)
termination_by sizeOf source

theorem interpretStructuralType?_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} :
    interpretStructuralType? table source = some type ↔ StructuralTypeDenotes table source type :=
  ⟨interpretStructuralType?_sound, StructuralTypeDenotes.complete⟩

theorem StructuralTypeDenotes.type_unique {table : TypeNameTable}
    {source : Syntax.TypeExpr} {left right : Core.Ty}
    (leftMeaning : StructuralTypeDenotes table source left)
    (rightMeaning : StructuralTypeDenotes table source right) : left = right :=
  Option.some.inj (leftMeaning.complete.symm.trans rightMeaning.complete)

theorem interpretStructuralType?_eq_none_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} :
    interpretStructuralType? table source = none ↔
      ¬ ∃ type, StructuralTypeDenotes table source type := by
  constructor
  · intro result ⟨type, meaning⟩
    have accepted := meaning.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : interpretStructuralType? table source with
    | none => rfl
    | some type => exact False.elim (absent ⟨type, interpretStructuralType?_sound result⟩)

/-- Only the outer occurrence range changes; recursive child ranges are untouched. -/
theorem interpretStructuralType?_span (table : TypeNameTable) (source : Syntax.TypeExpr)
    (span : Syntax.SourceSpan) :
    interpretStructuralType? table { source with span } = interpretStructuralType? table source := by
  cases source with
  | mk sourceSpan payload =>
      cases payload <;> try simp only [interpretStructuralType?]
      case named name arguments => cases arguments <;> simp only [interpretStructuralType?]
      case function keyword parameters returns =>
        rcases parameters with ⟨parametersSpan, parameters⟩
        cases parameters with
        | nil => simp only [interpretStructuralType?]
        | cons parameter rest =>
            cases rest with
            | cons next rest => simp only [interpretStructuralType?]
            | nil =>
                cases returns with
                | none => simp only [interpretStructuralType?]
                | some returns => cases returns; simp only [interpretStructuralType?]
      case tuple elements =>
        cases elements with
        | nil => simp only [interpretStructuralType?]
        | cons left remaining =>
            cases remaining with
            | nil => simp only [interpretStructuralType?]
            | cons right tail =>
                cases tail with
                | nil => simp only [interpretStructuralType?]
                | cons third rest =>
                    have tailSame := interpretStructuralType?_span table
                      ⟨sourceSpan, .tuple (right :: third :: rest)⟩ span
                    change interpretStructuralType? table ⟨span, .tuple (right :: third :: rest)⟩ =
                      interpretStructuralType? table ⟨sourceSpan, .tuple (right :: third :: rest)⟩ at tailSame
                    conv => lhs; rw [interpretStructuralType?]
                    conv => rhs; rw [interpretStructuralType?]
                    rw [tailSame]
termination_by sizeOf source

theorem TypeNameDenotes.structural {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes table source type) :
    StructuralTypeDenotes table source type := by
  cases meaning with
  | named found => exact .named found

theorem interpretStructuralType?_of_typeName {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretTypeName? table source = some type) :
    interpretStructuralType? table source = some type :=
  (interpretTypeName?_sound accepted).structural.complete

/-- Full optional-result agreement on the old named/no-arguments shape. -/
theorem interpretStructuralType?_named_eq_typeName (table : TypeNameTable)
    (name : Syntax.QualifiedName) (span : Syntax.SourceSpan) :
    interpretStructuralType? table ⟨span, .named name none⟩ =
      interpretTypeName? table ⟨span, .named name none⟩ := by
  simp only [interpretStructuralType?, interpretTypeName?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.StructuralTypeTableProperties`
-/

/-! Structural interpretation depends on first-match named-leaf meanings.
One-way extension preserves successful results; only lookup equality or mutual
extension preserves the entire optional result, including rejection. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem StructuralTypeDenotes.extend_types {old next : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : StructuralTypeDenotes old source type)
    (extension : TypeNameTable.Extends old next) : StructuralTypeDenotes next source type := by
  induction meaning with
  | named found => exact .named (extension found)
  | unit => exact .unit
  | single _ ih => exact .single ih
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | many _ _ headIH tailIH => exact .many headIH tailIH
  | functionDefault _ parameterIH => exact .functionDefault parameterIH
  | functionReturns _ _ parameterIH returnIH => exact .functionReturns parameterIH returnIH

theorem interpretStructuralType?_some_of_extends {old next : TypeNameTable}
    (extension : TypeNameTable.Extends old next) {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretStructuralType? old source = some type) :
    interpretStructuralType? next source = some type :=
  ((interpretStructuralType?_sound accepted).extend_types extension).complete

/-- Equality of every visible lookup, not row membership or uniqueness, is enough.
Hidden duplicate entries, table lengths and source occurrence ranges are unrestricted. -/
theorem interpretStructuralType?_congr_lookup (left right : TypeNameTable)
    (sameLookup : ∀ key, left.lookup? key = right.lookup? key) (source : Syntax.TypeExpr) :
    interpretStructuralType? left source = interpretStructuralType? right source := by
  have forward : TypeNameTable.Extends left right := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [← sameLookup key]
    exact TypeNameTable.lookup?_iff.mpr found
  have backward : TypeNameTable.Extends right left := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [sameLookup key]
    exact TypeNameTable.lookup?_iff.mpr found
  cases leftResult : interpretStructuralType? left source with
  | none =>
      cases rightResult : interpretStructuralType? right source with
      | none => rfl
      | some type =>
          have accepted := interpretStructuralType?_some_of_extends backward rightResult
          rw [leftResult] at accepted
          cases accepted
  | some type => exact (interpretStructuralType?_some_of_extends forward leftResult).symm

theorem interpretStructuralType?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : TypeNameTable.Extends left right) (backward : TypeNameTable.Extends right left)
    (source : Syntax.TypeExpr) : interpretStructuralType? left source = interpretStructuralType? right source :=
  interpretStructuralType?_congr_lookup left right
    (TypeNameTable.lookup?_eq_of_mutual_extends forward backward) source

end Solcore.Frontend
