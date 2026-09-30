import Solcore.SourceSemantics.CoreLowering.DataPatternLeaves

/-! Pure Core execution lemmas for the generated pattern combinators. These
composition facts are discharged structurally by the pattern certificate;
they do not introduce another executable pattern interpreter. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternExecution
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataEquality

theorem ListRel.append {α β : Type} {relation : α → β → Prop}
    {a c : List α} {b d : List β} (left : ListRel relation a b) (right : ListRel relation c d) :
    ListRel relation (a ++ c) (b ++ d) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem ListRel.map {α β : Type} {relation other : α → β → Prop}
    {a : List α} {b : List β} (related : ListRel relation a b)
    (transform : ∀ x y, relation x y → other x y) : ListRel other a b := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (transform _ _ head) ih

theorem ListRel.of_lookup {α β : Type} {relation : α → β → Prop} {a : List α} {b : List β}
    (length : a.length = b.length)
    (related : ∀ (index : Nat) x y, a[index]? = some x → b[index]? = some y → relation x y) :
    ListRel relation a b := by
  induction a generalizing b with
  | nil =>
    have empty : b = [] := by simpa using length.symm
    subst b; exact .nil
  | cons first rest ih =>
    cases b with
    | nil => simp at length
    | cons second tail =>
      refine .cons (related 0 first second rfl rfl) (ih (Nat.succ.inj length) ?_)
      intro index x y left right
      exact related (index + 1) x y left right

theorem projectionList_selects {environment : Environment} {expression : Expr}
    {types : List Ty} {values : List Value}
    (selected : Selects environment expression (packValues values)) (length : types.length = values.length) :
    ListRel (Selects environment)
      (types.zipIdx.map fun (_, index) => SourceCoreDataExpressions.projectPacked index types expression) values := by
  apply ListRel.of_lookup (by simpa using length)
  intro index projected value left right
  simp only [List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add, Option.map_map] at left
  cases found : types[index]? with
  | none => simp [found] at left
  | some type =>
    simp [found] at left
    subst projected
    exact projectPacked_selects selected length index right

theorem BindingsRep.length {catalog : SourceCoreDataCatalog.Catalog}
    {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog binders sources values) : binders.length = values.length := by
  induction represented with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem BindingsRep.append {catalog : SourceCoreDataCatalog.Catalog}
    {a c : List (TypedBinder × Ty)} {b d : List (TypedBinder × Dynamic.Value)} {v w : List Value}
    (left : BindingsRep catalog a b v) (right : BindingsRep catalog c d w) :
    BindingsRep catalog (a ++ c) (b ++ d) (v ++ w) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

/-- The same closed matcher can be applied in any surrounding environment;
the input expression is a pure projection path. -/
def MatcherRuns (pattern : Pattern) (input : Value) (bindings : List Value) : Prop :=
  ∀ environment store expression, Selects environment expression input →
    Evaluates environment store (.apply pattern.matcher expression)
      (.inRight .unit (packValues bindings)) store

/-- A child vector extends an already selected binding accumulated in source order. -/
def ChildrenRun (patterns : List Pattern) (inputs bindings : List Value) : Prop :=
  ∀ environment store expressions accumulated accumulatedValues outputType,
    ListRel (Selects environment) expressions inputs →
    ListRel (Selects environment) accumulated accumulatedValues →
    Evaluates environment store (matchChildren outputType patterns expressions accumulated)
      (.inRight .unit (packValues (accumulatedValues ++ bindings))) store

theorem ChildrenRun.nil : ChildrenRun [] [] [] := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected
  simpa [matchChildren] using Evaluates.inRight
    (leftType := Ty.unit) (bundle_evaluates (ListRel.map previous fun _ _ path => path.evaluates store))

theorem ChildrenRun.cons {pattern : Pattern} {patterns : List Pattern} {input : Value}
    {inputs headBindings tailBindings : List Value}
    (length : pattern.bindingTypes.length = headBindings.length)
    (head : MatcherRuns pattern input headBindings) (tail : ChildrenRun patterns inputs tailBindings) :
    ChildrenRun (pattern :: patterns) (input :: inputs) (headBindings ++ tailBindings) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected =>
    apply Evaluates.caseRight (head environment store _ inputSelected)
    have projections := projectionList_selects (environment := packValues headBindings :: environment)
      (expression := .var 0) (types := pattern.bindingTypes) (values := headBindings) (.var rfl) length
    have result := tail (packValues headBindings :: environment) store _ _ _ outputType
      (selects_weaken_list restSelected _) (ListRel.append (selects_weaken_list previous _) projections)
    simpa [List.append_assoc] using result

theorem ValueRep.unpack {catalog : SourceCoreDataCatalog.Catalog}
    {sources : List Dynamic.Value} {source : Dynamic.Value} {value : Value}
    (packing : Dynamic.ValuesPack sources source) (represented : ValueRep catalog source value) :
    ∃ values, ValuesRep catalog sources values ∧ value = packValues values := by
  induction packing generalizing value with
  | nil => cases represented; exact ⟨[], .nil, rfl⟩
  | singleton source => exact ⟨[value], .cons represented .nil, rfl⟩
  | @cons first second rest packed tail ih =>
    cases represented with
    | product left right =>
      obtain ⟨values, represented, same⟩ := ih right
      cases values with
      | nil => have length := represented.length; simp at length
      | cons next values =>
        refine ⟨_ :: next :: values, .cons left represented, ?_⟩
        simp only [packValues]
        rw [same]

end Solcore.SourceSemantics.CoreLowering.DataPatternExecution
