import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Source.ScalarMeaning.Internal.Renderer

/-!
# Mutation proofs

The private-mutation renderer, with its store-aware invariant.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.MutationSpec
/-! The simulation invariant for the private-mutation renderer. Core keeps each
mutable Word local in its store and binds a cell reference; the source keeps
it in an ordinary local named `sc_c<n>` that assignments update. Word and
Boolean bindings are immutable, and Unit bindings have no source name. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Source.MutationRenderer (Binding)

abbrev MTarget := Solcore.Synthesis.Core.LocalMutation.Target
abbrev MRendered := Solcore.Synthesis.Source.MutationRenderer.Rendered

/-- The renderer's cell names `sc_c0`, `sc_c1`, ... -/
def cellTemp (index : Nat) : String := "sc_c" ++ toString index

theorem cellTemp_injective {first second : Nat}
    (same : cellTemp first = cellTemp second) : first = second := by
  have chars := congrArg String.toList same
  simp only [cellTemp, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr,
    List.append_cancel_left_eq] at chars
  have values := congrArg (fun digits => Nat.ofDigitChars 10 digits 0) chars
  simpa using values

theorem cellTemp_ne_temporary (first second : Nat) : cellTemp first ≠ temporary second := by
  intro same
  have chars := congrArg String.toList same
  simp [cellTemp, temporary] at chars

/-- The source name of a binding; Unit bindings have none. -/
def bindingName? : Binding → Option String
  | .word name => some name
  | .bool name => some name
  | .cellWord name => some name
  | .unit => none

/-- The source name of the binding at `index`, if any. -/
def nameAt (bindings : List Binding) (index : Nat) : Option String :=
  (bindings[index]?).bind bindingName?

/-- `name` is no value or cell temporary numbered `next` or later. -/
def FreshBefore (next : Nat) (name : String) : Prop :=
  ∀ index, (name = temporary index ∨ name = cellTemp index) → index < next

/-- `name` is a value or cell temporary numbered in `[first, last)`. -/
def TempIn (first last : Nat) (name : String) : Prop :=
  ∃ index, (name = temporary index ∨ name = cellTemp index) ∧ first ≤ index ∧ index < last

/-- Every named binding is older than `first`. -/
def NamesFresh (bindings : List Binding) (first : Nat) : Prop :=
  ∀ index name, nameAt bindings index = some name → FreshBefore first name

/-- Distinct bindings have distinct source names. -/
def NamesDistinct (bindings : List Binding) : Prop :=
  ∀ first second name, nameAt bindings first = some name → nameAt bindings second = some name →
    first = second

/-- How the Core value of a binding is held in the source frames and the
Core store. -/
def BindingHolds (frames : Frames) (store : Solcore.Core.Store) : Binding → CoreValue → Prop
  | .word name, core =>
      ∃ word : Solcore.Core.Word, core = .word word ∧ frames.lookup name = some (.word word.val)
  | .bool name, core => ∃ flag : Bool, core = .bool flag ∧ frames.lookup name = some (.bool flag)
  | .unit, core => core = .unit
  | .cellWord name, core =>
      ∃ (elementType : Solcore.Core.Ty) (location : Nat) (word : Solcore.Core.Word),
        core = .cellRef elementType location ∧ store.read? location = some (.word word) ∧
        frames.lookup name = some (.word word.val)

/-- Core's de Bruijn environment, the Core store and the source frames agree on
every binding, nearest first. -/
def BindingsAgree (frames : Frames) (bindings : List Binding)
    (environment : Solcore.Core.Environment) (store : Solcore.Core.Store) : Prop :=
  ∀ (index : Nat) (binding : Binding), bindings[index]? = some binding →
    ∃ core, environment[index]? = some core ∧ BindingHolds frames store binding core

/-- The binding at `index` is a cell at `location`. -/
def CellAt (bindings : List Binding) (environment : Solcore.Core.Environment)
    (index location : Nat) : Prop :=
  (∃ name, bindings[index]? = some (Binding.cellWord name)) ∧
    ∃ elementType, environment[index]? = some (.cellRef elementType location)

/-- Distinct cell bindings hold distinct store locations. -/
def CellsDistinct (bindings : List Binding) (environment : Solcore.Core.Environment) : Prop :=
  ∀ first second location, CellAt bindings environment first location →
    CellAt bindings environment second location → first = second

/-- Evaluation may append cells and write the cells of the bindings; every other
existing location keeps its value. -/
def StoreFrame (bindings : List Binding) (environment : Solcore.Core.Environment)
    (store store' : Solcore.Core.Store) : Prop :=
  store.length ≤ store'.length ∧ ∀ location, location < store.length →
    (∀ index, ¬ CellAt bindings environment index location) →
    store'.read? location = store.read? location

/-- Representation of a Core value of a mutation target by the value a source
name holds; Unit needs no source value. -/
def MRepresents : MTarget → CoreValue → Option Value → Prop
  | .word, core, source =>
      ∃ word : Solcore.Core.Word, core = .word word ∧ source = some (.word word.val)
  | .bool, core, source => ∃ flag : Bool, core = .bool flag ∧ source = some (.bool flag)
  | .unit, core, _ => core = .unit

/-- Each rendered helper name denotes the Word function of its Core closure. A
helper cannot reach the caller's cells, so its evaluation keeps every
existing store location. -/
def MFunctionsAgree (context : Context) (functions : List String)
    (closures : List CoreValue) : Prop :=
  ∀ (index : Nat) (name : String), functions[index]? = some name →
    ∃ (parameterType resultType : Solcore.Core.Ty) (body : Solcore.Core.Expr)
      (captured : Solcore.Core.Environment),
      closures[index]? = some (.closure parameterType resultType body captured) ∧
      ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
        ∃ (result : Solcore.Core.Word) (store' : Solcore.Core.Store),
          Solcore.Core.Evaluates (.word argument :: captured) store body (.word result) store' ∧
          store.length ≤ store'.length ∧
          (∀ location, location < store.length → store'.read? location = store.read? location) ∧
          context.call name [.word argument.val] = some (.word result.val)

/-- Executing `statements` from frames that agree with a Core environment and
store evaluates `expression` there. Afterwards the bindings still agree with the
final store, only cells of the bindings and new locations of the store differ,
and only temporaries in `[first, last)` and the cells of the bindings change in
the frames. -/
def MSimulates (admits : Context → Prop) (expression : CoreExpr) (target : MTarget)
    (functions : List String) (bindings : List Binding) (first last : Nat)
    (statements : List Stmt) (valueName : Option String) : Prop :=
  ∀ (context : Context) (environment : Solcore.Core.Environment)
    (store : Solcore.Core.Store) (scope : Scope) (outer : Frames),
    admits context →
    BindingsAgree (scope :: outer) bindings environment store →
    CellsDistinct bindings environment →
    bindings.length ≤ environment.length →
    MFunctionsAgree context functions (environment.drop bindings.length) →
    ∃ (coreValue : CoreValue) (store' : Solcore.Core.Store) (scope' : Scope) (outer' : Frames)
      (added : List String),
      Solcore.Core.Evaluates environment store expression.toCore coreValue store' ∧
      MRepresents target coreValue (valueName.bind (Frames.lookup (scope' :: outer'))) ∧
      Stmt.execList context (scope :: outer) statements = some (scope' :: outer') ∧
      BindingsAgree (scope' :: outer') bindings environment store' ∧
      StoreFrame bindings environment store store' ∧
      (∀ name, ¬ TempIn first last name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name = Frames.lookup (scope :: outer) name) ∧
      Frames.shape outer' = Frames.shape outer ∧
      scope'.names = added ++ scope.names ∧
      (∀ name ∈ added, TempIn first last name)

/-- A value name is a Word or Boolean binding or a value temporary in range,
never a cell. -/
def ValueName (bindings : List Binding) (first last : Nat) (name : String) : Prop :=
  (∃ index : Nat, bindings[index]? = some (Binding.word name) ∨
      bindings[index]? = some (Binding.bool name)) ∨
    ∃ index, name = temporary index ∧ first ≤ index ∧ index < last

/-- What the mutation renderer establishes for one rendered expression. -/
def MRenderSpec (admits : Context → Prop) (expression : CoreExpr) (target : MTarget)
    (functions : List String) (bindings : List Binding) (indent first : Nat)
    (rendered : MRendered) : Prop :=
  ∃ statements : List Stmt,
    rendered.lines = Stmt.listLines indent statements ∧
    first ≤ rendered.nextId ∧
    (∀ name, rendered.value = some name → ValueName bindings first rendered.nextId name) ∧
    (∀ name ∈ Stmt.listIdentifiers statements,
      (∃ index, nameAt bindings index = some name) ∨ name ∈ functions ∨
        TempIn first rendered.nextId name) ∧
    MSimulates admits expression target functions bindings first rendered.nextId statements
      rendered.value

def MRenderIH (admits : Context → Prop) (expression : CoreExpr) : Prop :=
  ∀ (functions : List String) (target : MTarget) (bindings : List Binding) (indent first : Nat)
    (rendered : MRendered),
    Solcore.Synthesis.Core.LocalMutation.initializerKind? (bindings.map Binding.kind)
      functions.length expression = some target.toLocal →
    MutationRenderer.render functions target bindings indent first expression = .ok rendered →
    NamesFresh bindings first →
    NamesDistinct bindings →
    MRenderSpec admits expression target functions bindings indent first rendered

/-! ### Names and temporaries -/

theorem tempIn_temporary {first last index : Nat} (low : first ≤ index) (high : index < last) :
    TempIn first last (temporary index) :=
  ⟨index, Or.inl rfl, low, high⟩

theorem tempIn_cellTemp {first last index : Nat} (low : first ≤ index) (high : index < last) :
    TempIn first last (cellTemp index) :=
  ⟨index, Or.inr rfl, low, high⟩

theorem tempIn_mono {first last first' last' : Nat} {name : String}
    (temp : TempIn first last name) (low : first' ≤ first) (high : last ≤ last') :
    TempIn first' last' name := by
  obtain ⟨index, same, lower, upper⟩ := temp
  exact ⟨index, same, by omega, by omega⟩

theorem temp_index_eq {first second : Nat} {name : String}
    (one : name = temporary first ∨ name = cellTemp first)
    (two : name = temporary second ∨ name = cellTemp second) : first = second := by
  rcases one with rfl | rfl <;> rcases two with same | same
  · exact temporary_injective same
  · exact absurd same.symm (cellTemp_ne_temporary _ _)
  · exact absurd same (cellTemp_ne_temporary _ _)
  · exact cellTemp_injective same

/-- A temporary in one range is not in a disjoint range. -/
theorem not_tempIn_of_tempIn {first last first' last' : Nat} {name : String}
    (temp : TempIn first last name) (disjoint : last ≤ first' ∨ last' ≤ first) :
    ¬ TempIn first' last' name := by
  rintro ⟨index', same', lower', upper'⟩
  obtain ⟨index, same, lower, upper⟩ := temp
  have := temp_index_eq same same'
  omega

theorem not_tempIn_of_fresh {next first last : Nat} {name : String}
    (fresh : FreshBefore next name) (le : next ≤ first) : ¬ TempIn first last name := by
  rintro ⟨index, same, lower, _⟩
  have := fresh index same
  omega

theorem freshBefore_mono {first second : Nat} {name : String}
    (fresh : FreshBefore first name) (le : first ≤ second) : FreshBefore second name :=
  fun index same => Nat.lt_of_lt_of_le (fresh index same) le

theorem NamesFresh.mono {bindings : List Binding} {first second : Nat}
    (fresh : NamesFresh bindings first) (le : first ≤ second) : NamesFresh bindings second :=
  fun index name found => freshBefore_mono (fresh index name found) le

theorem NamesFresh.ne_temporary {bindings : List Binding} {first index : Nat} {name : String}
    {position : Nat} (fresh : NamesFresh bindings first)
    (found : nameAt bindings position = some name) (le : first ≤ index) :
    name ≠ temporary index := by
  intro same
  have := fresh position name found index (Or.inl same)
  omega

theorem NamesFresh.ne_cellTemp {bindings : List Binding} {first index : Nat} {name : String}
    {position : Nat} (fresh : NamesFresh bindings first)
    (found : nameAt bindings position = some name) (le : first ≤ index) :
    name ≠ cellTemp index := by
  intro same
  have := fresh position name found index (Or.inr same)
  omega

theorem nameAt_cons_zero (binding : Binding) (bindings : List Binding) :
    nameAt (binding :: bindings) 0 = bindingName? binding := by
  simp [nameAt]

theorem nameAt_cons_succ (binding : Binding) (bindings : List Binding) (index : Nat) :
    nameAt (binding :: bindings) (index + 1) = nameAt bindings index := by
  simp [nameAt]

theorem nameAt_of_getElem? {bindings : List Binding} {index : Nat} {binding : Binding}
    (found : bindings[index]? = some binding) : nameAt bindings index = bindingName? binding := by
  simp [nameAt, found]

/-- Adding a binding named by a fresh temporary keeps the names fresh and
distinct. -/
theorem NamesFresh.cons {bindings : List Binding} {first next : Nat} {binding : Binding}
    (fresh : NamesFresh bindings first) (le : first ≤ next)
    (named : ∀ name, bindingName? binding = some name → FreshBefore next name) :
    NamesFresh (binding :: bindings) next := by
  intro index name found
  cases index with
  | zero =>
      rw [nameAt_cons_zero] at found
      exact named name found
  | succ index =>
      rw [nameAt_cons_succ] at found
      exact freshBefore_mono (fresh index name found) le

theorem NamesDistinct.cons {bindings : List Binding} {first : Nat} {binding : Binding}
    (distinct : NamesDistinct bindings) (fresh : NamesFresh bindings first)
    (named : ∀ name, bindingName? binding = some name → ∃ index,
      (name = temporary index ∨ name = cellTemp index) ∧ first ≤ index) :
    NamesDistinct (binding :: bindings) := by
  have newName : ∀ index name, nameAt bindings index = some name →
      bindingName? binding = some name → False := by
    intro index name found same
    obtain ⟨position, isTemp, le⟩ := named name same
    have := fresh index name found position isTemp
    omega
  intro first' second' name one two
  cases first' with
  | zero =>
      cases second' with
      | zero => rfl
      | succ second' =>
          rw [nameAt_cons_zero] at one
          rw [nameAt_cons_succ] at two
          exact (newName second' name two one).elim
  | succ first' =>
      cases second' with
      | zero =>
          rw [nameAt_cons_succ] at one
          rw [nameAt_cons_zero] at two
          exact (newName first' name one two).elim
      | succ second' =>
          rw [nameAt_cons_succ] at one two
          exact congrArg (· + 1) (distinct first' second' name one two)

/-! ### Agreement of bindings -/

/-- Agreement carries over when every binding name keeps its lookup and every
cell keeps its stored Word. -/
theorem BindingsAgree.transfer {frames frames' : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store store' : Solcore.Core.Store}
    (agree : BindingsAgree frames bindings environment store)
    (sameNames : ∀ index name, nameAt bindings index = some name →
      frames'.lookup name = frames.lookup name)
    (sameCells : ∀ index location, CellAt bindings environment index location →
      store'.read? location = store.read? location) :
    BindingsAgree frames' bindings environment store' := by
  intro index binding found
  obtain ⟨core, inEnvironment, holds⟩ := agree index binding found
  refine ⟨core, inEnvironment, ?_⟩
  have named := nameAt_of_getElem? found
  cases binding with
  | word name =>
      obtain ⟨word, rfl, lookup⟩ := holds
      exact ⟨word, rfl, by rw [sameNames index name named]; exact lookup⟩
  | bool name =>
      obtain ⟨flag, rfl, lookup⟩ := holds
      exact ⟨flag, rfl, by rw [sameNames index name named]; exact lookup⟩
  | unit => exact holds
  | cellWord name =>
      obtain ⟨elementType, location, word, rfl, read, lookup⟩ := holds
      refine ⟨elementType, location, word, rfl, ?_, ?_⟩
      · rw [sameCells index location ⟨⟨name, found⟩, elementType, inEnvironment⟩]
        exact read
      · rw [sameNames index name named]
        exact lookup

theorem BindingsAgree.tail {frames : Frames} {binding : Binding} {bindings : List Binding}
    {core : CoreValue} {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : BindingsAgree frames (binding :: bindings) (core :: environment) store) :
    BindingsAgree frames bindings environment store := by
  intro index found inBindings
  obtain ⟨value, inEnvironment, holds⟩ := agree (index + 1) found (by simpa using inBindings)
  exact ⟨value, by simpa using inEnvironment, holds⟩

theorem BindingsAgree.cons {frames : Frames} {binding : Binding} {bindings : List Binding}
    {core : CoreValue} {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : BindingsAgree frames bindings environment store)
    (holds : BindingHolds frames store binding core) :
    BindingsAgree frames (binding :: bindings) (core :: environment) store := by
  intro index found inBindings
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at inBindings
      subst inBindings
      exact ⟨core, rfl, holds⟩
  | succ index =>
      obtain ⟨value, inEnvironment, holdsRest⟩ := agree index found (by simpa using inBindings)
      exact ⟨value, by simpa using inEnvironment, holdsRest⟩

theorem CellAt.cons {bindings : List Binding} {environment : Solcore.Core.Environment}
    {binding : Binding} {core : CoreValue} {index location : Nat}
    (cell : CellAt bindings environment index location) :
    CellAt (binding :: bindings) (core :: environment) (index + 1) location := by
  obtain ⟨⟨name, found⟩, elementType, inEnvironment⟩ := cell
  exact ⟨⟨name, by simpa using found⟩, elementType, by simpa using inEnvironment⟩

theorem CellAt.of_cons {bindings : List Binding} {environment : Solcore.Core.Environment}
    {binding : Binding} {core : CoreValue} {index location : Nat}
    (cell : CellAt (binding :: bindings) (core :: environment) (index + 1) location) :
    CellAt bindings environment index location := by
  obtain ⟨⟨name, found⟩, elementType, inEnvironment⟩ := cell
  exact ⟨⟨name, by simpa using found⟩, elementType, by simpa using inEnvironment⟩

/-- Every cell of agreeing bindings is a location of the store. -/
theorem BindingsAgree.cell_lt {frames : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : BindingsAgree frames bindings environment store) {index location : Nat}
    (cell : CellAt bindings environment index location) : location < store.length := by
  obtain ⟨⟨name, found⟩, elementType, inEnvironment⟩ := cell
  obtain ⟨core, inEnvironment', holds⟩ := agree index _ found
  rw [inEnvironment] at inEnvironment'
  cases inEnvironment'
  obtain ⟨_, location', word, same, read, _⟩ := holds
  cases same
  simp only [Solcore.Core.Store.read?] at read
  exact (List.getElem?_eq_some_iff.mp read).1

theorem StoreFrame.refl (bindings : List Binding) (environment : Solcore.Core.Environment)
    (store : Solcore.Core.Store) : StoreFrame bindings environment store store :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem StoreFrame.trans {bindings : List Binding} {environment : Solcore.Core.Environment}
    {store store' store'' : Solcore.Core.Store}
    (first : StoreFrame bindings environment store store')
    (second : StoreFrame bindings environment store' store'') :
    StoreFrame bindings environment store store'' := by
  refine ⟨Nat.le_trans first.1 second.1, fun location inBounds notCell => ?_⟩
  rw [second.2 location (Nat.lt_of_lt_of_le inBounds first.1) notCell,
    first.2 location inBounds notCell]

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.MutationEquations
/-! Equations for the actual `MutationRenderer.render`, stated with the scalar
source syntax and printer, and inversions of the mutation profile's acceptance
check `initializerKind?`. Private helpers of the renderer and of the profile are
unfolded by definitional equality; nothing here re-implements them. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.MutationRenderer (Binding)
open Solcore.Synthesis.Core.LocalMutation (Local initializerKind? infer?)
/-- The source type of a scalar mutation target. -/
def MTarget.localType : MTarget → LocalType
  | .bool => .bool
  | _ => .word

/-- The scalar target of a Word or Boolean mutation target. -/
def MTarget.scalar : MTarget → Solcore.Synthesis.Core.Target
  | .bool => .bool
  | _ => .word

/-- The binding a Word or Boolean `let` introduces. -/
def letBinding : MTarget → String → Binding
  | .word, name => .word name
  | .bool, name => .bool name
  | .unit, _ => .unit

theorem requireValue_ok {rendered : MRendered} {value : String}
    (equation : MutationRenderer.requireValue rendered = .ok value) :
    rendered.value = some value := by
  unfold MutationRenderer.requireValue at equation
  cases found : rendered.value with
  | none =>
      rw [found] at equation
      cases equation
  | some value' =>
      rw [found] at equation
      cases equation
      rfl

theorem cellDecl_lines (indent : Nat) (name value : String) :
    [indentLine indent ("let " ++ name ++ ": word = " ++ value ++ ";")] =
      Stmt.lines indent (.letDecl name .word (.name value)) := by
  simp only [Stmt.lines, LocalType.spelling, Expr.print, List.cons.injEq, and_true]
  congr 1
  apply String.toList_inj.mp
  simp

/-- The scalar target of a mutation target, as the renderer computes it. -/
def MTarget.scalarExcept : MTarget → Except EmitError Solcore.Synthesis.Core.Target
  | .word => .ok .word
  | .bool => .ok .bool
  | .unit => .error (.unsupportedExpression "Unit used as a scalar target")

namespace MutationEquations

variable {functions : List String} {target : MTarget} {bindings : List Binding}
  {indent first : Nat} {rendered : MRendered}

theorem word (value : Solcore.Core.Word) :
    MutationRenderer.render functions target bindings indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        some (temporary first), first + 1⟩ := by
  simp only [MutationRenderer.render]
  rfl

theorem bool (value : Bool) :
    MutationRenderer.render functions target bindings indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        some (temporary first), first + 1⟩ := by
  simp only [MutationRenderer.render]
  rfl

theorem unit :
    MutationRenderer.render functions target bindings indent first .unit =
      .ok ⟨[], none, first⟩ := by
  simp only [MutationRenderer.render]

theorem var_ok {index : Nat}
    (equation : MutationRenderer.render functions target bindings indent first (.var index) =
      .ok rendered) :
    (∃ name, (bindings[index]? = some (Binding.word name) ∨
        bindings[index]? = some (Binding.bool name)) ∧ rendered = ⟨[], some name, first⟩) ∨
      (bindings[index]? = some Binding.unit ∧ rendered = ⟨[], none, first⟩) := by
  simp only [MutationRenderer.render] at equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      cases binding with
      | word name => exact Or.inl ⟨name, Or.inl rfl, (Except.ok.inj equation).symm⟩
      | bool name => exact Or.inl ⟨name, Or.inr rfl, (Except.ok.inj equation).symm⟩
      | unit => exact Or.inr ⟨rfl, (Except.ok.inj equation).symm⟩
      | cellWord name => cases equation

theorem newCellLet_ok {initializer body : CoreExpr}
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE (.newCell .word initializer) body) = .ok rendered) :
    ∃ initial value rest,
      MutationRenderer.render functions .word bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      MutationRenderer.render functions target (.cellWord (cellTemp initial.nextId) :: bindings)
        indent (initial.nextId + 1) body = .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (cellTemp initial.nextId) .word (.name value)) ++ rest.lines,
        rest.value, rest.nextId⟩ := by
  simp only [MutationRenderer.render] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨initial, value, rest, initialEquation, requireValue_ok valueEquation, restEquation, ?_⟩
  rw [← cellDecl_lines]
  exact (Except.ok.inj equation).symm

theorem letE_infer {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ kind, infer? (bindings.map Binding.kind) functions.length initializer = some kind := by
  rw [MutationRenderer.render.eq_6 _ _ _ _ _ _ _ notCell] at equation
  cases inferred : infer? (bindings.map Binding.kind) functions.length initializer with
  | none =>
      rw [inferred] at equation
      cases equation
  | some kind => exact ⟨kind, rfl⟩

theorem letE_unit_ok {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some .unit)
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial rest,
      MutationRenderer.render functions .unit bindings indent first initializer = .ok initial ∧
      MutationRenderer.render functions target (.unit :: bindings) indent initial.nextId body =
        .ok rest ∧
      rendered = ⟨initial.lines ++ rest.lines, rest.value, rest.nextId⟩ := by
  rw [MutationRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨initial, rest, initialEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem letE_value_ok {initializer body : CoreExpr} {kind : MTarget}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (scalarKind : kind = .word ∨ kind = .bool)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some kind)
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial value rest,
      MutationRenderer.render functions kind bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      MutationRenderer.render functions target (letBinding kind (temporary initial.nextId) ::
        bindings) indent (initial.nextId + 1) body = .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (temporary initial.nextId) kind.localType (.name value)) ++
        rest.lines, rest.value, rest.nextId⟩ := by
  rw [MutationRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  rcases scalarKind with rfl | rfl <;>
  · obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨initial, value, rest, initialEquation, requireValue_ok valueEquation, restEquation,
      (Except.ok.inj equation).symm⟩

theorem loadCell_ok {index : Nat}
    (equation : MutationRenderer.render functions target bindings indent first
      (.loadCell (.var index)) = .ok rendered) :
    ∃ name, bindings[index]? = some (Binding.cellWord name) ∧
      rendered = ⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
        some (temporary first), first + 1⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => Except.ok (⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
          some (temporary first), first + 1⟩ : MRendered)) = .ok rendered := equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some binding =>
      rw [found] at unfolded
      cases binding with
      | cellWord name => exact ⟨name, rfl, (Except.ok.inj unfolded).symm⟩
      | word name => cases unfolded
      | bool name => cases unfolded
      | unit => cases unfolded

theorem unary_ok {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp} {operand : CoreExpr}
    (selected : sourceUnary? op = some sourceOp)
    (equation : MutationRenderer.render functions target bindings indent first
      (.unary op operand) = .ok rendered) :
    ∃ operandRendered value scalarTarget,
      MutationRenderer.render functions (if op == .boolNot then .bool else .word) bindings indent
        first operand = .ok operandRendered ∧
      operandRendered.value = some value ∧ target.scalarExcept = .ok scalarTarget ∧
      rendered = ⟨operandRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary operandRendered.nextId) (LocalType.ofTarget scalarTarget)
          (.unary sourceOp (.name value))),
        some (temporary operandRendered.nextId), operandRendered.nextId + 1⟩ := by
  have unfolded : ((MutationRenderer.render functions (if op == .boolNot then (.bool : MTarget)
      else .word) bindings indent first operand).bind fun operandRendered =>
      (MutationRenderer.requireValue operandRendered).bind fun value =>
        (target.scalarExcept.bind fun scalarTarget =>
          (ScalarRenderer.render scalarTarget [value] indent operandRendered.nextId
            (.unary op (.var 0))).bind fun result =>
              Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
          fun result => Except.ok (⟨operandRendered.lines ++ result.lines, result.value,
            result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨operandRendered, operandEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨value, valueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨result, resultEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨scalarTarget, scalarEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨scalarResult, scalarResultEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.unary, selected] at scalarResultEquation
  obtain ⟨operandValue, operandValueEquation, scalarResultEquation⟩ :=
    except_bind_eq_ok scalarResultEquation
  rw [RendererEquations.var] at operandValueEquation
  simp only [List.getElem?_cons_zero] at operandValueEquation
  cases operandValueEquation
  cases scalarResultEquation
  cases resultEquation
  cases unfolded
  exact ⟨operandRendered, value, scalarTarget, operandEquation, requireValue_ok valueEquation,
    scalarEquation, rfl⟩

theorem storeCell_ok {index : Nat} {value : CoreExpr}
    (equation : MutationRenderer.render functions target bindings indent first
      (.storeCell (.var index) value) = .ok rendered) :
    ∃ name written result, bindings[index]? = some (Binding.cellWord name) ∧
      MutationRenderer.render functions .word bindings indent first value = .ok written ∧
      written.value = some result ∧
      rendered = ⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
        written.nextId⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => (MutationRenderer.render functions .word bindings indent first value).bind
          fun written => (MutationRenderer.requireValue written).bind fun result =>
            Except.ok (⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
              written.nextId⟩ : MRendered)) = .ok rendered := equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some binding =>
      rw [found] at unfolded
      cases binding with
      | cellWord name =>
          obtain ⟨name', nameEquation, unfolded⟩ := except_bind_eq_ok unfolded
          cases nameEquation
          obtain ⟨written, writtenEquation, unfolded⟩ := except_bind_eq_ok unfolded
          obtain ⟨result, resultEquation, unfolded⟩ := except_bind_eq_ok unfolded
          exact ⟨name, written, result, rfl, writtenEquation, requireValue_ok resultEquation,
            (Except.ok.inj unfolded).symm⟩
      | word name => cases unfolded
      | bool name => cases unfolded
      | unit => cases unfolded

theorem binary_ok {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp} {left right : CoreExpr}
    (selected : sourceBinary? op = some sourceOp)
    (equation : MutationRenderer.render functions target bindings indent first
      (.binary op left right) = .ok rendered) :
    ∃ leftRendered leftValue rightRendered rightValue scalarTarget,
      MutationRenderer.render functions .word bindings indent first left = .ok leftRendered ∧
      leftRendered.value = some leftValue ∧
      MutationRenderer.render functions .word bindings indent leftRendered.nextId right =
        .ok rightRendered ∧
      rightRendered.value = some rightValue ∧ target.scalarExcept = .ok scalarTarget ∧
      rendered = ⟨leftRendered.lines ++ rightRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary rightRendered.nextId) (LocalType.ofTarget scalarTarget)
          (.binary sourceOp (.name leftValue) (.name rightValue))),
        some (temporary rightRendered.nextId), rightRendered.nextId + 1⟩ := by
  have unfolded : ((MutationRenderer.render functions .word bindings indent first left).bind
      fun leftRendered => (MutationRenderer.requireValue leftRendered).bind fun leftValue =>
        (MutationRenderer.render functions .word bindings indent leftRendered.nextId right).bind
          fun rightRendered => (MutationRenderer.requireValue rightRendered).bind
            fun rightValue => (target.scalarExcept.bind fun scalarTarget =>
              (ScalarRenderer.render scalarTarget [leftValue, rightValue] indent
                rightRendered.nextId (.binary op (.var 0) (.var 1))).bind fun result =>
                  Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
              fun result => Except.ok (⟨leftRendered.lines ++ rightRendered.lines ++
                result.lines, result.value, result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨leftRendered, leftEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨leftValue, leftValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨rightRendered, rightEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨rightValue, rightValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨result, resultEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨scalarTarget, scalarEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨scalarResult, scalarResultEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.binary, selected] at scalarResultEquation
  obtain ⟨first, firstEquation, scalarResultEquation⟩ := except_bind_eq_ok scalarResultEquation
  obtain ⟨second, secondEquation, scalarResultEquation⟩ := except_bind_eq_ok scalarResultEquation
  rw [RendererEquations.var] at firstEquation secondEquation
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at firstEquation secondEquation
  cases firstEquation
  cases secondEquation
  cases scalarResultEquation
  cases resultEquation
  cases unfolded
  exact ⟨leftRendered, leftValue, rightRendered, rightValue, scalarTarget, leftEquation,
    requireValue_ok leftValueEquation, rightEquation, requireValue_ok rightValueEquation,
    scalarEquation, rfl⟩

theorem apply_ok {index : Nat} {argument : CoreExpr}
    (equation : MutationRenderer.render functions target bindings indent first
      (.apply (.var index) argument) = .ok rendered) :
    bindings.length ≤ index ∧ ∃ callee argumentRendered value,
      functions[index - bindings.length]? = some callee ∧
      MutationRenderer.render functions .word bindings indent first argument =
        .ok argumentRendered ∧
      argumentRendered.value = some value ∧
      rendered = ⟨argumentRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary argumentRendered.nextId) .word (.call1 callee (.name value))),
        some (temporary argumentRendered.nextId), argumentRendered.nextId + 1⟩ := by
  by_cases below : index < bindings.length
  · dsimp only [MutationRenderer.render] at equation
    rw [if_pos below] at equation
    cases equation
  · cases found : functions[index - bindings.length]? with
    | none =>
        dsimp only [MutationRenderer.render] at equation
        rw [if_neg below, found] at equation
        cases equation
    | some callee =>
        dsimp only [MutationRenderer.render] at equation
        rw [if_neg below, found] at equation
        obtain ⟨argumentRendered, argumentEquation, equation⟩ := except_bind_eq_ok equation
        obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
        exact ⟨Nat.le_of_not_lt below, callee, argumentRendered, value, rfl, argumentEquation,
          requireValue_ok valueEquation, (Except.ok.inj equation).symm⟩

theorem ifE_unit_ok {condition yes no : CoreExpr}
    (equation : MutationRenderer.render functions .unit bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected fallback,
      MutationRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      MutationRenderer.render functions .unit bindings (indent + 4) tested.nextId yes =
        .ok selected ∧
      MutationRenderer.render functions .unit bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      rendered = ⟨tested.lines ++ [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++
        selected.lines ++ [indentLine indent "} else {"] ++ fallback.lines ++
        [indentLine indent "}"], none, fallback.nextId⟩ := by
  simp only [MutationRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
  have unitTest : ((.unit : MTarget) == .unit) = true := rfl
  rw [if_pos unitTest] at equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, conditionValue, selected, fallback, testedEquation,
    requireValue_ok conditionEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem ifE_value_ok {condition yes no : CoreExpr} (scalar : target = .word ∨ target = .bool)
    (equation : MutationRenderer.render functions target bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected selectedValue fallback fallbackValue,
      MutationRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      MutationRenderer.render functions target bindings (indent + 4) (tested.nextId + 1) yes =
        .ok selected ∧
      selected.value = some selectedValue ∧
      MutationRenderer.render functions target bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      fallback.value = some fallbackValue ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ zeroText target.scalar ++ ";")] ++
          [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";"),
            indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  rcases scalar with rfl | rfl <;>
  · simp only [MutationRenderer.render] at equation
    obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
    rw [if_neg (by decide)] at equation
    obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selectedValue, selectedValueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallbackValue, fallbackValueEquation, equation⟩ := except_bind_eq_ok equation
    have resultName : resultValue = temporary tested.nextId :=
      (Option.some.inj (requireValue_ok resultEquation)).symm
    subst resultName
    exact ⟨tested, conditionValue, selected, selectedValue, fallback, fallbackValue,
      testedEquation, requireValue_ok conditionEquation, selectedEquation,
      requireValue_ok selectedValueEquation, fallbackEquation,
      requireValue_ok fallbackValueEquation, (Except.ok.inj equation).symm⟩

theorem unary_unsupported {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (unsupported : sourceUnary? op = none)
    (equation : MutationRenderer.render functions target bindings indent first
      (.unary op operand) = .ok rendered) : False := by
  have unfolded : ((MutationRenderer.render functions (if op == .boolNot then (.bool : MTarget)
      else .word) bindings indent first operand).bind fun operandRendered =>
      (MutationRenderer.requireValue operandRendered).bind fun value =>
        (target.scalarExcept.bind fun scalarTarget =>
          (ScalarRenderer.render scalarTarget [value] indent operandRendered.nextId
            (.unary op (.var 0))).bind fun result =>
              Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
          fun result => Except.ok (⟨operandRendered.lines ++ result.lines, result.value,
            result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, resultEquation, _⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨_, scalarResultEquation, _⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.unary, unsupported] at scalarResultEquation
  cases scalarResultEquation

theorem binary_unsupported {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (unsupported : sourceBinary? op = none)
    (equation : MutationRenderer.render functions target bindings indent first
      (.binary op left right) = .ok rendered) : False := by
  have unfolded : ((MutationRenderer.render functions .word bindings indent first left).bind
      fun leftRendered => (MutationRenderer.requireValue leftRendered).bind fun leftValue =>
        (MutationRenderer.render functions .word bindings indent leftRendered.nextId right).bind
          fun rightRendered => (MutationRenderer.requireValue rightRendered).bind
            fun rightValue => (target.scalarExcept.bind fun scalarTarget =>
              (ScalarRenderer.render scalarTarget [leftValue, rightValue] indent
                rightRendered.nextId (.binary op (.var 0) (.var 1))).bind fun result =>
                  Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
              fun result => Except.ok (⟨leftRendered.lines ++ rightRendered.lines ++
                result.lines, result.value, result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, resultEquation, _⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨_, scalarResultEquation, _⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.binary, unsupported] at scalarResultEquation
  cases scalarResultEquation

end MutationEquations

namespace MutationKinds

theorem local_beq (first second : Local) : (first == second) = decide (first = second) := by
  cases first <;> cases second <;> rfl


theorem infer_toLocal {locals : List Local} {prior : Nat} {expression : CoreExpr}
    {kind : Solcore.Synthesis.Core.LocalMutation.Target}
    (inferred : infer? locals prior expression = some kind) :
    initializerKind? locals prior expression = some kind.toLocal := by
  have unfolded : (initializerKind? locals prior expression).bind Local.toTarget? = some kind :=
    inferred
  cases found : initializerKind? locals prior expression with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some found' =>
      rw [found] at unfolded
      cases found' <;> cases unfolded <;> rfl

theorem toLocal_infer {locals : List Local} {prior : Nat} {expression : CoreExpr}
    {kind : Solcore.Synthesis.Core.LocalMutation.Target}
    (inferred : initializerKind? locals prior expression = some kind.toLocal) :
    infer? locals prior expression = some kind := by
  show (initializerKind? locals prior expression).bind Local.toTarget? = some kind
  rw [inferred]
  cases kind <;> rfl

theorem var {locals : List Local} {prior index : Nat} {kind : Local}
    (inferred : initializerKind? locals prior (.var index) = some kind) :
    locals[index]? = some kind ∧ kind ≠ .cellWord := by
  have unfolded : ((locals[index]?).bind fun found =>
      if found == Local.cellWord then none else some found) = some kind := inferred
  cases found : locals[index]? with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some found' =>
      rw [found] at unfolded
      cases found' <;> simp [local_beq] at unfolded <;> subst unfolded <;> simp

theorem letE {locals : List Local} {prior : Nat} {initializer body : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.letE initializer body) = some result) :
    ∃ kind, initializerKind? locals prior initializer = some kind ∧
      initializerKind? (kind :: locals) prior body = some result ∧ result ≠ .cellWord := by
  have unfolded : ((initializerKind? locals prior initializer).bind fun kind =>
      (initializerKind? (kind :: locals) prior body).bind fun result =>
        if result == Local.cellWord then none else some result) = some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨kind, initializerKind, result', bodyKind, last⟩ := unfolded
  cases result' <;> simp [local_beq] at last <;> subst last <;>
    exact ⟨kind, initializerKind, bodyKind, by simp⟩

theorem newCell {locals : List Local} {prior : Nat} {inner : CoreExpr} {kind : Local}
    (inferred : initializerKind? locals prior (.newCell .word inner) = some kind) :
    kind = .cellWord ∧ initializerKind? locals prior inner = some .word := by
  have unfolded : ((initializerKind? locals prior inner).bind fun found =>
      (if found == Local.word then some () else none).bind fun _ => some Local.cellWord) =
      some kind := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, innerKind, checked, check, last⟩ := unfolded
  cases last
  cases found <;> simp [local_beq] at check
  exact ⟨rfl, innerKind⟩

/-- The local kind of a scalar result. -/
def scalarKind : Solcore.Synthesis.Core.Target → Local
  | .word => .word
  | .bool => .bool

theorem ifE {locals : List Local} {prior : Nat} {condition yes no : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.ifE condition yes no) = some result) :
    initializerKind? locals prior condition = some .bool ∧
      initializerKind? locals prior yes = some result ∧
      initializerKind? locals prior no = some result ∧ result ≠ .cellWord := by
  have unfolded : ((initializerKind? locals prior condition).bind fun found =>
      (if found == Local.bool then some () else none).bind fun _ =>
        (initializerKind? locals prior yes).bind fun left =>
          (initializerKind? locals prior no).bind fun right =>
            if (left == right && left != Local.cellWord) = true then some left else none) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, conditionKind, checked, check, left, yesKind, right, noKind, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases left <;> cases right <;> simp [local_beq, bne] at last <;> subst last <;>
    exact ⟨conditionKind, yesKind, noKind, by simp⟩

theorem loadCell {locals : List Local} {prior index : Nat} {result : Local}
    (inferred : initializerKind? locals prior (.loadCell (.var index)) = some result) :
    locals[index]? = some .cellWord ∧ result = .word := by
  have unfolded : ((locals[index]?).bind fun found =>
      (if found == Local.cellWord then some () else none).bind fun _ => some Local.word) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, foundEq, checked, check, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases last
  exact ⟨foundEq, rfl⟩

theorem storeCell {locals : List Local} {prior index : Nat} {value : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.storeCell (.var index) value) = some result) :
    locals[index]? = some .cellWord ∧ initializerKind? locals prior value = some .word ∧
      result = .unit := by
  have unfolded : ((locals[index]?).bind fun found =>
      (if found == Local.cellWord then some () else none).bind fun _ =>
        (initializerKind? locals prior value).bind fun written =>
          (if written == Local.word then some () else none).bind fun _ => some Local.unit) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, foundEq, checked, check, written, valueKind, checked', check', last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases written <;> simp [local_beq] at check'
  cases last
  exact ⟨foundEq, valueKind, rfl⟩

/-- The integer operations, which the mutation profile rejects. -/
def integerUnary : Solcore.Core.Wire.UnaryOp → Bool
  | .integerNot | .integerToWord | .wordToInteger => true
  | _ => false

def integerBinary : Solcore.Core.Wire.BinaryOp → Bool
  | .integerAdd | .integerSub | .integerMul | .integerDiv | .integerMod
  | .integerEq | .integerLt | .integerAnd | .integerOr | .integerXor => true
  | _ => false

theorem unary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.UnaryOp)
    (operand : CoreExpr) :
    initializerKind? locals prior (.unary op operand) =
      if integerUnary op then none else
        (initializerKind? locals prior operand).bind fun found =>
          (if found == scalarKind (Target.unaryOperand op) then some () else none).bind fun _ =>
            some (scalarKind (Target.unaryResult op)) := by
  cases op <;> rfl

theorem binary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.BinaryOp)
    (left right : CoreExpr) :
    initializerKind? locals prior (.binary op left right) =
      if integerBinary op then none else
        (initializerKind? locals prior left).bind fun found =>
          (if found == Local.word then some () else none).bind fun _ =>
            (initializerKind? locals prior right).bind fun found' =>
              (if found' == Local.word then some () else none).bind fun _ =>
                some (scalarKind (Target.binaryResult op)) := by
  cases op <;> rfl

theorem unary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.UnaryOp}
    {sourceOp : UnaryOp} {operand : CoreExpr} {result : Local}
    (selected : sourceUnary? op = some sourceOp)
    (inferred : initializerKind? locals prior (.unary op operand) = some result) :
    initializerKind? locals prior operand = some (scalarKind (Target.unaryOperand op)) ∧
      result = scalarKind (Target.unaryResult op) := by
  have notInteger : integerUnary op = false := by
    cases op <;> simp_all [sourceUnary?, integerUnary]
  rw [unary_eq, if_neg (by simp [notInteger])] at inferred
  simp only [Option.bind_eq_some_iff] at inferred
  obtain ⟨found, operandKind, checked, check, last⟩ := inferred
  have same : found = scalarKind (Target.unaryOperand op) := by
    by_cases same : found = scalarKind (Target.unaryOperand op)
    · exact same
    · rw [local_beq, decide_eq_false same] at check
      cases check
  cases last
  exact ⟨same ▸ operandKind, rfl⟩

theorem binary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.BinaryOp}
    {sourceOp : BinaryOp} {left right : CoreExpr} {result : Local}
    (selected : sourceBinary? op = some sourceOp)
    (inferred : initializerKind? locals prior (.binary op left right) = some result) :
    initializerKind? locals prior left = some .word ∧
      initializerKind? locals prior right = some .word ∧
      result = scalarKind (Target.binaryResult op) := by
  have notInteger : integerBinary op = false := by
    cases op <;> simp_all [sourceBinary?, integerBinary]
  rw [binary_eq, if_neg (by simp [notInteger])] at inferred
  simp only [Option.bind_eq_some_iff] at inferred
  obtain ⟨found, leftKind, checked, check, found', rightKind, checked', check', last⟩ := inferred
  cases found <;> simp [local_beq] at check
  cases found' <;> simp [local_beq] at check'
  cases last
  exact ⟨leftKind, rightKind, rfl⟩

theorem apply {locals : List Local} {prior index : Nat} {argument : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.apply (.var index) argument) = some result) :
    locals.length ≤ index ∧ index < locals.length + prior ∧
      initializerKind? locals prior argument = some .word ∧ result = .word := by
  have unfolded : (if (decide (locals.length ≤ index) &&
      decide (index < locals.length + prior)) = true then
        (initializerKind? locals prior argument).bind fun found =>
          (if found == Local.word then some () else none).bind fun _ => some Local.word
      else none) = some result := inferred
  by_cases range : (decide (locals.length ≤ index) && decide (index < locals.length + prior)) = true
  · rw [if_pos range] at unfolded
    simp only [Bool.and_eq_true, decide_eq_true_eq] at range
    simp only [Option.bind_eq_some_iff] at unfolded
    obtain ⟨found, argumentKind, checked, check, last⟩ := unfolded
    cases found <;> simp [local_beq] at check
    cases last
    exact ⟨range.1, range.2, argumentKind, rfl⟩
  · rw [if_neg range] at unfolded
    cases unfolded

end MutationKinds
end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.MutationPreservation
/-! Per-constructor simulation lemmas for the actual `MutationRenderer.render`
and the structural induction over Core expressions. A Core cell lives in the
store and the source keeps its Word in an `sc_c<n>` local; every read of a cell
is copied to a fresh immutable temporary before a later operand can write it. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.MutationRenderer (Binding)
open Solcore.Synthesis.Core.LocalMutation (Local initializerKind? infer?)

/-! ### Values and targets -/

/-- The mutation target of a scalar target. -/
def mutationTarget : Target → MTarget
  | .word => .word
  | .bool => .bool

theorem MRepresents.toScalar {target : Target} {core : CoreValue} {source : Value}
    (represents : MRepresents (mutationTarget target) core (some source)) :
    Represents target core source := by
  cases target
  · obtain ⟨word, rfl, same⟩ := represents
    cases same
    exact ⟨word, rfl, rfl⟩
  · obtain ⟨flag, rfl, same⟩ := represents
    cases same
    exact ⟨flag, rfl, rfl⟩

theorem Represents.toMutation {target : Target} {core : CoreValue} {source : Value}
    (represents : Represents target core source) :
    MRepresents (mutationTarget target) core (some source) := by
  cases target
  · obtain ⟨word, rfl, rfl⟩ := represents
    exact ⟨word, rfl, rfl⟩
  · obtain ⟨flag, rfl, rfl⟩ := represents
    exact ⟨flag, rfl, rfl⟩

theorem toLocal_scalarKind {target : MTarget} {scalar : Target}
    (same : target.toLocal = MutationKinds.scalarKind scalar) :
    target = (mutationTarget scalar) := by
  cases target <;> cases scalar <;> first | rfl | cases same

theorem mutation_scalarExcept (scalar : Target) :
    (mutationTarget scalar).scalarExcept = .ok scalar := by
  cases scalar <;> rfl

theorem mutation_localType (scalar : Target) :
    (mutationTarget scalar).localType = LocalType.ofTarget scalar := by
  cases scalar <;> rfl

theorem MRepresents.admits {target : MTarget} {core : CoreValue} {source : Value}
    (scalar : target = .word ∨ target = .bool)
    (represents : MRepresents target core (some source)) :
    target.localType.admits source = true := by
  rcases scalar with rfl | rfl
  · obtain ⟨word, _, same⟩ := represents
    cases same
    rfl
  · obtain ⟨flag, _, same⟩ := represents
    cases same
    rfl

/-! ### Frames -/

theorem BindingsAgree.declare {scope : Scope} {outer : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : BindingsAgree (scope :: outer) bindings environment store) {name : String}
    (fresh : ∀ index found, nameAt bindings index = some found → found ≠ name) (value : Value) :
    BindingsAgree (((name, value) :: scope) :: outer) bindings environment store :=
  agree.transfer (fun index found named => by
      rw [Frames.lookup_declared, if_neg (fun same => fresh index found named same.symm)])
    (fun _ _ _ => rfl)

theorem BindingsAgree.enter {scope : Scope} {outer : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : BindingsAgree (scope :: outer) bindings environment store) :
    BindingsAgree ([] :: scope :: outer) bindings environment store :=
  agree.transfer (fun _ _ _ => Frames.lookup_nil_cons _ _) (fun _ _ _ => rfl)

theorem NamesFresh.ne_temp {bindings : List Binding} {first last : Nat} {name : String}
    (fresh : NamesFresh bindings first) (temp : TempIn first last name) :
    ∀ index found, nameAt bindings index = some found → found ≠ name := by
  intro index found named same
  subst same
  exact not_tempIn_of_fresh (fresh index found named) (Nat.le_refl _) temp

/-- No binding is a cell named `name` when `name` is a fresh temporary. -/
theorem NamesFresh.not_cell {bindings : List Binding} {first last : Nat} {name : String}
    (fresh : NamesFresh bindings first) (temp : TempIn first last name) :
    ∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name) := by
  intro index found
  exact fresh.ne_temp temp index name (by rw [nameAt_of_getElem? found]; rfl) rfl

theorem StoreFrame.of_cons {binding : Binding} {bindings : List Binding} {core : CoreValue}
    {environment : Solcore.Core.Environment} {store store' : Solcore.Core.Store}
    (frame : StoreFrame (binding :: bindings) (core :: environment) store store')
    (head : ∀ location, location < store.length → ¬ CellAt (binding :: bindings)
      (core :: environment) 0 location) :
    StoreFrame bindings environment store store' := by
  refine ⟨frame.1, fun location inBounds notCell => frame.2 location inBounds ?_⟩
  intro index cell
  cases index with
  | zero => exact head location inBounds cell
  | succ index => exact notCell index cell.of_cons

/-! ### The common result binding -/

section

variable {admits : Context → Prop}

/-- The common tail of value expressions: a fresh temporary declared from
earlier names, with a value computed from the Core result. -/
theorem mresult_simulates {expression : CoreExpr} {target : MTarget}
    {functions : List String} {bindings : List Binding} {first middle : Nat}
    {statements : List Stmt} {initializer : Expr}
    (scalar : target = .word ∨ target = .bool) (fresh : NamesFresh bindings first)
    (core : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store) (scope : Scope) (outer : Frames),
      admits context → BindingsAgree (scope :: outer) bindings environment store →
      CellsDistinct bindings environment → bindings.length ≤ environment.length →
      MFunctionsAgree context functions (environment.drop bindings.length) →
      ∃ (coreValue : CoreValue) (value : Value) (store' : Solcore.Core.Store) (scope₁ : Scope)
        (outer₁ : Frames) (added : List String),
        Solcore.Core.Evaluates environment store expression.toCore coreValue store' ∧
        MRepresents target coreValue (some value) ∧
        Stmt.execList context (scope :: outer) statements = some (scope₁ :: outer₁) ∧
        initializer.eval context (scope₁ :: outer₁) = some value ∧
        BindingsAgree (scope₁ :: outer₁) bindings environment store' ∧
        StoreFrame bindings environment store store' ∧
        (∀ name, ¬ TempIn first middle name →
          (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
          Frames.lookup (scope₁ :: outer₁) name = Frames.lookup (scope :: outer) name) ∧
        Frames.shape outer₁ = Frames.shape outer ∧
        scope₁.names = added ++ scope.names ∧
        (∀ name ∈ added, TempIn first middle name))
    (le : first ≤ middle) :
    MSimulates admits expression target functions bindings first (middle + 1)
      (statements ++ [.letDecl (temporary middle) target.localType initializer])
      (some (temporary middle)) := by
  intro context environment store scope outer admitted agree distinct lengthOk functionsOk
  obtain ⟨coreValue, value, store', scope₁, outer₁, added, evaluates, represents, exec,
    initialized, agree₁, frame, keeps, shape, names, addedTemp⟩ :=
    core context environment store scope outer admitted agree distinct lengthOk functionsOk
  have temp : TempIn first (middle + 1) (temporary middle) :=
    tempIn_temporary le (Nat.lt_succ_self _)
  refine ⟨coreValue, store', (temporary middle, value) :: scope₁, outer₁,
    temporary middle :: added, evaluates, ?_, ?_, ?_, frame, ?_, shape, ?_, ?_⟩
  · simp only [Option.bind_some, Frames.lookup_declared, if_pos]
    exact represents
  · rw [Stmt.execList_append, exec]
    simp [Stmt.execList, Stmt.exec, initialized, represents.admits scalar, Frames.declare]
  · exact agree₁.declare (fresh.ne_temp temp) value
  · intro name notTemp notCell
    have different : temporary middle ≠ name := fun same => notTemp (same ▸ temp)
    rw [Frames.lookup_declared, if_neg different,
      keeps name (fun inRange => notTemp (tempIn_mono inRange (Nat.le_refl _) (Nat.le_succ _)))
        notCell]
  · show temporary middle :: scope₁.names = (temporary middle :: added) ++ scope.names
    rw [names]
    rfl
  · intro name mem
    rcases List.mem_cons.mp mem with same | mem
    · exact same ▸ temp
    · exact tempIn_mono (addedTemp name mem) (Nat.le_refl _) (Nat.le_succ _)

/-- An expression with no statements, whose value is already named. -/
theorem msimulates_nil {expression : CoreExpr} {target : MTarget}
    {functions : List String} {bindings : List Binding} {first : Nat}
    {valueName : Option String}
    (core : ∀ (environment : Solcore.Core.Environment) (store : Solcore.Core.Store)
      (scope : Scope) (outer : Frames),
      BindingsAgree (scope :: outer) bindings environment store →
      ∃ coreValue : CoreValue,
        Solcore.Core.Evaluates environment store expression.toCore coreValue store ∧
        MRepresents target coreValue (valueName.bind (Frames.lookup (scope :: outer)))) :
    MSimulates admits expression target functions bindings first first [] valueName := by
  intro context environment store scope outer _ agree _ _ _
  obtain ⟨coreValue, evaluates, represents⟩ := core environment store scope outer agree
  exact ⟨coreValue, store, scope, outer, [], evaluates, represents, rfl, agree,
    StoreFrame.refl _ _ _, fun _ _ _ => rfl, rfl, rfl, by simp⟩

/-! ### Literals, locals and cell reads -/

theorem mRenderIH_word (value : Solcore.Core.Word) : MRenderIH admits (.word value) := by
  intro functions target bindings indent first rendered accepted equation fresh _
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases accepted
  subst targetWord
  rw [MutationEquations.word] at equation
  cases equation
  have temp : TempIn first (first + 1) (temporary first) :=
    tempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _)
  refine ⟨[.letDecl (temporary first) .word (.number value.val)], by simp [Stmt.listLines],
    Nat.le_succ _, ?_, ?_, ?_⟩
  · intro name same
    cases same
    exact Or.inr ⟨first, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  · intro name mem
    simp [Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers] at mem
    subst mem
    exact Or.inr (Or.inr temp)
  · have simulates := mresult_simulates (admits := admits) (expression := .word value)
      (target := .word) (functions := functions) (statements := []) (initializer :=
        .number value.val) (Or.inl rfl) fresh
      (fun context environment store scope outer _ agree _ _ _ =>
        ⟨.word value, .word value.val, store, scope, outer, [], by
          simp only [Solcore.Core.Wire.Expr.toCore]; exact .word, ⟨value, rfl, rfl⟩, rfl,
          by simp [Expr.eval, word_lt_modulus], agree, StoreFrame.refl _ _ _,
          fun _ _ _ => rfl, rfl, rfl, by simp⟩) (Nat.le_refl first)
    exact simulates

theorem mRenderIH_bool (value : Bool) : MRenderIH admits (.bool value) := by
  intro functions target bindings indent first rendered accepted equation fresh _
  have targetBool : target = .bool := by
    cases target <;> first | rfl | cases accepted
  subst targetBool
  rw [MutationEquations.bool] at equation
  cases equation
  have temp : TempIn first (first + 1) (temporary first) :=
    tempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _)
  refine ⟨[.letDecl (temporary first) .bool (.bool value)], by simp [Stmt.listLines],
    Nat.le_succ _, ?_, ?_, ?_⟩
  · intro name same
    cases same
    exact Or.inr ⟨first, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  · intro name mem
    simp [Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers] at mem
    subst mem
    exact Or.inr (Or.inr temp)
  · have simulates := mresult_simulates (admits := admits) (expression := .bool value)
      (target := .bool) (functions := functions) (statements := []) (initializer :=
        .bool value) (Or.inr rfl) fresh
      (fun context environment store scope outer _ agree _ _ _ =>
        ⟨.bool value, .bool value, store, scope, outer, [], by
          simp only [Solcore.Core.Wire.Expr.toCore]; exact .bool, ⟨value, rfl, rfl⟩, rfl,
          rfl, agree, StoreFrame.refl _ _ _, fun _ _ _ => rfl, rfl, rfl, by simp⟩)
      (Nat.le_refl first)
    exact simulates

theorem mRenderIH_unit : MRenderIH admits .unit := by
  intro functions target bindings indent first rendered accepted equation _ _
  have targetUnit : target = .unit := by
    cases target <;> first | rfl | cases accepted
  subst targetUnit
  rw [MutationEquations.unit] at equation
  cases equation
  refine ⟨[], rfl, Nat.le_refl _, (fun _ same => by cases same),
    (by simp [Stmt.listIdentifiers]), msimulates_nil fun _ _ _ _ _ => ⟨.unit, ?_, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .unit

theorem mRenderIH_var (index : Nat) : MRenderIH admits (.var index) := by
  intro functions target bindings indent first rendered accepted equation _ _
  obtain ⟨kindFound, _⟩ := MutationKinds.var accepted
  rw [List.getElem?_map] at kindFound
  rcases MutationEquations.var_ok equation with ⟨name, found, rfl⟩ | ⟨found, rfl⟩
  · refine ⟨[], rfl, Nat.le_refl _, ?_, by simp [Stmt.listIdentifiers], ?_⟩
    · intro value same
      cases same
      exact Or.inl ⟨index, found⟩
    · refine msimulates_nil fun environment store scope outer agree => ?_
      rcases found with found | found
      · rw [found] at kindFound
        have targetWord : target = .word := by
          cases target <;> first | rfl | cases kindFound
        subst targetWord
        obtain ⟨core, inEnvironment, word, rfl, lookup⟩ := agree index _ found
        refine ⟨.word word, ?_, word, rfl, by simp [lookup]⟩
        simp only [Solcore.Core.Wire.Expr.toCore]
        exact .var inEnvironment
      · rw [found] at kindFound
        have targetBool : target = .bool := by
          cases target <;> first | rfl | cases kindFound
        subst targetBool
        obtain ⟨core, inEnvironment, flag, rfl, lookup⟩ := agree index _ found
        refine ⟨.bool flag, ?_, flag, rfl, by simp [lookup]⟩
        simp only [Solcore.Core.Wire.Expr.toCore]
        exact .var inEnvironment
  · rw [found] at kindFound
    have targetUnit : target = .unit := by
      cases target <;> first | rfl | cases kindFound
    subst targetUnit
    refine ⟨[], rfl, Nat.le_refl _, (fun _ same => by cases same),
      (by simp [Stmt.listIdentifiers]), ?_⟩
    refine msimulates_nil fun environment store scope outer agree => ?_
    obtain ⟨core, inEnvironment, same⟩ := agree index _ found
    subst same
    refine ⟨.unit, ?_, rfl⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .var inEnvironment

theorem mRenderIH_loadCell (index : Nat) : MRenderIH admits (.loadCell (.var index)) := by
  intro functions target bindings indent first rendered accepted equation fresh _
  obtain ⟨cellKind, resultWord⟩ := MutationKinds.loadCell accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨name, found, rfl⟩ := MutationEquations.loadCell_ok equation
  have temp : TempIn first (first + 1) (temporary first) :=
    tempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _)
  refine ⟨[.letDecl (temporary first) .word (.name name)], by simp [Stmt.listLines],
    Nat.le_succ _, ?_, ?_, ?_⟩
  · intro value same
    cases same
    exact Or.inr ⟨first, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  · intro identifier mem
    simp [Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers] at mem
    rcases mem with rfl | rfl
    · exact Or.inr (Or.inr temp)
    · exact Or.inl ⟨index, by rw [nameAt_of_getElem? found]; rfl⟩
  · have simulates := mresult_simulates (admits := admits)
      (expression := .loadCell (.var index)) (target := .word) (functions := functions)
      (statements := []) (initializer := .name name) (Or.inl rfl) fresh
      (fun context environment store scope outer _ agree _ _ _ => by
        obtain ⟨core, inEnvironment, elementType, location, word, rfl, read, lookup⟩ :=
          agree index _ found
        refine ⟨.word word, .word word.val, store, scope, outer, [], ?_, ⟨word, rfl, rfl⟩, rfl,
          lookup, agree, StoreFrame.refl _ _ _, fun _ _ _ => rfl, rfl, rfl, by simp⟩
        simp only [Solcore.Core.Wire.Expr.toCore]
        exact .loadCell (.var inEnvironment) read) (Nat.le_refl first)
    exact simulates

/-! ### Local bindings -/

theorem letBinding_kind {kind : MTarget} (scalar : kind = .word ∨ kind = .bool) (name : String) :
    (letBinding kind name).kind = kind.toLocal := by
  rcases scalar with rfl | rfl <;> rfl

theorem letBinding_name {kind : MTarget} (scalar : kind = .word ∨ kind = .bool) (name : String) :
    bindingName? (letBinding kind name) = some name := by
  rcases scalar with rfl | rfl <;> rfl

theorem letBinding_holds {kind : MTarget} (scalar : kind = .word ∨ kind = .bool)
    {frames : Frames} {store : Solcore.Core.Store} {name : String} {core : CoreValue}
    {value : Value} (represents : MRepresents kind core (some value))
    (lookup : frames.lookup name = some value) :
    BindingHolds frames store (letBinding kind name) core := by
  rcases scalar with rfl | rfl
  · obtain ⟨word, rfl, same⟩ := represents
    cases same
    exact ⟨word, rfl, lookup⟩
  · obtain ⟨flag, rfl, same⟩ := represents
    cases same
    exact ⟨flag, rfl, lookup⟩

theorem letBinding_valueName {kind : MTarget} (scalar : kind = .word ∨ kind = .bool)
    {bindings : List Binding} {first last : Nat} {name binding : String}
    (value : ValueName (letBinding kind binding :: bindings) first last name)
    (temporaryBinding : ∃ index, binding = temporary index ∧
      first ≤ index ∧ index < last) :
    ValueName bindings first last name := by
  rcases value with ⟨index, found⟩ | temp
  · cases index with
    | zero =>
        rcases scalar with rfl | rfl <;> rcases found with found | found <;>
          simp [letBinding] at found <;> subst found <;> exact Or.inr temporaryBinding
    | succ index => exact Or.inl ⟨index, by simpa using found⟩
  · exact Or.inr temp

/-- The source names a rendered statement list may use: bindings, helpers or
temporaries in range. -/
def UsesNames (bindings : List Binding) (functions : List String) (first last : Nat)
    (statements : List Stmt) : Prop :=
  ∀ name ∈ Stmt.listIdentifiers statements,
    (∃ index, nameAt bindings index = some name) ∨ name ∈ functions ∨ TempIn first last name

theorem ValueName.uses {bindings : List Binding} {functions : List String} {first last : Nat}
    {name : String} (value : ValueName bindings first last name) :
    (∃ index, nameAt bindings index = some name) ∨ name ∈ functions ∨ TempIn first last name := by
  rcases value with ⟨index, found | found⟩ | ⟨index, rfl, lower, upper⟩
  · exact Or.inl ⟨index, by rw [nameAt_of_getElem? found]; rfl⟩
  · exact Or.inl ⟨index, by rw [nameAt_of_getElem? found]; rfl⟩
  · exact Or.inr (Or.inr (tempIn_temporary lower upper))

/-- Identifiers of a body rendered under one more named binding. -/
theorem uses_cons {bindings : List Binding} {functions : List String} {first middle last : Nat}
    {binding : Binding} {name : String}
    (uses : (∃ index, nameAt (binding :: bindings) index = some name) ∨ name ∈ functions ∨
      TempIn middle last name)
    (bound : ∀ found, bindingName? binding = some found → TempIn first last found)
    (le : first ≤ middle) :
    (∃ index, nameAt bindings index = some name) ∨ name ∈ functions ∨
      TempIn first last name := by
  rcases uses with ⟨index, named⟩ | mem | temp
  · cases index with
    | zero =>
        rw [nameAt_cons_zero] at named
        exact Or.inr (Or.inr (bound name named))
    | succ index =>
        rw [nameAt_cons_succ] at named
        exact Or.inl ⟨index, named⟩
  · exact Or.inr (Or.inl mem)
  · exact Or.inr (Or.inr (tempIn_mono temp le (Nat.le_refl _)))

theorem uses_mono {bindings : List Binding} {functions : List String}
    {first last first' last' : Nat} {name : String}
    (uses : (∃ index, nameAt bindings index = some name) ∨ name ∈ functions ∨
      TempIn first last name) (low : first' ≤ first) (high : last ≤ last') :
    (∃ index, nameAt bindings index = some name) ∨ name ∈ functions ∨
      TempIn first' last' name := by
  rcases uses with named | mem | temp
  · exact Or.inl named
  · exact Or.inr (Or.inl mem)
  · exact Or.inr (Or.inr (tempIn_mono temp low high))

/-- A `let` that allocates a Core cell declares an `sc_c<n>` local. -/
theorem mRenderIH_newCellLet {inner body : CoreExpr} (innerIH : MRenderIH admits inner)
    (bodyIH : MRenderIH admits body) : MRenderIH admits (.letE (.newCell .word inner) body) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := MutationKinds.letE accepted
  obtain ⟨rfl, innerKind⟩ := MutationKinds.newCell initializerKind
  obtain ⟨initial, value, rest, initialEquation, valueFound, restEquation, rfl⟩ :=
    MutationEquations.newCellLet_ok equation
  obtain ⟨innerStatements, innerLines, innerLe, innerValue, innerNames, innerSimulates⟩ :=
    innerIH functions .word bindings indent first initial innerKind initialEquation fresh distinct
  have cellTemp' : ∀ last, initial.nextId < last → TempIn first last (cellTemp initial.nextId) :=
    fun _ lt => tempIn_cellTemp innerLe lt
  have bodyFresh : NamesFresh (.cellWord (cellTemp initial.nextId) :: bindings)
      (initial.nextId + 1) := by
    refine fresh.cons (Nat.le_succ_of_le innerLe) fun name same => ?_
    cases same
    intro index isTemp
    rcases isTemp with same | same
    · exact absurd same (cellTemp_ne_temporary _ _)
    · have := cellTemp_injective same
      omega
  have bodyDistinct : NamesDistinct (.cellWord (cellTemp initial.nextId) :: bindings) :=
    distinct.cons fresh fun name same => by
      cases same
      exact ⟨initial.nextId, Or.inr rfl, innerLe⟩
  obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
    bodyIH functions target (.cellWord (cellTemp initial.nextId) :: bindings) indent
      (initial.nextId + 1) rest bodyKind
      restEquation bodyFresh bodyDistinct
  refine ⟨innerStatements ++ [.letDecl (cellTemp initial.nextId) .word (.name value)] ++
      bodyStatements, ?_,
    by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, innerLines, bodyLines, Stmt.listLines, List.append_nil]
  · intro name same
    rcases bodyValue name same with ⟨index, found⟩ | ⟨index, rfl, lower, upper⟩
    · cases index with
      | zero => rcases found with found | found <;> simp at found
      | succ index => exact Or.inl ⟨index, by simpa using found⟩
    · exact Or.inr ⟨index, rfl, by omega, upper⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with (mem | same | same) | mem
    · exact uses_mono (innerNames name mem) (Nat.le_refl _) (by dsimp only; omega)
    · subst same
      exact Or.inr (Or.inr (cellTemp' _ (by dsimp only; omega)))
    · subst same
      exact uses_mono (innerValue name valueFound).uses (Nat.le_refl _) (by dsimp only; omega)
    · exact uses_cons (bodyNames name mem)
        (fun found same => by cases same; exact cellTemp' _ (by dsimp only; omega))
        (Nat.le_succ_of_le innerLe)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk functionsOk
    obtain ⟨innerCore, store₁, scope₁, outer₁, added₁, innerEvaluates, innerRepresents,
      innerExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      innerSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    rw [valueFound] at innerRepresents
    obtain ⟨word, rfl, lookupValue⟩ := innerRepresents
    simp only [Option.bind_some] at lookupValue
    have oldRead : ∀ other, other < store₁.length →
        (store₁ ++ [Solcore.Core.Value.word word]).read? other = store₁.read? other := by
      intro other lt
      simp [Solcore.Core.Store.read?, List.getElem?_append_left lt]
    have cellNew : ∀ index location, CellAt bindings environment index location →
        location ≠ store₁.length :=
      fun _ _ isCell same => absurd (agree₁.cell_lt isCell) (by omega)
    have bodyAgree : BindingsAgree (((cellTemp initial.nextId, .word word.val) :: scope₁) ::
        outer₁)
        (.cellWord (cellTemp initial.nextId) :: bindings)
        (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment)
        (store₁ ++ [.word word]) := by
      refine BindingsAgree.cons ?_ ⟨_, store₁.length, word, rfl, by
        simp [Solcore.Core.Store.read?], by simp [Frames.lookup_declared]⟩
      exact (agree₁.declare (fresh.ne_temp (cellTemp' _ (Nat.lt_succ_self _))) _).transfer
        (fun _ _ _ => rfl) fun _ location isCell => oldRead location (agree₁.cell_lt isCell)
    have bodyCells : CellsDistinct (.cellWord (cellTemp initial.nextId) :: bindings)
        (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) := by
      have headCell : ∀ location, CellAt (.cellWord (cellTemp initial.nextId) :: bindings)
          (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) 0 location →
          location = store₁.length := by
        intro location isCell
        obtain ⟨_, elementType, inEnvironment⟩ := isCell
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          Solcore.Core.Value.cellRef.injEq] at inEnvironment
        exact inEnvironment.2.symm
      intro one two location cellOne cellTwo
      cases one with
      | zero =>
          cases two with
          | zero => rfl
          | succ two =>
              exact absurd (headCell location cellOne) (cellNew two location cellTwo.of_cons)
      | succ one =>
          cases two with
          | zero =>
              exact absurd (headCell location cellTwo) (cellNew one location cellOne.of_cons)
          | succ two =>
              exact congrArg (· + 1) (distinctCells one two location cellOne.of_cons
                cellTwo.of_cons)
    obtain ⟨bodyCore, store₂, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents, bodyExec,
      agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      bodySimulates context _ (store₁ ++ [.word word])
        ((cellTemp initial.nextId, .word word.val) :: scope₁) outer₁
        admitted bodyAgree bodyCells (by simp; omega) (by simpa using functionsOk)
    have cellOutside : ∀ name, ¬ TempIn first rest.nextId name → (cellTemp initial.nextId) ≠ name :=
      fun name notTemp same => notTemp (same ▸ cellTemp' _ (by omega))
    refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ (cellTemp initial.nextId) :: added₁, ?_,
      bodyRepresents, ?_,
      agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .letE (.newCell innerEvaluates) bodyEvaluates
    · rw [Stmt.execList_append, Stmt.execList_append, innerExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, LocalType.admits, Frames.declare,
        bodyExec]
    · refine ⟨by have := frame₁.1; have := frame₂.1; simp at *; omega,
        fun other lt notCell => ?_⟩
      have lt₁ : other < store₁.length := Nat.lt_of_lt_of_le lt frame₁.1
      have notBodyCell : ∀ index, ¬ CellAt (.cellWord (cellTemp initial.nextId) :: bindings)
          (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) index
          other := by
        intro index isCell
        cases index with
        | zero =>
            obtain ⟨_, elementType, inEnvironment⟩ := isCell
            simp only [List.getElem?_cons_zero, Option.some.injEq,
              Solcore.Core.Value.cellRef.injEq] at inEnvironment
            have same : (store₁.length : Nat) = other := inEnvironment.2
            omega
        | succ index => exact notCell index isCell.of_cons
      rw [frame₂.2 other (by simp; omega) notBodyCell, oldRead other lt₁,
        frame₁.2 other lt notCell]
    · intro name notTemp notCell
      rw [keeps₂ name (fun temp => notTemp (tempIn_mono temp (by omega) (Nat.le_refl _)))
          (fun index found => ?_),
        Frames.lookup_declared, if_neg (cellOutside name notTemp),
        keeps₁ name (fun temp => notTemp (tempIn_mono temp (Nat.le_refl _) (by omega))) notCell]
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Binding.cellWord.injEq] at found
          exact cellOutside name notTemp found
      | succ index => exact notCell index (by simpa using found)
    · rw [names₂]
      show added₂ ++ (cellTemp initial.nextId) :: scope₁.names =
        (added₂ ++ (cellTemp initial.nextId) :: added₁) ++ scope.names
      rw [names₁]
      simp
    · intro name mem
      simp only [List.mem_append, List.mem_cons] at mem
      rcases mem with mem | same | mem
      · exact tempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
      · exact same ▸ cellTemp' _ (by omega)
      · exact tempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

theorem ValueName.mono {bindings : List Binding} {first last first' last' : Nat} {name : String}
    (value : ValueName bindings first last name) (low : first' ≤ first) (high : last ≤ last') :
    ValueName bindings first' last' name := by
  rcases value with found | ⟨index, rfl, lower, upper⟩
  · exact Or.inl found
  · exact Or.inr ⟨index, rfl, by omega, by omega⟩

theorem MRepresents.named {kind : MTarget} (scalar : kind = .word ∨ kind = .bool) {core : CoreValue}
    {source : Option Value} (represents : MRepresents kind core source) :
    ∃ value, source = some value ∧ MRepresents kind core (some value) := by
  rcases scalar with rfl | rfl
  · obtain ⟨word, rfl, rfl⟩ := represents
    exact ⟨_, rfl, word, rfl, rfl⟩
  · obtain ⟨flag, rfl, rfl⟩ := represents
    exact ⟨_, rfl, flag, rfl, rfl⟩

theorem CellsDistinct.cons_value {binding : Binding} {bindings : List Binding} {core : CoreValue}
    {environment : Solcore.Core.Environment} (distinct : CellsDistinct bindings environment)
    (notCell : ∀ name, binding ≠ .cellWord name) :
    CellsDistinct (binding :: bindings) (core :: environment) := by
  intro one two location cellOne cellTwo
  cases one with
  | zero =>
      obtain ⟨⟨name, found⟩, _⟩ := cellOne
      exact absurd (by simpa using found) (notCell name)
  | succ one =>
      cases two with
      | zero =>
          obtain ⟨⟨name, found⟩, _⟩ := cellTwo
          exact absurd (by simpa using found) (notCell name)
      | succ two =>
          exact congrArg (· + 1) (distinct one two location cellOne.of_cons cellTwo.of_cons)

/-- A `let` of a Unit, Word or Boolean value. A Unit binding has no source name;
a Word or Boolean value is copied to a fresh immutable temporary. -/
theorem mRenderIH_letE {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (initializerIH : MRenderIH admits initializer) (bodyIH : MRenderIH admits body) :
    MRenderIH admits (.letE initializer body) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := MutationKinds.letE accepted
  obtain ⟨kindTarget, inferred⟩ := MutationEquations.letE_infer notCell equation
  have sameKind : kind = kindTarget.toLocal := by
    have toLocal := MutationKinds.infer_toLocal inferred
    rw [initializerKind] at toLocal
    exact Option.some.inj toLocal
  subst sameKind
  have kinds : kindTarget = .unit ∨ kindTarget = .word ∨ kindTarget = .bool := by
    cases kindTarget <;> simp
  rcases kinds with rfl | scalar
  · obtain ⟨initial, rest, initialEquation, restEquation, rfl⟩ :=
      MutationEquations.letE_unit_ok notCell inferred equation
    obtain ⟨initStatements, initLines, initLe, _, initNames, initSimulates⟩ :=
      initializerIH functions .unit bindings indent first initial initializerKind initialEquation
        fresh distinct
    have bodyFresh : NamesFresh (.unit :: bindings) initial.nextId :=
      fresh.cons initLe fun _ same => by cases same
    have bodyDistinct : NamesDistinct (.unit :: bindings) :=
      distinct.cons fresh fun _ same => by cases same
    obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
      bodyIH functions target (.unit :: bindings) indent initial.nextId rest bodyKind restEquation
        bodyFresh bodyDistinct
    refine ⟨initStatements ++ bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
    · simp only [Stmt.listLines_append, initLines, bodyLines]
    · intro name same
      rcases bodyValue name same with ⟨index, found⟩ | ⟨index, rfl, lower, upper⟩
      · cases index with
        | zero => rcases found with found | found <;> simp at found
        | succ index => exact Or.inl ⟨index, by simpa using found⟩
      · exact Or.inr ⟨index, rfl, by omega, upper⟩
    · intro name mem
      rw [Stmt.listIdentifiers_append, List.mem_append] at mem
      rcases mem with mem | mem
      · exact uses_mono (initNames name mem) (Nat.le_refl _) (by dsimp only; omega)
      · exact uses_cons (bodyNames name mem) (fun _ same => by cases same) initLe
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨initCore, store₁, scope₁, outer₁, added₁, initEvaluates, initRepresents, initExec,
        agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        initSimulates context environment store scope outer admitted agree distinctCells
          lengthOk functionsOk
      have unitCore : initCore = .unit := initRepresents
      subst unitCore
      obtain ⟨bodyCore, store₂, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents, bodyExec,
        agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
        bodySimulates context (.unit :: environment) store₁ scope₁ outer₁ admitted
          (agree₁.cons rfl) (distinctCells.cons_value fun _ same => by cases same)
          (by simp; omega) (by simpa using functionsOk)
      refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ added₁, ?_, bodyRepresents, ?_,
        agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .letE initEvaluates bodyEvaluates
      · rw [Stmt.execList_append, initExec]
        simpa using bodyExec
      · exact frame₁.trans (StoreFrame.of_cons frame₂ fun _ _ isCell => by
          obtain ⟨⟨_, found⟩, _⟩ := isCell
          simp at found)
      · intro name notTemp notCell
        rw [keeps₂ name (fun temp => notTemp (tempIn_mono temp (by omega) (Nat.le_refl _)))
            (fun index found => ?_),
          keeps₁ name (fun temp => notTemp (tempIn_mono temp (Nat.le_refl _) (by omega)))
            notCell]
        cases index with
        | zero => simp at found
        | succ index => exact notCell index (by simpa using found)
      · rw [names₂, names₁]
        simp
      · intro name mem
        rcases List.mem_append.mp mem with mem | mem
        · exact tempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
        · exact tempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
  · obtain ⟨initial, value, rest, initialEquation, valueFound, restEquation, rfl⟩ :=
      MutationEquations.letE_value_ok notCell scalar inferred equation
    obtain ⟨initStatements, initLines, initLe, initValue, initNames, initSimulates⟩ :=
      initializerIH functions kindTarget bindings indent first initial initializerKind
        initialEquation fresh distinct
    have bound : ∀ last, initial.nextId < last → TempIn first last (temporary initial.nextId) :=
      fun _ lt => tempIn_temporary initLe lt
    have bodyFresh : NamesFresh (letBinding kindTarget (temporary initial.nextId) :: bindings)
        (initial.nextId + 1) := by
      refine fresh.cons (Nat.le_succ_of_le initLe) fun name same => ?_
      rw [letBinding_name scalar] at same
      cases same
      intro index isTemp
      rcases isTemp with same | same
      · have := temporary_injective same
        omega
      · exact absurd same.symm (cellTemp_ne_temporary _ _)
    have bodyDistinct : NamesDistinct (letBinding kindTarget (temporary initial.nextId) ::
        bindings) :=
      distinct.cons fresh fun name same => by
        rw [letBinding_name scalar] at same
        cases same
        exact ⟨initial.nextId, Or.inl rfl, initLe⟩
    have bodyKind' : initializerKind? ((letBinding kindTarget (temporary initial.nextId) ::
        bindings).map Binding.kind) functions.length body = some target.toLocal := by
      simpa [letBinding_kind scalar] using bodyKind
    obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
      bodyIH functions target (letBinding kindTarget (temporary initial.nextId) :: bindings)
        indent (initial.nextId + 1) rest bodyKind' restEquation bodyFresh bodyDistinct
    refine ⟨initStatements ++ [.letDecl (temporary initial.nextId) (MTarget.localType kindTarget)
      (.name value)] ++ bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
    · simp only [Stmt.listLines_append, initLines, bodyLines, Stmt.listLines, List.append_nil]
    · intro name same
      exact letBinding_valueName scalar ((bodyValue name same).mono (by omega) (Nat.le_refl _))
        ⟨initial.nextId, rfl, initLe, by dsimp only; omega⟩
    · intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with (mem | same | same) | mem
      · exact uses_mono (initNames name mem) (Nat.le_refl _) (by dsimp only; omega)
      · subst same
        exact Or.inr (Or.inr (bound _ (by dsimp only; omega)))
      · subst same
        exact uses_mono (initValue name valueFound).uses (Nat.le_refl _) (by dsimp only; omega)
      · exact uses_cons (bodyNames name mem)
          (fun found same => by
            rw [letBinding_name scalar] at same
            cases same
            exact bound _ (by dsimp only; omega))
          (Nat.le_succ_of_le initLe)
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨initCore, store₁, scope₁, outer₁, added₁, initEvaluates, initRepresents, initExec,
        agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        initSimulates context environment store scope outer admitted agree distinctCells
          lengthOk functionsOk
      rw [valueFound, Option.bind_some] at initRepresents
      obtain ⟨source, lookupValue, represents⟩ := MRepresents.named scalar initRepresents
      have bodyAgree : BindingsAgree (((temporary initial.nextId, source) :: scope₁) :: outer₁)
          (letBinding kindTarget (temporary initial.nextId) :: bindings) (initCore :: environment)
          store₁ :=
        (agree₁.declare (fresh.ne_temp (bound _ (Nat.lt_succ_self _))) source).cons
          (letBinding_holds scalar represents (by simp [Frames.lookup_declared]))
      have notCellBinding : ∀ name, letBinding kindTarget (temporary initial.nextId) ≠
          .cellWord name := by
        intro name same
        rcases scalar with rfl | rfl <;> cases same
      obtain ⟨bodyCore, store₂, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents, bodyExec,
        agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
        bodySimulates context (initCore :: environment) store₁
          ((temporary initial.nextId, source) :: scope₁) outer₁ admitted bodyAgree
          (distinctCells.cons_value notCellBinding) (by simp; omega) (by simpa using functionsOk)
      have outside : ∀ name, ¬ TempIn first rest.nextId name → temporary initial.nextId ≠ name :=
        fun name notTemp same => notTemp (same ▸ bound _ (by omega))
      refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ temporary initial.nextId :: added₁, ?_,
        bodyRepresents, ?_, agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .letE initEvaluates bodyEvaluates
      · rw [Stmt.execList_append, Stmt.execList_append, initExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, represents.admits scalar,
          Frames.declare, bodyExec]
      · exact frame₁.trans (StoreFrame.of_cons frame₂ fun _ _ isCell => by
          obtain ⟨⟨name, found⟩, _⟩ := isCell
          exact notCellBinding name (by simpa using found))
      · intro name notTemp notCell
        rw [keeps₂ name (fun temp => notTemp (tempIn_mono temp (by omega) (Nat.le_refl _)))
            (fun index found => ?_),
          Frames.lookup_declared, if_neg (outside name notTemp),
          keeps₁ name (fun temp => notTemp (tempIn_mono temp (Nat.le_refl _) (by omega)))
            notCell]
        cases index with
        | zero => exact notCellBinding name (by simpa using found)
        | succ index => exact notCell index (by simpa using found)
      · rw [names₂]
        show added₂ ++ temporary initial.nextId :: scope₁.names =
          (added₂ ++ temporary initial.nextId :: added₁) ++ scope.names
        rw [names₁]
        simp
      · intro name mem
        simp only [List.mem_append, List.mem_cons] at mem
        rcases mem with mem | same | mem
        · exact tempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
        · exact same ▸ bound _ (by omega)
        · exact tempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

/-! ### Cell writes -/

/-- Writing one cell keeps every other binding: distinct names keep their
lookups and distinct cells keep their locations. -/
theorem BindingsAgree.write {frames frames' : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store store' : Solcore.Core.Store}
    (agree : BindingsAgree frames bindings environment store)
    (namesDistinct : NamesDistinct bindings)
    (cellsDistinct : CellsDistinct bindings environment) {index location : Nat} {name : String}
    {elementType : Solcore.Core.Ty} {word : Solcore.Core.Word}
    (found : bindings[index]? = some (Binding.cellWord name))
    (inEnvironment : environment[index]? = some (.cellRef elementType location))
    (written : store.write? location (.word word) = some store')
    (lookups : ∀ other, frames'.lookup other =
      if name = other then some (.word word.val) else frames.lookup other) :
    BindingsAgree frames' bindings environment store' := by
  intro position binding foundBinding
  obtain ⟨core, inEnvironment', holds⟩ := agree position binding foundBinding
  refine ⟨core, inEnvironment', ?_⟩
  by_cases same : position = index
  · subst same
    rw [found] at foundBinding
    cases foundBinding
    rw [inEnvironment] at inEnvironment'
    cases inEnvironment'
    exact ⟨elementType, location, word, rfl, Solcore.Core.Store.write?_reads_written written,
      by rw [lookups name, if_pos rfl]⟩
  · have otherName : ∀ found, bindingName? binding = some found → name ≠ found := by
      intro found named sameName
      subst sameName
      exact same (namesDistinct position index name
        (by rw [nameAt_of_getElem? foundBinding]; exact named)
        (by rw [nameAt_of_getElem? found]; rfl))
    cases binding with
    | word other =>
        obtain ⟨value, rfl, lookup⟩ := holds
        exact ⟨value, rfl, by rw [lookups other, if_neg (otherName other rfl)]; exact lookup⟩
    | bool other =>
        obtain ⟨flag, rfl, lookup⟩ := holds
        exact ⟨flag, rfl, by rw [lookups other, if_neg (otherName other rfl)]; exact lookup⟩
    | unit => exact holds
    | cellWord other =>
        obtain ⟨elementType', location', value, rfl, read, lookup⟩ := holds
        have otherLocation : location' ≠ location := by
          intro sameLocation
          subst sameLocation
          exact same (cellsDistinct position index location' ⟨⟨other, foundBinding⟩, _,
            inEnvironment'⟩ ⟨⟨name, found⟩, _, inEnvironment⟩)
        exact ⟨elementType', location', value, rfl,
          by rw [Solcore.Core.Store.write?_preserves_other written otherLocation]; exact read,
          by rw [lookups other, if_neg (otherName other rfl)]; exact lookup⟩

/-- `storeCell` assigns the cell's `sc_c<n>` local after evaluating the value. -/
theorem mRenderIH_storeCell (index : Nat) {value : CoreExpr} (valueIH : MRenderIH admits value) :
    MRenderIH admits (.storeCell (.var index) value) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, valueKind, resultUnit⟩ := MutationKinds.storeCell accepted
  have targetUnit : target = .unit := by
    cases target <;> first | rfl | cases resultUnit
  subst targetUnit
  obtain ⟨name, written, result, found, writtenEquation, resultFound, rfl⟩ :=
    MutationEquations.storeCell_ok equation
  obtain ⟨statements, lines, le, writtenValue, names, simulates⟩ :=
    valueIH functions .word bindings indent first written valueKind writtenEquation fresh distinct
  refine ⟨statements ++ [.assign name (.name result)], ?_, le, (fun _ same => by cases same),
    ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro identifier mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with mem | same | same
    · exact names identifier mem
    · subst same
      exact Or.inl ⟨index, by rw [nameAt_of_getElem? found]; rfl⟩
    · subst same
      exact (writtenValue _ resultFound).uses
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨valueCore, store₁, scope₁, outer₁, added₁, valueEvaluates, valueRepresents,
      valueExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      simulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [resultFound, Option.bind_some] at valueRepresents
    obtain ⟨word, rfl, lookupResult⟩ := valueRepresents
    obtain ⟨cellCore, inEnvironment, elementType, location, old, rfl, oldRead, _⟩ :=
      agree index _ found
    obtain ⟨cellCore₁, inEnvironment₁, elementType₁, location₁, old₁, sameCell, oldRead₁,
      oldLookup₁⟩ := agree₁ index _ found
    rw [inEnvironment] at inEnvironment₁
    cases inEnvironment₁
    cases sameCell
    have inBounds : location < store₁.length := by
      simp only [Solcore.Core.Store.read?] at oldRead₁
      exact (List.getElem?_eq_some_iff.mp oldRead₁).1
    obtain ⟨store₂, written⟩ :=
      (Solcore.Core.Store.write?_success_iff store₁ location (.word word)).mpr inBounds
    obtain ⟨frames₂, assigned, shapeAssigned, lookups⟩ :=
      Frames.assign_spec (frames := scope₁ :: outer₁) (.word word.val) oldLookup₁
    have shapeCons : frames₂.shape = scope₁.names :: outer₁.shape := by
      rw [shapeAssigned]
      rfl
    obtain ⟨scope₂, outer₂, rfl⟩ : ∃ scope₂ outer₂, frames₂ = scope₂ :: outer₂ := by
      match frames₂, shapeCons with
      | scope₂ :: outer₂, _ => exact ⟨scope₂, outer₂, rfl⟩
      | [], impossible => simp [Frames.shape] at impossible
    simp only [Frames.shape, List.map_cons, List.cons.injEq] at shapeCons
    obtain ⟨scopeNames, outerShape⟩ := shapeCons
    refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, ?_, ?_, ?_,
      outerShape.trans shape₁, scopeNames.trans names₁, addedTemp₁⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .storeCell (.var inEnvironment) oldRead valueEvaluates written
    · rw [Stmt.execList_append, valueExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, lookupResult, oldLookup₁, Value.sameType,
        assigned]
    · exact agree₁.write distinct distinctCells found inEnvironment written lookups
    · refine frame₁.trans ⟨Nat.le_of_eq (Solcore.Core.Store.write?_preserves_length written).symm,
        fun other _ notCell => ?_⟩
      have otherLocation : other ≠ location := fun same =>
        notCell index (same ▸ ⟨⟨name, found⟩, _, inEnvironment⟩)
      exact Solcore.Core.Store.write?_preserves_other written otherLocation
    · intro other notTemp notCell
      have different : name ≠ other := fun same => notCell index (same ▸ found)
      rw [lookups other, if_neg different, keeps₁ other notTemp notCell]

/-! ### Operations and calls -/

theorem toLocal_mutationTarget (scalar : Target) :
    (mutationTarget scalar).toLocal = MutationKinds.scalarKind scalar := by
  cases scalar <;> rfl

theorem mutationTarget_scalar (scalar : Target) :
    mutationTarget scalar = .word ∨ mutationTarget scalar = .bool := by
  cases scalar
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A value name keeps its value while later statements run: it is neither a
later temporary nor a cell. -/
theorem ValueName.survives {bindings : List Binding} {first middle last : Nat} {name : String}
    (fresh : NamesFresh bindings first) (distinct : NamesDistinct bindings) (le : first ≤ middle)
    (value : ValueName bindings first middle name) :
    ¬ TempIn middle last name ∧ ∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name) := by
  rcases value with ⟨position, found⟩ | ⟨position, rfl, lower, upper⟩
  · have named : nameAt bindings position = some name := by
      rcases found with found | found <;> rw [nameAt_of_getElem? found] <;> rfl
    refine ⟨fun temp => not_tempIn_of_fresh (fresh position name named) le temp,
      fun index cell => ?_⟩
    · have sameIndex := distinct index position name
        (by rw [nameAt_of_getElem? cell]; rfl) named
      subst sameIndex
      rcases found with found | found <;> rw [cell] at found <;> cases found
  · refine ⟨fun temp => not_tempIn_of_tempIn (tempIn_temporary lower upper) (Or.inl (Nat.le_refl _))
      temp, fun index cell => ?_⟩
    have := fresh index (temporary position) (by rw [nameAt_of_getElem? cell]; rfl) position
      (Or.inl rfl)
    omega

theorem unaryOperand_eq {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp}
    (selected : sourceUnary? op = some sourceOp) :
    Target.unaryOperand op = if op == .boolNot then .bool else .word := by
  cases op <;> simp_all [sourceUnary?] <;> rfl

theorem mRenderIH_unary {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : MRenderIH admits operand) : MRenderIH admits (.unary op operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  cases selected : sourceUnary? op with
  | none => exact (MutationEquations.unary_unsupported selected equation).elim
  | some sourceOp =>
      obtain ⟨operandKind, resultKind⟩ := MutationKinds.unary selected accepted
      have targetEq : target = mutationTarget (Target.unaryResult op) :=
        toLocal_scalarKind resultKind
      subst targetEq
      obtain ⟨operandRendered, value, scalarTarget, operandEquation, valueFound, scalarEquation,
        rfl⟩ := MutationEquations.unary_ok selected equation
      rw [mutation_scalarExcept] at scalarEquation
      cases scalarEquation
      have operandTarget : (if op == .boolNot then (.bool : MTarget) else .word) =
          mutationTarget (Target.unaryOperand op) := by
        cases op <;> simp_all [sourceUnary?] <;> rfl
      rw [operandTarget] at operandEquation
      obtain ⟨operandStatements, operandLines, operandLe, operandValue, operandNames,
        operandSimulates⟩ :=
        operandIH functions (mutationTarget (Target.unaryOperand op)) bindings indent first
          operandRendered (by rw [toLocal_mutationTarget]; exact operandKind) operandEquation
          fresh distinct
      have temp : TempIn first (operandRendered.nextId + 1) (temporary operandRendered.nextId) :=
        tempIn_temporary operandLe (Nat.lt_succ_self _)
      refine ⟨operandStatements ++ [.letDecl (temporary operandRendered.nextId)
          (LocalType.ofTarget (Target.unaryResult op)) (.unary sourceOp (.name value))], ?_,
        by dsimp only; omega, ?_, ?_, ?_⟩
      · simp only [Stmt.listLines_append, operandLines, Stmt.listLines, List.append_nil]
      · intro name same
        cases same
        exact Or.inr ⟨operandRendered.nextId, rfl, operandLe, Nat.lt_succ_self _⟩
      · intro name mem
        simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
          Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
          or_false] at mem
        rcases mem with mem | same | same
        · exact uses_mono (operandNames name mem) (Nat.le_refl _) (Nat.le_succ _)
        · exact Or.inr (Or.inr (same ▸ temp))
        · subst same
          exact uses_mono (operandValue name valueFound).uses (Nat.le_refl _) (Nat.le_succ _)
      · dsimp only
        rw [← mutation_localType]
        refine mresult_simulates (mutationTarget_scalar _) fresh (fun context environment store
          scope outer admitted agree distinctCells lengthOk functionsOk => ?_) operandLe
        obtain ⟨core, store₁, scope₁, outer₁, added₁, evaluates, represents, exec, agree₁, frame₁,
          keeps₁, shape₁, names₁, addedTemp₁⟩ :=
          operandSimulates context environment store scope outer admitted agree distinctCells
            lengthOk functionsOk
        rw [valueFound, Option.bind_some] at represents
        obtain ⟨source, lookupValue, represents'⟩ :=
          MRepresents.named (mutationTarget_scalar _) represents
        have scalarRepresents := MRepresents.toScalar represents'
        rw [unaryOperand_eq selected] at scalarRepresents
        obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
          unary_agree selected scalarRepresents
        refine ⟨coreResult, sourceResult, store₁, scope₁, outer₁, added₁, ?_,
          resultRepresents.toMutation, exec, ?_, agree₁, frame₁, keeps₁, shape₁, names₁,
          addedTemp₁⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .unary evaluates coreApply
        · simp [Expr.eval, lookupValue, sourceApply]

theorem mRenderIH_binary {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : MRenderIH admits left) (rightIH : MRenderIH admits right) :
    MRenderIH admits (.binary op left right) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  cases selected : sourceBinary? op with
  | none => exact (MutationEquations.binary_unsupported selected equation).elim
  | some sourceOp =>
      obtain ⟨leftKind, rightKind, resultKind⟩ := MutationKinds.binary selected accepted
      have targetEq : target = mutationTarget (Target.binaryResult op) :=
        toLocal_scalarKind resultKind
      subst targetEq
      obtain ⟨leftRendered, leftValue, rightRendered, rightValue, scalarTarget, leftEquation,
        leftFound, rightEquation, rightFound, scalarEquation, rfl⟩ :=
        MutationEquations.binary_ok selected equation
      rw [mutation_scalarExcept] at scalarEquation
      cases scalarEquation
      obtain ⟨leftStatements, leftLines, leftLe, leftValueName, leftNames, leftSimulates⟩ :=
        leftIH functions .word bindings indent first leftRendered leftKind leftEquation fresh
          distinct
      obtain ⟨rightStatements, rightLines, rightLe, rightValueName, rightNames, rightSimulates⟩ :=
        rightIH functions .word bindings indent leftRendered.nextId rightRendered rightKind
          rightEquation (fresh.mono leftLe) distinct
      have temp : TempIn first (rightRendered.nextId + 1) (temporary rightRendered.nextId) :=
        tempIn_temporary (by omega) (Nat.lt_succ_self _)
      refine ⟨leftStatements ++ rightStatements ++ [.letDecl (temporary rightRendered.nextId)
          (LocalType.ofTarget (Target.binaryResult op))
          (.binary sourceOp (.name leftValue) (.name rightValue))], ?_,
        by dsimp only; omega, ?_, ?_, ?_⟩
      · simp only [Stmt.listLines_append, leftLines, rightLines, Stmt.listLines, List.append_nil]
      · intro name same
        cases same
        exact Or.inr ⟨rightRendered.nextId, rfl, by omega, Nat.lt_succ_self _⟩
      · dsimp only
        intro name mem
        simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
          Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
          or_false] at mem
        rcases mem with (mem | mem) | same | same | same
        · exact uses_mono (leftNames name mem) (Nat.le_refl _) (by omega)
        · exact uses_mono (rightNames name mem) leftLe (by omega)
        · exact Or.inr (Or.inr (same ▸ temp))
        · subst same
          exact uses_mono (leftValueName name leftFound).uses (Nat.le_refl _) (by omega)
        · subst same
          exact uses_mono (rightValueName name rightFound).uses leftLe (by omega)
      · dsimp only
        rw [← mutation_localType]
        refine mresult_simulates (mutationTarget_scalar _) fresh (fun context environment store
          scope outer admitted agree distinctCells lengthOk functionsOk => ?_) (by omega)
        obtain ⟨leftCore, store₁, scope₁, outer₁, added₁, leftEvaluates, leftRepresents,
          leftExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
          leftSimulates context environment store scope outer admitted agree distinctCells
            lengthOk functionsOk
        obtain ⟨rightCore, store₂, scope₂, outer₂, added₂, rightEvaluates, rightRepresents,
          rightExec, agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
          rightSimulates context environment store₁ scope₁ outer₁ admitted agree₁ distinctCells
            lengthOk functionsOk
        rw [leftFound, Option.bind_some] at leftRepresents
        rw [rightFound, Option.bind_some] at rightRepresents
        obtain ⟨leftWord, rfl, leftLookup⟩ := leftRepresents
        obtain ⟨rightWord, rfl, rightLookup⟩ := rightRepresents
        obtain ⟨leftSurvivesTemp, leftSurvivesCell⟩ :=
          (leftValueName leftValue leftFound).survives (last := rightRendered.nextId) fresh
            distinct leftLe
        have leftLookup₂ : Frames.lookup (scope₂ :: outer₂) leftValue =
            some (.word leftWord.val) := by
          rw [keeps₂ leftValue leftSurvivesTemp leftSurvivesCell]
          exact leftLookup
        obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
          binary_agree selected leftWord rightWord
        refine ⟨coreResult, sourceResult, store₂, scope₂, outer₂, added₂ ++ added₁, ?_,
          resultRepresents.toMutation, ?_, ?_, agree₂, frame₁.trans frame₂, ?_,
          shape₂.trans shape₁, ?_, ?_⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .binary leftEvaluates rightEvaluates coreApply
        · rw [Stmt.execList_append, leftExec]
          simpa using rightExec
        · simp [Expr.eval, leftLookup₂, rightLookup, sourceApply]
        · intro name notTemp notCell
          rw [keeps₂ name (fun temp => notTemp (tempIn_mono temp leftLe (Nat.le_refl _))) notCell,
            keeps₁ name (fun temp => notTemp (tempIn_mono temp (Nat.le_refl _) rightLe)) notCell]
        · rw [names₂, names₁]
          simp
        · intro name mem
          rcases List.mem_append.mp mem with mem | mem
          · exact tempIn_mono (addedTemp₂ name mem) leftLe (Nat.le_refl _)
          · exact tempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) rightLe

/-- A direct call to an earlier helper. The helper cannot reach the caller's
cells, so the call keeps every existing location of the store. -/
theorem mRenderIH_apply {index : Nat} {argument : CoreExpr}
    (argumentIH : MRenderIH admits argument) :
    MRenderIH admits (.apply (.var index) argument) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, _, argumentKind, resultWord⟩ := MutationKinds.apply accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨outside, callee, argumentRendered, value, found, argumentEquation, valueFound, rfl⟩ :=
    MutationEquations.apply_ok equation
  obtain ⟨argumentStatements, argumentLines, argumentLe, argumentValue, argumentNames,
    argumentSimulates⟩ :=
    argumentIH functions .word bindings indent first argumentRendered argumentKind
      argumentEquation fresh distinct
  have temp : TempIn first (argumentRendered.nextId + 1) (temporary argumentRendered.nextId) :=
    tempIn_temporary argumentLe (Nat.lt_succ_self _)
  refine ⟨argumentStatements ++ [.letDecl (temporary argumentRendered.nextId) .word
      (.call1 callee (.name value))], ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, argumentLines, Stmt.listLines, List.append_nil]
  · intro name same
    cases same
    exact Or.inr ⟨argumentRendered.nextId, rfl, argumentLe, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with mem | same | same | same
    · exact uses_mono (argumentNames name mem) (Nat.le_refl _) (Nat.le_succ _)
    · exact Or.inr (Or.inr (same ▸ temp))
    · subst same
      exact Or.inr (Or.inl (List.mem_of_getElem? found))
    · subst same
      exact uses_mono (argumentValue name valueFound).uses (Nat.le_refl _) (Nat.le_succ _)
  · dsimp only
    refine mresult_simulates (target := .word) (Or.inl rfl) fresh (fun context environment store
      scope outer admitted agree distinctCells lengthOk functionsOk => ?_) argumentLe
    obtain ⟨argumentCore, store₁, scope₁, outer₁, added₁, argumentEvaluates, argumentRepresents,
      argumentExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      argumentSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    rw [valueFound, Option.bind_some] at argumentRepresents
    obtain ⟨word, rfl, lookupValue⟩ := argumentRepresents
    obtain ⟨parameterType, resultType, body, captured, closureFound, behaves⟩ :=
      functionsOk (index - bindings.length) callee found
    obtain ⟨result, store₂, bodyEvaluates, grows, keepsStore, callResult⟩ := behaves word store₁
    have closureAt : environment[index]? =
        some (.closure parameterType resultType body captured) := by
      rw [List.getElem?_drop] at closureFound
      have position : bindings.length + (index - bindings.length) = index := by omega
      rwa [position] at closureFound
    refine ⟨.word result, .word result.val, store₂, scope₁, outer₁, added₁, ?_, ⟨result, rfl, rfl⟩,
      argumentExec, ?_, ?_, ?_, keeps₁, shape₁, names₁, addedTemp₁⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .apply (.var closureAt) argumentEvaluates bodyEvaluates
    · simp [Expr.eval, lookupValue, callResult]
    · exact agree₁.transfer (fun _ _ _ => rfl) fun _ location isCell =>
        keepsStore location (agree₁.cell_lt isCell)
    · exact frame₁.trans ⟨grows, fun location inBounds _ => keepsStore location inBounds⟩

/-! ### Conditionals -/

theorem MRepresents.sameType_zero {target : MTarget} (scalar : target = .word ∨ target = .bool)
    {core : CoreValue} {value : Value} (represents : MRepresents target core (some value)) :
    value.sameType (zeroValue target.scalar) = true := by
  rcases scalar with rfl | rfl
  · obtain ⟨_, _, same⟩ := represents
    cases same
    rfl
  · obtain ⟨_, _, same⟩ := represents
    cases same
    rfl

theorem zeroValue_admits_mutation {target : MTarget} (scalar : target = .word ∨ target = .bool) :
    (MTarget.localType target).admits (zeroValue target.scalar) = true := by
  rcases scalar with rfl | rfl <;> rfl

/-- The frames after a block are the enclosing frames, of the same shape. -/
theorem frames_after_block {frames : Frames} {scope : Scope} {outer : Frames}
    (shape : Frames.shape frames = Frames.shape (scope :: outer)) :
    ∃ scope' outer', frames = scope' :: outer' ∧ scope'.names = scope.names ∧
      Frames.shape outer' = Frames.shape outer := by
  match frames, shape with
  | scope' :: outer', same =>
      simp only [Frames.shape, List.map_cons, List.cons.injEq] at same
      exact ⟨scope', outer', rfl, same.1, same.2⟩
  | [], impossible => simp [Frames.shape] at impossible

/-- A Unit branch block runs in a fresh scope that is discarded afterwards;
only the cells of the bindings change in the enclosing frames. -/
theorem mbranch_unit {expression : CoreExpr} {functions : List String} {bindings : List Binding}
    {low high : Nat} {statements : List Stmt} {valueName : Option String}
    (simulates : MSimulates admits expression .unit functions bindings low high statements
      valueName)
    (fresh : NamesFresh bindings low) {context : Context}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    {scope : Scope} {outer : Frames} (admitted : admits context)
    (agree : BindingsAgree (scope :: outer) bindings environment store)
    (distinct : CellsDistinct bindings environment)
    (lengthOk : bindings.length ≤ environment.length)
    (functionsOk : MFunctionsAgree context functions (environment.drop bindings.length)) :
    ∃ (store' : Solcore.Core.Store) (top scope' : Scope) (outer' : Frames),
      Solcore.Core.Evaluates environment store expression.toCore .unit store' ∧
      Stmt.execList context ([] :: scope :: outer) statements = some (top :: scope' :: outer') ∧
      BindingsAgree (scope' :: outer') bindings environment store' ∧
      StoreFrame bindings environment store store' ∧
      scope'.names = scope.names ∧ Frames.shape outer' = Frames.shape outer ∧
      ∀ name, ¬ TempIn low high name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name = Frames.lookup (scope :: outer) name := by
  obtain ⟨coreValue, store', top, frames, added, evaluates, represents, exec, agree₁, frame,
    keeps, shape, topNames, addedTemp⟩ :=
    simulates context environment store [] (scope :: outer) admitted agree.enter distinct lengthOk
      functionsOk
  have unitCore : coreValue = .unit := represents
  subst unitCore
  obtain ⟨scope', outer', rfl, scopeNames, outerShape⟩ := frames_after_block shape
  have absent : ∀ name, ¬ TempIn low high name → name ∉ top.names := by
    intro name notTemp mem
    rw [topNames] at mem
    simp only [Scope.names, List.map_nil, List.append_nil] at mem
    exact notTemp (addedTemp name mem)
  refine ⟨store', top, scope', outer', evaluates, exec, ?_, frame, scopeNames, outerShape, ?_⟩
  · refine agree₁.transfer (fun index found named => ?_) (fun _ _ _ => rfl)
    exact (Frames.lookup_cons_of_not_mem (scope' :: outer')
      (absent found (not_tempIn_of_fresh (fresh index found named) (Nat.le_refl _)))).symm
  · intro name notTemp notCell
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') (absent name notTemp),
      keeps name notTemp notCell, Frames.lookup_nil_cons]

/-- A value branch block ends by assigning its value to the `if` result, which
was declared before the `if`. -/
theorem mbranch_value {expression : CoreExpr} {target : MTarget} {functions : List String}
    {bindings : List Binding} {low high : Nat} {statements : List Stmt} {valueName result : String}
    (scalar : target = .word ∨ target = .bool)
    (simulates : MSimulates admits expression target functions bindings low high statements
      (some valueName))
    (fresh : NamesFresh bindings low) (resultOutside : ¬ TempIn low high result)
    (resultNotBinding : ∀ index found, nameAt bindings index = some found → found ≠ result)
    {context : Context} {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    {scope : Scope} {outer : Frames} (admitted : admits context)
    (agree : BindingsAgree (scope :: outer) bindings environment store)
    (distinct : CellsDistinct bindings environment)
    (lengthOk : bindings.length ≤ environment.length)
    (functionsOk : MFunctionsAgree context functions (environment.drop bindings.length))
    (declared : Frames.lookup (scope :: outer) result = some (zeroValue target.scalar)) :
    ∃ (coreValue : CoreValue) (value : Value) (store' : Solcore.Core.Store) (top scope' : Scope)
      (outer' : Frames),
      Solcore.Core.Evaluates environment store expression.toCore coreValue store' ∧
      MRepresents target coreValue (some value) ∧
      Stmt.execList context ([] :: scope :: outer)
        (statements ++ [.assign result (.name valueName)]) = some (top :: scope' :: outer') ∧
      BindingsAgree (scope' :: outer') bindings environment store' ∧
      StoreFrame bindings environment store store' ∧
      scope'.names = scope.names ∧ Frames.shape outer' = Frames.shape outer ∧
      ∀ name, ¬ TempIn low high name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name =
          if result = name then some value else Frames.lookup (scope :: outer) name := by
  have resultNotCell : ∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord result) :=
    fun index found => resultNotBinding index result
      (by rw [nameAt_of_getElem? found]; rfl) rfl
  obtain ⟨coreValue, store', top₁, frames₁, added, evaluates, represents, exec, agree₁, frame,
    keeps, shape, topNames, addedTemp⟩ :=
    simulates context environment store [] (scope :: outer) admitted agree.enter distinct
      lengthOk functionsOk
  simp only [Option.bind_some] at represents
  obtain ⟨value, lookupValue, represents'⟩ := MRepresents.named scalar represents
  have resultFound : Frames.lookup (top₁ :: frames₁) result = some (zeroValue target.scalar) := by
    rw [keeps result resultOutside resultNotCell, Frames.lookup_nil_cons]
    exact declared
  obtain ⟨frames₂, assigned, shape₂, lookups⟩ :=
    Frames.assign_spec (frames := top₁ :: frames₁) value resultFound
  have shapeCons : Frames.shape frames₂ = top₁.names :: Frames.shape (scope :: outer) := by
    rw [shape₂]
    simp only [Frames.shape, List.map_cons] at shape ⊢
    rw [shape]
  obtain ⟨top₂, frames₃, rfl, topNames₂, shape₃⟩ := frames_after_block (outer := scope :: outer)
    (scope := top₁) (frames := frames₂) (by rw [shapeCons]; rfl)
  obtain ⟨scope', outer', rfl, scopeNames, outerShape⟩ := frames_after_block shape₃
  have absent : ∀ name, ¬ TempIn low high name → name ∉ top₂.names := by
    intro name notTemp mem
    rw [topNames₂, topNames] at mem
    simp only [Scope.names, List.map_nil, List.append_nil] at mem
    exact notTemp (addedTemp name mem)
  refine ⟨coreValue, value, store', top₂, scope', outer', evaluates, represents', ?_, ?_, frame,
    scopeNames, outerShape, ?_⟩
  · rw [Stmt.execList_append, exec]
    simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, resultFound,
      represents'.sameType_zero scalar, assigned]
  · refine agree₁.transfer (fun index found named => ?_) (fun _ _ _ => rfl)
    have notTemp := not_tempIn_of_fresh (last := high) (fresh index found named) (Nat.le_refl _)
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') (absent found notTemp), lookups found,
      if_neg (resultNotBinding index found named).symm]
  · intro name notTemp notCell
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') (absent name notTemp), lookups name,
      keeps name notTemp notCell, Frames.lookup_nil_cons]

theorem mRenderIH_ifE {condition yes no : CoreExpr} (conditionIH : MRenderIH admits condition)
    (yesIH : MRenderIH admits yes) (noIH : MRenderIH admits no) :
    MRenderIH admits (.ifE condition yes no) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨conditionKind, yesKind, noKind, _⟩ := MutationKinds.ifE accepted
  have targets : target = .unit ∨ (target = .word ∨ target = .bool) := by
    cases target <;> simp
  rcases targets with rfl | scalar
  · obtain ⟨tested, conditionValue, selected, fallback, testedEquation, conditionFound,
      selectedEquation, fallbackEquation, rfl⟩ := MutationEquations.ifE_unit_ok equation
    obtain ⟨cStatements, cLines, cLe, cValue, cNames, cSimulates⟩ :=
      conditionIH functions .bool bindings indent first tested conditionKind testedEquation fresh
        distinct
    obtain ⟨yStatements, yLines, yLe, _, yNames, ySimulates⟩ :=
      yesIH functions .unit bindings (indent + 4) tested.nextId selected yesKind selectedEquation
        (fresh.mono cLe) distinct
    obtain ⟨nStatements, nLines, nLe, _, nNames, nSimulates⟩ :=
      noIH functions .unit bindings (indent + 4) selected.nextId fallback noKind fallbackEquation
        (fresh.mono (by omega)) distinct
    refine ⟨cStatements ++ [.ifElse (.name conditionValue) yStatements nStatements], ?_,
      by dsimp only; omega, (fun _ same => by cases same), ?_, ?_⟩
    · simp only [Stmt.listLines_append, cLines, yLines, nLines, Stmt.listLines, Stmt.lines,
        Expr.print, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    · dsimp only
      intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with mem | (same | mem) | mem
      · exact uses_mono (cNames name mem) (Nat.le_refl _) (by omega)
      · subst same
        exact uses_mono (cValue name conditionFound).uses (Nat.le_refl _) (by omega)
      · exact uses_mono (yNames name mem) cLe (by omega)
      · exact uses_mono (nNames name mem) (by omega) (Nat.le_refl _)
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨cCore, store₁, scope₁, outer₁, added₁, cEvaluates, cRepresents, cExec, agree₁,
        frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        cSimulates context environment store scope outer admitted agree distinctCells lengthOk
          functionsOk
      rw [conditionFound, Option.bind_some] at cRepresents
      obtain ⟨flag, rfl, cLookup⟩ := cRepresents
      have addedOk : ∀ name ∈ added₁, TempIn first fallback.nextId name :=
        fun name mem => tempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
      cases flag with
      | true =>
          obtain ⟨store₂, top, scope₂, outer₂, yEvaluates, yExec, agree₂, frame₂, scopeNames,
            outerShape, keeps₂⟩ :=
            mbranch_unit ySimulates (fresh.mono cLe) admitted agree₁ distinctCells lengthOk
              functionsOk
          refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
            ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifTrue cEvaluates yEvaluates
          · rw [Stmt.execList_append, cExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, cLookup, yExec]
          · intro name notTemp notCell
            rw [keeps₂ name (fun temp => notTemp (tempIn_mono temp cLe (by omega))) notCell,
              keeps₁ name (fun temp => notTemp (tempIn_mono temp (Nat.le_refl _) (by omega)))
                notCell]
      | false =>
          obtain ⟨store₂, top, scope₂, outer₂, nEvaluates, nExec, agree₂, frame₂, scopeNames,
            outerShape, keeps₂⟩ :=
            mbranch_unit nSimulates (fresh.mono (by omega)) admitted agree₁ distinctCells lengthOk
              functionsOk
          refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
            ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifFalse cEvaluates nEvaluates
          · rw [Stmt.execList_append, cExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, cLookup, nExec]
          · intro name notTemp notCell
            rw [keeps₂ name (fun temp => notTemp (tempIn_mono temp (by omega) (Nat.le_refl _)))
                notCell,
              keeps₁ name (fun temp => notTemp (tempIn_mono temp (Nat.le_refl _) (by omega)))
                notCell]
  · obtain ⟨tested, conditionValue, selected, selectedValue, fallback, fallbackValue,
      testedEquation, conditionFound, selectedEquation, selectedFound, fallbackEquation,
      fallbackFound, rfl⟩ := MutationEquations.ifE_value_ok scalar equation
    obtain ⟨cStatements, cLines, cLe, cValue, cNames, cSimulates⟩ :=
      conditionIH functions .bool bindings indent first tested conditionKind testedEquation fresh
        distinct
    obtain ⟨yStatements, yLines, yLe, yValue, yNames, ySimulates⟩ :=
      yesIH functions target bindings (indent + 4) (tested.nextId + 1) selected yesKind
        selectedEquation (fresh.mono (by omega)) distinct
    obtain ⟨nStatements, nLines, nLe, nValue, nNames, nSimulates⟩ :=
      noIH functions target bindings (indent + 4) selected.nextId fallback noKind fallbackEquation
        (fresh.mono (by omega)) distinct
    have result : ∀ last, tested.nextId < last → TempIn first last (temporary tested.nextId) :=
      fun _ lt => tempIn_temporary cLe lt
    refine ⟨cStatements ++
        [.letDecl (temporary tested.nextId) (MTarget.localType target) (zeroExpr target.scalar),
          .ifElse (.name conditionValue)
            (yStatements ++ [.assign (temporary tested.nextId) (.name selectedValue)])
            (nStatements ++ [.assign (temporary tested.nextId) (.name fallbackValue)])],
      ?_, by dsimp only; omega, ?_, ?_, ?_⟩
    · simp only [Stmt.listLines_append, cLines, yLines, nLines, Stmt.listLines, Stmt.lines,
        Expr.print, zeroExpr_print, List.append_nil, List.append_assoc, List.cons_append,
        List.nil_append]
    · intro name same
      cases same
      exact Or.inr ⟨tested.nextId, rfl, cLe, by dsimp only; omega⟩
    · dsimp only
      intro name mem
      have zeroNames : (zeroExpr target.scalar).identifiers = [] := by
        rcases scalar with rfl | rfl <;> rfl
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, zeroNames, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at mem
      rcases mem with mem | same | (same | mem | same | same) | (mem | same | same)
      · exact uses_mono (cNames name mem) (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr (same ▸ result _ (by omega)))
      · subst same
        exact uses_mono (cValue name conditionFound).uses (Nat.le_refl _) (by omega)
      · exact uses_mono (yNames name mem) (by omega) (by omega)
      · exact Or.inr (Or.inr (same ▸ result _ (by omega)))
      · subst same
        exact uses_mono (yValue name selectedFound).uses (by omega) (by omega)
      · exact uses_mono (nNames name mem) (by omega) (Nat.le_refl _)
      · exact Or.inr (Or.inr (same ▸ result _ (by omega)))
      · subst same
        exact uses_mono (nValue name fallbackFound).uses (by omega) (Nat.le_refl _)
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨cCore, store₁, scope₁, outer₁, added₁, cEvaluates, cRepresents, cExec, agree₁,
        frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        cSimulates context environment store scope outer admitted agree distinctCells lengthOk
          functionsOk
      rw [conditionFound, Option.bind_some] at cRepresents
      obtain ⟨flag, rfl, cLookup⟩ := cRepresents
      have resultTemp := result (tested.nextId + 1) (Nat.lt_succ_self _)
      rw [selectedFound] at ySimulates
      rw [fallbackFound] at nSimulates
      have resultNotBinding : ∀ index found, nameAt bindings index = some found →
          found ≠ temporary tested.nextId :=
        fun _ _ named => fresh.ne_temporary named cLe
      have agreeDeclared := agree₁.declare (fresh.ne_temp resultTemp) (zeroValue target.scalar)
      have declared : Frames.lookup (((temporary tested.nextId, zeroValue target.scalar) ::
          scope₁) :: outer₁) (temporary tested.nextId) = some (zeroValue target.scalar) := by
        simp [Frames.lookup_declared]
      have conditionSurvives : temporary tested.nextId ≠ conditionValue := by
        intro same
        exact ((cValue conditionValue conditionFound).survives (last := tested.nextId + 1) fresh
          distinct cLe).1 (same ▸ tempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _))
      have conditionLookup : Frames.lookup (((temporary tested.nextId, zeroValue target.scalar) ::
          scope₁) :: outer₁) conditionValue = some (.bool flag) := by
        rw [Frames.lookup_declared, if_neg conditionSurvives]
        exact cLookup
      have prefixExec : Stmt.execList context (scope :: outer) (cStatements ++
          [.letDecl (temporary tested.nextId) (MTarget.localType target)
            (zeroExpr target.scalar)]) =
          some (((temporary tested.nextId, zeroValue target.scalar) :: scope₁) :: outer₁) := by
        rw [Stmt.execList_append, cExec]
        simp [Stmt.execList, Stmt.exec, zeroExpr_eval, zeroValue_admits_mutation scalar,
          Frames.declare]
      have keepsOutside : ∀ name, ¬ TempIn first fallback.nextId name →
          (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
          Frames.lookup (((temporary tested.nextId, zeroValue target.scalar) :: scope₁) :: outer₁)
            name = Frames.lookup (scope :: outer) name := by
        intro name notTemp notCell
        have different : temporary tested.nextId ≠ name := fun same =>
          notTemp (same ▸ result _ (by omega))
        rw [Frames.lookup_declared, if_neg different,
          keeps₁ name (fun temp => notTemp (tempIn_mono temp (Nat.le_refl _) (by omega))) notCell]
      have scopeNames₁ :
          Scope.names ((temporary tested.nextId, zeroValue target.scalar) :: scope₁) =
          (temporary tested.nextId :: added₁) ++ scope.names := by
        show temporary tested.nextId :: scope₁.names = _
        rw [names₁]
        rfl
      have addedOk : ∀ name ∈ temporary tested.nextId :: added₁,
          TempIn first fallback.nextId name := by
        intro name mem
        rcases List.mem_cons.mp mem with same | mem
        · exact same ▸ result _ (by omega)
        · exact tempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
      cases flag with
      | true =>
          obtain ⟨branchCore, value, store₂, top, scope₂, outer₂, branchEvaluates,
            branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
            mbranch_value scalar ySimulates (fresh.mono (by omega))
              (not_tempIn_of_tempIn resultTemp (Or.inl (Nat.le_refl _))) resultNotBinding
              admitted agreeDeclared distinctCells lengthOk functionsOk declared
          refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
            ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
            scopeNames.trans scopeNames₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifTrue cEvaluates branchEvaluates
          · rw [Option.bind_some, lookups _ (not_tempIn_of_tempIn resultTemp
              (Or.inl (Nat.le_refl _))) (fresh.not_cell resultTemp), if_pos rfl]
            exact branchRepresents
          · rw [List.append_cons, Stmt.execList_append, prefixExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, conditionLookup, branchExec]
          · intro name notTemp notCell
            have different : temporary tested.nextId ≠ name := fun same =>
              notTemp (same ▸ result _ (by omega))
            rw [lookups name (fun temp => notTemp (tempIn_mono temp (by omega) (by omega)))
              notCell, if_neg different, keepsOutside name notTemp notCell]
      | false =>
          obtain ⟨branchCore, value, store₂, top, scope₂, outer₂, branchEvaluates,
            branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
            mbranch_value scalar nSimulates (fresh.mono (by omega))
              (not_tempIn_of_tempIn resultTemp (Or.inl (by omega))) resultNotBinding
              admitted agreeDeclared distinctCells lengthOk functionsOk declared
          refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
            ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
            scopeNames.trans scopeNames₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifFalse cEvaluates branchEvaluates
          · rw [Option.bind_some, lookups _ (not_tempIn_of_tempIn resultTemp
              (Or.inl (by omega))) (fresh.not_cell resultTemp), if_pos rfl]
            exact branchRepresents
          · rw [List.append_cons, Stmt.execList_append, prefixExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, conditionLookup, branchExec]
          · intro name notTemp notCell
            have different : temporary tested.nextId ≠ name := fun same =>
              notTemp (same ▸ result _ (by omega))
            rw [lookups name (fun temp => notTemp (tempIn_mono temp (by omega) (Nat.le_refl _)))
              notCell, if_neg different, keepsOutside name notTemp notCell]

/-! ### The structural induction -/

theorem mRenderIH_let {initializer body : CoreExpr} (initializerIH : MRenderIH admits initializer)
    (cellIH : ∀ inner, initializer = .newCell .word inner → MRenderIH admits inner)
    (bodyIH : MRenderIH admits body) : MRenderIH admits (.letE initializer body) := by
  by_cases cell : ∃ inner, initializer = .newCell .word inner
  · obtain ⟨inner, rfl⟩ := cell
    exact mRenderIH_newCellLet (cellIH inner rfl) bodyIH
  · exact mRenderIH_letE (fun inner same => cell ⟨inner, same⟩) initializerIH bodyIH

/-- An expression the profile never accepts at a scalar or Unit target. -/
theorem mRenderIH_rejected (expression : CoreExpr)
    (rejected : ∀ locals prior, initializerKind? locals prior expression = none ∨
      initializerKind? locals prior expression = some .cellWord) :
    MRenderIH admits expression := by
  intro functions target bindings _ _ _ accepted
  rcases rejected (bindings.map Binding.kind) functions.length with none | cell
  · rw [none] at accepted
    cases accepted
  · rw [cell] at accepted
    cases target <;> cases accepted

/-- An expression the actual renderer always rejects. -/
theorem mRenderIH_error (expression : CoreExpr)
    (fails : ∀ (functions : List String) (target : MTarget) (bindings : List Binding)
      (indent first : Nat) (rendered : MRendered),
      MutationRenderer.render functions target bindings indent first expression ≠ .ok rendered) :
    MRenderIH admits expression := by
  intro functions target bindings indent first rendered _ equation
  exact absurd equation (fails functions target bindings indent first rendered)

theorem mRenderIH_applyAny {function argument : CoreExpr} (argumentIH : MRenderIH admits argument) :
    MRenderIH admits (.apply function argument) := by
  cases function
  case var index => exact mRenderIH_apply argumentIH
  all_goals exact mRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem mRenderIH_loadCellAny {reference : CoreExpr} : MRenderIH admits (.loadCell reference) := by
  cases reference
  case var index => exact mRenderIH_loadCell index
  all_goals exact mRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem mRenderIH_storeCellAny {reference value : CoreExpr} (valueIH : MRenderIH admits value) :
    MRenderIH admits (.storeCell reference value) := by
  cases reference
  case var index => exact mRenderIH_storeCell index valueIH
  all_goals exact mRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem mRenderIH_newCell (elementType : Solcore.Core.Wire.Ty) (inner : CoreExpr) :
    MRenderIH admits (.newCell elementType inner) := by
  refine mRenderIH_rejected _ fun locals prior => ?_
  cases found : initializerKind? locals prior (.newCell elementType inner) with
  | none => exact Or.inl rfl
  | some kind =>
      right
      cases elementType
      all_goals first
        | rw [(MutationKinds.newCell found).1]
        | cases found

/-- Every expression that the mutation profile accepts and the actual renderer
renders satisfies its rendering specification. The second component is the
specification for the initializer of a direct `newCell` let. -/
theorem mutation_render_spec : (expression : CoreExpr) →
    MRenderIH admits expression ∧
      ∀ inner, expression = .newCell .word inner → MRenderIH admits inner
  | .word value => ⟨mRenderIH_word value, fun _ same => by cases same⟩
  | .bool value => ⟨mRenderIH_bool value, fun _ same => by cases same⟩
  | .unit => ⟨mRenderIH_unit, fun _ same => by cases same⟩
  | .var index => ⟨mRenderIH_var index, fun _ same => by cases same⟩
  | .letE initializer body =>
      ⟨mRenderIH_let (mutation_render_spec initializer).1 (mutation_render_spec initializer).2
        (mutation_render_spec body).1, fun _ same => by cases same⟩
  | .ifE condition yes no =>
      ⟨mRenderIH_ifE (mutation_render_spec condition).1 (mutation_render_spec yes).1
        (mutation_render_spec no).1, fun _ same => by cases same⟩
  | .unary _ operand => ⟨mRenderIH_unary (mutation_render_spec operand).1,
      fun _ same => by cases same⟩
  | .binary _ left right =>
      ⟨mRenderIH_binary (mutation_render_spec left).1 (mutation_render_spec right).1,
        fun _ same => by cases same⟩
  | .ternary _ _ _ _ =>
      ⟨mRenderIH_error _ (fun _ _ _ _ _ _ equation => by cases equation),
        fun _ same => by cases same⟩
  | .apply _ argument => ⟨mRenderIH_applyAny (mutation_render_spec argument).1,
      fun _ same => by cases same⟩
  | .newCell elementType inner => ⟨mRenderIH_newCell elementType inner, fun _ same => by
      cases same
      exact (mutation_render_spec inner).1⟩
  | .loadCell _ => ⟨mRenderIH_loadCellAny, fun _ same => by cases same⟩
  | .storeCell _ value => ⟨mRenderIH_storeCellAny (mutation_render_spec value).1,
      fun _ same => by cases same⟩
  | .integer _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .pair _ _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .first _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .second _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .lambda _ _ _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .inLeft _ _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .inRight _ _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .caseE _ _ _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .construct _ _ => ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .matchData _ _ _ _ =>
      ⟨mRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩

end

end Solcore.Synthesis.Source.ScalarMeaning
end
