import Solcore.Synthesis.Core.LocalMutationDAG
import Solcore.Synthesis.Source.MutationRenderer
import Solcore.Synthesis.Source.ScalarMeaning.Renderer

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
