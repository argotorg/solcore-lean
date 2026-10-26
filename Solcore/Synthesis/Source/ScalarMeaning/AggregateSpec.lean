import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Source.AggregateRenderer
import Solcore.Synthesis.Source.ScalarMeaning.MutationSpec
import Solcore.Synthesis.Source.ScalarMeaning.PrimitivePreservation

/-! The simulation invariant for the aggregate renderer. As for private
mutation, Core keeps each mutable Word local in its store and binds a cell
reference, while the source keeps the Word in an `sc_c<n>` local. Word pairs
and sums are immutable: a pair binding holds a `(word, word)` value and a sum
binding an `inl` or `inr` value. A `case` payload or a projected component is
bound in a match case scope under a fresh `sc_p<n>` name. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Source.AggregateRenderer (Binding)

abbrev ATarget := Solcore.Synthesis.Core.Aggregates.Target
abbrev ARendered := AggregateRenderer.Rendered

/-- The renderer's pattern names `sc_p0`, `sc_p1`, ... -/
def payloadTemp (index : Nat) : String := "sc_p" ++ toString index

theorem payloadTemp_injective {first second : Nat}
    (same : payloadTemp first = payloadTemp second) : first = second := by
  have chars := congrArg String.toList same
  simp only [payloadTemp, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr,
    List.append_cancel_left_eq] at chars
  have values := congrArg (fun digits => Nat.ofDigitChars 10 digits 0) chars
  simpa using values

theorem payloadTemp_ne_temporary (first second : Nat) : payloadTemp first ≠ temporary second := by
  intro same
  have chars := congrArg String.toList same
  simp [payloadTemp, temporary] at chars

theorem payloadTemp_ne_cellTemp (first second : Nat) : payloadTemp first ≠ cellTemp second := by
  intro same
  have chars := congrArg String.toList same
  simp [payloadTemp, cellTemp] at chars

/-! ### Targets and values -/

/-- The source type of a value target. -/
def ATarget.localType : ATarget → LocalType
  | .bool => .bool
  | .wordPair => .wordPair
  | .wordSum => .wordSum
  | _ => .word

/-- The binding of a `let` or of a `case` payload of the given target. It is
the renderer's private `bindingFor`. -/
def valueBinding : ATarget → String → Binding
  | .word, name => .word name
  | .bool, name => .bool name
  | .unit, _ => .unit
  | .wordPair, name => .wordPair name
  | .wordSum, name => .wordSum name

/-- How a source value represents a Core value of a value target. Core tags a
sum with the type of its other side; the source sum has none. -/
def AValue : ATarget → CoreValue → Value → Prop
  | .word, core, source =>
      ∃ word : Solcore.Core.Word, core = .word word ∧ source = .word word.val
  | .bool, core, source => ∃ flag : Bool, core = .bool flag ∧ source = .bool flag
  | .unit, _, _ => False
  | .wordPair, core, source =>
      ∃ first second : Solcore.Core.Word,
        core = .pair (.word first) (.word second) ∧ source = .pair first.val second.val
  | .wordSum, core, source =>
      (∃ (type : Solcore.Core.Ty) (payload : Solcore.Core.Word),
        core = .inLeft type (.word payload) ∧ source = .inl payload.val) ∨
      ∃ (type : Solcore.Core.Ty) (payload : Solcore.Core.Word),
        core = .inRight type (.word payload) ∧ source = .inr payload.val

/-- Representation of a Core value of an aggregate target by the value a
source name holds; Unit needs no source value. -/
def ARepresents : ATarget → CoreValue → Option Value → Prop
  | .unit, core, _ => core = .unit
  | target, core, source => ∃ value, source = some value ∧ AValue target core value

theorem ARepresents.of_value {target : ATarget} {core : CoreValue} {value : Value}
    (represents : AValue target core value) : ARepresents target core (some value) := by
  cases target
  case unit => exact represents.elim
  all_goals exact ⟨value, rfl, represents⟩

theorem ARepresents.value {target : ATarget} (valued : target ≠ .unit) {core : CoreValue}
    {source : Option Value} (represents : ARepresents target core source) :
    ∃ value, source = some value ∧ AValue target core value := by
  cases target
  case unit => exact absurd rfl valued
  all_goals exact represents

theorem AValue.admits {target : ATarget} {core : CoreValue} {value : Value}
    (represents : AValue target core value) : target.localType.admits value = true := by
  cases target
  case word =>
    obtain ⟨_, _, rfl⟩ := represents
    rfl
  case bool =>
    obtain ⟨_, _, rfl⟩ := represents
    rfl
  case unit => exact represents.elim
  case wordPair =>
    obtain ⟨_, _, _, rfl⟩ := represents
    rfl
  case wordSum =>
    rcases represents with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

theorem AValue.sameType {target : ATarget} {core core' : CoreValue} {value value' : Value}
    (represents : AValue target core value) (represents' : AValue target core' value') :
    value.sameType value' = true := by
  cases target
  case word =>
    obtain ⟨_, _, rfl⟩ := represents
    obtain ⟨_, _, rfl⟩ := represents'
    rfl
  case bool =>
    obtain ⟨_, _, rfl⟩ := represents
    obtain ⟨_, _, rfl⟩ := represents'
    rfl
  case unit => exact represents.elim
  case wordPair =>
    obtain ⟨_, _, _, rfl⟩ := represents
    obtain ⟨_, _, _, rfl⟩ := represents'
    rfl
  case wordSum =>
    rcases represents with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
      rcases represents' with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

/-! ### Bindings and names -/

/-- The source name of a binding; Unit bindings have none. -/
def abindingName? : Binding → Option String
  | .word name | .bool name | .cellWord name | .wordPair name | .wordSum name => some name
  | .unit => none

/-- The source name of the binding at `index`, if any. -/
def anameAt (bindings : List Binding) (index : Nat) : Option String :=
  (bindings[index]?).bind abindingName?

/-- `name` is no value, cell or pattern temporary numbered `next` or later. -/
def AFreshBefore (next : Nat) (name : String) : Prop :=
  ∀ index, (name = temporary index ∨ name = cellTemp index ∨ name = payloadTemp index) →
    index < next

/-- `name` is a value, cell or pattern temporary numbered in `[first, last)`. -/
def ATempIn (first last : Nat) (name : String) : Prop :=
  ∃ index, (name = temporary index ∨ name = cellTemp index ∨ name = payloadTemp index) ∧
    first ≤ index ∧ index < last

/-- Every named binding is older than `first`. -/
def ANamesFresh (bindings : List Binding) (first : Nat) : Prop :=
  ∀ index name, anameAt bindings index = some name → AFreshBefore first name

/-- Distinct bindings have distinct source names. -/
def ANamesDistinct (bindings : List Binding) : Prop :=
  ∀ first second name, anameAt bindings first = some name → anameAt bindings second = some name →
    first = second

/-- How the Core value of a binding is held in the source frames and the Core
store. -/
def ABindingHolds (frames : Frames) (store : Solcore.Core.Store) : Binding → CoreValue → Prop
  | .word name, core => ARepresents .word core (frames.lookup name)
  | .bool name, core => ARepresents .bool core (frames.lookup name)
  | .wordPair name, core => ARepresents .wordPair core (frames.lookup name)
  | .wordSum name, core => ARepresents .wordSum core (frames.lookup name)
  | .unit, core => core = .unit
  | .cellWord name, core =>
      ∃ (elementType : Solcore.Core.Ty) (location : Nat) (word : Solcore.Core.Word),
        core = .cellRef elementType location ∧ store.read? location = some (.word word) ∧
        frames.lookup name = some (.word word.val)

/-- Core's de Bruijn environment, the Core store and the source frames agree on
every binding, nearest first. -/
def ABindingsAgree (frames : Frames) (bindings : List Binding)
    (environment : Solcore.Core.Environment) (store : Solcore.Core.Store) : Prop :=
  ∀ (index : Nat) (binding : Binding), bindings[index]? = some binding →
    ∃ core, environment[index]? = some core ∧ ABindingHolds frames store binding core

/-- The binding at `index` is a cell at `location`. -/
def ACellAt (bindings : List Binding) (environment : Solcore.Core.Environment)
    (index location : Nat) : Prop :=
  (∃ name, bindings[index]? = some (Binding.cellWord name)) ∧
    ∃ elementType, environment[index]? = some (.cellRef elementType location)

/-- Distinct cell bindings hold distinct store locations. -/
def ACellsDistinct (bindings : List Binding) (environment : Solcore.Core.Environment) : Prop :=
  ∀ first second location, ACellAt bindings environment first location →
    ACellAt bindings environment second location → first = second

/-- Evaluation may append cells and write the cells of the bindings; every other
existing location keeps its value. -/
def AStoreFrame (bindings : List Binding) (environment : Solcore.Core.Environment)
    (store store' : Solcore.Core.Store) : Prop :=
  store.length ≤ store'.length ∧ ∀ location, location < store.length →
    (∀ index, ¬ ACellAt bindings environment index location) →
    store'.read? location = store.read? location

/-- Executing `statements` from frames that agree with a Core environment and
store evaluates `expression` there. Afterwards the bindings still agree with the
final store, only cells of the bindings and new locations of the store differ,
and only temporaries in `[first, last)` and the cells of the bindings change in
the frames. -/
def ASimulates (admits : Context → Prop) (expression : CoreExpr) (target : ATarget)
    (functions : List String) (bindings : List Binding) (first last : Nat)
    (statements : List Stmt) (valueName : Option String) : Prop :=
  ∀ (context : Context) (environment : Solcore.Core.Environment)
    (store : Solcore.Core.Store) (scope : Scope) (outer : Frames),
    admits context →
    ABindingsAgree (scope :: outer) bindings environment store →
    ACellsDistinct bindings environment →
    bindings.length ≤ environment.length →
    MFunctionsAgree context functions (environment.drop bindings.length) →
    ∃ (coreValue : CoreValue) (store' : Solcore.Core.Store) (scope' : Scope) (outer' : Frames)
      (added : List String),
      Solcore.Core.Evaluates environment store expression.toCore coreValue store' ∧
      ARepresents target coreValue (valueName.bind (Frames.lookup (scope' :: outer'))) ∧
      Stmt.execList context (scope :: outer) statements = some (scope' :: outer') ∧
      ABindingsAgree (scope' :: outer') bindings environment store' ∧
      AStoreFrame bindings environment store store' ∧
      (∀ name, ¬ ATempIn first last name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name = Frames.lookup (scope :: outer) name) ∧
      Frames.shape outer' = Frames.shape outer ∧
      scope'.names = added ++ scope.names ∧
      (∀ name ∈ added, ATempIn first last name)

/-- A value name is a value binding or a value temporary in range, never a
cell. -/
def AValueName (bindings : List Binding) (first last : Nat) (name : String) : Prop :=
  (∃ (index : Nat) (target : ATarget), target ≠ .unit ∧
      bindings[index]? = some (valueBinding target name)) ∨
    ∃ index, name = temporary index ∧ first ≤ index ∧ index < last

/-- The source names a rendered statement list may use: bindings, helpers,
temporaries in range, raw opcode aliases and `tobool`. -/
def AUses (bindings : List Binding) (functions : List String) (first last : Nat)
    (name : String) : Prop :=
  (∃ index, anameAt bindings index = some name) ∨ name ∈ functions ∨ ATempIn first last name ∨
    name ∈ primitiveCallees

/-- What the aggregate renderer establishes for one rendered expression. -/
def ARenderSpec (admits : Context → Prop) (expression : CoreExpr) (target : ATarget)
    (functions : List String) (bindings : List Binding) (indent first : Nat)
    (rendered : ARendered) : Prop :=
  ∃ statements : List Stmt,
    rendered.lines = Stmt.listLines indent statements ∧
    first ≤ rendered.nextId ∧
    (∀ name, rendered.value = some name → AValueName bindings first rendered.nextId name) ∧
    (∀ name ∈ Stmt.listIdentifiers statements,
      AUses bindings functions first rendered.nextId name) ∧
    ASimulates admits expression target functions bindings first rendered.nextId statements
      rendered.value

/-- An expression whose rendering may print a raw opcode alias needs a call
context in which the aliases and `tobool` mean their opcodes. -/
def AliasesReady (expression : CoreExpr) (context : Context) : Prop :=
  AggregateRenderer.usesOpcodeAliases expression = true → PrimitiveContext context

def ARenderIH (expression : CoreExpr) : Prop :=
  ∀ (admits : Context → Prop), (∀ context, admits context → AliasesReady expression context) →
  ∀ (functions : List String) (target : ATarget) (bindings : List Binding) (indent first : Nat)
    (rendered : ARendered),
    Solcore.Synthesis.Core.Aggregates.initializerKind? (bindings.map Binding.kind)
      functions.length expression = some target.toLocal →
    AggregateRenderer.render functions target bindings indent first expression = .ok rendered →
    ANamesFresh bindings first →
    ANamesDistinct bindings →
    ARenderSpec admits expression target functions bindings indent first rendered

/-! ### Temporaries -/

theorem aTempIn_temporary {first last index : Nat} (low : first ≤ index) (high : index < last) :
    ATempIn first last (temporary index) :=
  ⟨index, Or.inl rfl, low, high⟩

theorem aTempIn_cellTemp {first last index : Nat} (low : first ≤ index) (high : index < last) :
    ATempIn first last (cellTemp index) :=
  ⟨index, Or.inr (Or.inl rfl), low, high⟩

theorem aTempIn_payloadTemp {first last index : Nat} (low : first ≤ index) (high : index < last) :
    ATempIn first last (payloadTemp index) :=
  ⟨index, Or.inr (Or.inr rfl), low, high⟩

theorem aTempIn_mono {first last first' last' : Nat} {name : String}
    (temp : ATempIn first last name) (low : first' ≤ first) (high : last ≤ last') :
    ATempIn first' last' name := by
  obtain ⟨index, same, lower, upper⟩ := temp
  exact ⟨index, same, by omega, by omega⟩

theorem atemp_index_eq {first second : Nat} {name : String}
    (one : name = temporary first ∨ name = cellTemp first ∨ name = payloadTemp first)
    (two : name = temporary second ∨ name = cellTemp second ∨ name = payloadTemp second) :
    first = second := by
  rcases one with rfl | rfl | rfl <;> rcases two with same | same | same
  · exact temporary_injective same
  · exact absurd same.symm (cellTemp_ne_temporary _ _)
  · exact absurd same.symm (payloadTemp_ne_temporary _ _)
  · exact absurd same (cellTemp_ne_temporary _ _)
  · exact cellTemp_injective same
  · exact absurd same.symm (payloadTemp_ne_cellTemp _ _)
  · exact absurd same (payloadTemp_ne_temporary _ _)
  · exact absurd same (payloadTemp_ne_cellTemp _ _)
  · exact payloadTemp_injective same

/-- A temporary in one range is not in a disjoint range. -/
theorem not_aTempIn_of_aTempIn {first last first' last' : Nat} {name : String}
    (temp : ATempIn first last name) (disjoint : last ≤ first' ∨ last' ≤ first) :
    ¬ ATempIn first' last' name := by
  rintro ⟨index', same', lower', upper'⟩
  obtain ⟨index, same, lower, upper⟩ := temp
  have := atemp_index_eq same same'
  omega

theorem not_aTempIn_of_fresh {next first last : Nat} {name : String}
    (fresh : AFreshBefore next name) (le : next ≤ first) : ¬ ATempIn first last name := by
  rintro ⟨index, same, lower, _⟩
  have := fresh index same
  omega

theorem aFreshBefore_mono {first second : Nat} {name : String}
    (fresh : AFreshBefore first name) (le : first ≤ second) : AFreshBefore second name :=
  fun index same => Nat.lt_of_lt_of_le (fresh index same) le

theorem ANamesFresh.mono {bindings : List Binding} {first second : Nat}
    (fresh : ANamesFresh bindings first) (le : first ≤ second) : ANamesFresh bindings second :=
  fun index name found => aFreshBefore_mono (fresh index name found) le

theorem ANamesFresh.ne_temp {bindings : List Binding} {first last : Nat} {name : String}
    (fresh : ANamesFresh bindings first) (temp : ATempIn first last name) :
    ∀ index found, anameAt bindings index = some found → found ≠ name := by
  intro index found named same
  subst same
  exact not_aTempIn_of_fresh (fresh index found named) (Nat.le_refl _) temp

/-! ### Names of bindings -/

theorem anameAt_cons_zero (binding : Binding) (bindings : List Binding) :
    anameAt (binding :: bindings) 0 = abindingName? binding := by
  simp [anameAt]

theorem anameAt_cons_succ (binding : Binding) (bindings : List Binding) (index : Nat) :
    anameAt (binding :: bindings) (index + 1) = anameAt bindings index := by
  simp [anameAt]

theorem anameAt_of_getElem? {bindings : List Binding} {index : Nat} {binding : Binding}
    (found : bindings[index]? = some binding) : anameAt bindings index = abindingName? binding := by
  simp [anameAt, found]

theorem valueBinding_name {target : ATarget} (valued : target ≠ .unit) (name : String) :
    abindingName? (valueBinding target name) = some name := by
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

theorem valueBinding_ne_cell {target : ATarget} (name other : String) :
    valueBinding target name ≠ .cellWord other := by
  cases target <;> simp [valueBinding]

theorem valueBinding_kind {target : ATarget} (valued : target ≠ .unit) (name : String) :
    (valueBinding target name).kind = target.toLocal := by
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

/-- No binding is a cell named `name` when `name` is a fresh temporary. -/
theorem ANamesFresh.not_cell {bindings : List Binding} {first last : Nat} {name : String}
    (fresh : ANamesFresh bindings first) (temp : ATempIn first last name) :
    ∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name) := by
  intro index found
  exact fresh.ne_temp temp index name (by rw [anameAt_of_getElem? found]; rfl) rfl

/-- Adding a binding named by a fresh temporary keeps the names fresh. -/
theorem ANamesFresh.cons {bindings : List Binding} {first next : Nat} {binding : Binding}
    (fresh : ANamesFresh bindings first) (le : first ≤ next)
    (named : ∀ name, abindingName? binding = some name → AFreshBefore next name) :
    ANamesFresh (binding :: bindings) next := by
  intro index name found
  cases index with
  | zero =>
      rw [anameAt_cons_zero] at found
      exact named name found
  | succ index =>
      rw [anameAt_cons_succ] at found
      exact aFreshBefore_mono (fresh index name found) le

/-- Adding a binding named by a temporary numbered `first` or later keeps the
names distinct. -/
theorem ANamesDistinct.cons {bindings : List Binding} {first : Nat} {binding : Binding}
    (distinct : ANamesDistinct bindings) (fresh : ANamesFresh bindings first)
    (named : ∀ name, abindingName? binding = some name → ∃ index,
      (name = temporary index ∨ name = cellTemp index ∨ name = payloadTemp index) ∧
        first ≤ index) :
    ANamesDistinct (binding :: bindings) := by
  have newName : ∀ index name, anameAt bindings index = some name →
      abindingName? binding = some name → False := by
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
          rw [anameAt_cons_zero] at one
          rw [anameAt_cons_succ] at two
          exact (newName second' name two one).elim
  | succ first' =>
      cases second' with
      | zero =>
          rw [anameAt_cons_succ] at one
          rw [anameAt_cons_zero] at two
          exact (newName first' name one two).elim
      | succ second' =>
          rw [anameAt_cons_succ] at one two
          exact congrArg (· + 1) (distinct first' second' name one two)

/-- A temporary binding numbered `index` is fresh before `index + 1`. -/
theorem temporary_fresh (index : Nat) : AFreshBefore (index + 1) (temporary index) := by
  intro other same
  rcases same with same | same | same
  · have := temporary_injective same
    omega
  · exact absurd same (cellTemp_ne_temporary _ _).symm
  · exact absurd same (payloadTemp_ne_temporary _ _).symm

theorem cellTemp_fresh (index : Nat) : AFreshBefore (index + 1) (cellTemp index) := by
  intro other same
  rcases same with same | same | same
  · exact absurd same (cellTemp_ne_temporary _ _)
  · have := cellTemp_injective same
    omega
  · exact absurd same (payloadTemp_ne_cellTemp _ _).symm

theorem payloadTemp_fresh (index : Nat) : AFreshBefore (index + 1) (payloadTemp index) := by
  intro other same
  rcases same with same | same | same
  · exact absurd same (payloadTemp_ne_temporary _ _)
  · exact absurd same (payloadTemp_ne_cellTemp _ _)
  · have := payloadTemp_injective same
    omega

/-! ### Agreement of bindings -/

/-- Agreement carries over when every binding name keeps its lookup and every
cell keeps its stored Word. -/
theorem ABindingsAgree.transfer {frames frames' : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store store' : Solcore.Core.Store}
    (agree : ABindingsAgree frames bindings environment store)
    (sameNames : ∀ index name, anameAt bindings index = some name →
      frames'.lookup name = frames.lookup name)
    (sameCells : ∀ index location, ACellAt bindings environment index location →
      store'.read? location = store.read? location) :
    ABindingsAgree frames' bindings environment store' := by
  intro index binding found
  obtain ⟨core, inEnvironment, holds⟩ := agree index binding found
  refine ⟨core, inEnvironment, ?_⟩
  have named := anameAt_of_getElem? found
  cases binding with
  | word name =>
      show ARepresents .word core (frames'.lookup name)
      rw [sameNames index name named]
      exact holds
  | bool name =>
      show ARepresents .bool core (frames'.lookup name)
      rw [sameNames index name named]
      exact holds
  | wordPair name =>
      show ARepresents .wordPair core (frames'.lookup name)
      rw [sameNames index name named]
      exact holds
  | wordSum name =>
      show ARepresents .wordSum core (frames'.lookup name)
      rw [sameNames index name named]
      exact holds
  | unit => exact holds
  | cellWord name =>
      obtain ⟨elementType, location, word, rfl, read, lookup⟩ := holds
      refine ⟨elementType, location, word, rfl, ?_, ?_⟩
      · rw [sameCells index location ⟨⟨name, found⟩, elementType, inEnvironment⟩]
        exact read
      · rw [sameNames index name named]
        exact lookup

theorem ABindingsAgree.tail {frames : Frames} {binding : Binding} {bindings : List Binding}
    {core : CoreValue} {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree frames (binding :: bindings) (core :: environment) store) :
    ABindingsAgree frames bindings environment store := by
  intro index found inBindings
  obtain ⟨value, inEnvironment, holds⟩ := agree (index + 1) found (by simpa using inBindings)
  exact ⟨value, by simpa using inEnvironment, holds⟩

theorem ABindingsAgree.cons {frames : Frames} {binding : Binding} {bindings : List Binding}
    {core : CoreValue} {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree frames bindings environment store)
    (holds : ABindingHolds frames store binding core) :
    ABindingsAgree frames (binding :: bindings) (core :: environment) store := by
  intro index found inBindings
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at inBindings
      subst inBindings
      exact ⟨core, rfl, holds⟩
  | succ index =>
      obtain ⟨value, inEnvironment, holdsRest⟩ := agree index found (by simpa using inBindings)
      exact ⟨value, by simpa using inEnvironment, holdsRest⟩

theorem ABindingsAgree.declare {scope : Scope} {outer : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree (scope :: outer) bindings environment store) {name : String}
    (fresh : ∀ index found, anameAt bindings index = some found → found ≠ name) (value : Value) :
    ABindingsAgree (((name, value) :: scope) :: outer) bindings environment store :=
  agree.transfer (fun index found named => by
      rw [Frames.lookup_declared, if_neg (fun same => fresh index found named same.symm)])
    (fun _ _ _ => rfl)

/-- Entering a block scope keeps the agreement when the block's first names
are not binding names. -/
theorem ABindingsAgree.enter {scope : Scope} {outer : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree (scope :: outer) bindings environment store) (top : Scope)
    (absent : ∀ index name, anameAt bindings index = some name → name ∉ top.names) :
    ABindingsAgree (top :: scope :: outer) bindings environment store :=
  agree.transfer (fun index name named =>
      Frames.lookup_cons_of_not_mem (scope :: outer) (absent index name named))
    (fun _ _ _ => rfl)

/-- Leaving a block scope keeps the agreement when the block declared no
binding name. -/
theorem ABindingsAgree.leave {top scope : Scope} {outer : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree (top :: scope :: outer) bindings environment store)
    (absent : ∀ index name, anameAt bindings index = some name → name ∉ top.names) :
    ABindingsAgree (scope :: outer) bindings environment store :=
  agree.transfer (fun index name named =>
      (Frames.lookup_cons_of_not_mem (scope :: outer) (absent index name named)).symm)
    (fun _ _ _ => rfl)

theorem ACellAt.cons {bindings : List Binding} {environment : Solcore.Core.Environment}
    {binding : Binding} {core : CoreValue} {index location : Nat}
    (cell : ACellAt bindings environment index location) :
    ACellAt (binding :: bindings) (core :: environment) (index + 1) location := by
  obtain ⟨⟨name, found⟩, elementType, inEnvironment⟩ := cell
  exact ⟨⟨name, by simpa using found⟩, elementType, by simpa using inEnvironment⟩

theorem ACellAt.of_cons {bindings : List Binding} {environment : Solcore.Core.Environment}
    {binding : Binding} {core : CoreValue} {index location : Nat}
    (cell : ACellAt (binding :: bindings) (core :: environment) (index + 1) location) :
    ACellAt bindings environment index location := by
  obtain ⟨⟨name, found⟩, elementType, inEnvironment⟩ := cell
  exact ⟨⟨name, by simpa using found⟩, elementType, by simpa using inEnvironment⟩

/-- Every cell of agreeing bindings is a location of the store. -/
theorem ABindingsAgree.cell_lt {frames : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree frames bindings environment store) {index location : Nat}
    (cell : ACellAt bindings environment index location) : location < store.length := by
  obtain ⟨⟨name, found⟩, elementType, inEnvironment⟩ := cell
  obtain ⟨core, inEnvironment', holds⟩ := agree index _ found
  rw [inEnvironment] at inEnvironment'
  cases inEnvironment'
  obtain ⟨_, location', word, same, read, _⟩ := holds
  cases same
  simp only [Solcore.Core.Store.read?] at read
  exact (List.getElem?_eq_some_iff.mp read).1

theorem ACellsDistinct.cons_value {binding : Binding} {bindings : List Binding}
    {core : CoreValue} {environment : Solcore.Core.Environment}
    (distinct : ACellsDistinct bindings environment) (notCell : ∀ name, binding ≠ .cellWord name) :
    ACellsDistinct (binding :: bindings) (core :: environment) := by
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

theorem AStoreFrame.refl (bindings : List Binding) (environment : Solcore.Core.Environment)
    (store : Solcore.Core.Store) : AStoreFrame bindings environment store store :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem AStoreFrame.trans {bindings : List Binding} {environment : Solcore.Core.Environment}
    {store store' store'' : Solcore.Core.Store}
    (first : AStoreFrame bindings environment store store')
    (second : AStoreFrame bindings environment store' store'') :
    AStoreFrame bindings environment store store'' := by
  refine ⟨Nat.le_trans first.1 second.1, fun location inBounds notCell => ?_⟩
  rw [second.2 location (Nat.lt_of_lt_of_le inBounds first.1) notCell,
    first.2 location inBounds notCell]

/-- A frame of the extended bindings is a frame of the original ones when the
new binding is no cell. -/
theorem AStoreFrame.of_cons {binding : Binding} {bindings : List Binding} {core : CoreValue}
    {environment : Solcore.Core.Environment} {store store' : Solcore.Core.Store}
    (frame : AStoreFrame (binding :: bindings) (core :: environment) store store')
    (notCell : ∀ name, binding ≠ .cellWord name) :
    AStoreFrame bindings environment store store' := by
  refine ⟨frame.1, fun location inBounds notCells => frame.2 location inBounds ?_⟩
  intro index cell
  cases index with
  | zero =>
      obtain ⟨⟨name, found⟩, _⟩ := cell
      exact notCell name (by simpa using found)
  | succ index => exact notCells index cell.of_cons

/-! ### Value names -/

theorem AValueName.mono {bindings : List Binding} {first last first' last' : Nat}
    {name : String} (value : AValueName bindings first last name) (low : first' ≤ first)
    (high : last ≤ last') : AValueName bindings first' last' name := by
  rcases value with found | ⟨index, rfl, lower, upper⟩
  · exact Or.inl found
  · exact Or.inr ⟨index, rfl, by omega, by omega⟩

theorem AValueName.uses {bindings : List Binding} {functions : List String} {first last : Nat}
    {name : String} (value : AValueName bindings first last name) :
    AUses bindings functions first last name := by
  rcases value with ⟨index, target, valued, found⟩ | ⟨index, rfl, lower, upper⟩
  · exact Or.inl ⟨index, by rw [anameAt_of_getElem? found, valueBinding_name valued]⟩
  · exact Or.inr (Or.inr (Or.inl (aTempIn_temporary lower upper)))

/-- A value name keeps its value while later statements run: it is neither a
later temporary nor a cell. -/
theorem AValueName.survives {bindings : List Binding} {first middle last : Nat}
    {name : String} (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (le : first ≤ middle) (value : AValueName bindings first middle name) :
    ¬ ATempIn middle last name ∧
      ∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name) := by
  rcases value with ⟨position, target, valued, found⟩ | ⟨position, rfl, lower, upper⟩
  · have named : anameAt bindings position = some name := by
      rw [anameAt_of_getElem? found, valueBinding_name valued]
    refine ⟨fun temp => not_aTempIn_of_fresh (fresh position name named) le temp,
      fun index cell => ?_⟩
    have sameIndex := distinct index position name
      (by rw [anameAt_of_getElem? cell]; rfl) named
    subst sameIndex
    rw [cell] at found
    exact valueBinding_ne_cell name name (Option.some.inj found).symm
  · refine ⟨fun temp => not_aTempIn_of_aTempIn (aTempIn_temporary lower upper)
      (Or.inl (Nat.le_refl _)) temp, fun index cell => ?_⟩
    have := fresh index (temporary position) (by rw [anameAt_of_getElem? cell]; rfl) position
      (Or.inl rfl)
    omega

theorem AUses.mono {bindings : List Binding} {functions : List String}
    {first last first' last' : Nat} {name : String}
    (uses : AUses bindings functions first last name) (low : first' ≤ first)
    (high : last ≤ last') : AUses bindings functions first' last' name := by
  rcases uses with named | mem | temp | called
  · exact Or.inl named
  · exact Or.inr (Or.inl mem)
  · exact Or.inr (Or.inr (Or.inl (aTempIn_mono temp low high)))
  · exact Or.inr (Or.inr (Or.inr called))

/-- Identifiers of a body rendered under one more named binding. -/
theorem AUses.of_cons {bindings : List Binding} {functions : List String}
    {first middle last : Nat} {binding : Binding} {name : String}
    (uses : AUses (binding :: bindings) functions middle last name)
    (bound : ∀ found, abindingName? binding = some found → ATempIn first last found)
    (le : first ≤ middle) : AUses bindings functions first last name := by
  rcases uses with ⟨index, named⟩ | mem | temp | called
  · cases index with
    | zero =>
        rw [anameAt_cons_zero] at named
        exact Or.inr (Or.inr (Or.inl (bound name named)))
    | succ index =>
        rw [anameAt_cons_succ] at named
        exact Or.inl ⟨index, named⟩
  · exact Or.inr (Or.inl mem)
  · exact Or.inr (Or.inr (Or.inl (aTempIn_mono temp le (Nat.le_refl _))))
  · exact Or.inr (Or.inr (Or.inr called))

end Solcore.Synthesis.Source.ScalarMeaning
