import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Source.ScalarMeaning.Internal.Mutation
import Solcore.Synthesis.Source.ScalarMeaning.Internal.CallGraphs

/-!
# Aggregate proofs

The aggregate and aggregate call-graph renderers.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregateSpec
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregateEquations
/-! Equations for the actual `AggregateRenderer.render`, stated with the source
syntax and printer, and inversions of the aggregate profile's acceptance check
`initializerKind?`. Private helpers of the renderer and of the profile are
unfolded by definitional equality; nothing here re-implements them. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-- The aggregate target of a scalar target. -/
def ATarget.ofScalar : Target → ATarget
  | .word => .word
  | .bool => .bool

theorem ATarget.ofScalar_localType (scalar : Target) :
    (ATarget.ofScalar scalar).localType = LocalType.ofTarget scalar := by
  cases scalar <;> rfl

theorem ATarget.ofScalar_ne_unit (scalar : Target) : ATarget.ofScalar scalar ≠ .unit := by
  cases scalar <;> simp [ATarget.ofScalar]

/-- The zero value printed for an `if` or `case` result. -/
def azero : ATarget → Expr
  | .bool => .bool false
  | .wordPair => .tuple (.number 0) (.number 0)
  | .wordSum => .inl (.number 0)
  | _ => .number 0

/-- The renderer's spelling of the zero values. -/
def azeroText : ATarget → String
  | .word => "0"
  | .bool => "false"
  | .unit => ""
  | .wordPair => "(0, 0)"
  | .wordSum => "inl(0)"

theorem azero_print {target : ATarget} (valued : target ≠ .unit) :
    (azero target).print = azeroText target := by
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

/-- A rendered scalar operand of the call-graph helpers, as the renderer's
private `scalarValue` builds it. -/
def ascalarValue (rendered : ARendered) : Except EmitError ScalarRenderer.Rendered :=
  (AggregateRenderer.requireValue rendered).bind fun value =>
    .ok ⟨rendered.lines, value, rendered.nextId⟩

/-- A scalar operand as an aggregate rendering with a value name. -/
def ARendered.ofScalar (rendered : ScalarRenderer.Rendered) : ARendered :=
  ⟨rendered.lines, some rendered.value, rendered.nextId⟩

/-- The statements printed for a projection: a zero result, then a pair match
whose case assigns the picked component. -/
def projectionStmts (next : Nat) (value : String) (picked : Nat) : List Stmt :=
  [.letDecl (temporary next) .word (.number 0),
    .matchPair (.name value) (payloadTemp (next + 1)) (payloadTemp (next + 2))
      [.assign (temporary next) (.name (payloadTemp picked))]]

theorem arequireValue_ok {rendered : ARendered} {value : String}
    (equation : AggregateRenderer.requireValue rendered = .ok value) :
    rendered.value = some value := by
  unfold AggregateRenderer.requireValue at equation
  cases found : rendered.value with
  | none =>
      rw [found] at equation
      cases equation
  | some value' =>
      rw [found] at equation
      cases equation
      rfl

theorem ascalarValue_ok {rendered : ARendered} {value : ScalarRenderer.Rendered}
    (equation : ascalarValue rendered = .ok value) :
    rendered.value = some value.value ∧ ARendered.ofScalar value = rendered := by
  unfold ascalarValue at equation
  obtain ⟨name, nameEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  have found := arequireValue_ok nameEquation
  refine ⟨found, ?_⟩
  obtain ⟨lines, value, next⟩ := rendered
  simp only at found
  subst found
  rfl

namespace AggregateEquations

variable {functions : List String} {target : ATarget} {bindings : List Binding}
  {indent first : Nat} {rendered : ARendered}

theorem word (value : Solcore.Core.Word) :
    AggregateRenderer.render functions target bindings indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        some (temporary first), first + 1⟩ := by
  simp only [AggregateRenderer.render]
  rfl

theorem bool (value : Bool) :
    AggregateRenderer.render functions target bindings indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        some (temporary first), first + 1⟩ := by
  simp only [AggregateRenderer.render]
  rfl

theorem unit :
    AggregateRenderer.render functions target bindings indent first .unit =
      .ok ⟨[], none, first⟩ := by
  simp only [AggregateRenderer.render]

theorem var_ok {index : Nat}
    (equation : AggregateRenderer.render functions target bindings indent first (.var index) =
      .ok rendered) :
    (∃ (name : String) (kind : ATarget), kind ≠ .unit ∧
        bindings[index]? = some (valueBinding kind name) ∧ rendered = ⟨[], some name, first⟩) ∨
      (bindings[index]? = some Binding.unit ∧ rendered = ⟨[], none, first⟩) := by
  simp only [AggregateRenderer.render] at equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      cases binding with
      | word name =>
          exact Or.inl ⟨name, .word, by simp, rfl, (Except.ok.inj equation).symm⟩
      | bool name =>
          exact Or.inl ⟨name, .bool, by simp, rfl, (Except.ok.inj equation).symm⟩
      | wordPair name =>
          exact Or.inl ⟨name, .wordPair, by simp, rfl, (Except.ok.inj equation).symm⟩
      | wordSum name =>
          exact Or.inl ⟨name, .wordSum, by simp, rfl, (Except.ok.inj equation).symm⟩
      | unit => exact Or.inr ⟨rfl, (Except.ok.inj equation).symm⟩
      | cellWord name => cases equation

theorem newCellLet_ok {initializer body : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE (.newCell .word initializer) body) = .ok rendered) :
    ∃ initial value rest,
      AggregateRenderer.render functions .word bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      AggregateRenderer.render functions target
        (.cellWord (cellTemp initial.nextId) :: bindings) indent (initial.nextId + 1) body =
          .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (cellTemp initial.nextId) .word (.name value)) ++ rest.lines,
        rest.value, rest.nextId⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨initial, value, rest, initialEquation, arequireValue_ok valueEquation, restEquation, ?_⟩
  rw [← cellDecl_lines]
  exact (Except.ok.inj equation).symm

theorem letE_infer {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ kind, infer? (bindings.map Binding.kind) functions.length initializer = some kind := by
  rw [AggregateRenderer.render.eq_6 _ _ _ _ _ _ _ notCell] at equation
  cases inferred : infer? (bindings.map Binding.kind) functions.length initializer with
  | none =>
      rw [inferred] at equation
      cases equation
  | some kind => exact ⟨kind, rfl⟩

theorem letE_unit_ok {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some .unit)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial rest,
      AggregateRenderer.render functions .unit bindings indent first initializer = .ok initial ∧
      AggregateRenderer.render functions target (.unit :: bindings) indent initial.nextId body =
        .ok rest ∧
      rendered = ⟨initial.lines ++ rest.lines, rest.value, rest.nextId⟩ := by
  rw [AggregateRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨initial, rest, initialEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem letE_value_ok {initializer body : CoreExpr} {kind : ATarget}
    (notCell : ∀ inner, initializer = .newCell .word inner → False) (valued : kind ≠ .unit)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some kind)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial value rest,
      AggregateRenderer.render functions kind bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      AggregateRenderer.render functions target
        (valueBinding kind (temporary initial.nextId) :: bindings) indent (initial.nextId + 1)
          body = .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (temporary initial.nextId) kind.localType (.name value)) ++
        rest.lines, rest.value, rest.nextId⟩ := by
  rw [AggregateRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  cases kind
  case unit => exact absurd rfl valued
  all_goals
    obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨initial, value, rest, initialEquation, arequireValue_ok valueEquation, restEquation,
      (Except.ok.inj equation).symm⟩

theorem ifE_unit_ok {condition yes no : CoreExpr}
    (equation : AggregateRenderer.render functions .unit bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected fallback,
      AggregateRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      AggregateRenderer.render functions .unit bindings (indent + 4) tested.nextId yes =
        .ok selected ∧
      AggregateRenderer.render functions .unit bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      rendered = ⟨tested.lines ++ [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++
        selected.lines ++ [indentLine indent "} else {"] ++ fallback.lines ++
        [indentLine indent "}"], none, fallback.nextId⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
  have unitTest : ((.unit : ATarget) == .unit) = true := rfl
  rw [if_pos unitTest] at equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, conditionValue, selected, fallback, testedEquation,
    arequireValue_ok conditionEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem ifE_value_ok {condition yes no : CoreExpr} (valued : target ≠ .unit)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected selectedValue fallback fallbackValue,
      AggregateRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      AggregateRenderer.render functions target bindings (indent + 4) (tested.nextId + 1) yes =
        .ok selected ∧
      selected.value = some selectedValue ∧
      AggregateRenderer.render functions target bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      fallback.value = some fallbackValue ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";"),
            indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  cases target
  case unit => exact absurd rfl valued
  all_goals
    simp only [AggregateRenderer.render] at equation
    obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
    rw [if_neg (by decide)] at equation
    obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selectedValue, selectedValueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallbackValue, fallbackValueEquation, equation⟩ := except_bind_eq_ok equation
    have resultName : resultValue = temporary tested.nextId :=
      (Option.some.inj (arequireValue_ok resultEquation)).symm
    subst resultName
    exact ⟨tested, conditionValue, selected, selectedValue, fallback, fallbackValue,
      testedEquation, arequireValue_ok conditionEquation, selectedEquation,
      arequireValue_ok selectedValueEquation, fallbackEquation,
      arequireValue_ok fallbackValueEquation, (Except.ok.inj equation).symm⟩

theorem pair_ok {left right : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.pair left right) = .ok rendered) :
    ∃ leftRendered leftValue rightRendered rightValue,
      AggregateRenderer.render functions .word bindings indent first left = .ok leftRendered ∧
      leftRendered.value = some leftValue ∧
      AggregateRenderer.render functions .word bindings indent leftRendered.nextId right =
        .ok rightRendered ∧
      rightRendered.value = some rightValue ∧
      rendered = ⟨leftRendered.lines ++ rightRendered.lines ++
          Stmt.lines indent (.letDecl (temporary rightRendered.nextId) .wordPair
            (.tuple (.name leftValue) (.name rightValue))),
        some (temporary rightRendered.nextId), rightRendered.nextId + 1⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨leftRendered, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftValue, leftValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightRendered, rightEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightValueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftRendered, leftValue, rightRendered, rightValue, leftEquation,
    arequireValue_ok leftValueEquation, rightEquation, arequireValue_ok rightValueEquation,
    (Except.ok.inj equation).symm⟩

theorem first_ok {operand : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.first operand) = .ok rendered) :
    ∃ operandRendered value,
      AggregateRenderer.render functions .wordPair bindings indent first operand =
        .ok operandRendered ∧
      operandRendered.value = some value ∧
      rendered = ⟨operandRendered.lines ++ Stmt.listLines indent
          (projectionStmts operandRendered.nextId value (operandRendered.nextId + 1)),
        some (temporary operandRendered.nextId), operandRendered.nextId + 3⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
  have resultName : resultValue = temporary operandRendered.nextId :=
    (Option.some.inj (arequireValue_ok resultEquation)).symm
  subst resultName
  refine ⟨operandRendered, value, operandEquation, arequireValue_ok valueEquation, ?_⟩
  rw [← (Except.ok.inj equation)]
  simp only [List.append_assoc]
  rfl

theorem second_ok {operand : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.second operand) = .ok rendered) :
    ∃ operandRendered value,
      AggregateRenderer.render functions .wordPair bindings indent first operand =
        .ok operandRendered ∧
      operandRendered.value = some value ∧
      rendered = ⟨operandRendered.lines ++ Stmt.listLines indent
          (projectionStmts operandRendered.nextId value (operandRendered.nextId + 2)),
        some (temporary operandRendered.nextId), operandRendered.nextId + 3⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
  have resultName : resultValue = temporary operandRendered.nextId :=
    (Option.some.inj (arequireValue_ok resultEquation)).symm
  subst resultName
  refine ⟨operandRendered, value, operandEquation, arequireValue_ok valueEquation, ?_⟩
  rw [← (Except.ok.inj equation)]
  simp only [List.append_assoc]
  rfl

theorem inLeft_ok {payload : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.inLeft .word payload) = .ok rendered) :
    ∃ payloadRendered value,
      AggregateRenderer.render functions .word bindings indent first payload =
        .ok payloadRendered ∧
      payloadRendered.value = some value ∧
      rendered = ⟨payloadRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadRendered.nextId) .wordSum (.inl (.name value))),
        some (temporary payloadRendered.nextId), payloadRendered.nextId + 1⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨payloadRendered, payloadEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨payloadRendered, value, payloadEquation, arequireValue_ok valueEquation,
    (Except.ok.inj equation).symm⟩

theorem inRight_ok {payload : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.inRight .word payload) = .ok rendered) :
    ∃ payloadRendered value,
      AggregateRenderer.render functions .word bindings indent first payload =
        .ok payloadRendered ∧
      payloadRendered.value = some value ∧
      rendered = ⟨payloadRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadRendered.nextId) .wordSum (.inr (.name value))),
        some (temporary payloadRendered.nextId), payloadRendered.nextId + 1⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨payloadRendered, payloadEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨payloadRendered, value, payloadEquation, arequireValue_ok valueEquation,
    (Except.ok.inj equation).symm⟩

theorem caseE_unit_ok {scrutinee yes no : CoreExpr}
    (equation : AggregateRenderer.render functions .unit bindings indent first
      (.caseE scrutinee yes no) = .ok rendered) :
    ∃ tested value selected fallback,
      AggregateRenderer.render functions .wordSum bindings indent first scrutinee =
        .ok tested ∧
      tested.value = some value ∧
      AggregateRenderer.render functions .unit (.word (payloadTemp tested.nextId) :: bindings)
        (indent + 8) (tested.nextId + 1) yes = .ok selected ∧
      AggregateRenderer.render functions .unit (.word (payloadTemp selected.nextId) :: bindings)
        (indent + 8) (selected.nextId + 1) no = .ok fallback ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("match (" ++ value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp tested.nextId ++ ") {")] ++
          selected.lines ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4) ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          fallback.lines ++ [indentLine (indent + 4) "}", indentLine indent "}"],
        none, fallback.nextId⟩ := by
  have unfolded : ((AggregateRenderer.render functions .wordSum bindings indent first
      scrutinee).bind fun tested => (AggregateRenderer.requireValue tested).bind fun value =>
        (AggregateRenderer.render functions .unit (.word (payloadTemp tested.nextId) :: bindings)
          (indent + 8) (tested.nextId + 1) yes).bind fun selected =>
          (AggregateRenderer.render functions .unit
            (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
              no).bind fun fallback =>
            (Except.ok selected.lines : Except EmitError (List String)).bind fun selectedLines =>
              (Except.ok fallback.lines : Except EmitError (List String)).bind
                fun fallbackLines => Except.ok (⟨tested.lines ++ [] ++
                  [indentLine indent ("match (" ++ value ++ ") {"),
                    indentLine (indent + 4) ("case inl(" ++ payloadTemp tested.nextId ++ ") {")] ++
                  selectedLines ++
                  [indentLine (indent + 4) "}",
                    indentLine (indent + 4)
                      ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
                  fallbackLines ++ [indentLine (indent + 4) "}", indentLine indent "}"],
                  none, fallback.nextId⟩ : ARendered)) = .ok rendered := by
    rw [← equation]
    simp only [AggregateRenderer.render]
    rfl
  obtain ⟨tested, testedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨value, valueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selected, selectedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallback, fallbackEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selectedLines, selectedLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallbackLines, fallbackLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  cases selectedLinesEquation
  cases fallbackLinesEquation
  refine ⟨tested, value, selected, fallback, testedEquation, arequireValue_ok valueEquation,
    selectedEquation, fallbackEquation, ?_⟩
  rw [← (Except.ok.inj unfolded), List.append_nil]

theorem caseE_value_ok {scrutinee yes no : CoreExpr} (valued : target ≠ .unit)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.caseE scrutinee yes no) = .ok rendered) :
    ∃ tested value selected selectedValue fallback fallbackValue,
      AggregateRenderer.render functions .wordSum bindings indent first scrutinee =
        .ok tested ∧
      tested.value = some value ∧
      AggregateRenderer.render functions target
        (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
          yes = .ok selected ∧
      selected.value = some selectedValue ∧
      AggregateRenderer.render functions target
        (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
          no = .ok fallback ∧
      fallback.value = some fallbackValue ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("match (" ++ value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
          (selected.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";")]) ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4) ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          (fallback.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";")]) ++
          [indentLine (indent + 4) "}", indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  have unfolded : ((AggregateRenderer.render functions .wordSum bindings indent first
      scrutinee).bind fun tested => (AggregateRenderer.requireValue tested).bind fun value =>
        (AggregateRenderer.render functions target
          (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8)
            (tested.nextId + 2) yes).bind fun selected =>
          (AggregateRenderer.render functions target
            (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
              no).bind fun fallback =>
            (AggregateRenderer.requireValue selected).bind fun selectedValue =>
              (Except.ok (selected.lines ++ [indentLine (indent + 8)
                (temporary tested.nextId ++ " = " ++ selectedValue ++ ";")]) :
                  Except EmitError (List String)).bind fun selectedLines =>
              (AggregateRenderer.requireValue fallback).bind fun fallbackValue =>
                (Except.ok (fallback.lines ++ [indentLine (indent + 8)
                  (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";")]) :
                    Except EmitError (List String)).bind fun fallbackLines =>
                Except.ok (⟨tested.lines ++
                  [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
                    target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
                  [indentLine indent ("match (" ++ value ++ ") {"),
                    indentLine (indent + 4)
                      ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
                  selectedLines ++
                  [indentLine (indent + 4) "}",
                    indentLine (indent + 4)
                      ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
                  fallbackLines ++ [indentLine (indent + 4) "}", indentLine indent "}"],
                  some (temporary tested.nextId), fallback.nextId⟩ : ARendered)) =
        .ok rendered := by
    rw [← equation]
    cases target
    case unit => exact absurd rfl valued
    all_goals
      simp only [AggregateRenderer.render]
      rfl
  obtain ⟨tested, testedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨value, valueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selected, selectedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallback, fallbackEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selectedValue, selectedValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selectedLines, selectedLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallbackValue, fallbackValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallbackLines, fallbackLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  cases selectedLinesEquation
  cases fallbackLinesEquation
  exact ⟨tested, value, selected, selectedValue, fallback, fallbackValue, testedEquation,
    arequireValue_ok valueEquation, selectedEquation, arequireValue_ok selectedValueEquation,
    fallbackEquation, arequireValue_ok fallbackValueEquation, (Except.ok.inj unfolded).symm⟩

theorem loadCell_ok {index : Nat}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.loadCell (.var index)) = .ok rendered) :
    ∃ name, bindings[index]? = some (Binding.cellWord name) ∧
      rendered = ⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
        some (temporary first), first + 1⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => Except.ok (⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
          some (temporary first), first + 1⟩ : ARendered)) = .ok rendered := equation
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
      | wordPair name => cases unfolded
      | wordSum name => cases unfolded

theorem storeCell_ok {index : Nat} {value : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.storeCell (.var index) value) = .ok rendered) :
    ∃ name written result, bindings[index]? = some (Binding.cellWord name) ∧
      AggregateRenderer.render functions .word bindings indent first value = .ok written ∧
      written.value = some result ∧
      rendered = ⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
        written.nextId⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => (AggregateRenderer.render functions .word bindings indent first value).bind
          fun written => (AggregateRenderer.requireValue written).bind fun result =>
            Except.ok (⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
              written.nextId⟩ : ARendered)) = .ok rendered := equation
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
          exact ⟨name, written, result, rfl, writtenEquation, arequireValue_ok resultEquation,
            (Except.ok.inj unfolded).symm⟩
      | word name => cases unfolded
      | bool name => cases unfolded
      | unit => cases unfolded
      | wordPair name => cases unfolded
      | wordSum name => cases unfolded

/-- `!` and `~` bind their result to a fresh temporary. -/
theorem unary (scalar : Target) (op : Solcore.Core.Wire.UnaryOp) (sourceOp : UnaryOp)
    (operand : CoreExpr) (selected : sourceUnary? op = some sourceOp) :
    AggregateRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.unary op operand) =
      (AggregateRenderer.render functions (if op == .boolNot then .bool else .word) bindings
        indent first operand).bind fun operandRendered =>
        (ascalarValue operandRendered).bind fun value =>
          .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
              (LocalType.ofTarget scalar) (.unary sourceOp (.name value.value))),
            some (temporary value.nextId), value.nextId + 1⟩ := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateRenderer.render] <;> rfl

/-- `CLZ` snapshots its operand, then calls the raw opcode alias. -/
theorem clz (operand : CoreExpr) :
    AggregateRenderer.render functions .word bindings indent first (.unary .wordClz operand) =
      (AggregateRenderer.render functions .word bindings indent first operand).bind
        fun operandRendered => (ascalarValue operandRendered).bind fun value =>
          .ok ⟨(snapshotOf indent value).lines ++ Stmt.lines indent
              (.letDecl (temporary (value.nextId + 1)) .word
                (.call1 "sc_clz" (.name (temporary value.nextId)))),
            some (temporary (value.nextId + 1)), value.nextId + 2⟩ := by
  simp only [AggregateRenderer.render]
  rfl

/-- The infix operations bind their result to a fresh temporary. -/
theorem binary (scalar : Target) (op : Solcore.Core.Wire.BinaryOp) (sourceOp : BinaryOp)
    (left right : CoreExpr) (selected : sourceBinary? op = some sourceOp) :
    AggregateRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateRenderer.render functions .word bindings indent first left).bind
        fun leftRendered => (ascalarValue leftRendered).bind fun leftValue =>
          (AggregateRenderer.render functions .word bindings indent leftValue.nextId right).bind
            fun rightRendered => (ascalarValue rightRendered).bind fun rightValue =>
              .ok ⟨leftValue.lines ++ rightValue.lines ++ Stmt.lines indent
                  (.letDecl (temporary rightValue.nextId) (LocalType.ofTarget scalar)
                    (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
                some (temporary rightValue.nextId), rightValue.nextId + 1⟩ := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateRenderer.render] <;> rfl

/-- Extended binary operations snapshot both operands, left to right, then
call the raw opcode alias. -/
theorem binary_primitive (scalar : Target) (op : Solcore.Core.Wire.BinaryOp)
    (build : String → String → Expr) (left right : CoreExpr)
    (selected : primitiveBinary? op = some build) :
    AggregateRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateRenderer.render functions .word bindings indent first left).bind
        fun leftRendered => (ascalarValue leftRendered).bind fun leftValue =>
          (AggregateRenderer.render functions .word bindings indent (leftValue.nextId + 1)
            right).bind fun rightRendered => (ascalarValue rightRendered).bind fun rightValue =>
              .ok ⟨(snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines ++
                  Stmt.lines indent (.letDecl (temporary (rightValue.nextId + 1))
                    (LocalType.ofTarget scalar)
                    (build (temporary leftValue.nextId) (temporary rightValue.nextId))),
                some (temporary (rightValue.nextId + 1)), rightValue.nextId + 2⟩ := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateRenderer.render] <;> rfl

/-- `ADDMOD` and `MULMOD` snapshot all three operands, then call the raw
opcode alias. -/
theorem ternary (op : Solcore.Core.Wire.TernaryOp) (one two three : CoreExpr) :
    AggregateRenderer.render functions .word bindings indent first (.ternary op one two three) =
      (AggregateRenderer.render functions .word bindings indent first one).bind
        fun oneRendered => (ascalarValue oneRendered).bind fun oneValue =>
          (AggregateRenderer.render functions .word bindings indent (oneValue.nextId + 1)
            two).bind fun twoRendered => (ascalarValue twoRendered).bind fun twoValue =>
              (AggregateRenderer.render functions .word bindings indent (twoValue.nextId + 1)
                three).bind fun threeRendered => (ascalarValue threeRendered).bind
                  fun threeValue =>
                    .ok ⟨(snapshotOf indent oneValue).lines ++
                        (snapshotOf indent twoValue).lines ++
                        (snapshotOf indent threeValue).lines ++
                        Stmt.lines indent (.letDecl (temporary (threeValue.nextId + 1)) .word
                          (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
                            (.name (temporary twoValue.nextId))
                            (.name (temporary threeValue.nextId)))),
                      some (temporary (threeValue.nextId + 1)), threeValue.nextId + 2⟩ := by
  simp only [AggregateRenderer.render]
  cases op <;> rfl

theorem apply_ok {index : Nat} {argument : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.apply (.var index) argument) = .ok rendered) :
    bindings.length ≤ index ∧ ∃ callee argumentRendered value,
      functions[index - bindings.length]? = some callee ∧
      AggregateRenderer.render functions .word bindings indent first argument =
        .ok argumentRendered ∧
      argumentRendered.value = some value ∧
      rendered = ⟨argumentRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary argumentRendered.nextId) .word (.call1 callee (.name value))),
        some (temporary argumentRendered.nextId), argumentRendered.nextId + 1⟩ := by
  by_cases below : index < bindings.length
  · dsimp only [AggregateRenderer.render] at equation
    rw [if_pos below] at equation
    cases equation
  · cases found : functions[index - bindings.length]? with
    | none =>
        dsimp only [AggregateRenderer.render] at equation
        rw [if_neg below, found] at equation
        cases equation
    | some callee =>
        dsimp only [AggregateRenderer.render] at equation
        rw [if_neg below, found] at equation
        obtain ⟨argumentRendered, argumentEquation, equation⟩ := except_bind_eq_ok equation
        obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
        exact ⟨Nat.le_of_not_lt below, callee, argumentRendered, value, rfl, argumentEquation,
          arequireValue_ok valueEquation, (Except.ok.inj equation).symm⟩

end AggregateEquations

namespace AggregateKinds

theorem local_beq (first second : Local) : (first == second) = decide (first = second) := by
  cases first <;> cases second <;> rfl

theorem infer_toLocal {locals : List Local} {prior : Nat} {expression : CoreExpr}
    {kind : ATarget} (inferred : infer? locals prior expression = some kind) :
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
    {kind : ATarget} (inferred : initializerKind? locals prior expression = some kind.toLocal) :
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

theorem pair {locals : List Local} {prior : Nat} {left right : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.pair left right) = some result) :
    initializerKind? locals prior left = some .word ∧
      initializerKind? locals prior right = some .word ∧ result = .wordPair := by
  have unfolded : ((initializerKind? locals prior left).bind fun found =>
      (if found == Local.word then some () else none).bind fun _ =>
        (initializerKind? locals prior right).bind fun found' =>
          (if found' == Local.word then some () else none).bind fun _ => some Local.wordPair) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, leftKind, checked, check, found', rightKind, checked', check', last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases found' <;> simp [local_beq] at check'
  cases last
  exact ⟨leftKind, rightKind, rfl⟩

theorem first {locals : List Local} {prior : Nat} {operand : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.first operand) = some result) :
    initializerKind? locals prior operand = some .wordPair ∧ result = .word := by
  have unfolded : ((initializerKind? locals prior operand).bind fun found =>
      (if found == Local.wordPair then some () else none).bind fun _ => some Local.word) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, operandKind, checked, check, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases last
  exact ⟨operandKind, rfl⟩

theorem second {locals : List Local} {prior : Nat} {operand : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.second operand) = some result) :
    initializerKind? locals prior operand = some .wordPair ∧ result = .word := by
  have unfolded : ((initializerKind? locals prior operand).bind fun found =>
      (if found == Local.wordPair then some () else none).bind fun _ => some Local.word) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, operandKind, checked, check, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases last
  exact ⟨operandKind, rfl⟩

theorem inLeft {locals : List Local} {prior : Nat} {type : Solcore.Core.Wire.Ty}
    {payload : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.inLeft type payload) = some result) :
    type = .word ∧ initializerKind? locals prior payload = some .word ∧ result = .wordSum := by
  cases type
  case word =>
    have unfolded : ((initializerKind? locals prior payload).bind fun found =>
        (if found == Local.word then some () else none).bind fun _ => some Local.wordSum) =
        some result := inferred
    simp only [Option.bind_eq_some_iff] at unfolded
    obtain ⟨found, payloadKind, checked, check, last⟩ := unfolded
    cases found <;> simp [local_beq] at check
    cases last
    exact ⟨rfl, payloadKind, rfl⟩
  all_goals cases inferred

theorem inRight {locals : List Local} {prior : Nat} {type : Solcore.Core.Wire.Ty}
    {payload : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.inRight type payload) = some result) :
    type = .word ∧ initializerKind? locals prior payload = some .word ∧ result = .wordSum := by
  cases type
  case word =>
    have unfolded : ((initializerKind? locals prior payload).bind fun found =>
        (if found == Local.word then some () else none).bind fun _ => some Local.wordSum) =
        some result := inferred
    simp only [Option.bind_eq_some_iff] at unfolded
    obtain ⟨found, payloadKind, checked, check, last⟩ := unfolded
    cases found <;> simp [local_beq] at check
    cases last
    exact ⟨rfl, payloadKind, rfl⟩
  all_goals cases inferred

theorem caseE {locals : List Local} {prior : Nat} {scrutinee yes no : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.caseE scrutinee yes no) = some result) :
    initializerKind? locals prior scrutinee = some .wordSum ∧
      initializerKind? (.word :: locals) prior yes = some result ∧
      initializerKind? (.word :: locals) prior no = some result ∧ result ≠ .cellWord := by
  have unfolded : ((initializerKind? locals prior scrutinee).bind fun found =>
      (if found == Local.wordSum then some () else none).bind fun _ =>
        (initializerKind? (.word :: locals) prior yes).bind fun left =>
          (initializerKind? (.word :: locals) prior no).bind fun right =>
            if (left == right && left != Local.cellWord) = true then some left else none) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, scrutineeKind, checked, check, left, yesKind, right, noKind, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases left <;> cases right <;> simp [local_beq, bne] at last <;> subst last <;>
    exact ⟨scrutineeKind, yesKind, noKind, by simp⟩

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

/-- The local kind of a scalar result. -/
def scalarKind : Target → Local
  | .word => .word
  | .bool => .bool

theorem unary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.UnaryOp)
    (operand : CoreExpr) :
    initializerKind? locals prior (.unary op operand) =
      if MutationKinds.integerUnary op then none else
        (initializerKind? locals prior operand).bind fun found =>
          (if found == scalarKind (Target.unaryOperand op) then some () else none).bind fun _ =>
            some (scalarKind (Target.unaryResult op)) := by
  cases op <;> rfl

theorem binary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.BinaryOp)
    (left right : CoreExpr) :
    initializerKind? locals prior (.binary op left right) =
      if MutationKinds.integerBinary op then none else
        (initializerKind? locals prior left).bind fun found =>
          (if found == Local.word then some () else none).bind fun _ =>
            (initializerKind? locals prior right).bind fun found' =>
              (if found' == Local.word then some () else none).bind fun _ =>
                some (scalarKind (Target.binaryResult op)) := by
  cases op <;> rfl

theorem unary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.UnaryOp}
    {operand : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.unary op operand) = some result) :
    MutationKinds.integerUnary op = false ∧
      initializerKind? locals prior operand = some (scalarKind (Target.unaryOperand op)) ∧
      result = scalarKind (Target.unaryResult op) := by
  rw [unary_eq] at inferred
  cases integer : MutationKinds.integerUnary op
  · rw [integer, if_neg (by simp)] at inferred
    simp only [Option.bind_eq_some_iff] at inferred
    obtain ⟨found, operandKind, checked, check, last⟩ := inferred
    have same : found = scalarKind (Target.unaryOperand op) := by
      by_cases same : found = scalarKind (Target.unaryOperand op)
      · exact same
      · rw [local_beq, decide_eq_false same] at check
        cases check
    cases last
    exact ⟨rfl, same ▸ operandKind, rfl⟩
  · rw [integer, if_pos rfl] at inferred
    cases inferred

theorem binary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.BinaryOp}
    {left right : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.binary op left right) = some result) :
    MutationKinds.integerBinary op = false ∧
      initializerKind? locals prior left = some .word ∧
      initializerKind? locals prior right = some .word ∧
      result = scalarKind (Target.binaryResult op) := by
  rw [binary_eq] at inferred
  cases integer : MutationKinds.integerBinary op
  · rw [integer, if_neg (by simp)] at inferred
    simp only [Option.bind_eq_some_iff] at inferred
    obtain ⟨found, leftKind, checked, check, found', rightKind, checked', check', last⟩ :=
      inferred
    cases found <;> simp [local_beq] at check
    cases found' <;> simp [local_beq] at check'
    cases last
    exact ⟨rfl, leftKind, rightKind, rfl⟩
  · rw [integer, if_pos rfl] at inferred
    cases inferred

theorem ternary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.TernaryOp}
    {one two three : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.ternary op one two three) = some result) :
    initializerKind? locals prior one = some .word ∧
      initializerKind? locals prior two = some .word ∧
      initializerKind? locals prior three = some .word ∧ result = .word := by
  have unfolded : ((initializerKind? locals prior one).bind fun found =>
      (if found == Local.word then some () else none).bind fun _ =>
        (initializerKind? locals prior two).bind fun found' =>
          (if found' == Local.word then some () else none).bind fun _ =>
            (initializerKind? locals prior three).bind fun found'' =>
              (if found'' == Local.word then some () else none).bind fun _ =>
                some Local.word) = some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, oneKind, checked, check, found', twoKind, checked', check', found'', threeKind,
    checked'', check'', last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases found' <;> simp [local_beq] at check'
  cases found'' <;> simp [local_beq] at check''
  cases last
  exact ⟨oneKind, twoKind, threeKind, rfl⟩

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

end AggregateKinds

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregatePreservation
/-! Simulation lemmas for the actual `AggregateRenderer.render`: literals,
locals, cell reads and writes, `let`, operations, pairs, sum constructors and
helper calls. Operations print the call-graph formatting: raw opcode operands
are copied into fresh `word` temporaries first, and a copy is one more
rendering of the operand. The control forms are in `AggregateControl`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-! ### Values -/

theorem AValue.ofScalar_iff {scalar : Target} {core : CoreValue} {source : Value} :
    AValue (ATarget.ofScalar scalar) core source ↔ Represents scalar core source := by
  cases scalar <;> exact Iff.rfl

theorem valueBinding_holds {target : ATarget} (valued : target ≠ .unit) (frames : Frames)
    (store : Solcore.Core.Store) (name : String) (core : CoreValue) :
    ABindingHolds frames store (valueBinding target name) core =
      ARepresents target core (frames.lookup name) := by
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

theorem toLocal_injective {first second : ATarget} (same : first.toLocal = second.toLocal) :
    first = second := by
  cases first <;> cases second <;> first | rfl | cases same

theorem atoLocal_scalarKind {target : ATarget} {scalar : Target}
    (same : target.toLocal = AggregateKinds.scalarKind scalar) :
    target = ATarget.ofScalar scalar := by
  cases target <;> cases scalar <;> first | rfl | cases same

theorem ofScalar_toLocal (scalar : Target) :
    (ATarget.ofScalar scalar).toLocal = AggregateKinds.scalarKind scalar := by
  cases scalar <;> rfl

theorem ARenderSpec.le {admits : Context → Prop} {expression : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {rendered : ARendered}
    (spec : ARenderSpec admits expression target functions bindings indent first rendered) :
    first ≤ rendered.nextId := by
  obtain ⟨_, _, le, _⟩ := spec
  exact le

/-! ### Call contexts -/

/-- An expression needs the alias context only if one of its parts does. -/
theorem AliasesReady.of_sub {expression sub : CoreExpr} {admits : Context → Prop}
    (ready : ∀ context, admits context → AliasesReady expression context)
    (uses : AggregateRenderer.usesOpcodeAliases sub = true →
      AggregateRenderer.usesOpcodeAliases expression = true) :
    ∀ context, admits context → AliasesReady sub context :=
  fun context admitted used => ready context admitted (uses used)

section

variable {admits : Context → Prop}

/-! ### Results -/

/-- The common tail of value expressions: after `statements`, the `tail`
declares the temporary `middle` with the value of the expression. -/
theorem aresult_simulates {expression : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {first middle last : Nat}
    {statements tail : List Stmt}
    (fresh : ANamesFresh bindings first)
    (core : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store) (scope : Scope) (outer : Frames),
      admits context → ABindingsAgree (scope :: outer) bindings environment store →
      ACellsDistinct bindings environment → bindings.length ≤ environment.length →
      MFunctionsAgree context functions (environment.drop bindings.length) →
      ∃ (coreValue : CoreValue) (value : Value) (store' : Solcore.Core.Store) (scope₁ : Scope)
        (outer₁ : Frames) (added : List String),
        Solcore.Core.Evaluates environment store expression.toCore coreValue store' ∧
        AValue target coreValue value ∧
        Stmt.execList context (scope :: outer) statements = some (scope₁ :: outer₁) ∧
        Stmt.execList context (scope₁ :: outer₁) tail =
          some (((temporary middle, value) :: scope₁) :: outer₁) ∧
        ABindingsAgree (scope₁ :: outer₁) bindings environment store' ∧
        AStoreFrame bindings environment store store' ∧
        (∀ name, ¬ ATempIn first middle name →
          (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
          Frames.lookup (scope₁ :: outer₁) name = Frames.lookup (scope :: outer) name) ∧
        Frames.shape outer₁ = Frames.shape outer ∧
        scope₁.names = added ++ scope.names ∧
        (∀ name ∈ added, ATempIn first middle name))
    (le : first ≤ middle) (high : middle < last) :
    ASimulates admits expression target functions bindings first last (statements ++ tail)
      (some (temporary middle)) := by
  intro context environment store scope outer admitted agree distinct lengthOk functionsOk
  obtain ⟨coreValue, value, store', scope₁, outer₁, added, evaluates, represents, exec, tailExec,
    agree₁, frame, keeps, shape, names, addedTemp⟩ :=
    core context environment store scope outer admitted agree distinct lengthOk functionsOk
  have temp : ATempIn first last (temporary middle) := aTempIn_temporary le high
  refine ⟨coreValue, store', (temporary middle, value) :: scope₁, outer₁,
    temporary middle :: added, evaluates, ?_, ?_, ?_, frame, ?_, shape, ?_, ?_⟩
  · simp only [Option.bind_some, Frames.lookup_declared, if_pos]
    exact ARepresents.of_value represents
  · rw [Stmt.execList_append, exec]
    simpa using tailExec
  · exact agree₁.declare (fresh.ne_temp temp) value
  · intro name notTemp notCell
    have different : temporary middle ≠ name := fun same => notTemp (same ▸ temp)
    rw [Frames.lookup_declared, if_neg different,
      keeps name (fun inRange => notTemp (aTempIn_mono inRange (Nat.le_refl _)
        (Nat.le_of_lt high))) notCell]
  · show temporary middle :: scope₁.names = (temporary middle :: added) ++ scope.names
    rw [names]
    rfl
  · intro name mem
    rcases List.mem_cons.mp mem with same | mem
    · exact same ▸ temp
    · exact aTempIn_mono (addedTemp name mem) (Nat.le_refl _) (Nat.le_of_lt high)

/-- The tail `let` of a value expression. -/
theorem let_exec {context : Context} {scope : Scope} {outer : Frames} {target : ATarget}
    {name : String} {initializer : Expr} {core : CoreValue} {value : Value}
    (initialized : initializer.eval context (scope :: outer) = some value)
    (represents : AValue target core value) :
    Stmt.execList context (scope :: outer) [.letDecl name target.localType initializer] =
      some (((name, value) :: scope) :: outer) := by
  simp [Stmt.execList, Stmt.exec, initialized, represents.admits, Frames.declare]

/-- An expression with no statements, whose value is already named. -/
theorem asimulates_nil {expression : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {first : Nat}
    {valueName : Option String}
    (core : ∀ (environment : Solcore.Core.Environment) (store : Solcore.Core.Store)
      (scope : Scope) (outer : Frames),
      ABindingsAgree (scope :: outer) bindings environment store →
      ∃ coreValue : CoreValue,
        Solcore.Core.Evaluates environment store expression.toCore coreValue store ∧
        ARepresents target coreValue (valueName.bind (Frames.lookup (scope :: outer)))) :
    ASimulates admits expression target functions bindings first first [] valueName := by
  intro context environment store scope outer _ agree _ _ _
  obtain ⟨coreValue, evaluates, represents⟩ := core environment store scope outer agree
  exact ⟨coreValue, store, scope, outer, [], evaluates, represents, rfl, agree,
    AStoreFrame.refl _ _ _, fun _ _ _ => rfl, rfl, rfl, by simp⟩

/-- A value bound by one `let` whose initializer reads only bindings. -/
theorem aleaf_spec {expression : CoreExpr} {target : ATarget} {functions : List String}
    {bindings : List Binding} {indent first : Nat} {initializer : Expr}
    (fresh : ANamesFresh bindings first)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      ∃ index, anameAt bindings index = some name)
    (evaluates : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store) (frames : Frames),
      ABindingsAgree frames bindings environment store →
      ∃ (coreValue : CoreValue) (value : Value),
        Solcore.Core.Evaluates environment store expression.toCore coreValue store ∧
        initializer.eval context frames = some value ∧ AValue target coreValue value) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨Stmt.lines indent (.letDecl (temporary first) target.localType initializer),
        some (temporary first), first + 1⟩ := by
  unfold ARenderSpec
  dsimp only
  refine ⟨[.letDecl (temporary first) target.localType initializer], by simp [Stmt.listLines],
    Nat.le_succ _, ?_, ?_, ?_⟩
  · intro name same
    cases same
    exact Or.inr ⟨first, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers, Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with same | mem
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary (Nat.le_refl _)
        (Nat.lt_succ_self _))))
    · exact Or.inl (initializerNames name mem)
  · have simulates := aresult_simulates (admits := admits) (expression := expression)
      (functions := functions) (statements := [])
      (tail := [.letDecl (temporary first) target.localType initializer]) fresh
      (fun context environment store scope outer _ agree _ _ _ => by
        obtain ⟨coreValue, value, evaluates', initialized, represents⟩ :=
          evaluates context environment store (scope :: outer) agree
        exact ⟨coreValue, value, store, scope, outer, [], evaluates', represents, rfl,
          let_exec initialized represents, agree, AStoreFrame.refl _ _ _, fun _ _ _ => rfl, rfl,
          rfl, by simp⟩)
      (Nat.le_refl first) (Nat.lt_succ_self first)
    rw [List.nil_append] at simulates
    exact simulates

/-- One operand followed by a fresh temporary bound to `initializer`, which
reads the operand's value name. The final step may run a helper, which
allocates only new store locations. -/
theorem aoneResult_spec {expression operand : CoreExpr} {operandTarget target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {operandRendered : ARendered} {operandValue : String} {initializer : Expr}
    (operandValued : operandTarget ≠ .unit) (fresh : ANamesFresh bindings first)
    (spec : ARenderSpec admits operand operandTarget functions bindings indent first
      operandRendered)
    (named : operandRendered.value = some operandValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = operandValue ∨ name ∈ functions ∨ name ∈ primitiveCallees)
    (combine : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store store₁ : Solcore.Core.Store) (operandCore : CoreValue) (frames : Frames)
      (source : Value),
      admits context → bindings.length ≤ environment.length →
      MFunctionsAgree context functions (environment.drop bindings.length) →
      Solcore.Core.Evaluates environment store operand.toCore operandCore store₁ →
      frames.lookup operandValue = some source → AValue operandTarget operandCore source →
      ∃ (coreResult : CoreValue) (sourceResult : Value) (store₂ : Solcore.Core.Store),
        Solcore.Core.Evaluates environment store expression.toCore coreResult store₂ ∧
        store₁.length ≤ store₂.length ∧
        (∀ location, location < store₁.length →
          store₂.read? location = store₁.read? location) ∧
        initializer.eval context frames = some sourceResult ∧
        AValue target coreResult sourceResult) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨operandRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary operandRendered.nextId) target.localType initializer),
        some (temporary operandRendered.nextId), operandRendered.nextId + 1⟩ := by
  obtain ⟨statements, lines, le, valueName, uses, simulates⟩ := spec
  unfold ARenderSpec
  dsimp only
  refine ⟨statements ++ [.letDecl (temporary operandRendered.nextId) target.localType
      initializer], ?_, by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines, Stmt.listLines, List.append_nil]
  · intro name same
    cases same
    exact Or.inr ⟨operandRendered.nextId, rfl, le, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with mem | same | mem
    · exact (uses name mem).mono (Nat.le_refl _) (Nat.le_succ _)
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary le (Nat.lt_succ_self _))))
    · rcases initializerNames name mem with same | mem | called
      · subst same
        exact (valueName _ named).uses.mono (Nat.le_refl _) (Nat.le_succ _)
      · exact Or.inr (Or.inl mem)
      · exact Or.inr (Or.inr (Or.inr called))
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinct lengthOk functionsOk => ?_) le (Nat.lt_succ_self _)
    obtain ⟨core, store₁, scope₁, outer₁, added₁, evaluates, represents, exec, agree₁, frame₁,
      keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      simulates context environment store scope outer admitted agree distinct lengthOk
        functionsOk
    rw [named, Option.bind_some] at represents
    obtain ⟨source, lookup, operandValue'⟩ := represents.value operandValued
    obtain ⟨coreResult, sourceResult, store₂, evaluates', grows, keepsStore, initialized,
      resultValue⟩ :=
      combine context environment store store₁ core _ source admitted lengthOk functionsOk
        evaluates lookup operandValue'
    refine ⟨coreResult, sourceResult, store₂, scope₁, outer₁, added₁, evaluates', resultValue,
      exec, let_exec initialized resultValue, ?_, ?_, keeps₁, shape₁, names₁, addedTemp₁⟩
    · exact agree₁.transfer (fun _ _ _ => rfl) fun _ location isCell =>
        keepsStore location (agree₁.cell_lt isCell)
    · exact frame₁.trans ⟨grows, fun location inBounds _ => keepsStore location inBounds⟩

/-- Two Word operands, left to right, followed by a fresh temporary bound to
`initializer`, which reads both value names. -/
theorem atwoResult_spec {expression left right : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {leftRendered rightRendered : ARendered} {leftValue rightValue : String}
    {initializer : Expr}
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (leftSpec : ARenderSpec admits left .word functions bindings indent first leftRendered)
    (leftNamed : leftRendered.value = some leftValue)
    (rightSpec : ARenderSpec admits right .word functions bindings indent leftRendered.nextId
      rightRendered)
    (rightNamed : rightRendered.value = some rightValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = leftValue ∨ name = rightValue ∨ name ∈ primitiveCallees)
    (combine : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store store₁ store₂ : Solcore.Core.Store) (leftWord rightWord : Solcore.Core.Word)
      (frames : Frames),
      admits context →
      Solcore.Core.Evaluates environment store left.toCore (.word leftWord) store₁ →
      Solcore.Core.Evaluates environment store₁ right.toCore (.word rightWord) store₂ →
      frames.lookup leftValue = some (.word leftWord.val) →
      frames.lookup rightValue = some (.word rightWord.val) →
      ∃ (coreResult : CoreValue) (sourceResult : Value),
        Solcore.Core.Evaluates environment store expression.toCore coreResult store₂ ∧
        initializer.eval context frames = some sourceResult ∧
        AValue target coreResult sourceResult) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨leftRendered.lines ++ rightRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary rightRendered.nextId) target.localType initializer),
        some (temporary rightRendered.nextId), rightRendered.nextId + 1⟩ := by
  obtain ⟨leftStatements, leftLines, leftLe, leftValueName, leftUses, leftSimulates⟩ := leftSpec
  obtain ⟨rightStatements, rightLines, rightLe, rightValueName, rightUses, rightSimulates⟩ :=
    rightSpec
  unfold ARenderSpec
  dsimp only
  refine ⟨leftStatements ++ rightStatements ++ [.letDecl (temporary rightRendered.nextId)
      target.localType initializer], ?_, by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, leftLines, rightLines, Stmt.listLines, List.append_nil]
  · intro name same
    cases same
    exact Or.inr ⟨rightRendered.nextId, rfl, by omega, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with (mem | mem) | same | mem
    · exact (leftUses name mem).mono (Nat.le_refl _) (by omega)
    · exact (rightUses name mem).mono leftLe (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary (by omega) (Nat.lt_succ_self _))))
    · rcases initializerNames name mem with same | same | called
      · subst same
        exact (leftValueName _ leftNamed).uses.mono (Nat.le_refl _) (by omega)
      · subst same
        exact (rightValueName _ rightNamed).uses.mono leftLe (by omega)
      · exact Or.inr (Or.inr (Or.inr called))
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinctCells lengthOk functionsOk => ?_) (by omega) (Nat.lt_succ_self _)
    obtain ⟨leftCore, store₁, scope₁, outer₁, added₁, leftEvaluates, leftRepresents,
      leftExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      leftSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    obtain ⟨rightCore, store₂, scope₂, outer₂, added₂, rightEvaluates, rightRepresents,
      rightExec, agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      rightSimulates context environment store₁ scope₁ outer₁ admitted agree₁ distinctCells
        lengthOk functionsOk
    rw [leftNamed, Option.bind_some] at leftRepresents
    rw [rightNamed, Option.bind_some] at rightRepresents
    obtain ⟨_, leftLookup, leftWord, rfl, rfl⟩ := leftRepresents
    obtain ⟨_, rightLookup, rightWord, rfl, rfl⟩ := rightRepresents
    obtain ⟨leftSurvivesTemp, leftSurvivesCell⟩ :=
      (leftValueName leftValue leftNamed).survives (last := rightRendered.nextId) fresh
        distinct leftLe
    have leftLookup₂ : Frames.lookup (scope₂ :: outer₂) leftValue =
        some (.word leftWord.val) := by
      rw [keeps₂ leftValue leftSurvivesTemp leftSurvivesCell]
      exact leftLookup
    obtain ⟨coreResult, sourceResult, evaluates, initialized, resultValue⟩ :=
      combine context environment store store₁ store₂ leftWord rightWord _ admitted
        leftEvaluates rightEvaluates leftLookup₂ rightLookup
    refine ⟨coreResult, sourceResult, store₂, scope₂, outer₂, added₂ ++ added₁, evaluates,
      resultValue, ?_, let_exec initialized resultValue, agree₂, frame₁.trans frame₂, ?_,
      shape₂.trans shape₁, ?_, ?_⟩
    · rw [Stmt.execList_append, leftExec]
      simpa using rightExec
    · intro name notTemp notCell
      rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp leftLe (Nat.le_refl _))) notCell,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) rightLe)) notCell]
    · rw [names₂, names₁]
      simp
    · intro name mem
      rcases List.mem_append.mp mem with mem | mem
      · exact aTempIn_mono (addedTemp₂ name mem) leftLe (Nat.le_refl _)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) rightLe

/-- Three Word operands, left to right, followed by a fresh temporary bound to
`initializer`, which reads the three value names. -/
theorem athreeResult_spec {expression one two three : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {oneRendered twoRendered threeRendered : ARendered} {oneValue twoValue threeValue : String}
    {initializer : Expr}
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (oneSpec : ARenderSpec admits one .word functions bindings indent first oneRendered)
    (oneNamed : oneRendered.value = some oneValue)
    (twoSpec : ARenderSpec admits two .word functions bindings indent oneRendered.nextId
      twoRendered)
    (twoNamed : twoRendered.value = some twoValue)
    (threeSpec : ARenderSpec admits three .word functions bindings indent twoRendered.nextId
      threeRendered)
    (threeNamed : threeRendered.value = some threeValue)
    (initializerNames : ∀ name ∈ initializer.identifiers,
      name = oneValue ∨ name = twoValue ∨ name = threeValue ∨ name ∈ primitiveCallees)
    (combine : ∀ (context : Context) (environment : Solcore.Core.Environment)
      (store store₁ store₂ store₃ : Solcore.Core.Store)
      (oneWord twoWord threeWord : Solcore.Core.Word) (frames : Frames),
      admits context →
      Solcore.Core.Evaluates environment store one.toCore (.word oneWord) store₁ →
      Solcore.Core.Evaluates environment store₁ two.toCore (.word twoWord) store₂ →
      Solcore.Core.Evaluates environment store₂ three.toCore (.word threeWord) store₃ →
      frames.lookup oneValue = some (.word oneWord.val) →
      frames.lookup twoValue = some (.word twoWord.val) →
      frames.lookup threeValue = some (.word threeWord.val) →
      ∃ (coreResult : CoreValue) (sourceResult : Value),
        Solcore.Core.Evaluates environment store expression.toCore coreResult store₃ ∧
        initializer.eval context frames = some sourceResult ∧
        AValue target coreResult sourceResult) :
    ARenderSpec admits expression target functions bindings indent first
      ⟨oneRendered.lines ++ twoRendered.lines ++ threeRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary threeRendered.nextId) target.localType initializer),
        some (temporary threeRendered.nextId), threeRendered.nextId + 1⟩ := by
  obtain ⟨oneStatements, oneLines, oneLe, oneValueName, oneUses, oneSimulates⟩ := oneSpec
  obtain ⟨twoStatements, twoLines, twoLe, twoValueName, twoUses, twoSimulates⟩ := twoSpec
  obtain ⟨threeStatements, threeLines, threeLe, threeValueName, threeUses, threeSimulates⟩ :=
    threeSpec
  unfold ARenderSpec
  dsimp only
  refine ⟨oneStatements ++ twoStatements ++ threeStatements ++
      [.letDecl (temporary threeRendered.nextId) target.localType initializer], ?_,
    by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, oneLines, twoLines, threeLines, Stmt.listLines,
      List.append_nil]
  · intro name same
    cases same
    exact Or.inr ⟨threeRendered.nextId, rfl, by omega, Nat.lt_succ_self _⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, List.append_nil, List.mem_cons] at mem
    rcases mem with ((mem | mem) | mem) | same | mem
    · exact (oneUses name mem).mono (Nat.le_refl _) (by omega)
    · exact (twoUses name mem).mono oneLe (by omega)
    · exact (threeUses name mem).mono (by omega) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_temporary (by omega) (Nat.lt_succ_self _))))
    · rcases initializerNames name mem with same | same | same | called
      · subst same
        exact (oneValueName _ oneNamed).uses.mono (Nat.le_refl _) (by omega)
      · subst same
        exact (twoValueName _ twoNamed).uses.mono oneLe (by omega)
      · subst same
        exact (threeValueName _ threeNamed).uses.mono (by omega) (by omega)
      · exact Or.inr (Or.inr (Or.inr called))
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinctCells lengthOk functionsOk => ?_) (by omega) (Nat.lt_succ_self _)
    obtain ⟨oneCore, store₁, scope₁, outer₁, added₁, oneEvaluates, oneRepresents, oneExec,
      agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      oneSimulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    obtain ⟨twoCore, store₂, scope₂, outer₂, added₂, twoEvaluates, twoRepresents, twoExec,
      agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      twoSimulates context environment store₁ scope₁ outer₁ admitted agree₁ distinctCells
        lengthOk functionsOk
    obtain ⟨threeCore, store₃, scope₃, outer₃, added₃, threeEvaluates, threeRepresents,
      threeExec, agree₃, frame₃, keeps₃, shape₃, names₃, addedTemp₃⟩ :=
      threeSimulates context environment store₂ scope₂ outer₂ admitted agree₂ distinctCells
        lengthOk functionsOk
    rw [oneNamed, Option.bind_some] at oneRepresents
    rw [twoNamed, Option.bind_some] at twoRepresents
    rw [threeNamed, Option.bind_some] at threeRepresents
    obtain ⟨_, oneLookup, oneWord, rfl, rfl⟩ := oneRepresents
    obtain ⟨_, twoLookup, twoWord, rfl, rfl⟩ := twoRepresents
    obtain ⟨_, threeLookup, threeWord, rfl, rfl⟩ := threeRepresents
    obtain ⟨oneSurvivesTwo, oneNotCell⟩ :=
      (oneValueName oneValue oneNamed).survives (last := twoRendered.nextId) fresh distinct oneLe
    obtain ⟨oneSurvivesThree, _⟩ :=
      ((oneValueName oneValue oneNamed).mono (Nat.le_refl _) twoLe).survives
        (last := threeRendered.nextId) fresh distinct (Nat.le_trans oneLe twoLe)
    obtain ⟨twoSurvivesThree, twoNotCell⟩ :=
      (twoValueName twoValue twoNamed).survives (last := threeRendered.nextId)
        (fresh.mono oneLe) distinct twoLe
    have oneLookup₃ : Frames.lookup (scope₃ :: outer₃) oneValue = some (.word oneWord.val) := by
      rw [keeps₃ oneValue oneSurvivesThree oneNotCell,
        keeps₂ oneValue oneSurvivesTwo oneNotCell]
      exact oneLookup
    have twoLookup₃ : Frames.lookup (scope₃ :: outer₃) twoValue = some (.word twoWord.val) := by
      rw [keeps₃ twoValue twoSurvivesThree twoNotCell]
      exact twoLookup
    obtain ⟨coreResult, sourceResult, evaluates, initialized, resultValue⟩ :=
      combine context environment store store₁ store₂ store₃ oneWord twoWord threeWord _ admitted
        oneEvaluates twoEvaluates threeEvaluates oneLookup₃ twoLookup₃ threeLookup
    refine ⟨coreResult, sourceResult, store₃, scope₃, outer₃, added₃ ++ added₂ ++ added₁,
      evaluates, resultValue, ?_, let_exec initialized resultValue, agree₃,
      (frame₁.trans frame₂).trans frame₃, ?_, (shape₃.trans shape₂).trans shape₁, ?_, ?_⟩
    · rw [Stmt.execList_append, Stmt.execList_append, oneExec]
      simp [twoExec, threeExec]
    · intro name notTemp notCell
      rw [keeps₃ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
          notCell,
        keeps₂ name (fun temp => notTemp (aTempIn_mono temp oneLe (by omega))) notCell,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
    · rw [names₃, names₂, names₁]
      simp
    · intro name mem
      simp only [List.mem_append] at mem
      rcases mem with (mem | mem) | mem
      · exact aTempIn_mono (addedTemp₃ name mem) (by omega) (Nat.le_refl _)
      · exact aTempIn_mono (addedTemp₂ name mem) oneLe (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

/-- A snapshot of a rendered Word operand is one more rendering of it. -/
theorem asnapshot_spec {expression : CoreExpr} {functions : List String}
    {bindings : List Binding} {indent first : Nat} {value : ScalarRenderer.Rendered}
    (fresh : ANamesFresh bindings first)
    (spec : ARenderSpec admits expression .word functions bindings indent first
      (ARendered.ofScalar value)) :
    ARenderSpec admits expression .word functions bindings indent first
      (ARendered.ofScalar (snapshotOf indent value)) := by
  have result := aoneResult_spec (expression := expression) (operand := expression)
    (target := .word) (initializer := .name value.value) (by simp) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem)
    (fun context environment store store₁ operandCore frames source _ _ _ evaluates lookup
      represents => ⟨operandCore, source, store₁, evaluates, Nat.le_refl _, fun _ _ => rfl,
        by simpa [Expr.eval] using lookup, represents⟩)
  exact result

/-! ### Literals, locals and cell reads -/

theorem aRenderIH_word (value : Solcore.Core.Word) : ARenderIH (.word value) := by
  intro admits _ functions target bindings indent first rendered accepted equation fresh _
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases accepted
  subst targetWord
  rw [AggregateEquations.word] at equation
  cases equation
  exact aleaf_spec (target := .word) (initializer := .number value.val) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.word value, .word value.val, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .word,
      by simp [Expr.eval, word_lt_modulus], value, rfl, rfl⟩)

theorem aRenderIH_bool (value : Bool) : ARenderIH (.bool value) := by
  intro admits _ functions target bindings indent first rendered accepted equation fresh _
  have targetBool : target = .bool := by
    cases target <;> first | rfl | cases accepted
  subst targetBool
  rw [AggregateEquations.bool] at equation
  cases equation
  exact aleaf_spec (target := .bool) (initializer := .bool value) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.bool value, .bool value, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .bool, rfl, value, rfl, rfl⟩)

theorem aRenderIH_unit : ARenderIH .unit := by
  intro admits _ functions target bindings indent first rendered accepted equation _ _
  have targetUnit : target = .unit := by
    cases target <;> first | rfl | cases accepted
  subst targetUnit
  rw [AggregateEquations.unit] at equation
  cases equation
  refine ⟨[], rfl, Nat.le_refl _, (fun _ same => by cases same),
    (by simp [Stmt.listIdentifiers]), asimulates_nil fun _ _ _ _ _ => ⟨.unit, ?_, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .unit

theorem aRenderIH_var (index : Nat) : ARenderIH (.var index) := by
  intro admits _ functions target bindings indent first rendered accepted equation _ _
  obtain ⟨kindFound, _⟩ := AggregateKinds.var accepted
  rw [List.getElem?_map] at kindFound
  rcases AggregateEquations.var_ok equation with ⟨name, kind, valued, found, rfl⟩ | ⟨found, rfl⟩
  · rw [found] at kindFound
    simp only [Option.map_some, Option.some.injEq] at kindFound
    rw [valueBinding_kind valued] at kindFound
    have sameTarget := toLocal_injective kindFound
    subst sameTarget
    refine ⟨[], rfl, Nat.le_refl _, ?_, by simp [Stmt.listIdentifiers], ?_⟩
    · intro value same
      cases same
      exact Or.inl ⟨index, kind, valued, found⟩
    · refine asimulates_nil fun environment store scope outer agree => ?_
      obtain ⟨core, inEnvironment, holds⟩ := agree index _ found
      rw [valueBinding_holds valued] at holds
      refine ⟨core, ?_, by simpa using holds⟩
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact .var inEnvironment
  · rw [found] at kindFound
    simp only [Option.map_some, Option.some.injEq] at kindFound
    have targetUnit : target = .unit := by
      cases target <;> first | rfl | cases kindFound
    subst targetUnit
    refine ⟨[], rfl, Nat.le_refl _, (fun _ same => by cases same),
      (by simp [Stmt.listIdentifiers]), ?_⟩
    refine asimulates_nil fun environment store scope outer agree => ?_
    obtain ⟨core, inEnvironment, same⟩ := agree index _ found
    refine ⟨core, ?_, same⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .var inEnvironment

theorem aRenderIH_loadCell (index : Nat) : ARenderIH (.loadCell (.var index)) := by
  intro admits _ functions target bindings indent first rendered accepted equation fresh _
  obtain ⟨cellKind, resultWord⟩ := AggregateKinds.loadCell accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨name, found, rfl⟩ := AggregateEquations.loadCell_ok equation
  exact aleaf_spec (target := .word) (initializer := .name name) fresh
    (fun other mem => by
      simp only [Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact ⟨index, by rw [anameAt_of_getElem? found]; rfl⟩)
    (fun _ environment store frames agree => by
      obtain ⟨core, inEnvironment, elementType, location, word, rfl, read, lookup⟩ :=
        agree index _ found
      refine ⟨.word word, .word word.val, ?_, by simpa [Expr.eval] using lookup, word, rfl, rfl⟩
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact .loadCell (.var inEnvironment) read)

/-! ### Operations, pairs, sum constructors and helper calls -/

theorem aRenderIH_unarySource {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp}
    {operand : CoreExpr} (selected : sourceUnary? op = some sourceOp)
    (operandIH : ARenderIH operand) : ARenderIH (.unary op operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateEquations.unary _ _ _ _ selected] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨named, ofScalar⟩ := ascalarValue_ok valueEquation
  cases equation
  have operandTarget : (if op == .boolNot then (.bool : ATarget) else .word) =
      ATarget.ofScalar (Target.unaryOperand op) := by
    cases op <;> simp_all [sourceUnary?] <;> rfl
  rw [operandTarget] at operandEquation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions (ATarget.ofScalar (Target.unaryOperand op)) bindings indent first operandRendered
    (by rw [ofScalar_toLocal]; exact operandKind) operandEquation fresh distinct
  rw [← ofScalar] at spec
  rw [← ATarget.ofScalar_localType]
  refine aoneResult_spec (ATarget.ofScalar_ne_unit _) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  have scalarRepresents := AValue.ofScalar_iff.mp represents
  rw [unaryOperand_eq selected] at scalarRepresents
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    unary_agree selected scalarRepresents
  refine ⟨coreResult, sourceResult, store₁, ?_, Nat.le_refl _, fun _ _ => rfl, ?_,
    AValue.ofScalar_iff.mpr resultRepresents⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates coreApply
  · simp [Expr.eval, lookup, sourceApply]

theorem aRenderIH_clz {operand : CoreExpr} (operandIH : ARenderIH operand) :
    ARenderIH (.unary .wordClz operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [show ATarget.ofScalar (Target.unaryResult .wordClz) = .word from rfl,
    AggregateEquations.clz] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨named, ofScalar⟩ := ascalarValue_ok valueEquation
  cases equation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first operandRendered operandKind operandEquation fresh
    distinct
  rw [← ofScalar] at spec
  have snapshot := asnapshot_spec fresh spec
  refine aoneResult_spec (target := .word) (by simp) fresh snapshot rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inr (same ▸ by simp [primitiveCallees, primitiveAliases]))
      · exact Or.inl same) ?_
  intro context environment store store₁ operandCore frames source admitted _ _ evaluates
    lookup represents
  have primitive : PrimitiveContext context :=
    ready context admitted rfl
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.word word.clz, .word (Evm.clz word.val), store₁, ?_, Nat.le_refl _,
    fun _ _ => rfl, ?_, word.clz, rfl, by rw [evm_clz]⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates rfl
  · simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, primitive.reaches (opcode := "clz") (alias := "sc_clz")
      (by decide), opcodeMeaning]

theorem aRenderIH_binarySource {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp}
    {left right : CoreExpr} (selected : sourceBinary? op = some sourceOp)
    (leftIH : ARenderIH left) (rightIH : ARenderIH right) :
    ARenderIH (.binary op left right) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateEquations.binary _ _ _ _ _ selected] at equation
  obtain ⟨leftRendered, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftValue, leftValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightRendered, rightEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftNamed, leftOfScalar⟩ := ascalarValue_ok leftValueEquation
  obtain ⟨rightNamed, rightOfScalar⟩ := ascalarValue_ok rightValueEquation
  cases equation
  have leftSpec := leftIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first leftRendered leftKind leftEquation fresh distinct
  rw [← leftOfScalar] at leftSpec
  have rightSpec := rightIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent leftValue.nextId rightRendered rightKind rightEquation
    (fresh.mono leftSpec.le) distinct
  rw [← rightOfScalar] at rightSpec
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSpec rfl rightSpec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_singleton] at mem
      rcases mem with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames _ leftEvaluates
    rightEvaluates leftLookup rightLookup
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    binary_agree selected leftWord rightWord
  refine ⟨coreResult, sourceResult, ?_, ?_, AValue.ofScalar_iff.mpr resultRepresents⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .binary leftEvaluates rightEvaluates coreApply
  · simp [Expr.eval, leftLookup, rightLookup, sourceApply]

theorem primitiveBinary_uses {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} (selected : primitiveBinary? op = some build)
    (left right : CoreExpr) :
    AggregateRenderer.usesOpcodeAliases (.binary op left right) = true := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq] at selected <;> rfl

theorem aRenderIH_binaryPrimitive {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} {left right : CoreExpr}
    (selected : primitiveBinary? op = some build)
    (leftIH : ARenderIH left) (rightIH : ARenderIH right) :
    ARenderIH (.binary op left right) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateEquations.binary_primitive _ _ _ _ _ selected] at equation
  obtain ⟨leftRendered, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftValue, leftValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightRendered, rightEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftNamed, leftOfScalar⟩ := ascalarValue_ok leftValueEquation
  obtain ⟨rightNamed, rightOfScalar⟩ := ascalarValue_ok rightValueEquation
  cases equation
  have leftSpec := leftIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first leftRendered leftKind leftEquation fresh distinct
  rw [← leftOfScalar] at leftSpec
  have leftSnapshot := asnapshot_spec fresh leftSpec
  have rightSpec := rightIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent (leftValue.nextId + 1) rightRendered rightKind rightEquation
    (fresh.mono leftSnapshot.le) distinct
  rw [← rightOfScalar] at rightSpec
  have rightSnapshot := asnapshot_spec (fresh.mono leftSnapshot.le) rightSpec
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSnapshot rfl rightSnapshot rfl
    (primitiveBinary_names selected _ _) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames admitted
    leftEvaluates rightEvaluates leftLookup rightLookup
  have primitive : PrimitiveContext context :=
    ready context admitted (primitiveBinary_uses selected left right)
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    primitiveBinary_agree selected context frames _ _ leftWord rightWord primitive leftLookup
      rightLookup
  refine ⟨coreResult, sourceResult, ?_, sourceApply, AValue.ofScalar_iff.mpr resultRepresents⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .binary leftEvaluates rightEvaluates coreApply

theorem aRenderIH_ternary {op : Solcore.Core.Wire.TernaryOp} {one two three : CoreExpr}
    (oneIH : ARenderIH one) (twoIH : ARenderIH two) (threeIH : ARenderIH three) :
    ARenderIH (.ternary op one two three) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨oneKind, twoKind, threeKind, resultWord⟩ := AggregateKinds.ternary accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  rw [AggregateEquations.ternary] at equation
  obtain ⟨oneRendered, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨oneValue, oneValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoRendered, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeRendered, threeEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨_, oneOfScalar⟩ := ascalarValue_ok oneValueEquation
  obtain ⟨_, twoOfScalar⟩ := ascalarValue_ok twoValueEquation
  obtain ⟨_, threeOfScalar⟩ := ascalarValue_ok threeValueEquation
  cases equation
  have uses : ∀ sub, sub = one ∨ sub = two ∨ sub = three →
      ∀ context, admits context → AliasesReady sub context := by
    intro sub _
    exact AliasesReady.of_sub ready fun _ => rfl
  have oneSpec := oneIH admits (uses one (Or.inl rfl)) functions .word bindings indent first
    oneRendered oneKind oneEquation fresh distinct
  rw [← oneOfScalar] at oneSpec
  have oneSnapshot := asnapshot_spec fresh oneSpec
  have twoSpec := twoIH admits (uses two (Or.inr (Or.inl rfl))) functions .word bindings indent
    (oneValue.nextId + 1) twoRendered twoKind twoEquation (fresh.mono oneSnapshot.le) distinct
  rw [← twoOfScalar] at twoSpec
  have twoSnapshot := asnapshot_spec (fresh.mono oneSnapshot.le) twoSpec
  have threeSpec := threeIH admits (uses three (Or.inr (Or.inr rfl))) functions .word bindings
    indent (twoValue.nextId + 1) threeRendered threeKind threeEquation
    (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) distinct
  rw [← threeOfScalar] at threeSpec
  have threeSnapshot :=
    asnapshot_spec (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) threeSpec
  refine athreeResult_spec (target := .word) fresh distinct oneSnapshot rfl twoSnapshot rfl
    threeSnapshot rfl ?_ ?_
  · intro name mem
    simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at mem
    rcases mem with same | (same | same) | same
    · refine Or.inr (Or.inr (Or.inr (same ▸ ?_)))
      cases op <;> simp [ternaryCallee, primitiveCallees, primitiveAliases]
    · exact Or.inl same
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (Or.inl same))
  · intro context environment store store₁ store₂ store₃ oneWord twoWord threeWord frames
      admitted oneEvaluates twoEvaluates threeEvaluates oneLookup twoLookup threeLookup
    have primitive : PrimitiveContext context := ready context admitted rfl
    obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
      ternary_agree op context frames _ _ _ oneWord twoWord threeWord primitive oneLookup
        twoLookup threeLookup
    refine ⟨coreResult, sourceResult, ?_, sourceApply, resultRepresents⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .ternary oneEvaluates twoEvaluates threeEvaluates coreApply

theorem aRenderIH_pair {left right : CoreExpr} (leftIH : ARenderIH left)
    (rightIH : ARenderIH right) : ARenderIH (.pair left right) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨leftKind, rightKind, resultPair⟩ := AggregateKinds.pair accepted
  have targetPair : target = .wordPair := by
    cases target <;> first | rfl | cases resultPair
  subst targetPair
  obtain ⟨leftRendered, leftValue, rightRendered, rightValue, leftEquation, leftNamed,
    rightEquation, rightNamed, rfl⟩ := AggregateEquations.pair_ok equation
  have leftSpec := leftIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first leftRendered leftKind leftEquation fresh distinct
  have rightSpec := rightIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent leftRendered.nextId rightRendered rightKind rightEquation
    (fresh.mono leftSpec.le) distinct
  refine atwoResult_spec (target := .wordPair) fresh distinct leftSpec leftNamed rightSpec
    rightNamed (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_singleton] at mem
      rcases mem with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames _ leftEvaluates
    rightEvaluates leftLookup rightLookup
  refine ⟨.pair (.word leftWord) (.word rightWord), .pair leftWord.val rightWord.val, ?_, ?_,
    leftWord, rightWord, rfl, rfl⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .pair leftEvaluates rightEvaluates
  · simp [Expr.eval, leftLookup, rightLookup]

theorem aRenderIH_inLeft {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : ARenderIH payload) : ARenderIH (.inLeft type payload) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨rfl, payloadKind, resultSum⟩ := AggregateKinds.inLeft accepted
  have targetSum : target = .wordSum := by
    cases target <;> first | rfl | cases resultSum
  subst targetSum
  obtain ⟨payloadRendered, value, payloadEquation, named, rfl⟩ :=
    AggregateEquations.inLeft_ok equation
  have spec := payloadIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first payloadRendered payloadKind payloadEquation fresh
    distinct
  refine aoneResult_spec (target := .wordSum) (by simp) fresh spec named
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inLeft (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inl word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inl ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inLeft evaluates

theorem aRenderIH_inRight {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : ARenderIH payload) : ARenderIH (.inRight type payload) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨rfl, payloadKind, resultSum⟩ := AggregateKinds.inRight accepted
  have targetSum : target = .wordSum := by
    cases target <;> first | rfl | cases resultSum
  subst targetSum
  obtain ⟨payloadRendered, value, payloadEquation, named, rfl⟩ :=
    AggregateEquations.inRight_ok equation
  have spec := payloadIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first payloadRendered payloadKind payloadEquation fresh
    distinct
  refine aoneResult_spec (target := .wordSum) (by simp) fresh spec named
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inRight (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inr word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inr ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inRight evaluates

/-- A direct call to an earlier helper. The helper cannot reach the caller's
cells, so the call keeps every existing location of the store. -/
theorem aRenderIH_apply {index : Nat} {argument : CoreExpr} (argumentIH : ARenderIH argument) :
    ARenderIH (.apply (.var index) argument) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, _, argumentKind, resultWord⟩ := AggregateKinds.apply accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨outside, callee, argumentRendered, value, found, argumentEquation, named, rfl⟩ :=
    AggregateEquations.apply_ok equation
  have spec := argumentIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .word bindings indent first argumentRendered argumentKind argumentEquation fresh
    distinct
  refine aoneResult_spec (target := .word) (by simp) fresh spec named
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inl (same ▸ List.mem_of_getElem? found))
      · exact Or.inl same) ?_
  intro context environment store store₁ operandCore frames source _ _ functionsOk evaluates
    lookup represents
  obtain ⟨word, rfl, rfl⟩ := represents
  obtain ⟨parameterType, resultType, body, captured, closureFound, behaves⟩ :=
    functionsOk (index - bindings.length) callee found
  obtain ⟨result, store₂, bodyEvaluates, grows, keepsStore, callResult⟩ := behaves word store₁
  have closureAt : environment[index]? =
      some (.closure parameterType resultType body captured) := by
    rw [List.getElem?_drop] at closureFound
    have position : bindings.length + (index - bindings.length) = index := by omega
    rwa [position] at closureFound
  refine ⟨.word result, .word result.val, store₂, ?_, grows, keepsStore, ?_, result, rfl, rfl⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .apply (.var closureAt) evaluates bodyEvaluates
  · simp [Expr.eval, lookup, callResult]

end

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregateControl
/-! Simulation lemmas for the binding and control forms of the actual
`AggregateRenderer.render`, and the structural induction over Core
expressions. A Core `case` binds its payload before every existing local; the
source binds it in the selected case scope under a fresh `sc_p<n>` name. A
projection matches the pair once and assigns the picked component to a fresh
temporary. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-! ### Zero values -/

/-- The value of an `if` or `case` result before a branch assigns it. -/
def azeroValue : ATarget → Value
  | .bool => .bool false
  | .wordPair => .pair 0 0
  | .wordSum => .inl 0
  | _ => .word 0

theorem azero_eval (context : Context) (frames : Frames) (target : ATarget) :
    (azero target).eval context frames = some (azeroValue target) := by
  cases target <;> simp [azero, azeroValue, Expr.eval, Evm.modulus]

theorem azeroValue_admits (target : ATarget) :
    target.localType.admits (azeroValue target) = true := by
  cases target <;> rfl

theorem azero_identifiers (target : ATarget) : (azero target).identifiers = [] := by
  cases target <;> rfl

theorem AValue.sameType_zero {target : ATarget} {core : CoreValue} {value : Value}
    (represents : AValue target core value) : value.sameType (azeroValue target) = true := by
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

theorem not_mem_names_nil (name : String) : name ∉ Scope.names [] := by
  simp [Scope.names]

theorem payloadTemp_inj {first second : Nat} :
    payloadTemp first = payloadTemp second ↔ first = second :=
  ⟨payloadTemp_injective, fun same => same ▸ rfl⟩

/-! ### Frames -/

/-- A case scope that binds a fresh payload name extends the agreement by
that payload. -/
theorem ABindingsAgree.payload {scope : Scope} {outer : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store : Solcore.Core.Store}
    (agree : ABindingsAgree (scope :: outer) bindings environment store) {name : String}
    (absent : ∀ index found, anameAt bindings index = some found → found ≠ name)
    (word : Solcore.Core.Word) :
    ABindingsAgree ([(name, .word word.val)] :: scope :: outer) (.word name :: bindings)
      (.word word :: environment) store := by
  refine (agree.enter [(name, .word word.val)] fun index found named mem => ?_).cons ?_
  · simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
    exact absent index found named mem
  · exact ⟨.word word.val, by simp [Frames.lookup, Scope.get?], word, rfl, rfl⟩

theorem ABindingsAgree.write {frames frames' : Frames} {bindings : List Binding}
    {environment : Solcore.Core.Environment} {store store' : Solcore.Core.Store}
    (agree : ABindingsAgree frames bindings environment store)
    (namesDistinct : ANamesDistinct bindings)
    (cellsDistinct : ACellsDistinct bindings environment) {index location : Nat}
    {name : String} {elementType : Solcore.Core.Ty} {word : Solcore.Core.Word}
    (found : bindings[index]? = some (Binding.cellWord name))
    (inEnvironment : environment[index]? = some (.cellRef elementType location))
    (written : store.write? location (.word word) = some store')
    (lookups : ∀ other, frames'.lookup other =
      if name = other then some (.word word.val) else frames.lookup other) :
    ABindingsAgree frames' bindings environment store' := by
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
  · have otherName : ∀ found, abindingName? binding = some found → name ≠ found := by
      intro found' named sameName
      subst sameName
      exact same (namesDistinct position index name
        (by rw [anameAt_of_getElem? foundBinding]; exact named)
        (by rw [anameAt_of_getElem? found]; rfl))
    cases binding with
    | word other =>
        show ARepresents .word core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
    | bool other =>
        show ARepresents .bool core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
    | wordPair other =>
        show ARepresents .wordPair core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
    | wordSum other =>
        show ARepresents .wordSum core (frames'.lookup other)
        rw [lookups other, if_neg (otherName other rfl)]
        exact holds
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

section

variable {admits : Context → Prop}

/-! ### Branch and case bodies -/

/-- A branch or case body of Unit type runs in a block scope that starts as
`armScope` and is discarded afterwards. A case body's bindings extend the
enclosing bindings by the payload; an `if` body keeps them. -/
theorem aarm_unit {expression : CoreExpr} {functions : List String}
    {bindings bodyBindings : List Binding}
    {environment bodyEnvironment : Solcore.Core.Environment} {low high : Nat}
    {statements : List Stmt} {valueName : Option String} {context : Context}
    {store : Solcore.Core.Store} {armScope scope : Scope} {outer : Frames}
    (simulates : ASimulates admits expression .unit functions bodyBindings low high statements
      valueName)
    (fresh : ANamesFresh bindings low) (admitted : admits context)
    (entryAgree : ABindingsAgree (armScope :: scope :: outer) bodyBindings bodyEnvironment store)
    (entryCells : ACellsDistinct bodyBindings bodyEnvironment)
    (entryLength : bodyBindings.length ≤ bodyEnvironment.length)
    (entryFunctions : MFunctionsAgree context functions
      (bodyEnvironment.drop bodyBindings.length))
    (exitAgree : ∀ (frames : Frames) (store' : Solcore.Core.Store),
      ABindingsAgree frames bodyBindings bodyEnvironment store' →
        ABindingsAgree frames bindings environment store')
    (exitFrame : ∀ store' : Solcore.Core.Store,
      AStoreFrame bodyBindings bodyEnvironment store store' →
        AStoreFrame bindings environment store store')
    (exitCells : ∀ name, (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
      ∀ index : Nat, bodyBindings[index]? ≠ some (Binding.cellWord name))
    (armOutside : ∀ index name, anameAt bindings index = some name → name ∉ armScope.names) :
    ∃ (store' : Solcore.Core.Store) (top scope' : Scope) (outer' : Frames),
      Solcore.Core.Evaluates bodyEnvironment store expression.toCore .unit store' ∧
      Stmt.execList context (armScope :: scope :: outer) statements =
        some (top :: scope' :: outer') ∧
      ABindingsAgree (scope' :: outer') bindings environment store' ∧
      AStoreFrame bindings environment store store' ∧
      scope'.names = scope.names ∧ Frames.shape outer' = Frames.shape outer ∧
      ∀ name, ¬ ATempIn low high name → name ∉ armScope.names →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name = Frames.lookup (scope :: outer) name := by
  obtain ⟨coreValue, store', top, frames, added, evaluates, represents, exec, agree₁, frame, keeps,
    shape, topNames, addedTemp⟩ :=
    simulates context bodyEnvironment store armScope (scope :: outer) admitted entryAgree
      entryCells entryLength entryFunctions
  have unitCore : coreValue = .unit := represents
  subst unitCore
  obtain ⟨scope', outer', rfl, scopeNames, outerShape⟩ := frames_after_block shape
  have absent : ∀ name, ¬ ATempIn low high name → name ∉ armScope.names → name ∉ top.names := by
    intro name notTemp notArm mem
    rw [topNames] at mem
    rcases List.mem_append.mp mem with mem | mem
    · exact notTemp (addedTemp name mem)
    · exact notArm mem
  refine ⟨store', top, scope', outer', evaluates, exec, ?_, exitFrame store' frame, scopeNames,
    outerShape, ?_⟩
  · exact (exitAgree _ store' agree₁).leave fun index name named =>
      absent name (not_aTempIn_of_fresh (fresh index name named) (Nat.le_refl _))
        (armOutside index name named)
  · intro name notTemp notArm notCell
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') (absent name notTemp notArm),
      keeps name notTemp (exitCells name notCell),
      Frames.lookup_cons_of_not_mem (scope :: outer) notArm]

/-- A branch or case body of a value type ends by assigning its value to the
result declared before the `if` or `match`. -/
theorem aarm_value {expression : CoreExpr} {target : ATarget} {functions : List String}
    {bindings bodyBindings : List Binding}
    {environment bodyEnvironment : Solcore.Core.Environment} {low high : Nat}
    {statements : List Stmt} {valueName result : String} {context : Context}
    {store : Solcore.Core.Store} {armScope scope : Scope} {outer : Frames}
    (valued : target ≠ .unit)
    (simulates : ASimulates admits expression target functions bodyBindings low high statements
      (some valueName))
    (fresh : ANamesFresh bindings low) (admitted : admits context)
    (entryAgree : ABindingsAgree (armScope :: scope :: outer) bodyBindings bodyEnvironment store)
    (entryCells : ACellsDistinct bodyBindings bodyEnvironment)
    (entryLength : bodyBindings.length ≤ bodyEnvironment.length)
    (entryFunctions : MFunctionsAgree context functions
      (bodyEnvironment.drop bodyBindings.length))
    (exitAgree : ∀ (frames : Frames) (store' : Solcore.Core.Store),
      ABindingsAgree frames bodyBindings bodyEnvironment store' →
        ABindingsAgree frames bindings environment store')
    (exitFrame : ∀ store' : Solcore.Core.Store,
      AStoreFrame bodyBindings bodyEnvironment store store' →
        AStoreFrame bindings environment store store')
    (exitCells : ∀ name, (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
      ∀ index : Nat, bodyBindings[index]? ≠ some (Binding.cellWord name))
    (armOutside : ∀ index name, anameAt bindings index = some name → name ∉ armScope.names)
    (resultOutside : ¬ ATempIn low high result) (resultNotArm : result ∉ armScope.names)
    (resultNotCell : ∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord result))
    (resultNotBinding : ∀ index found, anameAt bindings index = some found → found ≠ result)
    (declared : Frames.lookup (scope :: outer) result = some (azeroValue target)) :
    ∃ (coreValue : CoreValue) (value : Value) (store' : Solcore.Core.Store) (top scope' : Scope)
      (outer' : Frames),
      Solcore.Core.Evaluates bodyEnvironment store expression.toCore coreValue store' ∧
      AValue target coreValue value ∧
      Stmt.execList context (armScope :: scope :: outer)
        (statements ++ [.assign result (.name valueName)]) = some (top :: scope' :: outer') ∧
      ABindingsAgree (scope' :: outer') bindings environment store' ∧
      AStoreFrame bindings environment store store' ∧
      scope'.names = scope.names ∧ Frames.shape outer' = Frames.shape outer ∧
      ∀ name, ¬ ATempIn low high name → name ∉ armScope.names →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (scope' :: outer') name =
          if result = name then some value else Frames.lookup (scope :: outer) name := by
  obtain ⟨coreValue, store', top₁, frames₁, added, evaluates, represents, exec, agree₁, frame,
    keeps, shape, topNames, addedTemp⟩ :=
    simulates context bodyEnvironment store armScope (scope :: outer) admitted entryAgree
      entryCells entryLength entryFunctions
  simp only [Option.bind_some] at represents
  obtain ⟨value, lookupValue, represents'⟩ := represents.value valued
  have resultFound : Frames.lookup (top₁ :: frames₁) result = some (azeroValue target) := by
    rw [keeps result resultOutside (exitCells result resultNotCell),
      Frames.lookup_cons_of_not_mem (scope :: outer) resultNotArm]
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
  have absent : ∀ name, ¬ ATempIn low high name → name ∉ armScope.names →
      name ∉ top₂.names := by
    intro name notTemp notArm mem
    rw [topNames₂, topNames] at mem
    rcases List.mem_append.mp mem with mem | mem
    · exact notTemp (addedTemp name mem)
    · exact notArm mem
  refine ⟨coreValue, value, store', top₂, scope', outer', evaluates, represents', ?_, ?_,
    exitFrame store' frame, scopeNames, outerShape, ?_⟩
  · rw [Stmt.execList_append, exec]
    simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, resultFound,
      represents'.sameType_zero, assigned]
  · refine (exitAgree _ store' agree₁).transfer (fun index found named => ?_) (fun _ _ _ => rfl)
    have notTemp := not_aTempIn_of_fresh (last := high) (fresh index found named)
      (Nat.le_refl _)
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer')
        (absent found notTemp (armOutside index found named)), lookups found,
      if_neg (resultNotBinding index found named).symm]
  · intro name notTemp notArm notCell
    rw [← Frames.lookup_cons_of_not_mem (scope' :: outer') (absent name notTemp notArm),
      lookups name, keeps name notTemp (exitCells name notCell),
      Frames.lookup_cons_of_not_mem (scope :: outer) notArm]

/-! ### Local bindings -/

/-- A `let` that allocates a Core cell declares an `sc_c<n>` local. -/
theorem aRenderIH_newCellLet {inner body : CoreExpr} (innerIH : ARenderIH inner)
    (bodyIH : ARenderIH body) : ARenderIH (.letE (.newCell .word inner) body) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := AggregateKinds.letE accepted
  obtain ⟨rfl, innerKind⟩ := AggregateKinds.newCell initializerKind
  obtain ⟨initial, value, rest, initialEquation, valueFound, restEquation, rfl⟩ :=
    AggregateEquations.newCellLet_ok equation
  obtain ⟨innerStatements, innerLines, innerLe, innerValue, innerNames, innerSimulates⟩ :=
    innerIH admits (AliasesReady.of_sub ready fun uses => by
        simp [AggregateRenderer.usesOpcodeAliases, uses])
      functions .word bindings indent first initial innerKind initialEquation fresh distinct
  have cellTemp' : ∀ last, initial.nextId < last →
      ATempIn first last (cellTemp initial.nextId) :=
    fun _ lt => aTempIn_cellTemp innerLe lt
  have bodyFresh : ANamesFresh (.cellWord (cellTemp initial.nextId) :: bindings)
      (initial.nextId + 1) := by
    refine fresh.cons (Nat.le_succ_of_le innerLe) fun name same => ?_
    cases same
    exact cellTemp_fresh _
  have bodyDistinct : ANamesDistinct (.cellWord (cellTemp initial.nextId) :: bindings) :=
    distinct.cons fresh fun name same => by
      cases same
      exact ⟨initial.nextId, Or.inr (Or.inl rfl), innerLe⟩
  obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
    bodyIH admits (AliasesReady.of_sub ready fun uses => by
        simp [AggregateRenderer.usesOpcodeAliases, uses])
      functions target (.cellWord (cellTemp initial.nextId) :: bindings) indent
      (initial.nextId + 1) rest bodyKind restEquation bodyFresh bodyDistinct
  refine ⟨innerStatements ++ [.letDecl (cellTemp initial.nextId) .word (.name value)] ++
      bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, innerLines, bodyLines, Stmt.listLines, List.append_nil]
  · intro name same
    rcases bodyValue name same with ⟨index, kind, valued, found⟩ | ⟨index, rfl, lower, upper⟩
    · cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          exact absurd found.symm (valueBinding_ne_cell _ _)
      | succ index => exact Or.inl ⟨index, kind, valued, by simpa using found⟩
    · exact Or.inr ⟨index, rfl, by omega, upper⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with (mem | same | same) | mem
    · exact (innerNames name mem).mono (Nat.le_refl _) (by dsimp only; omega)
    · subst same
      exact Or.inr (Or.inr (Or.inl (cellTemp' _ (by dsimp only; omega))))
    · subst same
      exact (innerValue name valueFound).uses.mono (Nat.le_refl _) (by dsimp only; omega)
    · exact (bodyNames name mem).of_cons
        (fun found same => by cases same; exact cellTemp' _ (by omega))
        (Nat.le_succ_of_le innerLe)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk functionsOk
    obtain ⟨innerCore, store₁, scope₁, outer₁, added₁, innerEvaluates, innerRepresents,
      innerExec, agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      innerSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    rw [valueFound, Option.bind_some] at innerRepresents
    obtain ⟨_, lookupValue, word, rfl, rfl⟩ := innerRepresents
    have oldRead : ∀ other, other < store₁.length →
        (store₁ ++ [Solcore.Core.Value.word word]).read? other = store₁.read? other := by
      intro other lt
      simp [Solcore.Core.Store.read?, List.getElem?_append_left lt]
    have cellNew : ∀ index location, ACellAt bindings environment index location →
        location ≠ store₁.length :=
      fun _ _ isCell same => absurd (agree₁.cell_lt isCell) (by omega)
    have bodyAgree : ABindingsAgree (((cellTemp initial.nextId, .word word.val) :: scope₁) ::
        outer₁)
        (.cellWord (cellTemp initial.nextId) :: bindings)
        (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment)
        (store₁ ++ [.word word]) := by
      refine ABindingsAgree.cons ?_ ⟨_, store₁.length, word, rfl, by
        simp [Solcore.Core.Store.read?], by simp [Frames.lookup_declared]⟩
      exact (agree₁.declare (fresh.ne_temp (cellTemp' _ (Nat.lt_succ_self _))) _).transfer
        (fun _ _ _ => rfl) fun _ location isCell => oldRead location (agree₁.cell_lt isCell)
    have bodyCells : ACellsDistinct (.cellWord (cellTemp initial.nextId) :: bindings)
        (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) := by
      have headCell : ∀ location, ACellAt (.cellWord (cellTemp initial.nextId) :: bindings)
          (.cellRef (Solcore.Core.Wire.Ty.toCore .word) store₁.length :: environment) 0
            location → location = store₁.length := by
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
    have cellOutside : ∀ name, ¬ ATempIn first rest.nextId name →
        cellTemp initial.nextId ≠ name :=
      fun name notTemp same => notTemp (same ▸ cellTemp' _ (by omega))
    refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ cellTemp initial.nextId :: added₁, ?_,
      bodyRepresents, ?_, agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .letE (.newCell innerEvaluates) bodyEvaluates
    · rw [Stmt.execList_append, Stmt.execList_append, innerExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, LocalType.admits, Frames.declare,
        bodyExec]
    · refine ⟨by have := frame₁.1; have := frame₂.1; simp at *; omega,
        fun other lt notCell => ?_⟩
      have lt₁ : other < store₁.length := Nat.lt_of_lt_of_le lt frame₁.1
      have notBodyCell : ∀ index, ¬ ACellAt (.cellWord (cellTemp initial.nextId) :: bindings)
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
      rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
          (fun index found => ?_),
        Frames.lookup_declared, if_neg (cellOutside name notTemp),
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Binding.cellWord.injEq] at found
          exact cellOutside name notTemp found
      | succ index => exact notCell index (by simpa using found)
    · rw [names₂]
      show added₂ ++ cellTemp initial.nextId :: scope₁.names =
        (added₂ ++ cellTemp initial.nextId :: added₁) ++ scope.names
      rw [names₁]
      simp
    · intro name mem
      simp only [List.mem_append, List.mem_cons] at mem
      rcases mem with mem | same | mem
      · exact aTempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
      · exact same ▸ cellTemp' _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

/-- A `let` of a Word, Boolean, pair or sum value copies it to a fresh
temporary, which the body sees as a value binding. -/
theorem aletValue_spec {initializer body : CoreExpr} {kindTarget target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {initial rest : ARendered} {value : String}
    (unitKind : ¬ kindTarget = .unit) (fresh : ANamesFresh bindings first)
    (initSpec : ARenderSpec admits initializer kindTarget functions bindings indent first initial)
    (valueFound : initial.value = some value)
    (bodySpec : ARenderSpec admits body target functions
      (valueBinding kindTarget (temporary initial.nextId) :: bindings) indent
      (initial.nextId + 1) rest) :
    ARenderSpec admits (.letE initializer body) target functions bindings indent first
      ⟨initial.lines ++ Stmt.lines indent (.letDecl (temporary initial.nextId)
          (ATarget.localType kindTarget) (.name value)) ++ rest.lines,
        rest.value, rest.nextId⟩ := by
  obtain ⟨initStatements, initLines, initLe, initValue, initNames, initSimulates⟩ := initSpec
  obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ := bodySpec
  have bound : ∀ last, initial.nextId < last →
      ATempIn first last (temporary initial.nextId) :=
    fun _ lt => aTempIn_temporary initLe lt
  refine ⟨initStatements ++ [.letDecl (temporary initial.nextId) (ATarget.localType kindTarget)
    (.name value)] ++ bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, initLines, bodyLines, Stmt.listLines, List.append_nil]
  · intro name same
    rcases (bodyValue name same).mono (Nat.le_succ_of_le initLe) (Nat.le_refl _) with
      ⟨index, kind, valued, found⟩ | ⟨index, rfl, lower, upper⟩
    · cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          have sameName : name = temporary initial.nextId := by
            have := congrArg abindingName? found
            rw [valueBinding_name unitKind, valueBinding_name valued] at this
            exact (Option.some.inj this).symm
          subst sameName
          exact Or.inr ⟨initial.nextId, rfl, initLe, by dsimp only; omega⟩
      | succ index => exact Or.inl ⟨index, kind, valued, by simpa using found⟩
    · exact Or.inr ⟨index, rfl, lower, upper⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with (mem | same | same) | mem
    · exact (initNames name mem).mono (Nat.le_refl _) (by dsimp only; omega)
    · subst same
      exact Or.inr (Or.inr (Or.inl (bound _ (by dsimp only; omega))))
    · subst same
      exact (initValue name valueFound).uses.mono (Nat.le_refl _) (by dsimp only; omega)
    · exact (bodyNames name mem).of_cons
        (fun found same => by
          rw [valueBinding_name unitKind] at same
          cases same
          exact bound _ (by omega))
        (Nat.le_succ_of_le initLe)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨initCore, store₁, scope₁, outer₁, added₁, initEvaluates, initRepresents, initExec,
      agree₁, frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      initSimulates context environment store scope outer admitted agree distinctCells
        lengthOk functionsOk
    rw [valueFound, Option.bind_some] at initRepresents
    obtain ⟨source, lookupValue, represents⟩ := initRepresents.value unitKind
    have bodyAgree : ABindingsAgree (((temporary initial.nextId, source) :: scope₁) :: outer₁)
        (valueBinding kindTarget (temporary initial.nextId) :: bindings)
        (initCore :: environment) store₁ := by
      refine (agree₁.declare (fresh.ne_temp (bound _ (Nat.lt_succ_self _))) source).cons ?_
      rw [valueBinding_holds unitKind]
      simp only [Frames.lookup_declared, if_pos]
      exact ARepresents.of_value represents
    have notCellBinding : ∀ name, valueBinding kindTarget (temporary initial.nextId) ≠
        .cellWord name := fun name => valueBinding_ne_cell _ _
    obtain ⟨bodyCore, store₂, scope₂, outer₂, added₂, bodyEvaluates, bodyRepresents, bodyExec,
      agree₂, frame₂, keeps₂, shape₂, names₂, addedTemp₂⟩ :=
      bodySimulates context (initCore :: environment) store₁
        ((temporary initial.nextId, source) :: scope₁) outer₁ admitted bodyAgree
        (distinctCells.cons_value notCellBinding) (by simp; omega) (by simpa using functionsOk)
    have outside : ∀ name, ¬ ATempIn first rest.nextId name →
        temporary initial.nextId ≠ name :=
      fun name notTemp same => notTemp (same ▸ bound _ (by omega))
    refine ⟨bodyCore, store₂, scope₂, outer₂, added₂ ++ temporary initial.nextId :: added₁,
      ?_, bodyRepresents, ?_, agree₂.tail, ?_, ?_, shape₂.trans shape₁, ?_, ?_⟩
    · simp only [Solcore.Core.Wire.Expr.toCore]
      exact .letE initEvaluates bodyEvaluates
    · rw [Stmt.execList_append, Stmt.execList_append, initExec]
      simp [Stmt.execList, Stmt.exec, Expr.eval, lookupValue, represents.admits,
        Frames.declare, bodyExec]
    · exact frame₁.trans (frame₂.of_cons notCellBinding)
    · intro name notTemp notCell
      rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
          (fun index found => ?_),
        Frames.lookup_declared, if_neg (outside name notTemp),
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
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
      · exact aTempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
      · exact same ▸ bound _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)

/-- A `let` of a Unit or value initializer. A Unit binding has no source name;
a Word, Boolean, pair or sum value is copied to a fresh immutable temporary. -/
theorem aRenderIH_letE {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (initializerIH : ARenderIH initializer) (bodyIH : ARenderIH body) :
    ARenderIH (.letE initializer body) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := AggregateKinds.letE accepted
  obtain ⟨kindTarget, inferred⟩ := AggregateEquations.letE_infer notCell equation
  have sameKind : kind = kindTarget.toLocal := by
    have toLocal := AggregateKinds.infer_toLocal inferred
    rw [initializerKind] at toLocal
    exact Option.some.inj toLocal
  subst sameKind
  have initializerReady := AliasesReady.of_sub ready (sub := initializer) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have bodyReady := AliasesReady.of_sub ready (sub := body) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  by_cases unitKind : kindTarget = .unit
  · subst unitKind
    obtain ⟨initial, rest, initialEquation, restEquation, rfl⟩ :=
      AggregateEquations.letE_unit_ok notCell inferred equation
    obtain ⟨initStatements, initLines, initLe, _, initNames, initSimulates⟩ :=
      initializerIH admits initializerReady functions .unit bindings indent first initial
        initializerKind initialEquation fresh distinct
    have bodyFresh : ANamesFresh (.unit :: bindings) initial.nextId :=
      fresh.cons initLe fun _ same => by cases same
    have bodyDistinct : ANamesDistinct (.unit :: bindings) :=
      distinct.cons fresh fun _ same => by cases same
    obtain ⟨bodyStatements, bodyLines, bodyLe, bodyValue, bodyNames, bodySimulates⟩ :=
      bodyIH admits bodyReady functions target (.unit :: bindings) indent initial.nextId rest
        bodyKind restEquation bodyFresh bodyDistinct
    refine ⟨initStatements ++ bodyStatements, ?_, by dsimp only; omega, ?_, ?_, ?_⟩
    · simp only [Stmt.listLines_append, initLines, bodyLines]
    · intro name same
      rcases bodyValue name same with ⟨index, kind, valued, found⟩ | ⟨index, rfl, lower, upper⟩
      · cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            cases kind <;> first | exact absurd rfl valued | cases found
        | succ index => exact Or.inl ⟨index, kind, valued, by simpa using found⟩
      · exact Or.inr ⟨index, rfl, by omega, upper⟩
    · intro name mem
      rw [Stmt.listIdentifiers_append, List.mem_append] at mem
      rcases mem with mem | mem
      · exact (initNames name mem).mono (Nat.le_refl _) (by dsimp only; omega)
      · exact (bodyNames name mem).of_cons (fun _ same => by cases same) initLe
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
      · exact frame₁.trans (frame₂.of_cons fun _ same => by cases same)
      · intro name notTemp notCell
        rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
            (fun index found => ?_),
          keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
            notCell]
        cases index with
        | zero => simp at found
        | succ index => exact notCell index (by simpa using found)
      · rw [names₂, names₁]
        simp
      · intro name mem
        rcases List.mem_append.mp mem with mem | mem
        · exact aTempIn_mono (addedTemp₂ name mem) (by omega) (Nat.le_refl _)
        · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
  · obtain ⟨initial, value, rest, initialEquation, valueFound, restEquation, rfl⟩ :=
      AggregateEquations.letE_value_ok notCell unitKind inferred equation
    have initSpec := initializerIH admits initializerReady functions kindTarget bindings indent
      first initial initializerKind initialEquation fresh distinct
    have initLe := initSpec.le
    have bodyFresh : ANamesFresh (valueBinding kindTarget (temporary initial.nextId) :: bindings)
        (initial.nextId + 1) := by
      refine fresh.cons (Nat.le_succ_of_le initLe) fun name same => ?_
      rw [valueBinding_name unitKind] at same
      cases same
      exact temporary_fresh _
    have bodyDistinct : ANamesDistinct (valueBinding kindTarget (temporary initial.nextId) ::
        bindings) :=
      distinct.cons fresh fun name same => by
        rw [valueBinding_name unitKind] at same
        cases same
        exact ⟨initial.nextId, Or.inl rfl, initLe⟩
    have bodyKind' : initializerKind? ((valueBinding kindTarget (temporary initial.nextId) ::
        bindings).map Binding.kind) functions.length body = some target.toLocal := by
      simpa [valueBinding_kind unitKind] using bodyKind
    exact aletValue_spec unitKind fresh initSpec valueFound
      (bodyIH admits bodyReady functions target
        (valueBinding kindTarget (temporary initial.nextId) :: bindings) indent
        (initial.nextId + 1) rest bodyKind' restEquation bodyFresh bodyDistinct)
/-! ### Cell writes -/

/-- `storeCell` assigns the cell's `sc_c<n>` local after evaluating the value. -/
theorem aRenderIH_storeCell (index : Nat) {value : CoreExpr} (valueIH : ARenderIH value) :
    ARenderIH (.storeCell (.var index) value) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨_, valueKind, resultUnit⟩ := AggregateKinds.storeCell accepted
  have targetUnit : target = .unit := by
    cases target <;> first | rfl | cases resultUnit
  subst targetUnit
  obtain ⟨name, written, result, found, writtenEquation, resultFound, rfl⟩ :=
    AggregateEquations.storeCell_ok equation
  obtain ⟨statements, lines, le, writtenValue, names, simulates⟩ :=
    valueIH admits (AliasesReady.of_sub ready fun uses => by
        simp [AggregateRenderer.usesOpcodeAliases, uses])
      functions .word bindings indent first written valueKind writtenEquation fresh distinct
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
      exact Or.inl ⟨index, by rw [anameAt_of_getElem? found]; rfl⟩
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
    obtain ⟨_, lookupResult, word, rfl, rfl⟩ := valueRepresents
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
    · refine frame₁.trans ⟨Nat.le_of_eq
        (Solcore.Core.Store.write?_preserves_length written).symm, fun other _ notCell => ?_⟩
      have otherLocation : other ≠ location := fun same =>
        notCell index (same ▸ ⟨⟨name, found⟩, _, inEnvironment⟩)
      exact Solcore.Core.Store.write?_preserves_other written otherLocation
    · intro other notTemp notCell
      have different : name ≠ other := fun same => notCell index (same ▸ found)
      rw [lookups other, if_neg different, keeps₁ other notTemp notCell]

/-! ### Conditionals -/

/-- An `if` of a value type declares its zero result, then assigns the value
of the selected branch inside the branch block. -/
theorem aifValue_spec {condition yes no : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {tested selected fallback : ARendered}
    {conditionValue selectedValue fallbackValue : String}
    (unitTarget : ¬ target = .unit) (fresh : ANamesFresh bindings first)
    (distinct : ANamesDistinct bindings)
    (conditionSpec : ARenderSpec admits condition .bool functions bindings indent first tested)
    (conditionFound : tested.value = some conditionValue)
    (yesSpec : ARenderSpec admits yes target functions bindings (indent + 4) (tested.nextId + 1)
      selected)
    (selectedFound : selected.value = some selectedValue)
    (noSpec : ARenderSpec admits no target functions bindings (indent + 4) selected.nextId
      fallback)
    (fallbackFound : fallback.value = some fallbackValue) :
    ARenderSpec admits (.ifE condition yes no) target functions bindings indent first
      ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";"),
            indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  have enterNil : ∀ (scope : Scope) (outer : Frames) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store), ABindingsAgree (scope :: outer) bindings environment store →
      ABindingsAgree ([] :: scope :: outer) bindings environment store :=
    fun _ _ _ _ agree => agree.enter [] fun _ _ _ => not_mem_names_nil _
  obtain ⟨cStatements, cLines, cLe, cValue, cNames, cSimulates⟩ := conditionSpec
  obtain ⟨yStatements, yLines, yLe, yValue, yNames, ySimulates⟩ := yesSpec
  obtain ⟨nStatements, nLines, nLe, nValue, nNames, nSimulates⟩ := noSpec
  have result : ∀ last, tested.nextId < last → ATempIn first last (temporary tested.nextId) :=
    fun _ lt => aTempIn_temporary cLe lt
  refine ⟨cStatements ++
      [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target),
        .ifElse (.name conditionValue)
          (yStatements ++ [.assign (temporary tested.nextId) (.name selectedValue)])
          (nStatements ++ [.assign (temporary tested.nextId) (.name fallbackValue)])],
    ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, cLines, yLines, nLines, Stmt.listLines, Stmt.lines,
      Expr.print, azero_print unitTarget, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]
  · intro name same
    cases same
    exact Or.inr ⟨tested.nextId, rfl, cLe, by dsimp only; omega⟩
  · dsimp only
    intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, azero_identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | (same | mem | same | same) | (mem | same | same)
    · exact (cNames name mem).mono (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (cValue name conditionFound).uses.mono (Nat.le_refl _) (by omega)
    · exact (yNames name mem).mono (by omega) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (yValue name selectedFound).uses.mono (by omega) (by omega)
    · exact (nNames name mem).mono (by omega) (Nat.le_refl _)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (nValue name fallbackFound).uses.mono (by omega) (Nat.le_refl _)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨cCore, store₁, scope₁, outer₁, added₁, cEvaluates, cRepresents, cExec, agree₁,
      frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      cSimulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [conditionFound, Option.bind_some] at cRepresents
    obtain ⟨_, cLookup, flag, rfl, rfl⟩ := cRepresents
    have resultTemp := result (tested.nextId + 1) (Nat.lt_succ_self _)
    rw [selectedFound] at ySimulates
    rw [fallbackFound] at nSimulates
    have resultNotBinding : ∀ index found, anameAt bindings index = some found →
        found ≠ temporary tested.nextId := fresh.ne_temp resultTemp
    have agreeDeclared := agree₁.declare (fresh.ne_temp resultTemp) (azeroValue target)
    have declared : Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) ::
        outer₁) (temporary tested.nextId) = some (azeroValue target) := by
      simp [Frames.lookup_declared]
    have conditionSurvives : temporary tested.nextId ≠ conditionValue := by
      intro same
      exact ((cValue conditionValue conditionFound).survives (last := tested.nextId + 1) fresh
        distinct cLe).1 (same ▸ aTempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _))
    have conditionLookup : Frames.lookup (((temporary tested.nextId, azeroValue target) ::
        scope₁) :: outer₁) conditionValue = some (.bool flag) := by
      rw [Frames.lookup_declared, if_neg conditionSurvives]
      exact cLookup
    have prefixExec : Stmt.execList context (scope :: outer) (cStatements ++
        [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target)]) =
        some (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁) := by
      rw [Stmt.execList_append, cExec]
      simp [Stmt.execList, Stmt.exec, azero_eval, azeroValue_admits, Frames.declare]
    have keepsOutside : ∀ name, ¬ ATempIn first fallback.nextId name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁)
          name = Frames.lookup (scope :: outer) name := by
      intro name notTemp notCell
      have different : temporary tested.nextId ≠ name := fun same =>
        notTemp (same ▸ result _ (by omega))
      rw [Frames.lookup_declared, if_neg different,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
    have scopeNames₁ :
        Scope.names ((temporary tested.nextId, azeroValue target) :: scope₁) =
        (temporary tested.nextId :: added₁) ++ scope.names := by
      show temporary tested.nextId :: scope₁.names = _
      rw [names₁]
      rfl
    have addedOk : ∀ name ∈ temporary tested.nextId :: added₁,
        ATempIn first fallback.nextId name := by
      intro name mem
      rcases List.mem_cons.mp mem with same | mem
      · exact same ▸ result _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
    cases flag with
    | true =>
        obtain ⟨branchCore, value, store₂, top, scope₂, outer₂, branchEvaluates,
          branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
          aarm_value unitTarget ySimulates (fresh.mono (by omega)) admitted
            (enterNil _ _ _ _ agreeDeclared) distinctCells lengthOk functionsOk
            (fun _ _ agree => agree) (fun _ frame => frame) (fun _ notCell => notCell)
            (fun _ _ _ => not_mem_names_nil _)
            (not_aTempIn_of_aTempIn resultTemp (Or.inl (Nat.le_refl _)))
            (not_mem_names_nil _) (fresh.not_cell resultTemp) resultNotBinding declared
        refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
          ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
          scopeNames.trans scopeNames₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .ifTrue cEvaluates branchEvaluates
        · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
            (Or.inl (Nat.le_refl _))) (not_mem_names_nil _) (fresh.not_cell resultTemp),
            if_pos rfl]
          exact ARepresents.of_value branchRepresents
        · rw [List.append_cons, Stmt.execList_append, prefixExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, conditionLookup, branchExec]
        · intro name notTemp notCell
          have different : temporary tested.nextId ≠ name := fun same =>
            notTemp (same ▸ result _ (by omega))
          rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (by omega)))
            (not_mem_names_nil _) notCell, if_neg different, keepsOutside name notTemp notCell]
    | false =>
        obtain ⟨branchCore, value, store₂, top, scope₂, outer₂, branchEvaluates,
          branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
          aarm_value unitTarget nSimulates (fresh.mono (by omega)) admitted
            (enterNil _ _ _ _ agreeDeclared) distinctCells lengthOk functionsOk
            (fun _ _ agree => agree) (fun _ frame => frame) (fun _ notCell => notCell)
            (fun _ _ _ => not_mem_names_nil _)
            (not_aTempIn_of_aTempIn resultTemp (Or.inl (by omega)))
            (not_mem_names_nil _) (fresh.not_cell resultTemp) resultNotBinding declared
        refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
          ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
          scopeNames.trans scopeNames₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .ifFalse cEvaluates branchEvaluates
        · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
            (Or.inl (by omega))) (not_mem_names_nil _) (fresh.not_cell resultTemp),
            if_pos rfl]
          exact ARepresents.of_value branchRepresents
        · rw [List.append_cons, Stmt.execList_append, prefixExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, conditionLookup, branchExec]
        · intro name notTemp notCell
          have different : temporary tested.nextId ≠ name := fun same =>
            notTemp (same ▸ result _ (by omega))
          rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
            (not_mem_names_nil _) notCell, if_neg different, keepsOutside name notTemp notCell]

theorem aRenderIH_ifE {condition yes no : CoreExpr} (conditionIH : ARenderIH condition)
    (yesIH : ARenderIH yes) (noIH : ARenderIH no) : ARenderIH (.ifE condition yes no) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨conditionKind, yesKind, noKind, _⟩ := AggregateKinds.ifE accepted
  have conditionReady := AliasesReady.of_sub ready (sub := condition) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have yesReady := AliasesReady.of_sub ready (sub := yes) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have noReady := AliasesReady.of_sub ready (sub := no) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have enterNil : ∀ (scope : Scope) (outer : Frames) (environment : Solcore.Core.Environment)
      (store : Solcore.Core.Store), ABindingsAgree (scope :: outer) bindings environment store →
      ABindingsAgree ([] :: scope :: outer) bindings environment store :=
    fun _ _ _ _ agree => agree.enter [] fun _ _ _ => not_mem_names_nil _
  by_cases unitTarget : target = .unit
  · subst unitTarget
    obtain ⟨tested, conditionValue, selected, fallback, testedEquation, conditionFound,
      selectedEquation, fallbackEquation, rfl⟩ := AggregateEquations.ifE_unit_ok equation
    obtain ⟨cStatements, cLines, cLe, cValue, cNames, cSimulates⟩ :=
      conditionIH admits conditionReady functions .bool bindings indent first tested
        conditionKind testedEquation fresh distinct
    obtain ⟨yStatements, yLines, yLe, _, yNames, ySimulates⟩ :=
      yesIH admits yesReady functions .unit bindings (indent + 4) tested.nextId selected yesKind
        selectedEquation (fresh.mono cLe) distinct
    obtain ⟨nStatements, nLines, nLe, _, nNames, nSimulates⟩ :=
      noIH admits noReady functions .unit bindings (indent + 4) selected.nextId fallback noKind
        fallbackEquation (fresh.mono (by omega)) distinct
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
      · exact (cNames name mem).mono (Nat.le_refl _) (by omega)
      · subst same
        exact (cValue name conditionFound).uses.mono (Nat.le_refl _) (by omega)
      · exact (yNames name mem).mono cLe (by omega)
      · exact (nNames name mem).mono (by omega) (Nat.le_refl _)
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨cCore, store₁, scope₁, outer₁, added₁, cEvaluates, cRepresents, cExec, agree₁,
        frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        cSimulates context environment store scope outer admitted agree distinctCells lengthOk
          functionsOk
      rw [conditionFound, Option.bind_some] at cRepresents
      obtain ⟨_, cLookup, flag, rfl, rfl⟩ := cRepresents
      have addedOk : ∀ name ∈ added₁, ATempIn first fallback.nextId name :=
        fun name mem => aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
      cases flag with
      | true =>
          obtain ⟨store₂, top, scope₂, outer₂, yEvaluates, yExec, agree₂, frame₂, scopeNames,
            outerShape, keeps₂⟩ :=
            aarm_unit ySimulates (fresh.mono cLe) admitted (enterNil _ _ _ _ agree₁)
              distinctCells lengthOk functionsOk (fun _ _ agree => agree) (fun _ frame => frame)
              (fun _ notCell => notCell) (fun _ _ _ => not_mem_names_nil _)
          refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
            ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifTrue cEvaluates yEvaluates
          · rw [Stmt.execList_append, cExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, cLookup, yExec]
          · intro name notTemp notCell
            rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp cLe (by omega)))
                (not_mem_names_nil _) notCell,
              keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
                notCell]
      | false =>
          obtain ⟨store₂, top, scope₂, outer₂, nEvaluates, nExec, agree₂, frame₂, scopeNames,
            outerShape, keeps₂⟩ :=
            aarm_unit nSimulates (fresh.mono (by omega)) admitted (enterNil _ _ _ _ agree₁)
              distinctCells lengthOk functionsOk (fun _ _ agree => agree) (fun _ frame => frame)
              (fun _ notCell => notCell) (fun _ _ _ => not_mem_names_nil _)
          refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
            ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
          · simp only [Solcore.Core.Wire.Expr.toCore]
            exact .ifFalse cEvaluates nEvaluates
          · rw [Stmt.execList_append, cExec]
            simp [Stmt.execList, Stmt.exec, Expr.eval, cLookup, nExec]
          · intro name notTemp notCell
            rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
                (not_mem_names_nil _) notCell,
              keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
                notCell]
  · obtain ⟨tested, conditionValue, selected, selectedValue, fallback, fallbackValue,
      testedEquation, conditionFound, selectedEquation, selectedFound, fallbackEquation,
      fallbackFound, rfl⟩ := AggregateEquations.ifE_value_ok unitTarget equation
    have conditionSpec := conditionIH admits conditionReady functions .bool bindings indent
      first tested conditionKind testedEquation fresh distinct
    have yesSpec := yesIH admits yesReady functions target bindings (indent + 4)
      (tested.nextId + 1) selected yesKind selectedEquation
      (fresh.mono (by have := conditionSpec.le; omega)) distinct
    have noSpec := noIH admits noReady functions target bindings (indent + 4) selected.nextId
      fallback noKind fallbackEquation
      (fresh.mono (by have := conditionSpec.le; have := yesSpec.le; omega)) distinct
    exact aifValue_spec unitTarget fresh distinct conditionSpec conditionFound yesSpec
      selectedFound noSpec fallbackFound
/-! ### Sum cases -/

/-- A case body sees one more binding: its payload, named by a fresh pattern
temporary. -/
theorem payload_fresh {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (le : first ≤ payload) :
    ANamesFresh (.word (payloadTemp payload) :: bindings) (payload + 1) :=
  fresh.cons (by omega) fun name same => by
    cases same
    exact payloadTemp_fresh _

theorem payload_distinct {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (le : first ≤ payload) : ANamesDistinct (.word (payloadTemp payload) :: bindings) :=
  distinct.cons fresh fun name same => by
    cases same
    exact ⟨payload, Or.inr (Or.inr rfl), le⟩

theorem payload_absent {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (le : first ≤ payload) :
    ∀ index found, anameAt bindings index = some found → found ≠ payloadTemp payload := by
  intro index found named same
  have := fresh index found named payload (Or.inr (Or.inr same))
  omega

theorem payload_outside {bindings : List Binding} {first payload : Nat}
    (fresh : ANamesFresh bindings first) (le : first ≤ payload) (word : Value) :
    ∀ index name, anameAt bindings index = some name →
      name ∉ Scope.names [(payloadTemp payload, word)] := by
  intro index name named mem
  simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
  exact payload_absent fresh le index name named mem

theorem payload_cells {bindings : List Binding} (payload name : String) :
    (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
      ∀ index : Nat, (Binding.word payload :: bindings)[index]? ≠ some (Binding.cellWord name) := by
  intro notCell index
  cases index with
  | zero => simp
  | succ index => simpa using notCell index

theorem payload_kinds (payload : String) (bindings : List Binding) :
    (Binding.word payload :: bindings).map Binding.kind = .word :: bindings.map Binding.kind :=
  rfl

/-- A sum `case` of a value type declares its zero result and matches the
scrutinee once; the selected case binds the payload under a fresh pattern name
and assigns its value to the result. -/
theorem acaseValue_spec {scrutinee yes no : CoreExpr} {target : ATarget}
    {functions : List String} {bindings : List Binding} {indent first : Nat}
    {tested selected fallback : ARendered} {value selectedValue fallbackValue : String}
    (unitTarget : ¬ target = .unit) (fresh : ANamesFresh bindings first)
    (distinct : ANamesDistinct bindings)
    (scrutineeSpec : ARenderSpec admits scrutinee .wordSum functions bindings indent first
      tested)
    (valueFound : tested.value = some value)
    (yesSpec : ARenderSpec admits yes target functions
      (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
      selected)
    (selectedFound : selected.value = some selectedValue)
    (noSpec : ARenderSpec admits no target functions
      (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
      fallback)
    (fallbackFound : fallback.value = some fallbackValue) :
    ARenderSpec admits (.caseE scrutinee yes no) target functions bindings indent first
      ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("match (" ++ value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
          (selected.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";")]) ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4)
              ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          (fallback.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";")]) ++
          [indentLine (indent + 4) "}", indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  obtain ⟨sStatements, sLines, sLe, sValue, sNames, sSimulates⟩ := scrutineeSpec
  obtain ⟨yStatements, yLines, yLe, yValue, yNames, ySimulates⟩ := yesSpec
  obtain ⟨nStatements, nLines, nLe, nValue, nNames, nSimulates⟩ := noSpec
  have result : ∀ last, tested.nextId < last → ATempIn first last (temporary tested.nextId) :=
    fun _ lt => aTempIn_temporary sLe lt
  have leftTemp : ATempIn first fallback.nextId (payloadTemp (tested.nextId + 1)) :=
    aTempIn_payloadTemp (by omega) (by omega)
  have rightTemp : ATempIn first fallback.nextId (payloadTemp selected.nextId) :=
    aTempIn_payloadTemp (by omega) (by omega)
  refine ⟨sStatements ++
      [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target),
        .matchSum (.name value) (payloadTemp (tested.nextId + 1))
          (yStatements ++ [.assign (temporary tested.nextId) (.name selectedValue)])
          (payloadTemp selected.nextId)
          (nStatements ++ [.assign (temporary tested.nextId) (.name fallbackValue)])],
    ?_, by dsimp only; omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, sLines, yLines, nLines, Stmt.listLines, Stmt.lines,
      Expr.print, azero_print unitTarget, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]
  · intro name same
    cases same
    exact Or.inr ⟨tested.nextId, rfl, sLe, by dsimp only; omega⟩
  · dsimp only
    intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
      Stmt.identifiers, Expr.identifiers, azero_identifiers, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with mem | same | ((same | same | mem | same | same) | same | mem | same | same)
    · exact (sNames name mem).mono (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact (sValue name valueFound).uses.mono (Nat.le_refl _) (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ leftTemp)))
    · exact ((yNames name mem).of_cons (fun found same => by
        cases same
        exact aTempIn_payloadTemp (by omega) (by omega)) (by omega)).mono (Nat.le_refl _)
          (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact ((yValue name selectedFound).uses.of_cons
        (fun found same => by
          cases same
          exact aTempIn_payloadTemp (by omega) (by omega)) (by omega)).mono (Nat.le_refl _)
          (by omega)
    · exact Or.inr (Or.inr (Or.inl (same ▸ rightTemp)))
    · exact ((nNames name mem).of_cons (fun found same => by cases same; exact rightTemp)
        (by omega)).mono (Nat.le_refl _) (Nat.le_refl _)
    · exact Or.inr (Or.inr (Or.inl (same ▸ result _ (by omega))))
    · subst same
      exact ((nValue name fallbackFound).uses.of_cons
        (fun found same => by cases same; exact rightTemp) (by omega)).mono (Nat.le_refl _)
          (Nat.le_refl _)
  · dsimp only
    intro context environment store scope outer admitted agree distinctCells lengthOk
      functionsOk
    obtain ⟨sCore, store₁, scope₁, outer₁, added₁, sEvaluates, sRepresents, sExec, agree₁,
      frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      sSimulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [valueFound, Option.bind_some] at sRepresents
    obtain ⟨sumSource, sLookup, sumValue⟩ := sRepresents
    have resultTemp := result (tested.nextId + 1) (Nat.lt_succ_self _)
    rw [selectedFound] at ySimulates
    rw [fallbackFound] at nSimulates
    have resultNotBinding : ∀ index found, anameAt bindings index = some found →
        found ≠ temporary tested.nextId := fresh.ne_temp resultTemp
    have agreeDeclared := agree₁.declare (fresh.ne_temp resultTemp) (azeroValue target)
    have declared : Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) ::
        outer₁) (temporary tested.nextId) = some (azeroValue target) := by
      simp [Frames.lookup_declared]
    have scrutineeSurvives : temporary tested.nextId ≠ value := by
      intro same
      exact ((sValue value valueFound).survives (last := tested.nextId + 1) fresh distinct
        sLe).1 (same ▸ aTempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _))
    have scrutineeLookup : Frames.lookup (((temporary tested.nextId, azeroValue target) ::
        scope₁) :: outer₁) value = some sumSource := by
      rw [Frames.lookup_declared, if_neg scrutineeSurvives]
      exact sLookup
    have prefixExec : Stmt.execList context (scope :: outer) (sStatements ++
        [.letDecl (temporary tested.nextId) (ATarget.localType target) (azero target)]) =
        some (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁) := by
      rw [Stmt.execList_append, sExec]
      simp [Stmt.execList, Stmt.exec, azero_eval, azeroValue_admits, Frames.declare]
    have keepsOutside : ∀ name, ¬ ATempIn first fallback.nextId name →
        (∀ index : Nat, bindings[index]? ≠ some (Binding.cellWord name)) →
        Frames.lookup (((temporary tested.nextId, azeroValue target) :: scope₁) :: outer₁)
          name = Frames.lookup (scope :: outer) name := by
      intro name notTemp notCell
      have different : temporary tested.nextId ≠ name := fun same =>
        notTemp (same ▸ result _ (by omega))
      rw [Frames.lookup_declared, if_neg different,
        keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
          notCell]
    have scopeNames₁ :
        Scope.names ((temporary tested.nextId, azeroValue target) :: scope₁) =
        (temporary tested.nextId :: added₁) ++ scope.names := by
      show temporary tested.nextId :: scope₁.names = _
      rw [names₁]
      rfl
    have addedOk : ∀ name ∈ temporary tested.nextId :: added₁,
        ATempIn first fallback.nextId name := by
      intro name mem
      rcases List.mem_cons.mp mem with same | mem
      · exact same ▸ result _ (by omega)
      · exact aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
    have resultNotPayload : ∀ payload : Nat, ∀ word : Value,
        temporary tested.nextId ∉ Scope.names [(payloadTemp payload, word)] := by
      intro payload word mem
      simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
      exact payloadTemp_ne_temporary _ _ mem.symm
    rcases sumValue with ⟨type, payload, rfl, rfl⟩ | ⟨type, payload, rfl, rfl⟩
    · obtain ⟨branchCore, branchValue, store₂, top, scope₂, outer₂, branchEvaluates,
        branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
        aarm_value (bindings := bindings) (environment := environment) unitTarget ySimulates
          (fresh.mono (by omega)) admitted
          (agreeDeclared.payload (payload_absent fresh (by omega)) payload)
          (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
          (by simpa using functionsOk) (fun _ _ agree => agree.tail)
          (fun _ frame => frame.of_cons fun _ same => by cases same)
          (payload_cells _) (payload_outside fresh (by omega) _)
          (not_aTempIn_of_aTempIn resultTemp (Or.inl (by omega)))
          (resultNotPayload _ _) (fresh.not_cell resultTemp) resultNotBinding declared
      refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
        ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
        scopeNames.trans scopeNames₁, addedOk⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .caseLeft sEvaluates branchEvaluates
      · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
          (Or.inl (by omega))) (resultNotPayload _ _) (fresh.not_cell resultTemp), if_pos rfl]
        exact ARepresents.of_value branchRepresents
      · rw [List.append_cons, Stmt.execList_append, prefixExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, scrutineeLookup, branchExec]
      · intro name notTemp notCell
        have different : temporary tested.nextId ≠ name := fun same =>
          notTemp (same ▸ result _ (by omega))
        rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (by omega)))
            (fun mem => by
              simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
              exact notTemp (mem ▸ leftTemp)) notCell,
          if_neg different, keepsOutside name notTemp notCell]
    · obtain ⟨branchCore, branchValue, store₂, top, scope₂, outer₂, branchEvaluates,
        branchRepresents, branchExec, agree₂, frame₂, scopeNames, outerShape, lookups⟩ :=
        aarm_value (bindings := bindings) (environment := environment) unitTarget nSimulates
          (fresh.mono (by omega)) admitted
          (agreeDeclared.payload (payload_absent fresh (by omega)) payload)
          (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
          (by simpa using functionsOk) (fun _ _ agree => agree.tail)
          (fun _ frame => frame.of_cons fun _ same => by cases same)
          (payload_cells _) (payload_outside fresh (by omega) _)
          (not_aTempIn_of_aTempIn resultTemp (Or.inl (by omega)))
          (resultNotPayload _ _) (fresh.not_cell resultTemp) resultNotBinding declared
      refine ⟨branchCore, store₂, scope₂, outer₂, temporary tested.nextId :: added₁, ?_, ?_,
        ?_, agree₂, frame₁.trans frame₂, ?_, outerShape.trans shape₁,
        scopeNames.trans scopeNames₁, addedOk⟩
      · simp only [Solcore.Core.Wire.Expr.toCore]
        exact .caseRight sEvaluates branchEvaluates
      · rw [Option.bind_some, lookups _ (not_aTempIn_of_aTempIn resultTemp
          (Or.inl (by omega))) (resultNotPayload _ _) (fresh.not_cell resultTemp), if_pos rfl]
        exact ARepresents.of_value branchRepresents
      · rw [List.append_cons, Stmt.execList_append, prefixExec]
        simp [Stmt.execList, Stmt.exec, Expr.eval, scrutineeLookup, branchExec]
      · intro name notTemp notCell
        have different : temporary tested.nextId ≠ name := fun same =>
          notTemp (same ▸ result _ (by omega))
        rw [lookups name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
            (fun mem => by
              simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
              exact notTemp (mem ▸ rightTemp)) notCell,
          if_neg different, keepsOutside name notTemp notCell]

theorem aRenderIH_caseE {scrutinee yes no : CoreExpr} (scrutineeIH : ARenderIH scrutinee)
    (yesIH : ARenderIH yes) (noIH : ARenderIH no) : ARenderIH (.caseE scrutinee yes no) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨scrutineeKind, yesKind, noKind, _⟩ := AggregateKinds.caseE accepted
  have scrutineeReady := AliasesReady.of_sub ready (sub := scrutinee) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have yesReady := AliasesReady.of_sub ready (sub := yes) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  have noReady := AliasesReady.of_sub ready (sub := no) fun uses => by
    simp [AggregateRenderer.usesOpcodeAliases, uses]
  by_cases unitTarget : target = .unit
  · subst unitTarget
    obtain ⟨tested, value, selected, fallback, testedEquation, valueFound, selectedEquation,
      fallbackEquation, rfl⟩ := AggregateEquations.caseE_unit_ok equation
    obtain ⟨sStatements, sLines, sLe, sValue, sNames, sSimulates⟩ :=
      scrutineeIH admits scrutineeReady functions .wordSum bindings indent first tested
        scrutineeKind testedEquation fresh distinct
    obtain ⟨yStatements, yLines, yLe, _, yNames, ySimulates⟩ :=
      yesIH admits yesReady functions .unit (.word (payloadTemp tested.nextId) :: bindings)
        (indent + 8) (tested.nextId + 1) selected (by rw [payload_kinds]; exact yesKind)
        selectedEquation (payload_fresh fresh sLe) (payload_distinct fresh distinct sLe)
    obtain ⟨nStatements, nLines, nLe, _, nNames, nSimulates⟩ :=
      noIH admits noReady functions .unit (.word (payloadTemp selected.nextId) :: bindings)
        (indent + 8) (selected.nextId + 1) fallback (by rw [payload_kinds]; exact noKind)
        fallbackEquation (payload_fresh fresh (by omega))
        (payload_distinct fresh distinct (by omega))
    refine ⟨sStatements ++ [.matchSum (.name value) (payloadTemp tested.nextId) yStatements
        (payloadTemp selected.nextId) nStatements], ?_,
      by dsimp only; omega, (fun _ same => by cases same), ?_, ?_⟩
    · simp only [Stmt.listLines_append, sLines, yLines, nLines, Stmt.listLines, Stmt.lines,
        Expr.print, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    · dsimp only
      intro name mem
      simp only [Stmt.listIdentifiers_append, List.mem_append, Stmt.listIdentifiers,
        Stmt.identifiers, Expr.identifiers, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      have leftTemp : ATempIn first fallback.nextId (payloadTemp tested.nextId) :=
        aTempIn_payloadTemp sLe (by omega)
      have rightTemp : ATempIn first fallback.nextId (payloadTemp selected.nextId) :=
        aTempIn_payloadTemp (by omega) (by omega)
      rcases mem with mem | ((same | same | mem) | same | mem)
      · exact (sNames name mem).mono (Nat.le_refl _) (by omega)
      · subst same
        exact (sValue name valueFound).uses.mono (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr (Or.inl (same ▸ leftTemp)))
      · exact ((yNames name mem).of_cons (fun found same => by
          cases same
          exact aTempIn_payloadTemp (by omega) (by omega)) (by omega)).mono (Nat.le_refl _)
            (by omega)
      · exact Or.inr (Or.inr (Or.inl (same ▸ rightTemp)))
      · exact ((nNames name mem).of_cons (fun found same => by cases same; exact rightTemp)
          (by omega)).mono (Nat.le_refl _) (Nat.le_refl _)
    · dsimp only
      intro context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
      obtain ⟨sCore, store₁, scope₁, outer₁, added₁, sEvaluates, sRepresents, sExec, agree₁,
        frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
        sSimulates context environment store scope outer admitted agree distinctCells lengthOk
          functionsOk
      rw [valueFound, Option.bind_some] at sRepresents
      obtain ⟨_, sLookup, sumValue⟩ := sRepresents
      have addedOk : ∀ name ∈ added₁, ATempIn first fallback.nextId name :=
        fun name mem => aTempIn_mono (addedTemp₁ name mem) (Nat.le_refl _) (by omega)
      rcases sumValue with ⟨type, payload, rfl, rfl⟩ | ⟨type, payload, rfl, rfl⟩
      · obtain ⟨store₂, top, scope₂, outer₂, yEvaluates, yExec, agree₂, frame₂, scopeNames,
          outerShape, keeps₂⟩ :=
          aarm_unit (bindings := bindings) (environment := environment) ySimulates
            (fresh.mono (by omega)) admitted
            (agree₁.payload (payload_absent fresh sLe) payload)
            (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
            (by simpa using functionsOk) (fun _ _ agree => agree.tail)
            (fun _ frame => frame.of_cons fun _ same => by cases same)
            (payload_cells _) (payload_outside fresh sLe _)
        refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
          ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .caseLeft sEvaluates yEvaluates
        · rw [Stmt.execList_append, sExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, sLookup, yExec]
        · intro name notTemp notCell
          rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (by omega)))
              (fun mem => by
                simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
                exact notTemp (mem ▸ aTempIn_payloadTemp sLe (by omega))) notCell,
            keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
              notCell]
      · obtain ⟨store₂, top, scope₂, outer₂, nEvaluates, nExec, agree₂, frame₂, scopeNames,
          outerShape, keeps₂⟩ :=
          aarm_unit (bindings := bindings) (environment := environment) nSimulates
            (fresh.mono (by omega)) admitted
            (agree₁.payload (payload_absent fresh (by omega)) payload)
            (distinctCells.cons_value fun _ same => by cases same) (by simp; omega)
            (by simpa using functionsOk) (fun _ _ agree => agree.tail)
            (fun _ frame => frame.of_cons fun _ same => by cases same)
            (payload_cells _) (payload_outside fresh (by omega) _)
        refine ⟨.unit, store₂, scope₂, outer₂, added₁, ?_, rfl, ?_, agree₂, frame₁.trans frame₂,
          ?_, outerShape.trans shape₁, scopeNames.trans names₁, addedOk⟩
        · simp only [Solcore.Core.Wire.Expr.toCore]
          exact .caseRight sEvaluates nEvaluates
        · rw [Stmt.execList_append, sExec]
          simp [Stmt.execList, Stmt.exec, Expr.eval, sLookup, nExec]
        · intro name notTemp notCell
          rw [keeps₂ name (fun temp => notTemp (aTempIn_mono temp (by omega) (Nat.le_refl _)))
              (fun mem => by
                simp only [Scope.names, List.map_cons, List.map_nil, List.mem_singleton] at mem
                exact notTemp (mem ▸ aTempIn_payloadTemp (by omega) (by omega))) notCell,
            keeps₁ name (fun temp => notTemp (aTempIn_mono temp (Nat.le_refl _) (by omega)))
              notCell]
  · obtain ⟨tested, value, selected, selectedValue, fallback, fallbackValue, testedEquation,
      valueFound, selectedEquation, selectedFound, fallbackEquation, fallbackFound, rfl⟩ :=
      AggregateEquations.caseE_value_ok unitTarget equation
    have scrutineeSpec := scrutineeIH admits scrutineeReady functions .wordSum bindings indent
      first tested scrutineeKind testedEquation fresh distinct
    have sLe := scrutineeSpec.le
    have yesSpec := yesIH admits yesReady functions target
      (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
      selected (by rw [payload_kinds]; exact yesKind) selectedEquation
      (payload_fresh fresh (by omega)) (payload_distinct fresh distinct (by omega))
    have yLe := yesSpec.le
    have noSpec := noIH admits noReady functions target
      (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
      fallback (by rw [payload_kinds]; exact noKind) fallbackEquation
      (payload_fresh fresh (by omega)) (payload_distinct fresh distinct (by omega))
    exact acaseValue_spec unitTarget fresh distinct scrutineeSpec valueFound yesSpec
      selectedFound noSpec fallbackFound
/-! ### Projections -/

/-- A projection declares its zero result, matches the pair once, and assigns
the picked component inside the case scope. -/
theorem projection_exec (context : Context) (scope : Scope) (outer : Frames) (next : Nat)
    (value : String) (left right : Nat) (pickFirst : Bool)
    (lookup : Frames.lookup (scope :: outer) value = some (.pair left right))
    (distinct : temporary next ≠ value) :
    Stmt.execList context (scope :: outer)
        (projectionStmts next value (if pickFirst then next + 1 else next + 2)) =
      some (((temporary next, .word (if pickFirst then left else right)) :: scope) :: outer) := by
  have lookup' : Frames.lookup (((temporary next, .word 0) :: scope) :: outer) value =
      some (.pair left right) := by
    rw [Frames.lookup_declared, if_neg distinct]
    exact lookup
  have firstNe : payloadTemp (next + 2) ≠ payloadTemp (next + 1) := fun same => by
    have := payloadTemp_injective same
    omega
  have zero : 0 < Evm.modulus := Nat.two_pow_pos 256
  have resultLookup : ∀ word : Value, Frames.lookup ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, word) :: scope) :: outer)
      (temporary next) = some word := by
    intro word
    simp [Frames.lookup, Scope.get?, payloadTemp_ne_temporary]
  have firstLookup : ∀ word : Value, Frames.lookup ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, word) :: scope) :: outer)
      (payloadTemp (next + 1)) = some (.word left) := by
    intro word
    simp [Frames.lookup, Scope.get?, firstNe]
  have secondLookup : ∀ word : Value, Frames.lookup ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, word) :: scope) :: outer)
      (payloadTemp (next + 2)) = some (.word right) := by
    intro word
    simp [Frames.lookup, Scope.get?]
  have assigned : ∀ old new : Value, Frames.assign ([(payloadTemp (next + 2), .word right),
      (payloadTemp (next + 1), .word left)] :: ((temporary next, old) :: scope) :: outer)
      (temporary next) new = some ([(payloadTemp (next + 2), .word right),
        (payloadTemp (next + 1), .word left)] :: ((temporary next, new) :: scope) :: outer) := by
    intro old new
    simp [Frames.assign, Scope.set?, payloadTemp_ne_temporary]
  cases pickFirst <;>
    simp [projectionStmts, Stmt.execList, Stmt.exec, Expr.eval, zero, LocalType.admits,
      Frames.declare, lookup', resultLookup, firstLookup, secondLookup, assigned, Value.sameType]

theorem aprojection_spec {expression operand : CoreExpr} {functions : List String}
    {bindings : List Binding} {indent first : Nat} {operandRendered : ARendered}
    {value : String} (pickFirst : Bool)
    (fresh : ANamesFresh bindings first) (distinct : ANamesDistinct bindings)
    (spec : ARenderSpec admits operand .wordPair functions bindings indent first operandRendered)
    (named : operandRendered.value = some value)
    (core : ∀ (environment : Solcore.Core.Environment) (store store₁ : Solcore.Core.Store)
      (left right : Solcore.Core.Word),
      Solcore.Core.Evaluates environment store operand.toCore
        (.pair (.word left) (.word right)) store₁ →
      Solcore.Core.Evaluates environment store expression.toCore
        (.word (if pickFirst then left else right)) store₁) :
    ARenderSpec admits expression .word functions bindings indent first
      ⟨operandRendered.lines ++ Stmt.listLines indent (projectionStmts operandRendered.nextId value
          (if pickFirst then operandRendered.nextId + 1 else operandRendered.nextId + 2)),
        some (temporary operandRendered.nextId), operandRendered.nextId + 3⟩ := by
  obtain ⟨statements, lines, le, valueName, uses, simulates⟩ := spec
  unfold ARenderSpec
  dsimp only
  have resultTemp : ATempIn first (operandRendered.nextId + 3)
      (temporary operandRendered.nextId) := aTempIn_temporary le (by omega)
  refine ⟨statements ++ projectionStmts operandRendered.nextId value
      (if pickFirst then operandRendered.nextId + 1 else operandRendered.nextId + 2), ?_,
    by omega, ?_, ?_, ?_⟩
  · simp only [Stmt.listLines_append, lines]
  · intro name same
    cases same
    exact Or.inr ⟨operandRendered.nextId, rfl, le, by omega⟩
  · intro name mem
    simp only [Stmt.listIdentifiers_append, List.mem_append] at mem
    rcases mem with mem | mem
    · exact (uses name mem).mono (Nat.le_refl _) (by omega)
    · simp only [projectionStmts, Stmt.listIdentifiers, Stmt.identifiers, Expr.identifiers,
        List.append_nil, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at mem
      rcases mem with same | same | same | same | same | same
      · exact Or.inr (Or.inr (Or.inl (same ▸ resultTemp)))
      · subst same
        exact (valueName name named).uses.mono (Nat.le_refl _) (by omega)
      · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_payloadTemp (by omega) (by omega))))
      · exact Or.inr (Or.inr (Or.inl (same ▸ aTempIn_payloadTemp (by omega) (by omega))))
      · exact Or.inr (Or.inr (Or.inl (same ▸ resultTemp)))
      · refine Or.inr (Or.inr (Or.inl (same ▸ ?_)))
        cases pickFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          exact aTempIn_payloadTemp (by omega) (by omega)
  · refine aresult_simulates fresh (fun context environment store scope outer admitted agree
      distinctCells lengthOk functionsOk => ?_) le (by omega)
    obtain ⟨operandCore, store₁, scope₁, outer₁, added₁, evaluates, represents, exec, agree₁,
      frame₁, keeps₁, shape₁, names₁, addedTemp₁⟩ :=
      simulates context environment store scope outer admitted agree distinctCells lengthOk
        functionsOk
    rw [named, Option.bind_some] at represents
    obtain ⟨_, lookup, left, right, rfl, rfl⟩ := represents
    have distinctName : temporary operandRendered.nextId ≠ value := by
      intro same
      exact ((valueName value named).survives (last := operandRendered.nextId + 1) fresh
        distinct le).1 (same ▸ aTempIn_temporary (Nat.le_refl _) (Nat.lt_succ_self _))
    have tail := projection_exec context scope₁ outer₁ operandRendered.nextId value left.val
      right.val pickFirst lookup distinctName
    refine ⟨.word (if pickFirst then left else right),
      .word (if pickFirst then left.val else right.val), store₁, scope₁, outer₁, added₁,
      core _ _ _ _ _ evaluates, ?_, exec, tail, agree₁, frame₁, keeps₁, shape₁, names₁,
      addedTemp₁⟩
    cases pickFirst
    · exact ⟨right, rfl, rfl⟩
    · exact ⟨left, rfl, rfl⟩

theorem aRenderIH_first {operand : CoreExpr} (operandIH : ARenderIH operand) :
    ARenderIH (.first operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨operandKind, resultWord⟩ := AggregateKinds.first accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨operandRendered, value, operandEquation, named, rfl⟩ :=
    AggregateEquations.first_ok equation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .wordPair bindings indent first operandRendered operandKind operandEquation fresh
    distinct
  exact aprojection_spec true fresh distinct spec named fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .first evaluates

theorem aRenderIH_second {operand : CoreExpr} (operandIH : ARenderIH operand) :
    ARenderIH (.second operand) := by
  intro admits ready functions target bindings indent first rendered accepted equation fresh
    distinct
  obtain ⟨operandKind, resultWord⟩ := AggregateKinds.second accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  obtain ⟨operandRendered, value, operandEquation, named, rfl⟩ :=
    AggregateEquations.second_ok equation
  have spec := operandIH admits (AliasesReady.of_sub ready fun uses => by
      simp [AggregateRenderer.usesOpcodeAliases, uses])
    functions .wordPair bindings indent first operandRendered operandKind operandEquation fresh
    distinct
  exact aprojection_spec false fresh distinct spec named fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .second evaluates

end

/-! ### The structural induction -/

/-- An expression the profile never accepts at a value or Unit target. -/
theorem aRenderIH_rejected (expression : CoreExpr)
    (rejected : ∀ locals prior, initializerKind? locals prior expression = none ∨
      initializerKind? locals prior expression = some .cellWord) :
    ARenderIH expression := by
  intro _ _ functions target bindings _ _ _ accepted
  rcases rejected (bindings.map Binding.kind) functions.length with none | cell
  · rw [none] at accepted
    cases accepted
  · rw [cell] at accepted
    cases target <;> cases accepted

theorem aRenderIH_let {initializer body : CoreExpr} (initializerIH : ARenderIH initializer)
    (cellIH : ∀ inner, initializer = .newCell .word inner → ARenderIH inner)
    (bodyIH : ARenderIH body) : ARenderIH (.letE initializer body) := by
  by_cases cell : ∃ inner, initializer = .newCell .word inner
  · obtain ⟨inner, rfl⟩ := cell
    exact aRenderIH_newCellLet (cellIH inner rfl) bodyIH
  · exact aRenderIH_letE (fun inner same => cell ⟨inner, same⟩) initializerIH bodyIH

theorem aRenderIH_unary {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : ARenderIH operand) : ARenderIH (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact aRenderIH_unarySource selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz => exact aRenderIH_clz operandIH
      all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_binary {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : ARenderIH left) (rightIH : ARenderIH right) : ARenderIH (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact aRenderIH_binarySource selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some _ => exact aRenderIH_binaryPrimitive extended leftIH rightIH
      | none =>
          cases op <;> first
            | exact aRenderIH_rejected _ fun _ _ => Or.inl rfl
            | (simp [sourceBinary?] at selected; done)
            | (simp [primitiveBinary?] at extended; done)

theorem aRenderIH_applyAny {function argument : CoreExpr} (argumentIH : ARenderIH argument) :
    ARenderIH (.apply function argument) := by
  cases function
  case var index => exact aRenderIH_apply argumentIH
  all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_loadCellAny {reference : CoreExpr} : ARenderIH (.loadCell reference) := by
  cases reference
  case var index => exact aRenderIH_loadCell index
  all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_storeCellAny {reference value : CoreExpr} (valueIH : ARenderIH value) :
    ARenderIH (.storeCell reference value) := by
  cases reference
  case var index => exact aRenderIH_storeCell index valueIH
  all_goals exact aRenderIH_rejected _ fun _ _ => Or.inl rfl

theorem aRenderIH_newCell (elementType : Solcore.Core.Wire.Ty) (inner : CoreExpr) :
    ARenderIH (.newCell elementType inner) := by
  refine aRenderIH_rejected _ fun locals prior => ?_
  cases found : initializerKind? locals prior (.newCell elementType inner) with
  | none => exact Or.inl rfl
  | some kind =>
      right
      cases elementType
      all_goals first
        | rw [(AggregateKinds.newCell found).1]
        | cases found

/-- Every expression that the aggregate profile accepts and the actual
renderer renders satisfies its rendering specification. The second component
is the specification for the initializer of a direct `newCell` let. -/
theorem aggregate_render_spec : (expression : CoreExpr) →
    ARenderIH expression ∧ ∀ inner, expression = .newCell .word inner → ARenderIH inner
  | .word value => ⟨aRenderIH_word value, fun _ same => by cases same⟩
  | .bool value => ⟨aRenderIH_bool value, fun _ same => by cases same⟩
  | .unit => ⟨aRenderIH_unit, fun _ same => by cases same⟩
  | .var index => ⟨aRenderIH_var index, fun _ same => by cases same⟩
  | .letE initializer body =>
      ⟨aRenderIH_let (aggregate_render_spec initializer).1 (aggregate_render_spec initializer).2
        (aggregate_render_spec body).1, fun _ same => by cases same⟩
  | .ifE condition yes no =>
      ⟨aRenderIH_ifE (aggregate_render_spec condition).1 (aggregate_render_spec yes).1
        (aggregate_render_spec no).1, fun _ same => by cases same⟩
  | .pair left right =>
      ⟨aRenderIH_pair (aggregate_render_spec left).1 (aggregate_render_spec right).1,
        fun _ same => by cases same⟩
  | .first operand => ⟨aRenderIH_first (aggregate_render_spec operand).1,
      fun _ same => by cases same⟩
  | .second operand => ⟨aRenderIH_second (aggregate_render_spec operand).1,
      fun _ same => by cases same⟩
  | .inLeft _ payload => ⟨aRenderIH_inLeft (aggregate_render_spec payload).1,
      fun _ same => by cases same⟩
  | .inRight _ payload => ⟨aRenderIH_inRight (aggregate_render_spec payload).1,
      fun _ same => by cases same⟩
  | .caseE scrutinee yes no =>
      ⟨aRenderIH_caseE (aggregate_render_spec scrutinee).1 (aggregate_render_spec yes).1
        (aggregate_render_spec no).1, fun _ same => by cases same⟩
  | .unary _ operand => ⟨aRenderIH_unary (aggregate_render_spec operand).1,
      fun _ same => by cases same⟩
  | .binary _ left right =>
      ⟨aRenderIH_binary (aggregate_render_spec left).1 (aggregate_render_spec right).1,
        fun _ same => by cases same⟩
  | .ternary _ one two three =>
      ⟨aRenderIH_ternary (aggregate_render_spec one).1 (aggregate_render_spec two).1
        (aggregate_render_spec three).1, fun _ same => by cases same⟩
  | .apply _ argument => ⟨aRenderIH_applyAny (aggregate_render_spec argument).1,
      fun _ same => by cases same⟩
  | .newCell elementType inner => ⟨aRenderIH_newCell elementType inner, fun _ same => by
      cases same
      exact (aggregate_render_spec inner).1⟩
  | .loadCell _ => ⟨aRenderIH_loadCellAny, fun _ same => by cases same⟩
  | .storeCell _ value => ⟨aRenderIH_storeCellAny (aggregate_render_spec value).1,
      fun _ same => by cases same⟩
  | .integer _ => ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .lambda _ _ _ => ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .construct _ _ => ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩
  | .matchData _ _ _ _ =>
      ⟨aRenderIH_rejected _ fun _ _ => Or.inl rfl, fun _ same => by cases same⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregateCallGraphEquations
/-! Equations for the actual `AggregateCallGraphRenderer.render`, stated with
the source syntax and printer. This renderer prints the aggregate forms of
`AggregateRenderer` and the call-graph formatting of scalar operations and
calls, but has no cells and no Unit values; every binding is a Word, Boolean,
pair or sum. Its private helpers are unfolded by definitional equality. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

abbrev GBinding := AggregateCallGraphRenderer.Binding

/-- A binding of the aggregate call-graph renderer as a binding of the
aggregate renderer; both name the same kinds of value. -/
def GBinding.toAggregate : GBinding → AggregateRenderer.Binding
  | .word name => .word name
  | .bool name => .bool name
  | .wordPair name => .wordPair name
  | .wordSum name => .wordSum name

theorem GBinding.toAggregate_kind (binding : GBinding) :
    binding.toAggregate.kind = binding.kind := by
  cases binding <;> rfl

theorem kinds_toAggregate (bindings : List GBinding) :
    (bindings.map GBinding.toAggregate).map AggregateRenderer.Binding.kind =
      bindings.map AggregateCallGraphRenderer.Binding.kind := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih => simp [GBinding.toAggregate_kind, ih]

/-- The binding the renderer's private `binding` builds for a value kind. -/
def gvalueBinding : ATarget → String → GBinding
  | .bool, name => .bool name
  | .wordPair, name => .wordPair name
  | .wordSum, name => .wordSum name
  | _, name => .word name

theorem gvalueBinding_toAggregate {kind : ATarget} (valued : kind ≠ .unit) (name : String) :
    (gvalueBinding kind name).toAggregate = valueBinding kind name := by
  cases kind
  case unit => exact absurd rfl valued
  all_goals rfl

namespace AggregateCallGraphEquations

variable {functions : List String} {target : ATarget} {bindings : List GBinding}
  {indent first : Nat} {rendered : ScalarRenderer.Rendered}

theorem word (value : Solcore.Core.Word) :
    AggregateCallGraphRenderer.render functions target bindings indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        temporary first, first + 1⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  rfl

theorem bool (value : Bool) :
    AggregateCallGraphRenderer.render functions target bindings indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        temporary first, first + 1⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  rfl

theorem var_ok {index : Nat}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.var index) = .ok rendered) :
    ∃ name, target ≠ .unit ∧ bindings[index]? = some (gvalueBinding target name) ∧
      rendered = ⟨[], name, first⟩ := by
  simp only [AggregateCallGraphRenderer.render] at equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      cases binding <;> cases target <;> first
        | exact ⟨_, by simp, rfl, (Except.ok.inj equation).symm⟩
        | cases equation

theorem letE_ok {initializer body : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ kind value rest, kind ≠ .unit ∧
      infer? (bindings.map AggregateCallGraphRenderer.Binding.kind) functions.length initializer =
        some kind ∧
      AggregateCallGraphRenderer.render functions kind bindings indent first initializer =
        .ok value ∧
      AggregateCallGraphRenderer.render functions target
        (gvalueBinding kind (temporary value.nextId) :: bindings) indent (value.nextId + 1)
          body = .ok rest ∧
      rendered = ⟨value.lines ++
        Stmt.lines indent (.letDecl (temporary value.nextId) (ATarget.localType kind)
          (.name value.value)) ++
        rest.lines, rest.value, rest.nextId⟩ := by
  simp only [AggregateCallGraphRenderer.render] at equation
  split at equation
  · rename_i kind inferred
    obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    cases kind
    case unit => cases equation
    all_goals
      obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
      exact ⟨_, value, rest, by simp, inferred, valueEquation, restEquation,
        (Except.ok.inj equation).symm⟩
  · cases equation

theorem ifE_ok {condition yes no : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested selected fallback,
      AggregateCallGraphRenderer.render functions .bool bindings indent first condition =
        .ok tested ∧
      AggregateCallGraphRenderer.render functions target bindings (indent + 4)
        (tested.nextId + 1) yes = .ok selected ∧
      AggregateCallGraphRenderer.render functions target bindings (indent + 4) selected.nextId
        no = .ok fallback ∧
      (target ≠ .unit → rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selected.value ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallback.value ++ ";"),
            indentLine indent "}"],
        temporary tested.nextId, fallback.nextId⟩) := by
  simp only [AggregateCallGraphRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    fun valued => ?_⟩
  rw [← Except.ok.inj equation]
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

/-- `!` and `~` bind their result to a fresh temporary. -/
theorem unary (scalar : Target) (op : Solcore.Core.Wire.UnaryOp) (sourceOp : UnaryOp)
    (operand : CoreExpr) (selected : sourceUnary? op = some sourceOp) :
    AggregateCallGraphRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.unary op operand) =
      (AggregateCallGraphRenderer.render functions (if op == .boolNot then .bool else .word)
        bindings indent first operand).bind fun value =>
          .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
              (LocalType.ofTarget scalar) (.unary sourceOp (.name value.value))),
            temporary value.nextId, value.nextId + 1⟩ := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateCallGraphRenderer.render] <;> rfl

/-- `CLZ` snapshots its operand, then calls the raw opcode alias. -/
theorem clz (operand : CoreExpr) :
    AggregateCallGraphRenderer.render functions .word bindings indent first
        (.unary .wordClz operand) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first operand).bind
        fun value =>
          .ok ⟨(snapshotOf indent value).lines ++ Stmt.lines indent
              (.letDecl (temporary (value.nextId + 1)) .word
                (.call1 "sc_clz" (.name (temporary value.nextId)))),
            temporary (value.nextId + 1), value.nextId + 2⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  rfl

/-- The infix operations bind their result to a fresh temporary. -/
theorem binary (scalar : Target) (op : Solcore.Core.Wire.BinaryOp) (sourceOp : BinaryOp)
    (left right : CoreExpr) (selected : sourceBinary? op = some sourceOp) :
    AggregateCallGraphRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first left).bind
        fun leftValue =>
          (AggregateCallGraphRenderer.render functions .word bindings indent leftValue.nextId
            right).bind fun rightValue =>
              .ok ⟨leftValue.lines ++ rightValue.lines ++ Stmt.lines indent
                  (.letDecl (temporary rightValue.nextId) (LocalType.ofTarget scalar)
                    (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
                temporary rightValue.nextId, rightValue.nextId + 1⟩ := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateCallGraphRenderer.render] <;> rfl

/-- Extended binary operations snapshot both operands, left to right, then
call the raw opcode alias. -/
theorem binary_primitive (scalar : Target) (op : Solcore.Core.Wire.BinaryOp)
    (build : String → String → Expr) (left right : CoreExpr)
    (selected : primitiveBinary? op = some build) :
    AggregateCallGraphRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first left).bind
        fun leftValue =>
          (AggregateCallGraphRenderer.render functions .word bindings indent
            (leftValue.nextId + 1) right).bind fun rightValue =>
              .ok ⟨(snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines ++
                  Stmt.lines indent (.letDecl (temporary (rightValue.nextId + 1))
                    (LocalType.ofTarget scalar)
                    (build (temporary leftValue.nextId) (temporary rightValue.nextId))),
                temporary (rightValue.nextId + 1), rightValue.nextId + 2⟩ := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateCallGraphRenderer.render] <;> rfl

/-- `ADDMOD` and `MULMOD` snapshot all three operands, then call the raw
opcode alias. -/
theorem ternary (op : Solcore.Core.Wire.TernaryOp) (one two three : CoreExpr) :
    AggregateCallGraphRenderer.render functions .word bindings indent first
        (.ternary op one two three) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first one).bind
        fun oneValue =>
          (AggregateCallGraphRenderer.render functions .word bindings indent
            (oneValue.nextId + 1) two).bind fun twoValue =>
              (AggregateCallGraphRenderer.render functions .word bindings indent
                (twoValue.nextId + 1) three).bind fun threeValue =>
                  .ok ⟨(snapshotOf indent oneValue).lines ++
                      (snapshotOf indent twoValue).lines ++
                      (snapshotOf indent threeValue).lines ++
                      Stmt.lines indent (.letDecl (temporary (threeValue.nextId + 1)) .word
                        (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
                          (.name (temporary twoValue.nextId))
                          (.name (temporary threeValue.nextId)))),
                    temporary (threeValue.nextId + 1), threeValue.nextId + 2⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  cases op <;> rfl

/-- A call to an earlier helper snapshots its argument, then calls the helper. -/
theorem apply_ok {index : Nat} {argument : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.apply (.var index) argument) = .ok rendered) :
    target = .word ∧ bindings.length ≤ index ∧ ∃ callee value,
      functions[index - bindings.length]? = some callee ∧
      AggregateCallGraphRenderer.render functions .word bindings indent first argument =
        .ok value ∧
      rendered = ⟨(snapshotOf indent value).lines ++ Stmt.lines indent
          (.letDecl (temporary (value.nextId + 1)) .word
            (.call1 callee (.name (temporary value.nextId)))),
        temporary (value.nextId + 1), value.nextId + 2⟩ := by
  cases target
  case word =>
    by_cases below : index < bindings.length
    · dsimp only [AggregateCallGraphRenderer.render] at equation
      rw [if_pos below] at equation
      cases equation
    · cases found : functions[index - bindings.length]? with
      | none =>
          dsimp only [AggregateCallGraphRenderer.render] at equation
          rw [if_neg below, found] at equation
          cases equation
      | some callee =>
          dsimp only [AggregateCallGraphRenderer.render] at equation
          rw [if_neg below, found] at equation
          obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
          exact ⟨rfl, Nat.le_of_not_lt below, callee, value, rfl, valueEquation,
            (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem pair_ok {left right : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.pair left right) = .ok rendered) :
    target = .wordPair ∧ ∃ leftValue rightValue,
      AggregateCallGraphRenderer.render functions .word bindings indent first left =
        .ok leftValue ∧
      AggregateCallGraphRenderer.render functions .word bindings indent leftValue.nextId right =
        .ok rightValue ∧
      rendered = ⟨leftValue.lines ++ rightValue.lines ++
          Stmt.lines indent (.letDecl (temporary rightValue.nextId) .wordPair
            (.tuple (.name leftValue.value) (.name rightValue.value))),
        temporary rightValue.nextId, rightValue.nextId + 1⟩ := by
  cases target
  case wordPair =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨rfl, leftValue, rightValue, leftEquation, rightEquation,
      (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem first_ok {operand : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.first operand) = .ok rendered) :
    target = .word ∧ ∃ operandValue,
      AggregateCallGraphRenderer.render functions .wordPair bindings indent first operand =
        .ok operandValue ∧
      rendered = ⟨operandValue.lines ++ Stmt.listLines indent
          (projectionStmts operandValue.nextId operandValue.value (operandValue.nextId + 1)),
        temporary operandValue.nextId, operandValue.nextId + 3⟩ := by
  cases target
  case word =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨operandValue, operandEquation, equation⟩ := except_bind_eq_ok equation
    refine ⟨rfl, operandValue, operandEquation, ?_⟩
    rw [← Except.ok.inj equation]
    show (⟨operandValue.lines ++ _ ++ _, _, _⟩ : ScalarRenderer.Rendered) = _
    simp only [List.append_assoc]
    rfl
  all_goals cases equation

theorem second_ok {operand : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.second operand) = .ok rendered) :
    target = .word ∧ ∃ operandValue,
      AggregateCallGraphRenderer.render functions .wordPair bindings indent first operand =
        .ok operandValue ∧
      rendered = ⟨operandValue.lines ++ Stmt.listLines indent
          (projectionStmts operandValue.nextId operandValue.value (operandValue.nextId + 2)),
        temporary operandValue.nextId, operandValue.nextId + 3⟩ := by
  cases target
  case word =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨operandValue, operandEquation, equation⟩ := except_bind_eq_ok equation
    refine ⟨rfl, operandValue, operandEquation, ?_⟩
    rw [← Except.ok.inj equation]
    show (⟨operandValue.lines ++ _ ++ _, _, _⟩ : ScalarRenderer.Rendered) = _
    simp only [List.append_assoc]
    rfl
  all_goals cases equation

theorem inLeft_ok {payload : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.inLeft .word payload) = .ok rendered) :
    target = .wordSum ∧ ∃ payloadValue,
      AggregateCallGraphRenderer.render functions .word bindings indent first payload =
        .ok payloadValue ∧
      rendered = ⟨payloadValue.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadValue.nextId) .wordSum (.inl (.name payloadValue.value))),
        temporary payloadValue.nextId, payloadValue.nextId + 1⟩ := by
  cases target
  case wordSum =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨payloadValue, payloadEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨rfl, payloadValue, payloadEquation, (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem inRight_ok {payload : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.inRight .word payload) = .ok rendered) :
    target = .wordSum ∧ ∃ payloadValue,
      AggregateCallGraphRenderer.render functions .word bindings indent first payload =
        .ok payloadValue ∧
      rendered = ⟨payloadValue.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadValue.nextId) .wordSum (.inr (.name payloadValue.value))),
        temporary payloadValue.nextId, payloadValue.nextId + 1⟩ := by
  cases target
  case wordSum =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨payloadValue, payloadEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨rfl, payloadValue, payloadEquation, (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem caseE_ok {scrutinee yes no : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.caseE scrutinee yes no) = .ok rendered) :
    ∃ tested selected fallback,
      AggregateCallGraphRenderer.render functions .wordSum bindings indent first scrutinee =
        .ok tested ∧
      AggregateCallGraphRenderer.render functions target
        (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
          yes = .ok selected ∧
      AggregateCallGraphRenderer.render functions target
        (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
          no = .ok fallback ∧
      (target ≠ .unit → rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("match (" ++ tested.value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
          (selected.lines ++ [indentLine (indent + 8)
            (temporary tested.nextId ++ " = " ++ selected.value ++ ";")]) ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4)
              ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          (fallback.lines ++ [indentLine (indent + 8)
            (temporary tested.nextId ++ " = " ++ fallback.value ++ ";")]) ++
          [indentLine (indent + 4) "}", indentLine indent "}"],
        temporary tested.nextId, fallback.nextId⟩) := by
  simp only [AggregateCallGraphRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    fun valued => ?_⟩
  rw [← Except.ok.inj equation]
  cases target
  case unit => exact absurd rfl valued
  all_goals
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- The renderer rejects Unit, cells, integers, closures, data and indirect
calls outright. -/
theorem rejected {expression : CoreExpr}
    (rejects : expression = .unit ∨ (∃ value, expression = .integer value) ∨
      (∃ parameterType resultType body, expression = .lambda parameterType resultType body) ∨
      (∃ elementType inner, expression = .newCell elementType inner) ∨
      (∃ reference, expression = .loadCell reference) ∨
      (∃ reference value, expression = .storeCell reference value) ∨
      (∃ constructor payload, expression = .construct constructor payload) ∨
      (∃ dataType resultType scrutinee branches,
        expression = .matchData dataType resultType scrutinee branches))
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      expression = .ok rendered) : False := by
  rcases rejects with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ |
    ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> cases equation

end AggregateCallGraphEquations

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.AggregateCallGraphPreservation
/-! Meaning preservation for the actual `AggregateCallGraphRenderer.render`. Its
bindings are a subset of the aggregate renderer's, so its rendering
specification is the aggregate one over the translated bindings. The emitter
always imports the raw opcode aliases, so every body runs in a primitive call
context. Each case applies the renderer-independent combinators of
`AggregatePreservation` and `AggregateControl`; this renderer has no cells,
no Unit values, and snapshots a helper call's argument before the call. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-- What the induction establishes for one expression: a successful rendering
is at a value type and satisfies the aggregate rendering specification over
the translated bindings. -/
def GRenderIH (expression : CoreExpr) : Prop :=
  ∀ (functions : List String) (target : ATarget) (bindings : List GBinding) (indent first : Nat)
    (rendered : ScalarRenderer.Rendered),
    initializerKind? (bindings.map AggregateCallGraphRenderer.Binding.kind) functions.length
      expression = some target.toLocal →
    AggregateCallGraphRenderer.render functions target bindings indent first expression =
      .ok rendered →
    ANamesFresh (bindings.map GBinding.toAggregate) first →
    ANamesDistinct (bindings.map GBinding.toAggregate) →
    target ≠ .unit ∧
      ARenderSpec PrimitiveContext expression target functions
        (bindings.map GBinding.toAggregate) indent first (ARendered.ofScalar rendered)

theorem gvalueBinding_kind {kind : ATarget} (valued : kind ≠ .unit) (name : String) :
    (gvalueBinding kind name).kind = kind.toLocal := by
  cases kind
  case unit => exact absurd rfl valued
  all_goals rfl

/-! ### Literals and locals -/

theorem gRenderIH_word (value : Solcore.Core.Word) : GRenderIH (.word value) := by
  intro functions target bindings indent first rendered accepted equation fresh _
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases accepted
  subst targetWord
  rw [AggregateCallGraphEquations.word] at equation
  cases equation
  exact ⟨by simp, aleaf_spec (target := .word) (initializer := .number value.val) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.word value, .word value.val, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .word,
      by simp [Expr.eval, word_lt_modulus], value, rfl, rfl⟩)⟩

theorem gRenderIH_bool (value : Bool) : GRenderIH (.bool value) := by
  intro functions target bindings indent first rendered accepted equation fresh _
  have targetBool : target = .bool := by
    cases target <;> first | rfl | cases accepted
  subst targetBool
  rw [AggregateCallGraphEquations.bool] at equation
  cases equation
  exact ⟨by simp, aleaf_spec (target := .bool) (initializer := .bool value) fresh
    (fun _ mem => by simp [Expr.identifiers] at mem)
    (fun _ _ store _ _ => ⟨.bool value, .bool value, by
      simp only [Solcore.Core.Wire.Expr.toCore]; exact .bool, rfl, value, rfl, rfl⟩)⟩

theorem gRenderIH_var (index : Nat) : GRenderIH (.var index) := by
  intro functions target bindings indent first rendered _ equation _ _
  obtain ⟨name, valued, found, rfl⟩ := AggregateCallGraphEquations.var_ok equation
  have found' : (bindings.map GBinding.toAggregate)[index]? =
      some (valueBinding target name) := by
    rw [List.getElem?_map, found]
    simp [gvalueBinding_toAggregate valued]
  refine ⟨valued, [], rfl, Nat.le_refl _, ?_, by simp [Stmt.listIdentifiers], ?_⟩
  · intro value same
    cases same
    exact Or.inl ⟨index, target, valued, found'⟩
  · refine asimulates_nil fun environment store scope outer agree => ?_
    obtain ⟨core, inEnvironment, holds⟩ := agree index _ found'
    rw [valueBinding_holds valued] at holds
    refine ⟨core, ?_, by simpa [ARendered.ofScalar] using holds⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .var inEnvironment

/-! ### Local bindings and control -/

theorem gRenderIH_letE {initializer body : CoreExpr} (initializerIH : GRenderIH initializer)
    (bodyIH : GRenderIH body) : GRenderIH (.letE initializer body) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨kind, initializerKind, bodyKind, _⟩ := AggregateKinds.letE accepted
  obtain ⟨kindTarget, value, rest, unitKind, inferred, initialEquation, restEquation, rfl⟩ :=
    AggregateCallGraphEquations.letE_ok equation
  have sameKind : kind = kindTarget.toLocal := by
    have toLocal := AggregateKinds.infer_toLocal inferred
    rw [initializerKind] at toLocal
    exact Option.some.inj toLocal
  subst sameKind
  obtain ⟨_, initSpec⟩ := initializerIH functions kindTarget bindings indent first value
    initializerKind initialEquation fresh distinct
  have initLe : first ≤ value.nextId := initSpec.le
  have mapped : (gvalueBinding kindTarget (temporary value.nextId) :: bindings).map
      GBinding.toAggregate =
      valueBinding kindTarget (temporary value.nextId) :: bindings.map GBinding.toAggregate := by
    simp [gvalueBinding_toAggregate unitKind]
  have bodyFresh : ANamesFresh ((gvalueBinding kindTarget (temporary value.nextId) ::
      bindings).map GBinding.toAggregate) (value.nextId + 1) := by
    rw [mapped]
    refine fresh.cons (Nat.le_succ_of_le initLe) fun name same => ?_
    rw [valueBinding_name unitKind] at same
    cases same
    exact temporary_fresh _
  have bodyDistinct : ANamesDistinct ((gvalueBinding kindTarget (temporary value.nextId) ::
      bindings).map GBinding.toAggregate) := by
    rw [mapped]
    exact distinct.cons fresh fun name same => by
      rw [valueBinding_name unitKind] at same
      cases same
      exact ⟨value.nextId, Or.inl rfl, initLe⟩
  have bodyKind' : initializerKind? ((gvalueBinding kindTarget (temporary value.nextId) ::
      bindings).map AggregateCallGraphRenderer.Binding.kind) functions.length body =
        some target.toLocal := by
    simpa [gvalueBinding_kind unitKind] using bodyKind
  obtain ⟨valued, bodySpec⟩ := bodyIH functions target
    (gvalueBinding kindTarget (temporary value.nextId) :: bindings) indent (value.nextId + 1)
    rest bodyKind' restEquation bodyFresh bodyDistinct
  rw [mapped] at bodySpec
  exact ⟨valued, aletValue_spec unitKind fresh initSpec rfl bodySpec⟩

theorem gRenderIH_ifE {condition yes no : CoreExpr} (conditionIH : GRenderIH condition)
    (yesIH : GRenderIH yes) (noIH : GRenderIH no) : GRenderIH (.ifE condition yes no) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨conditionKind, yesKind, noKind, _⟩ := AggregateKinds.ifE accepted
  obtain ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    shape⟩ := AggregateCallGraphEquations.ifE_ok equation
  obtain ⟨_, conditionSpec⟩ := conditionIH functions .bool bindings indent first tested
    conditionKind testedEquation fresh distinct
  have conditionLe : first ≤ tested.nextId := conditionSpec.le
  obtain ⟨valued, yesSpec⟩ := yesIH functions target bindings (indent + 4) (tested.nextId + 1)
    selected yesKind selectedEquation (fresh.mono (by omega)) distinct
  have yesLe : tested.nextId + 1 ≤ selected.nextId := yesSpec.le
  obtain ⟨_, noSpec⟩ := noIH functions target bindings (indent + 4) selected.nextId fallback
    noKind fallbackEquation (fresh.mono (by omega)) distinct
  rw [shape valued]
  exact ⟨valued, aifValue_spec valued fresh distinct conditionSpec rfl yesSpec rfl noSpec rfl⟩

theorem gRenderIH_caseE {scrutinee yes no : CoreExpr} (scrutineeIH : GRenderIH scrutinee)
    (yesIH : GRenderIH yes) (noIH : GRenderIH no) : GRenderIH (.caseE scrutinee yes no) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨scrutineeKind, yesKind, noKind, _⟩ := AggregateKinds.caseE accepted
  obtain ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    shape⟩ := AggregateCallGraphEquations.caseE_ok equation
  obtain ⟨_, scrutineeSpec⟩ := scrutineeIH functions .wordSum bindings indent first tested
    scrutineeKind testedEquation fresh distinct
  have sLe : first ≤ tested.nextId := scrutineeSpec.le
  obtain ⟨valued, yesSpec⟩ := yesIH functions target
    (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
    selected yesKind selectedEquation (payload_fresh fresh (by omega))
    (payload_distinct fresh distinct (by omega))
  have yLe : tested.nextId + 2 ≤ selected.nextId := yesSpec.le
  obtain ⟨_, noSpec⟩ := noIH functions target (.word (payloadTemp selected.nextId) :: bindings)
    (indent + 8) (selected.nextId + 1) fallback noKind fallbackEquation
    (payload_fresh fresh (by omega)) (payload_distinct fresh distinct (by omega))
  rw [shape valued]
  exact ⟨valued, acaseValue_spec valued fresh distinct scrutineeSpec rfl yesSpec rfl noSpec rfl⟩

/-! ### Operations, pairs, sum constructors and helper calls -/

theorem gRenderIH_unarySource {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp}
    {operand : CoreExpr} (selected : sourceUnary? op = some sourceOp)
    (operandIH : GRenderIH operand) : GRenderIH (.unary op operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateCallGraphEquations.unary _ _ _ _ selected] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  have operandTarget : (if op == .boolNot then (.bool : ATarget) else .word) =
      ATarget.ofScalar (Target.unaryOperand op) := by
    cases op <;> simp_all [sourceUnary?] <;> rfl
  rw [operandTarget] at valueEquation
  obtain ⟨_, spec⟩ := operandIH functions (ATarget.ofScalar (Target.unaryOperand op)) bindings
    indent first value (by rw [ofScalar_toLocal]; exact operandKind) valueEquation fresh
    distinct
  refine ⟨ATarget.ofScalar_ne_unit _, ?_⟩
  rw [← ATarget.ofScalar_localType]
  refine aoneResult_spec (ATarget.ofScalar_ne_unit _) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  have scalarRepresents := AValue.ofScalar_iff.mp represents
  rw [unaryOperand_eq selected] at scalarRepresents
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    unary_agree selected scalarRepresents
  refine ⟨coreResult, sourceResult, store₁, ?_, Nat.le_refl _, fun _ _ => rfl, ?_,
    AValue.ofScalar_iff.mpr resultRepresents⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates coreApply
  · simp [Expr.eval, lookup, sourceApply]

theorem gRenderIH_clz {operand : CoreExpr} (operandIH : GRenderIH operand) :
    GRenderIH (.unary .wordClz operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, operandKind, resultKind⟩ := AggregateKinds.unary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [show ATarget.ofScalar (Target.unaryResult .wordClz) = .word from rfl,
    AggregateCallGraphEquations.clz] at equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, spec⟩ := operandIH functions .word bindings indent first value operandKind
    valueEquation fresh distinct
  have snapshot := asnapshot_spec fresh spec
  refine ⟨ATarget.ofScalar_ne_unit _, aoneResult_spec (target := .word) (by simp) fresh snapshot
    rfl (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inr (same ▸ by simp [primitiveCallees, primitiveAliases]))
      · exact Or.inl same) ?_⟩
  intro context environment store store₁ operandCore frames source admitted _ _ evaluates
    lookup represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.word word.clz, .word (Evm.clz word.val), store₁, ?_, Nat.le_refl _,
    fun _ _ => rfl, ?_, word.clz, rfl, by rw [evm_clz]⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .unary evaluates rfl
  · simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, admitted.reaches (opcode := "clz") (alias := "sc_clz")
      (by decide), opcodeMeaning]

theorem gRenderIH_binarySource {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp}
    {left right : CoreExpr} (selected : sourceBinary? op = some sourceOp)
    (leftIH : GRenderIH left) (rightIH : GRenderIH right) :
    GRenderIH (.binary op left right) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateCallGraphEquations.binary _ _ _ _ _ selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, leftSpec⟩ := leftIH functions .word bindings indent first leftValue leftKind
    leftEquation fresh distinct
  obtain ⟨_, rightSpec⟩ := rightIH functions .word bindings indent leftValue.nextId rightValue
    rightKind rightEquation (fresh.mono leftSpec.le) distinct
  refine ⟨ATarget.ofScalar_ne_unit _, ?_⟩
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSpec rfl rightSpec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames _ leftEvaluates
    rightEvaluates leftLookup rightLookup
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    binary_agree selected leftWord rightWord
  refine ⟨coreResult, sourceResult, ?_, ?_, AValue.ofScalar_iff.mpr resultRepresents⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .binary leftEvaluates rightEvaluates coreApply
  · simp [Expr.eval, leftLookup, rightLookup, sourceApply]

theorem gRenderIH_binaryPrimitive {op : Solcore.Core.Wire.BinaryOp}
    {build : String → String → Expr} {left right : CoreExpr}
    (selected : primitiveBinary? op = some build)
    (leftIH : GRenderIH left) (rightIH : GRenderIH right) :
    GRenderIH (.binary op left right) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, leftKind, rightKind, resultKind⟩ := AggregateKinds.binary accepted
  have targetEq := atoLocal_scalarKind resultKind
  subst targetEq
  rw [AggregateCallGraphEquations.binary_primitive _ _ _ _ _ selected] at equation
  obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, leftSpec⟩ := leftIH functions .word bindings indent first leftValue leftKind
    leftEquation fresh distinct
  have leftSnapshot := asnapshot_spec fresh leftSpec
  obtain ⟨_, rightSpec⟩ := rightIH functions .word bindings indent (leftValue.nextId + 1)
    rightValue rightKind rightEquation (fresh.mono leftSnapshot.le) distinct
  have rightSnapshot := asnapshot_spec (fresh.mono leftSnapshot.le) rightSpec
  refine ⟨ATarget.ofScalar_ne_unit _, ?_⟩
  rw [← ATarget.ofScalar_localType]
  refine atwoResult_spec fresh distinct leftSnapshot rfl rightSnapshot rfl
    (primitiveBinary_names selected _ _) ?_
  intro context environment store store₁ store₂ leftWord rightWord frames admitted
    leftEvaluates rightEvaluates leftLookup rightLookup
  obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
    primitiveBinary_agree selected context frames _ _ leftWord rightWord admitted leftLookup
      rightLookup
  refine ⟨coreResult, sourceResult, ?_, sourceApply, AValue.ofScalar_iff.mpr resultRepresents⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .binary leftEvaluates rightEvaluates coreApply

theorem gRenderIH_ternary {op : Solcore.Core.Wire.TernaryOp} {one two three : CoreExpr}
    (oneIH : GRenderIH one) (twoIH : GRenderIH two) (threeIH : GRenderIH three) :
    GRenderIH (.ternary op one two three) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨oneKind, twoKind, threeKind, resultWord⟩ := AggregateKinds.ternary accepted
  have targetWord : target = .word := by
    cases target <;> first | rfl | cases resultWord
  subst targetWord
  rw [AggregateCallGraphEquations.ternary] at equation
  obtain ⟨oneValue, oneEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨twoValue, twoEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨threeValue, threeEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  obtain ⟨_, oneSpec⟩ := oneIH functions .word bindings indent first oneValue oneKind
    oneEquation fresh distinct
  have oneSnapshot := asnapshot_spec fresh oneSpec
  obtain ⟨_, twoSpec⟩ := twoIH functions .word bindings indent (oneValue.nextId + 1) twoValue
    twoKind twoEquation (fresh.mono oneSnapshot.le) distinct
  have twoSnapshot := asnapshot_spec (fresh.mono oneSnapshot.le) twoSpec
  obtain ⟨_, threeSpec⟩ := threeIH functions .word bindings indent (twoValue.nextId + 1)
    threeValue threeKind threeEquation
    (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) distinct
  have threeSnapshot :=
    asnapshot_spec (fresh.mono (Nat.le_trans oneSnapshot.le twoSnapshot.le)) threeSpec
  refine ⟨by simp, athreeResult_spec (target := .word) fresh distinct oneSnapshot rfl
    twoSnapshot rfl threeSnapshot rfl ?_ ?_⟩
  · intro name mem
    simp only [Expr.identifiers, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at mem
    rcases mem with same | (same | same) | same
    · refine Or.inr (Or.inr (Or.inr (same ▸ ?_)))
      cases op <;> simp [ternaryCallee, primitiveCallees, primitiveAliases]
    · exact Or.inl same
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (Or.inl same))
  · intro context environment store store₁ store₂ store₃ oneWord twoWord threeWord frames
      admitted oneEvaluates twoEvaluates threeEvaluates oneLookup twoLookup threeLookup
    obtain ⟨coreResult, sourceResult, coreApply, sourceApply, resultRepresents⟩ :=
      ternary_agree op context frames _ _ _ oneWord twoWord threeWord admitted oneLookup
        twoLookup threeLookup
    refine ⟨coreResult, sourceResult, ?_, sourceApply, resultRepresents⟩
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .ternary oneEvaluates twoEvaluates threeEvaluates coreApply

theorem gRenderIH_pair {left right : CoreExpr} (leftIH : GRenderIH left)
    (rightIH : GRenderIH right) : GRenderIH (.pair left right) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨leftKind, rightKind, _⟩ := AggregateKinds.pair accepted
  obtain ⟨rfl, leftValue, rightValue, leftEquation, rightEquation, rfl⟩ :=
    AggregateCallGraphEquations.pair_ok equation
  obtain ⟨_, leftSpec⟩ := leftIH functions .word bindings indent first leftValue leftKind
    leftEquation fresh distinct
  obtain ⟨_, rightSpec⟩ := rightIH functions .word bindings indent leftValue.nextId rightValue
    rightKind rightEquation (fresh.mono leftSpec.le) distinct
  refine ⟨by simp, atwoResult_spec (target := .wordPair) fresh distinct leftSpec rfl rightSpec
    rfl (fun name mem => by
      simp only [Expr.identifiers, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      rcases mem with same | same
      · exact Or.inl same
      · exact Or.inr (Or.inl same)) ?_⟩
  intro context environment store store₁ store₂ leftWord rightWord frames _ leftEvaluates
    rightEvaluates leftLookup rightLookup
  refine ⟨.pair (.word leftWord) (.word rightWord), .pair leftWord.val rightWord.val, ?_, ?_,
    leftWord, rightWord, rfl, rfl⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .pair leftEvaluates rightEvaluates
  · simp [Expr.eval, leftLookup, rightLookup]

theorem gRenderIH_inLeft {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : GRenderIH payload) : GRenderIH (.inLeft type payload) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨rfl, payloadKind, _⟩ := AggregateKinds.inLeft accepted
  obtain ⟨rfl, payloadValue, payloadEquation, rfl⟩ :=
    AggregateCallGraphEquations.inLeft_ok equation
  obtain ⟨_, spec⟩ := payloadIH functions .word bindings indent first payloadValue payloadKind
    payloadEquation fresh distinct
  refine ⟨by simp, aoneResult_spec (target := .wordSum) (by simp) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_⟩
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inLeft (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inl word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inl ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inLeft evaluates

theorem gRenderIH_inRight {type : Solcore.Core.Wire.Ty} {payload : CoreExpr}
    (payloadIH : GRenderIH payload) : GRenderIH (.inRight type payload) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨rfl, payloadKind, _⟩ := AggregateKinds.inRight accepted
  obtain ⟨rfl, payloadValue, payloadEquation, rfl⟩ :=
    AggregateCallGraphEquations.inRight_ok equation
  obtain ⟨_, spec⟩ := payloadIH functions .word bindings indent first payloadValue payloadKind
    payloadEquation fresh distinct
  refine ⟨by simp, aoneResult_spec (target := .wordSum) (by simp) fresh spec rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      exact Or.inl mem) ?_⟩
  intro context environment store store₁ operandCore frames source _ _ _ evaluates lookup
    represents
  obtain ⟨word, rfl, rfl⟩ := represents
  refine ⟨.inRight (Solcore.Core.Wire.Ty.toCore .word) (.word word), .inr word.val, store₁, ?_,
    Nat.le_refl _, fun _ _ => rfl, by simp [Expr.eval, lookup], Or.inr ⟨_, word, rfl, rfl⟩⟩
  simp only [Solcore.Core.Wire.Expr.toCore]
  exact .inRight evaluates

theorem gRenderIH_first {operand : CoreExpr} (operandIH : GRenderIH operand) :
    GRenderIH (.first operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨operandKind, _⟩ := AggregateKinds.first accepted
  obtain ⟨rfl, operandValue, operandEquation, rfl⟩ :=
    AggregateCallGraphEquations.first_ok equation
  obtain ⟨_, spec⟩ := operandIH functions .wordPair bindings indent first operandValue
    operandKind operandEquation fresh distinct
  exact ⟨by simp, aprojection_spec true fresh distinct spec rfl fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .first evaluates⟩

theorem gRenderIH_second {operand : CoreExpr} (operandIH : GRenderIH operand) :
    GRenderIH (.second operand) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨operandKind, _⟩ := AggregateKinds.second accepted
  obtain ⟨rfl, operandValue, operandEquation, rfl⟩ :=
    AggregateCallGraphEquations.second_ok equation
  obtain ⟨_, spec⟩ := operandIH functions .wordPair bindings indent first operandValue
    operandKind operandEquation fresh distinct
  exact ⟨by simp, aprojection_spec false fresh distinct spec rfl fun _ _ _ _ _ evaluates => by
    simp only [Solcore.Core.Wire.Expr.toCore]
    exact .second evaluates⟩

/-- A direct call to an earlier helper copies its argument first. The helper
cannot reach the caller's frames, and its evaluation keeps every existing
store location. -/
theorem gRenderIH_apply {index : Nat} {argument : CoreExpr} (argumentIH : GRenderIH argument) :
    GRenderIH (.apply (.var index) argument) := by
  intro functions target bindings indent first rendered accepted equation fresh distinct
  obtain ⟨_, _, argumentKind, _⟩ := AggregateKinds.apply accepted
  obtain ⟨rfl, outside, callee, value, found, valueEquation, rfl⟩ :=
    AggregateCallGraphEquations.apply_ok equation
  obtain ⟨_, spec⟩ := argumentIH functions .word bindings indent first value argumentKind
    valueEquation fresh distinct
  have snapshot := asnapshot_spec fresh spec
  refine ⟨by simp, aoneResult_spec (target := .word) (by simp) fresh snapshot rfl
    (fun name mem => by
      simp only [Expr.identifiers, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with same | same
      · exact Or.inr (Or.inl (same ▸ List.mem_of_getElem? found))
      · exact Or.inl same) ?_⟩
  intro context environment store store₁ operandCore frames source _ _ functionsOk evaluates
    lookup represents
  obtain ⟨word, rfl, rfl⟩ := represents
  rw [List.length_map] at functionsOk
  obtain ⟨parameterType, resultType, body, captured, closureFound, behaves⟩ :=
    functionsOk (index - bindings.length) callee found
  obtain ⟨result, store₂, bodyEvaluates, grows, keepsStore, callResult⟩ := behaves word store₁
  have closureAt : environment[index]? =
      some (.closure parameterType resultType body captured) := by
    rw [List.getElem?_drop] at closureFound
    have position : bindings.length + (index - bindings.length) = index := by omega
    rwa [position] at closureFound
  refine ⟨.word result, .word result.val, store₂, ?_, grows, keepsStore, ?_, result, rfl, rfl⟩
  · simp only [Solcore.Core.Wire.Expr.toCore]
    exact .apply (.var closureAt) evaluates bodyEvaluates
  · simp only [snapshotOf] at lookup
    simp [Expr.eval, lookup, callResult]

/-! ### The structural induction -/

/-- An expression the actual renderer always rejects. -/
theorem gRenderIH_error (expression : CoreExpr)
    (fails : ∀ (functions : List String) (target : ATarget) (bindings : List GBinding)
      (indent first : Nat) (rendered : ScalarRenderer.Rendered),
      AggregateCallGraphRenderer.render functions target bindings indent first expression ≠
        .ok rendered) :
    GRenderIH expression := by
  intro functions target bindings indent first rendered _ equation
  exact absurd equation (fails functions target bindings indent first rendered)

theorem gRenderIH_rejected (expression : CoreExpr)
    (rejects : expression = .unit ∨ (∃ value, expression = .integer value) ∨
      (∃ parameterType resultType body, expression = .lambda parameterType resultType body) ∨
      (∃ elementType inner, expression = .newCell elementType inner) ∨
      (∃ reference, expression = .loadCell reference) ∨
      (∃ reference value, expression = .storeCell reference value) ∨
      (∃ constructor payload, expression = .construct constructor payload) ∨
      (∃ dataType resultType scrutinee branches,
        expression = .matchData dataType resultType scrutinee branches)) :
    GRenderIH expression :=
  gRenderIH_error _ fun _ _ _ _ _ _ equation =>
    AggregateCallGraphEquations.rejected rejects equation

theorem gRenderIH_unary {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (operandIH : GRenderIH operand) : GRenderIH (.unary op operand) := by
  cases selected : sourceUnary? op with
  | some _ => exact gRenderIH_unarySource selected operandIH
  | none =>
      cases op
      case boolNot => simp [sourceUnary?] at selected
      case wordNot => simp [sourceUnary?] at selected
      case wordClz => exact gRenderIH_clz operandIH
      all_goals
        intro _ _ _ _ _ _ accepted
        exact absurd (AggregateKinds.unary accepted).1 (by simp [MutationKinds.integerUnary])

theorem gRenderIH_binary {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (leftIH : GRenderIH left) (rightIH : GRenderIH right) : GRenderIH (.binary op left right) := by
  cases selected : sourceBinary? op with
  | some _ => exact gRenderIH_binarySource selected leftIH rightIH
  | none =>
      cases extended : primitiveBinary? op with
      | some _ => exact gRenderIH_binaryPrimitive extended leftIH rightIH
      | none =>
          cases op <;> first
            | (simp [sourceBinary?] at selected; done)
            | (simp [primitiveBinary?] at extended; done)
            | (intro _ _ _ _ _ _ accepted
               exact absurd (AggregateKinds.binary accepted).1
                 (by simp [MutationKinds.integerBinary]))

theorem gRenderIH_applyAny {function argument : CoreExpr} (argumentIH : GRenderIH argument) :
    GRenderIH (.apply function argument) := by
  cases function
  case var index => exact gRenderIH_apply argumentIH
  all_goals
    exact gRenderIH_error _ fun _ _ _ _ _ _ equation => by cases equation

/-- Every expression that the aggregate profile accepts and the actual
aggregate call-graph renderer renders is rendered at a value type and
satisfies the aggregate rendering specification in every primitive call
context. -/
theorem aggregateCallGraph_render_spec : (expression : CoreExpr) → GRenderIH expression
  | .word value => gRenderIH_word value
  | .bool value => gRenderIH_bool value
  | .var index => gRenderIH_var index
  | .letE initializer body =>
      gRenderIH_letE (aggregateCallGraph_render_spec initializer)
        (aggregateCallGraph_render_spec body)
  | .ifE condition yes no =>
      gRenderIH_ifE (aggregateCallGraph_render_spec condition)
        (aggregateCallGraph_render_spec yes) (aggregateCallGraph_render_spec no)
  | .pair left right =>
      gRenderIH_pair (aggregateCallGraph_render_spec left) (aggregateCallGraph_render_spec right)
  | .first operand => gRenderIH_first (aggregateCallGraph_render_spec operand)
  | .second operand => gRenderIH_second (aggregateCallGraph_render_spec operand)
  | .inLeft _ payload => gRenderIH_inLeft (aggregateCallGraph_render_spec payload)
  | .inRight _ payload => gRenderIH_inRight (aggregateCallGraph_render_spec payload)
  | .caseE scrutinee yes no =>
      gRenderIH_caseE (aggregateCallGraph_render_spec scrutinee)
        (aggregateCallGraph_render_spec yes) (aggregateCallGraph_render_spec no)
  | .unary _ operand => gRenderIH_unary (aggregateCallGraph_render_spec operand)
  | .binary _ left right =>
      gRenderIH_binary (aggregateCallGraph_render_spec left)
        (aggregateCallGraph_render_spec right)
  | .ternary _ one two three =>
      gRenderIH_ternary (aggregateCallGraph_render_spec one) (aggregateCallGraph_render_spec two)
        (aggregateCallGraph_render_spec three)
  | .apply _ argument => gRenderIH_applyAny (aggregateCallGraph_render_spec argument)
  | .unit => gRenderIH_rejected _ (Or.inl rfl)
  | .integer _ => gRenderIH_rejected _ (Or.inr (Or.inl ⟨_, rfl⟩))
  | .lambda _ _ _ => gRenderIH_rejected _ (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))
  | .newCell _ _ => gRenderIH_rejected _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | .loadCell _ => gRenderIH_rejected _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
  | .storeCell _ _ =>
      gRenderIH_rejected _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))))
  | .construct _ _ =>
      gRenderIH_rejected _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))))))
  | .matchData _ _ _ _ =>
      gRenderIH_rejected _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩)))))))

end Solcore.Synthesis.Source.ScalarMeaning
end
