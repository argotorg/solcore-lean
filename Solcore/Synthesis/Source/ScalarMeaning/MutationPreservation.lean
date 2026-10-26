import Solcore.Synthesis.Source.ScalarMeaning.MutationEquations

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
