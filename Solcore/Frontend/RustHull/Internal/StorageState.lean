import Solcore.Frontend.RustHull.Internal.NamedFunctions
import Solcore.Frontend.RustHull.Semantics
import Solcore.Frontend.RustHull.Semantics.World

/-!
# Storage and effect state

Core storage against the independent world, and the state relation of the effect runtime.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.EffectEnvironmentCorrespondence
/-! Reserved runtime references retain their actual locations under source
binders and compiler-generated administrative prefixes. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

structure EffectSlot where
  name : String
  type : Core.Ty
  location : Nat

def EffectEnvironmentRel (slots : List EffectSlot) (scope : Scope)
    (mapping : Core.Renaming) (environment : Core.Environment) : Prop :=
  ∀ slot ∈ slots, ∀ binding index,
    scope.lookup (Effects.slotName slot.name) = .ok (binding, index) →
    environment[mapping index]? = some (.cellRef slot.type slot.location)

theorem EffectEnvironmentRel.empty (scope : Scope) (mapping : Core.Renaming)
    (environment : Core.Environment) : EffectEnvironmentRel [] scope mapping environment := by
  intro slot member
  cases member

theorem EffectEnvironmentRel.temporary {slots : List EffectSlot} {scope : Scope}
    {mapping : Core.Renaming} {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope mapping environment)
    (type : Core.Ty) (value : Core.Value) :
    EffectEnvironmentRel slots (scope.temporary type) mapping.lift (value :: environment) := by
  intro slot member binding index looked
  rw [Scope.temporary, scope_lookup_cons] at looked
  simp only [Option.none_beq_some, Bool.false_eq_true, ↓reduceIte] at looked
  cases previous : scope.lookup (Effects.slotName slot.name) with
  | error error => simp only [previous] at looked; contradiction
  | ok found =>
      rcases found with ⟨oldBinding, oldIndex⟩
      simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
      obtain ⟨rfl, rfl⟩ := looked
      exact related slot member oldBinding oldIndex previous

theorem EffectEnvironmentRel.addLocal {slots : List EffectSlot} {scope : Scope}
    {mapping : Core.Renaming} {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope mapping environment)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (allowed : name.startsWith Effects.reservedPrefix = false) :
    EffectEnvironmentRel slots (scope.addLocal name type) mapping.lift (value :: environment) := by
  intro slot member binding index looked
  have different : name ≠ Effects.slotName slot.name := by
    intro same
    have reserved := slotName_reserved slot.name
    rw [← same, allowed] at reserved
    contradiction
  rw [Scope.addLocal, scope_lookup_cons] at looked
  simp only [Option.some_beq_some, beq_iff_eq, different, ↓reduceIte] at looked
  cases previous : scope.lookup (Effects.slotName slot.name) with
  | error error => simp only [previous] at looked; contradiction
  | ok found =>
      rcases found with ⟨oldBinding, oldIndex⟩
      simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
      obtain ⟨rfl, rfl⟩ := looked
      exact related slot member oldBinding oldIndex previous

theorem EffectEnvironmentRel.prepend {slots : List EffectSlot} {scope : Scope}
    {mapping : Core.Renaming} {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope mapping environment) (extra : Core.Environment) :
    EffectEnvironmentRel slots scope (fun index => extra.length + mapping index) (extra ++ environment) := by
  intro slot member binding index looked
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    using related slot member binding index looked

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.EffectBuiltinCorrespondenceSupport
/-! Compiler-derived argument constraints and actual reserved references for
concrete Hull builtin correspondence. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EffectBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence

private def checkWords (arguments : List Lowered) : LowerM PUnit :=
  forIn arguments PUnit.unit fun argument _ => do
    expectType .word argument.type
    pure (.yield PUnit.unit)

private theorem checkedWords {arguments : List Lowered}
    (checked : checkWords arguments = .ok PUnit.unit) :
    ∀ argument ∈ arguments, argument.type = .word := by
  induction arguments with
  | nil => simp
  | cons argument rest ih =>
      by_cases same : argument.type = .word
      · have tail : checkWords rest = .ok PUnit.unit := by
          simpa [checkWords, List.forIn_cons, expectType, same] using checked
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact same
        · exact ih tail value member
      · simp [checkWords, List.forIn_cons, expectType, Ne.symm same, fail,
          Bind.bind, Except.bind] at checked

theorem outer_components {name : String}
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (supported : Effects.supports name = true)
    (compiled : lowerBuiltin scope name expected arguments = .ok lowered) :
    (∀ argument ∈ arguments, argument.type = .word) ∧
    ∃ raw, Effects.lowerBuiltin (scope.temporary (packArguments arguments).type) name
      ((List.range arguments.length).map fun index => projectArgument index arguments.length (.var 0)) = .ok raw ∧
      expected = raw.type ∧ lowered = ⟨expected, LanguageResult.bind expected (packArguments arguments).expression raw.expression⟩ := by
  simp only [lowerBuiltin, supported, ↓reduceIte] at compiled
  obtain ⟨checked, words, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨raw, rawCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, typed, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  exact ⟨checkedWords words, raw, rawCompiled, expectType_eq_of_ok typed, (Except.ok.inj returned).symm⟩

theorem reference_evaluates {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} {slot : EffectSlot} {reference : Core.Expr}
    (related : EffectEnvironmentRel slots scope mapping environment) (member : slot ∈ slots)
    (compiled : Effects.reference scope slot.name slot.type = .ok reference) (store : Store) :
    Evaluates environment store (reference.rename mapping) (.cellRef slot.type slot.location) store := by
  unfold Effects.reference at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  cases returned
  exact .var (related slot member binding index looked)

theorem word_arguments {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) :
    ∃ (expressions : List Core.Expr) (values : List Core.Word),
      arguments = expressions.map (fun expression => Lowered.mk .word expression) ∧
      sources = values.map Semantics.Value.word ∧ targets = values.map Core.Value.word ∧
      expressions.length = values.length := by
  induction related with
  | nil => exact ⟨[], [], rfl, rfl, rfl, rfl⟩
  | @cons argument arguments source sources target targets head tail ih =>
      obtain ⟨expressions, values, rfl, rfl, rfl, lengths⟩ :=
        ih (fun member selected => words member (List.mem_cons_of_mem _ selected))
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word value =>
              exact ⟨expression :: expressions, value :: values, rfl, rfl, rfl, congrArg Nat.succ lengths⟩

theorem one_word {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 1) :
    ∃ expression value, arguments = [⟨.word, expression⟩] ∧
      sources = [.word value] ∧ targets = [.word value] := by
  obtain ⟨expressions, values, rfl, rfl, rfl, sizes⟩ := word_arguments related words
  simp only [List.length_map] at length
  cases expressions with
  | nil => cases length
  | cons expression rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj length)
      subst rest
      cases values with
      | nil => cases sizes
      | cons value rest =>
          have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj sizes.symm)
          subst rest
          exact ⟨expression, value, rfl, rfl, rfl⟩

theorem two_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 2) :
    ∃ first second left right, arguments = [⟨.word, first⟩, ⟨.word, second⟩] ∧
      sources = [.word left, .word right] ∧ targets = [.word left, .word right] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, right, rfl, rfl, rfl⟩ := one_word tail
        (fun argument member => words argument (List.mem_cons_of_mem _ member)) (Nat.succ.inj length)
      have typed := words first (List.mem_cons_self ..)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left => exact ⟨expression, second, left, right, rfl, rfl, rfl⟩

end Solcore.Frontend.RustHull.EffectBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.EffectProjectionPreservation
/-! A property of external state survives an entire independent Hull execution
when each external operation preserves it. Local allocation and assignment,
recursive calls, loops and all fault paths are covered by the same induction. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EffectProjectionPreservation
open Semantics

/-- The external specification preserves an observation of its state. -/
structure Preserves {σ τ : Type} (effects : ExternalSemantics σ) (project : σ → τ) : Prop where
  builtin : ∀ {name type arguments initial result final},
    effects.builtin name type arguments initial result final → project final = project initial
  assembly : ∀ {functions environment body initial control final},
    effects.assembly functions environment body initial control final →
      project final.external = project initial.external
  revert : ∀ {message initial control final},
    effects.revert message initial control final → project final = project initial

theorem write_external {σ : Type} {initial final : State σ} {location : Nat} {value : Value}
    (written : write? initial location value = some final) : final.external = initial.external := by
  unfold write? at written
  split at written
  · cases Option.some.inj written
    rfl
  · contradiction

theorem assign_external {σ : Type} {environment : Environment} {initial final : State σ}
    {lhs : Expr} {value : Value}
    (written : assignResult environment initial lhs value = .value final) :
    final.external = initial.external := by
  unfold assignResult at written
  repeat' (split at written <;> try contradiction)
  cases written
  exact write_external ‹write? initial _ _ = some _›

theorem bind_external {σ : Type} {arguments : List Arg} {values : List Value}
    {environment finalEnvironment : Environment} {initial final : State σ}
    (bound : bindArguments arguments values environment initial = some (finalEnvironment, final)) :
    final.external = initial.external := by
  induction arguments generalizing values environment initial with
  | nil =>
    cases values <;> simp_all [bindArguments]
  | cons argument arguments ih =>
    cases values with
    | nil => simp [bindArguments] at bound
    | cons value values => exact ih (initial := (allocate initial value).2) bound

/-- The conclusion includes successful results and faults, with no assumption
about termination of another execution or the absence of recursive calls. -/
theorem function_preserves {σ τ : Type} {effects : ExternalSemantics σ}
    {project : σ → τ} (preserved : Preserves effects project)
    {functions : List Function} {function : Function} {arguments : List Value}
    {initial final : State σ} {result : Result Value}
    (evaluated : EvalFunction functions effects function arguments initial result final) :
    project final.external = project initial.external := by
  refine EvalFunction.rec
    (motive_1 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_2 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_3 := fun _ _ _ initial _ final _ => project final.external = project initial.external)
    (motive_4 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_5 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_6 := fun _ _ initial _ final _ => project final.external = project initial.external)
    (motive_7 := fun _ _ _ _ initial _ final _ => project final.external = project initial.external)
    (motive_8 := fun _ _ _ _ initial _ final _ => project final.external = project initial.external)
    ?word ?bool ?unit ?var ?pair ?pairFault ?fst ?snd ?inl ?inr ?inK
    ?call ?callFault ?ifTrue ?ifFalse ?ifFault ?ifInvalid
    ?nil ?cons ?fault ?function ?primitive ?external ?body ?arity
    ?declare ?declareInvalid ?assign ?assignFault ?assignInvalid
    ?expression ?expressionFault ?returned ?returnFault ?block ?forInit ?forLoop
    ?breaking ?continuing ?matchStmt ?matchFault ?assembly ?revert ?comment
    ?nil_1 ?declare_1 ?declareInvalid_1 ?next ?stop
    ?done ?conditionFault ?conditionInvalid ?step ?bodyBreak ?bodyStop ?postBreak ?postStop
    ?nil_2 ?matched ?next_1 evaluated
  all_goals intros
  all_goals try (solve | simp_all only [allocate])
  case external => exact preserved.builtin ‹effects.builtin _ _ _ _ _ _›
  case body =>
    have bound := bind_external ‹bindArguments _ _ _ _ = some (_, _)›
    simp_all only
  case assign =>
    have written := assign_external ‹assignResult _ _ _ _ = .value _›
    simp_all only
  case assembly => exact preserved.assembly ‹effects.assembly _ _ _ _ _ _›
  case revert => exact preserved.revert ‹effects.revert _ _ _ _›

end Solcore.Frontend.RustHull.EffectProjectionPreservation
end

section
-- leanmerge: from Solcore.Frontend.RustHull.EffectStateCorrespondence
/-! State relations for independent Hull effects. Runtime resources occupy a
fixed prefix of the Core store; source locals are allocated beyond that prefix.
The generic model requires only structural store laws, never an execution or
compiler-correctness premise. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

/-- All cells already present keep their values; later allocations may add cells. -/
structure StoreRetains (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location, location < initial.length → final.read? location = initial.read? location

theorem StoreRetains.refl (store : Core.Store) : StoreRetains store store :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem StoreRetains.trans {initial middle final : Core.Store}
    (first : StoreRetains initial middle) (second : StoreRetains middle final) :
    StoreRetains initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun location bound => by
    rw [second.read location (Nat.lt_of_lt_of_le bound first.length_le), first.read location bound]⟩

theorem StoreRetains.append (store suffix : Core.Store) : StoreRetains store (store ++ suffix) := by
  refine ⟨by simp, ?_⟩
  intro location bound
  exact List.getElem?_append_left bound

/-- An external-state representation and the three structural frame rules used
by ordinary Hull code. Writes are restricted to represented source locations. -/
structure StateModel (σ : Type) where
  rel : σ → World → Core.Store → Prop
  retained : ∀ {source world initial final}, rel source world initial →
    StoreRetains initial final → rel source world final
  allocate : ∀ {source world store} (type : Core.Ty) (value : Core.Value),
    rel source world store →
    rel source (world ++ [(type, store.length)]) (store ++ [.inRight .unit value])
  write : ∀ {source world store updated} {index : Nat} {type : Core.Ty} {location : Nat} {value : Core.Value},
    rel source world store → world[index]? = some (type, location) →
    store.write? location value = some updated → rel source world updated

/-- Pure scalar execution carries no external resources. -/
def StateModel.trivial (σ : Type) : StateModel σ where
  rel := fun _ _ _ => True
  retained := fun _ _ => True.intro
  allocate := fun _ _ _ => True.intro
  write := fun _ _ _ => True.intro

/-- Read exactly the resource prefix. No observation can inspect later locals. -/
def prefixRead (boundary : Nat) (store : Core.Store) (location : Nat) : Option Core.Value :=
  if location < boundary then store.read? location else none

def WorldAbove (boundary : Nat) (world : World) : Prop :=
  ∀ (index : Nat) (type : Core.Ty) (location : Nat), world[index]? = some (type, location) → boundary ≤ location

theorem WorldAbove.allocate {boundary : Nat} {world : World} {store : Core.Store}
    (separated : WorldAbove boundary world) (bounded : boundary ≤ store.length) (type : Core.Ty) :
    WorldAbove boundary (world ++ [(type, store.length)]) := by
  intro index foundType location found
  by_cases old : index < world.length
  · rw [List.getElem?_append_left old] at found
    exact separated index foundType location found
  · have bound := (List.getElem?_eq_some_iff.mp found).1
    have fresh : index = world.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst index
    simp only [List.getElem?_concat_length, Option.some.injEq, Prod.mk.injEq] at found
    have same : store.length = location := found.2
    omega

theorem prefixRead_retained {boundary : Nat} {initial final : Core.Store}
    (bounded : boundary ≤ initial.length) (retained : StoreRetains initial final) :
    prefixRead boundary final = prefixRead boundary initial := by
  funext location
  by_cases before : location < boundary
  · simp only [prefixRead, before, ↓reduceIte]
    exact retained.read location (Nat.lt_of_lt_of_le before bounded)
  · simp only [prefixRead, before, ↓reduceIte]

theorem prefixRead_write {boundary location : Nat} {initial final : Core.Store} {value : Core.Value}
    (separated : boundary ≤ location) (written : initial.write? location value = some final) :
    prefixRead boundary final = prefixRead boundary initial := by
  funext other
  by_cases before : other < boundary
  · simp only [prefixRead, before, ↓reduceIte]
    exact Core.Store.write?_preserves_other (location := location) (otherLocation := other) written
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le before separated))
  · simp only [prefixRead, before, ↓reduceIte]

/-- Any concrete representation using only the fixed resource cells satisfies
all local-code frame laws. The boundary and local separation are established by
actual runtime initialization, not inferred from the shapes of cell values. -/
def StateModel.cutoff {σ : Type} (boundary : Nat)
    (resources : σ → (Nat → Option Core.Value) → Prop) : StateModel σ where
  rel source world store := boundary ≤ store.length ∧ WorldAbove boundary world ∧
    resources source (prefixRead boundary store)
  retained := by
    intro source world initial final related retained
    exact ⟨Nat.le_trans related.1 retained.length_le, related.2.1,
      by rw [prefixRead_retained related.1 retained]; exact related.2.2⟩
  allocate := by
    intro source world store type value related
    refine ⟨by simp; omega, related.2.1.allocate related.1 type, ?_⟩
    rw [prefixRead_retained related.1 (StoreRetains.append store [.inRight .unit value])]
    exact related.2.2
  write := by
    intro source world store updated index type location value related entry written
    refine ⟨by rw [Core.Store.write?_preserves_length written]; exact related.1, related.2.1, ?_⟩
    rw [prefixRead_write (related.2.1 index type location entry) written]
    exact related.2.2

/-- Local-heap correspondence and external-state correspondence at one actual
Core store. Extending HeapRel keeps its cell and distinctness projections. -/
structure StateRel {σ : Type} (model : StateModel σ) (world : World)
    (source : Semantics.State σ) (store : Core.Store) : Prop extends HeapRel world source.heap store where
  external : model.rel source.external world store

theorem StateRel.trivial {σ : Type} {world : World} {source : Semantics.State σ} {store : Core.Store}
    (heap : HeapRel world source.heap store) : StateRel (StateModel.trivial σ) world source store :=
  ⟨heap, True.intro⟩

theorem StateRel.appendCore {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store : Core.Store}
    (related : StateRel model world source store) (suffix : Core.Store) :
    StateRel model world source (store ++ suffix) :=
  ⟨related.toHeapRel.appendCore suffix, model.retained related.external (StoreRetains.append store suffix)⟩

theorem StateRel.allocate {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store : Core.Store} (related : StateRel model world source store)
    {type : Core.Ty} {sourceValue : Semantics.Value} {targetValue : Core.Value}
    (valueRelated : ValueRel type sourceValue targetValue) :
    StateRel model (world ++ [(type, store.length)]) (Semantics.allocate source sourceValue).2
      (store ++ [.inRight .unit targetValue]) :=
  ⟨related.toHeapRel.allocate valueRelated, model.allocate type targetValue related.external⟩

theorem StateRel.write {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store updated : Core.Store} (related : StateRel model world source store)
    {index : Nat} {type : Core.Ty} {location : Nat}
    (entry : world[index]? = some (type, location))
    {sourceValue : Semantics.Value} {targetValue : Core.Value}
    (valueRelated : ValueRel type sourceValue targetValue)
    (written : store.write? location (.inRight .unit targetValue) = some updated) :
    StateRel model world {source with heap := source.heap.set index sourceValue} updated :=
  ⟨related.toHeapRel.write entry valueRelated written, model.write related.external entry written⟩

theorem initializedGlobals_retains (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) (store : Core.Store) :
    StoreRetains store (initializedGlobals signatures codes environment store) := by
  refine ⟨?_, ?_⟩
  · simp [initializedGlobals, installationStore_length, globalStore]
  · intro location bound
    rw [initializedGlobals, installationStore_preserves]
    · exact List.getElem?_append_left bound
    · intro offset _
      simp only [globalLocations]
      omega

theorem StateRel.initializeGlobals {σ : Type} {model : StateModel σ} {world : World}
    {source : Semantics.State σ} {store : Core.Store}
    (related : StateRel model world source store) (signatures : List Signature) (codes : List GlobalCode)
    (environment : Core.Environment) :
    StateRel model world source (initializedGlobals signatures codes environment store) :=
  ⟨related.toHeapRel.initializeGlobals signatures codes environment,
    model.retained related.external (initializedGlobals_retains signatures codes environment store)⟩

/-- Resource updates preserve all cells beyond their fixed prefix, including
source locals and function/loop cells. Appended helper cells remain available. -/
structure StoreRetainsFrom (boundary : Nat) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location, boundary ≤ location → location < initial.length →
    final.read? location = initial.read? location

theorem StoreRetainsFrom.ofRetains {boundary : Nat} {initial final : Core.Store}
    (retained : StoreRetains initial final) : StoreRetainsFrom boundary initial final :=
  ⟨retained.length_le, fun location _ bound => retained.read location bound⟩

theorem StoreRetainsFrom.trans {boundary : Nat} {initial middle final : Core.Store}
    (first : StoreRetainsFrom boundary initial middle)
    (second : StoreRetainsFrom boundary middle final) : StoreRetainsFrom boundary initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun location separated bound => by
    rw [second.read location separated (Nat.lt_of_lt_of_le bound first.length_le),
      first.read location separated bound]⟩

theorem StoreRetainsFrom.writeBelow {boundary location : Nat}
    {initial final : Core.Store} {value : Core.Value} (below : location < boundary)
    (written : initial.write? location value = some final) : StoreRetainsFrom boundary initial final := by
  refine ⟨by simp only [Core.Store.write?_preserves_length written, Nat.le_refl], ?_⟩
  intro other separated _
  exact Core.Store.write?_preserves_other (location := location) (otherLocation := other) written
    (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le below separated)))

theorem HeapRel.frameAbove {boundary : Nat} {world : World} {source : Semantics.Heap}
    {initial final : Core.Store} (heap : HeapRel world source initial)
    (separated : WorldAbove boundary world) (retained : StoreRetainsFrom boundary initial final) :
    HeapRel world source final where
  length_eq := heap.length_eq
  distinct := heap.distinct
  cell := by
    intro index type location entry
    obtain ⟨sourceValue, targetValue, sourceFound, targetFound, related⟩ := heap.cell index type location entry
    exact ⟨sourceValue, targetValue, sourceFound, by
      rw [retained.read location (separated index type location entry) (heap.location_bound entry)]
      exact targetFound, related⟩

/-- Concrete effect primitives supply their updated resource observations and
frame all preexisting non-resource cells. No source allocation is hidden here. -/
theorem StateRel.cutoff_effect {σ : Type} {boundary : Nat}
    {resources : σ → (Nat → Option Core.Value) → Prop} {world : World}
    {source : Semantics.State σ} {initial final : Core.Store}
    (related : StateRel (StateModel.cutoff boundary resources) world source initial)
    {external : σ} (retained : StoreRetainsFrom boundary initial final)
    (updated : resources external (prefixRead boundary final)) :
    StateRel (StateModel.cutoff boundary resources) world {source with external := external} final :=
  ⟨related.toHeapRel.frameAbove related.external.2.1 retained,
    Nat.le_trans related.external.1 retained.length_le, related.external.2.1, updated⟩

/-- Actual runtime initialization fixes the resource prefix before allocating
any Hull local. Concrete contents are checked at that exact initialized store. -/
theorem StateRel.cutoff_initial {σ : Type} {resources : σ → (Nat → Option Core.Value) → Prop}
    (external : σ) (store : Core.Store)
    (initialized : resources external (prefixRead store.length store)) :
    StateRel (StateModel.cutoff store.length resources) [] ⟨[], external⟩ store :=
  ⟨HeapRel.empty store, Nat.le_refl _, (by intro index type location found; cases found), initialized⟩

/-- The real parameter allocator extends the state model along with the local
heap. The final relation refers to the state returned by source bindArguments. -/
theorem initialize_parameters_state_renamed {σ : Type} {model : StateModel σ}
    {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel types sources targets) (arity : arguments.length = types.length)
    {sourceEnvironment : Semantics.Environment} {scope : Scope} {sourceState : Semantics.State σ}
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (stateRelated : StateRel model world sourceState store)
    {external : σ → Core.Store → Prop} (externalRelated : external sourceState.external store)
    (frame : ∀ state store type value, external state store →
      external state (store ++ [Core.Value.inRight type value])) :
    ∃ extension sourceEnvironment' sourceState' environment' store',
      Semantics.bindArguments arguments sources sourceEnvironment sourceState = some (sourceEnvironment', sourceState') ∧
      ParameterCells types targets environment store environment' store' ∧
      EnvironmentRel (world ++ extension) sourceEnvironment' (parameterScope arguments types scope)
        (parameterRenaming types.length mapping) environment' ∧
      StateRel model (world ++ extension) sourceState' store' ∧
      external sourceState'.external store' := by
  induction values generalizing arguments sourceEnvironment scope sourceState world mapping environment store with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact ⟨[], sourceEnvironment, sourceState, environment, store, rfl, .nil,
        by simpa [parameterScope, parameterRenaming] using environmentRelated,
        by simpa using stateRelated, externalRelated⟩
  | @cons type types source sources target targets head tail ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          have arity' : arguments.length = types.length := Nat.succ.inj arity
          have entry : (world ++ [(type, store.length)])[sourceState.heap.length]? = some (type, store.length) := by
            rw [← stateRelated.length_eq, List.getElem?_concat_length]
          have environment' := ((environmentRelated.extendWorld [(type, store.length)]).addLocal
            argument.name type sourceState.heap.length store.length entry)
          have state' := stateRelated.allocate head
          have external' := frame sourceState.external store .unit target externalRelated
          obtain ⟨extension, sourceEnvironment', sourceState', environment'', store', bound,
            allocated, locals, state, external⟩ := ih arity'
              (sourceState := (Semantics.allocate sourceState source).2)
              (sourceEnvironment := (argument.name, sourceState.heap.length) :: sourceEnvironment)
              (scope := scope.addLocal argument.name type)
              (world := world ++ [(type, store.length)])
              (mapping := mapping.lift)
              (environment := .cellRef (Core.OptionalCell.cellType type) store.length :: environment)
              (store := store ++ [.inRight .unit target]) environment' state'
              (by simpa only [Semantics.allocate] using external')
          refine ⟨[(type, store.length)] ++ extension, sourceEnvironment', sourceState', environment'', store',
            ?_, .cons allocated, ?_, ?_, external⟩
          · exact bound
          · simpa only [List.append_assoc, parameterScope, List.zip_cons_cons, List.foldl_cons,
              List.length_cons, parameterRenaming] using locals
          · simpa only [List.append_assoc] using state

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.StorageCorrespondence
/-! Storage meaning follows the actual account helpers. Code identities are
representation inputs; the source observations use only ordinary account data. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StorageCorrespondence
open Core ScalarExecution

abbrev Accounts := List (AccountState.Account × Nat)

def record (account : AccountState.Account) (identity : Nat) : Core.Value :=
  bundleValues [WordMapping.encode account.storage, WordMapping.encode account.transient,
    .word account.nonce, .word (Word.ofNatModulo identity),
    WordMapping.encode (Memory.packBytes (account.code.getD [])),
    .word (Word.ofNatModulo (account.code.getD []).length),
    .bool account.code.isSome, .bool account.created, .bool account.destroyed]

def entries (accounts : Accounts) : OrderedMapping.Entries :=
  accounts.map fun (account, identity) => (.word account.address, record account identity)

def world (accounts : Accounts) : Core.Value := OrderedMapping.encode AccountState.layout (entries accounts)

def lookup (address : Word) : Accounts → Option (AccountState.Account × Nat)
  | [] => none
  | (account, identity) :: rest =>
      if address == account.address then some (account, identity) else lookup address rest

def get (accounts : Accounts) (address : Word) (complete : Bool) : Except Word (AccountState.Account × Nat) :=
  match lookup address accounts with
  | some account => .ok account
  | none => if complete then .ok ({address := address}, 0) else .error (Word.ofNatModulo 7)

def equal : OrderedMapping.Predicate
  | .word left, .word right => left == right
  | _, _ => false

def comparator (environment : Core.Environment) : Core.Value :=
  .closure (.product .word .word) .bool
    (.binary .wordEq (.first (.var 0)) (.second (.var 0))) environment

def lookupStore (accounts : Accounts) (address : Word) (environment : Core.Environment)
    (store : Core.Store) : Core.Store :=
  OrderedMapping.installedStore store AccountState.layout.lookupParameter AccountState.layout.lookupResult
    (OrderedMapping.lookupBody AccountState.layout)
    (.pair (world accounts) (.pair (.word address) (comparator environment))) environment

def getStore (accounts : Accounts) (address : Word) (complete : Bool)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  lookupStore accounts address (bundleValues [world accounts, .word address, .bool complete] :: environment) store

def getValue : Except Word (AccountState.Account × Nat) → Core.Value
  | .ok (account, identity) => .inRight .word (record account identity)
  | .error reason => .inLeft AccountState.recordType (.word reason)

theorem readWord_eq (key : Word) (values : StorageSemantics.Words) :
    StorageSemantics.readWord key values = WordMapping.lookupEntries key values := by
  induction values with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨stored, value⟩; simp [StorageSemantics.readWord, WordMapping.lookupEntries, ih]

theorem writeWord_eq (key value : Word) (values : StorageSemantics.Words) :
    StorageSemantics.writeWord key value values = WordMapping.insertEntries key value values := by
  induction values with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨stored, old⟩; simp [StorageSemantics.writeWord, WordMapping.insertEntries, ih]

theorem lookup_source (accounts : Accounts) (address : Word) :
    (lookup address accounts).map Prod.fst = StorageSemantics.lookup address (accounts.map Prod.fst) := by
  induction accounts with
  | nil => rfl
  | cons account rest ih =>
      rcases account with ⟨account, identity⟩
      simp only [lookup, List.map_cons, StorageSemantics.lookup]
      split <;> simp_all

theorem get_source (accounts : Accounts) (address : Word) (complete : Bool) :
    (get accounts address complete).map Prod.fst = StorageSemantics.get (accounts.map Prod.fst) address complete := by
  unfold get StorageSemantics.get
  rw [← lookup_source]
  cases lookup address accounts with
  | none => cases complete <;> rfl
  | some account => cases account; rfl

theorem record_evaluates (account : AccountState.Account) (identity : Nat)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (AccountState.recordLiteral account identity) (record account identity) store := by
  exact .pair (WordMapping.literal_evaluates _ _ _) (.pair (WordMapping.literal_evaluates _ _ _)
    (.pair .word (.pair .word (.pair (WordMapping.literal_evaluates _ _ _)
      (.pair .word (.pair .bool (.pair .bool .bool)))))))

theorem default_evaluates (address : Word) (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store AccountState.defaultRecord (record {address := address} 0) store := by
  exact .pair (.construct .unit) (.pair (.construct .unit) (.pair .word (.pair .word
    (.pair (.construct .unit) (.pair .word (.pair .bool (.pair .bool .bool)))))))

theorem comparisons (accounts : Accounts) (address : Word) (environment : Core.Environment) (store : Core.Store) :
    OrderedMapping.Comparisons AccountState.layout (comparator environment) equal (.word address) (entries accounts) store := by
  intro key value member
  obtain ⟨⟨account, identity⟩, _, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨_, _, rfl, .binary (.first (.var rfl)) (.second (.var rfl)) rfl⟩

theorem lookup_entries (accounts : Accounts) (address : Word) :
    OrderedMapping.lookupEntries equal (.word address) (entries accounts) =
      (lookup address accounts).map (fun (account, identity) => record account identity) := by
  induction accounts with
  | nil => rfl
  | cons account rest ih =>
      rcases account with ⟨account, identity⟩
      simp only [entries, List.map_cons, OrderedMapping.lookupEntries, equal, lookup]
      split <;> rename_i test
      · simp [test]
      · simpa only [entries, test, Bool.false_eq_true, ↓reduceIte] using ih

theorem lookup_evaluates {environment : Core.Environment} {initial mappingStore final : Core.Store}
    {mapping addressExpr : Core.Expr} (accounts : Accounts) (address : Word)
    (mappingEvaluated : Core.Evaluates environment initial mapping (world accounts) mappingStore)
    (addressEvaluated : Core.Evaluates environment mappingStore addressExpr (.word address) final) :
    Core.Evaluates environment initial (AccountState.lookup mapping addressExpr)
      (.inRight .word (OrderedMapping.optionValue AccountState.recordType
        ((lookup address accounts).map (fun (account, identity) => record account identity))))
      (lookupStore accounts address environment final) := by
  have evaluated := OrderedMapping.lookup_evaluates (entries accounts) (.word address)
    (comparator environment) equal mappingEvaluated addressEvaluated (.lambda) (comparisons accounts address _ _)
  simpa only [lookup_entries, AccountState.lookup, AccountState.equal, AccountState.layout,
    lookupStore, comparator, world] using evaluated

theorem get_evaluates {environment : Core.Environment} {initial worldStore addressStore final : Core.Store}
    {worldExpr addressExpr completeExpr : Core.Expr} (accounts : Accounts) (address : Word) (complete : Bool)
    (worldEvaluated : Core.Evaluates environment initial worldExpr (world accounts) worldStore)
    (addressEvaluated : Core.Evaluates environment worldStore addressExpr (.word address) addressStore)
    (completeEvaluated : Core.Evaluates environment addressStore completeExpr (.bool complete) final) :
    Core.Evaluates environment initial (AccountState.get worldExpr addressExpr completeExpr)
      (getValue (get accounts address complete)) (getStore accounts address complete environment final) := by
  apply Core.Evaluates.letE (.pair worldEvaluated (.pair addressEvaluated completeEvaluated))
  have looked := lookup_evaluates (environment := bundleValues [world accounts, .word address, .bool complete] :: environment)
    (initial := final) (mappingStore := final) (final := final)
    (mapping := .first (.var 0)) (addressExpr := .first (.second (.var 0))) accounts address
    (Core.Evaluates.first (Core.Evaluates.var (by rfl)))
    (Core.Evaluates.first (Core.Evaluates.second (Core.Evaluates.var (by rfl))))
  apply LanguageResult.bind_success _ looked
  cases found : lookup address accounts with
  | none =>
      simp only [get, found, Option.map_none, OrderedMapping.optionValue]
      apply Core.Evaluates.caseLeft (.var rfl)
      cases complete
      · exact .ifFalse (.second (.second (.var rfl))) (.inLeft .word)
      · exact .ifTrue (.second (.second (.var rfl))) (.inRight (default_evaluates address _ _))
  | some account =>
      rcases account with ⟨account, identity⟩
      simp only [get, found, Option.map_some, OrderedMapping.optionValue, getValue]
      exact .caseRight (.var rfl) (.inRight (.var rfl))


def wordResult : Except Word Word → Core.Value
  | .ok value => .inRight .word (.word value)
  | .error reason => .inLeft .word (.word reason)

def readArguments (location : Nat) (address : Word) (complete : Bool) (key : Word) : Core.Value :=
  bundleValues [.cellRef AccountState.type location, .word address, .bool complete, .word key]

def readStore (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key : Word) (transient : Bool) (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  let arguments := readArguments location address complete key
  let fetched := getStore accounts address complete (arguments :: environment) store
  match get accounts address complete with
  | .error _ => fetched
  | .ok (account, identity) =>
      WordMapping.installedStore fetched WordMapping.lookupParameter .word WordMapping.lookupBody
        (.pair (WordMapping.encode (StorageSemantics.storage account transient)) (.word key))
        (record account identity :: arguments :: environment)

theorem read_source (accounts : Accounts) (address : Word) (complete : Bool)
    (key : Word) (transient : Bool) :
    StorageSemantics.readStorage (accounts.map Prod.fst) address complete key transient =
      match get accounts address complete with
      | .error reason => .error reason
      | .ok (account, _) => .ok (StorageSemantics.readWord key (StorageSemantics.storage account transient)) := by
  unfold StorageSemantics.readStorage
  rw [← get_source]
  cases get accounts address complete with
  | error reason => rfl
  | ok account => cases account; rfl

theorem readStorage_evaluates {environment : Core.Environment} {initial store : Core.Store}
    {worldReference addressExpr completeExpr keyExpr : Core.Expr}
    (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool) (key : Word) (transient : Bool)
    (arguments : Core.Evaluates environment initial
      (bundle [worldReference, addressExpr, completeExpr, keyExpr])
      (readArguments location address complete key) store)
    (found : store.read? location = some (world accounts)) :
    Core.Evaluates environment initial
      (AccountState.readStorage worldReference addressExpr completeExpr keyExpr transient)
      (wordResult (StorageSemantics.readStorage (accounts.map Prod.fst) address complete key transient))
      (readStore accounts location address complete key transient environment store) := by
  unfold AccountState.readStorage CodeBuilder.bind CodeBuilder.constant
  apply Core.Evaluates.letE arguments
  have fetched := get_evaluates
    (environment := readArguments location address complete key :: environment)
    (initial := store) (worldStore := store) (addressStore := store) (final := store)
    (worldExpr := .loadCell (.first (.var 0)))
    (addressExpr := .first (.second (.var 0)))
    (completeExpr := .first (.second (.second (.var 0)))) accounts address complete
    (.loadCell (.first (.var rfl)) found)
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
  rw [read_source]
  cases obtained : get accounts address complete with
  | error reason =>
      simp only [obtained, getValue] at fetched
      simp only [readStore, obtained, wordResult]
      exact LanguageResult.bind_failure .word fetched
  | ok account =>
      rcases account with ⟨account, identity⟩
      simp only [obtained, getValue] at fetched
      simp only [readStore, obtained, wordResult]
      apply LanguageResult.bind_success .word fetched
      rw [readWord_eq]
      apply WordMapping.lookup_evaluates
      · cases transient
        · exact .first (.var rfl)
        · exact .first (.second (.var rfl))
      · exact .second (.second (.second (.var rfl)))


def put (address : Word) (account : AccountState.Account) (identity : Nat) : Accounts → Accounts
  | [] => [({account with address := address}, identity)]
  | (head, headIdentity) :: rest =>
      if address == head.address then ({account with address := address}, identity) :: rest
      else (head, headIdentity) :: put address account identity rest

theorem put_source (accounts : Accounts) (address : Word) (account : AccountState.Account) (identity : Nat) :
    (put address account identity accounts).map Prod.fst =
      StorageSemantics.put address account (accounts.map Prod.fst) := by
  induction accounts with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨head, headIdentity⟩
      simp only [put, List.map_cons, StorageSemantics.put]
      split <;> simp_all

theorem put_entries (accounts : Accounts) (address : Word) (account : AccountState.Account) (identity : Nat) :
    OrderedMapping.insertEntries equal (.word address) (record account identity) (entries accounts) =
      entries (put address account identity accounts) := by
  induction accounts with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨head, headIdentity⟩
      simp only [put, entries, List.map_cons, OrderedMapping.insertEntries, equal]
      split <;> rename_i test
      · simp [test, record]
      · simpa only [test, Bool.false_eq_true, ↓reduceIte, entries, List.map_cons] using
          congrArg (fun rest => (.word head.address, record head headIdentity) :: rest) ih

def putStore (accounts : Accounts) (address : Word) (account : AccountState.Account) (identity : Nat)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  OrderedMapping.installedStore store AccountState.layout.insertParameter AccountState.type
    (OrderedMapping.insertBody AccountState.layout)
    (.pair (world accounts) (.pair (.pair (.word address) (record account identity)) (comparator environment))) environment

theorem put_evaluates {environment : Core.Environment}
    {initial mappingStore addressStore final : Core.Store} {mapping addressExpr accountExpr : Core.Expr}
    (accounts : Accounts) (address : Word) (account : AccountState.Account) (identity : Nat)
    (mappingEvaluated : Core.Evaluates environment initial mapping (world accounts) mappingStore)
    (addressEvaluated : Core.Evaluates environment mappingStore addressExpr (.word address) addressStore)
    (accountEvaluated : Core.Evaluates environment addressStore accountExpr (record account identity) final) :
    Core.Evaluates environment initial (AccountState.put mapping addressExpr accountExpr)
      (.inRight .word (world (put address account identity accounts)))
      (putStore accounts address account identity environment final) := by
  have evaluated := OrderedMapping.insert_evaluates (entries accounts) (.word address) (record account identity)
    (comparator environment) equal mappingEvaluated addressEvaluated accountEvaluated (.lambda) (comparisons accounts address _ _)
  simpa only [put_entries, AccountState.put, AccountState.equal, AccountState.layout,
    putStore, comparator, world, AccountState.type, AccountState.layout] using evaluated

theorem replaceStorage_evaluates {environment : Core.Environment} {store : Core.Store}
    {recordExpr updatedExpr : Core.Expr} (account : AccountState.Account) (identity : Nat)
    (key value : Word) (transient : Bool)
    (original : Core.Evaluates environment store recordExpr (record account identity) store)
    (updated : Core.Evaluates environment store updatedExpr
      (WordMapping.encode (WordMapping.insertEntries key value (StorageSemantics.storage account transient))) store) :
    Core.Evaluates environment store
      (AccountState.replace recordExpr (if transient then 1 else 0) updatedExpr)
      (record (StorageSemantics.update account transient key value) identity) store := by
  cases transient <;>
    simp only [StorageSemantics.storage, StorageSemantics.update, Bool.false_eq_true, ↓reduceIte,
      writeWord_eq] at updated ⊢
  · exact (.pair updated
        (.pair (.first (.second original))
          (.pair (.first (.second (.second original)))
            (.pair (.first (.second (.second (.second original))))
              (.pair (.first (.second (.second (.second (.second original)))))
                (.pair (.first (.second (.second (.second (.second (.second original))))))
                  (.pair (.first (.second (.second (.second (.second (.second (.second original)))))))
                    (.pair (.first (.second (.second (.second (.second (.second (.second (.second original))))))))
                      (.second (.second (.second (.second (.second (.second (.second (.second original))))))))))))))))
  · exact (.pair (.first original)
        (.pair updated
          (.pair (.first (.second (.second original)))
            (.pair (.first (.second (.second (.second original))))
              (.pair (.first (.second (.second (.second (.second original)))))
                (.pair (.first (.second (.second (.second (.second (.second original))))))
                  (.pair (.first (.second (.second (.second (.second (.second (.second original)))))))
                    (.pair (.first (.second (.second (.second (.second (.second (.second (.second original))))))))
                      (.second (.second (.second (.second (.second (.second (.second (.second original))))))))))))))))

theorem appended_read {store : Core.Store} {location : Nat} {value : Core.Value}
    (found : store.read? location = some value) (suffix : Core.Store) :
    (store ++ suffix).read? location = some value := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simpa only [Store.read?, List.getElem?_append_left bound] using found

def writeArguments (location : Nat) (address : Word) (complete : Bool) (key value : Word) : Core.Value :=
  bundleValues [.cellRef AccountState.type location, .word address, .bool complete, .word key, .word value]

def insertedStore (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) (account : AccountState.Account) (identity : Nat)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  let arguments := writeArguments location address complete key value
  let fetched := getStore accounts address complete (arguments :: environment) store
  WordMapping.installedStore fetched WordMapping.insertParameter WordMapping.type WordMapping.insertBody
    (.pair (WordMapping.encode (StorageSemantics.storage account transient)) (.pair (.word key) (.word value)))
    (record account identity :: arguments :: environment)

def beforeWriteStore (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) (account : AccountState.Account) (identity : Nat)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  let inserted := insertedStore accounts location address complete key value transient account identity environment store
  putStore accounts address (StorageSemantics.update account transient key value) identity
    (WordMapping.encode (WordMapping.insertEntries key value (StorageSemantics.storage account transient)) ::
      record account identity :: writeArguments location address complete key value :: environment) inserted

def writeStore (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  match get accounts address complete with
  | .error _ => getStore accounts address complete (writeArguments location address complete key value :: environment) store
  | .ok (account, identity) =>
      (beforeWriteStore accounts location address complete key value transient account identity environment store).set location
        (world (put address (StorageSemantics.update account transient key value) identity accounts))

def unitResult {α : Type} : Except Word α → Core.Value
  | .ok _ => .inRight .word .unit
  | .error reason => .inLeft .unit (.word reason)

theorem write_source (accounts : Accounts) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) :
    StorageSemantics.writeStorage (accounts.map Prod.fst) address complete key value transient =
      match get accounts address complete with
      | .error reason => .error reason
      | .ok (account, identity) =>
          .ok ((put address (StorageSemantics.update account transient key value) identity accounts).map Prod.fst) := by
  unfold StorageSemantics.writeStorage
  rw [← get_source]
  cases get accounts address complete with
  | error reason => rfl
  | ok account =>
      rcases account with ⟨account, identity⟩
      change Except.ok _ = Except.ok _
      exact congrArg Except.ok (put_source accounts address _ _).symm


theorem writeStorage_evaluates {environment : Core.Environment} {initial store : Core.Store}
    {worldReference addressExpr completeExpr keyExpr valueExpr : Core.Expr}
    (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool)
    (arguments : Core.Evaluates environment initial
      (bundle [worldReference, addressExpr, completeExpr, keyExpr, valueExpr])
      (writeArguments location address complete key value) store)
    (found : store.read? location = some (world accounts)) :
    Core.Evaluates environment initial
      (AccountState.writeStorage worldReference addressExpr completeExpr keyExpr valueExpr transient)
      (unitResult (StorageSemantics.writeStorage (accounts.map Prod.fst) address complete key value transient))
      (writeStore accounts location address complete key value transient environment store) := by
  unfold AccountState.writeStorage CodeBuilder.bind CodeBuilder.constant
  apply Core.Evaluates.letE arguments
  have fetched := get_evaluates
    (environment := writeArguments location address complete key value :: environment)
    (initial := store) (worldStore := store) (addressStore := store) (final := store)
    (worldExpr := .loadCell (.first (.var 0)))
    (addressExpr := .first (.second (.var 0)))
    (completeExpr := .first (.second (.second (.var 0)))) accounts address complete
    (.loadCell (.first (.var rfl)) found)
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
  rw [write_source]
  cases obtained : get accounts address complete with
  | error reason =>
      simp only [obtained, getValue] at fetched
      simp only [writeStore, obtained, unitResult]
      exact LanguageResult.bind_failure .unit fetched
  | ok account =>
      rcases account with ⟨account, identity⟩
      simp only [obtained, getValue] at fetched
      simp only [writeStore, obtained, unitResult]
      apply LanguageResult.bind_success .unit fetched
      have inserted : Core.Evaluates
          (record account identity :: writeArguments location address complete key value :: environment)
          (getStore accounts address complete (writeArguments location address complete key value :: environment) store)
          (WordMapping.insert (projectArgument (if transient then 1 else 0) 9 (.var 0))
            (projectArgument 3 5 (.var 1)) (projectArgument 4 5 (.var 1)))
          (.inRight .word (WordMapping.encode (WordMapping.insertEntries key value (StorageSemantics.storage account transient))))
          (insertedStore accounts location address complete key value transient account identity environment store) := by
        apply WordMapping.insert_evaluates
        · cases transient
          · exact .first (.var rfl)
          · exact .first (.second (.var rfl))
        · exact .first (.second (.second (.second (.var rfl))))
        · exact .second (.second (.second (.second (.var rfl))))
      apply LanguageResult.bind_success .unit inserted
      have current :
          (insertedStore accounts location address complete key value transient account identity environment store).read? location =
            some (world accounts) := appended_read (appended_read found _) _
      have updated := put_evaluates
        (environment := WordMapping.encode (WordMapping.insertEntries key value (StorageSemantics.storage account transient)) ::
          record account identity :: writeArguments location address complete key value :: environment)
        (initial := insertedStore accounts location address complete key value transient account identity environment store)
        (mappingStore := insertedStore accounts location address complete key value transient account identity environment store)
        (addressStore := insertedStore accounts location address complete key value transient account identity environment store)
        (final := insertedStore accounts location address complete key value transient account identity environment store)
        (mapping := .loadCell (projectArgument 0 5 (.var 2)))
        (addressExpr := projectArgument 1 5 (.var 2))
        (accountExpr := AccountState.replace (.var 1) (if transient then 1 else 0) (.var 0))
        accounts address (StorageSemantics.update account transient key value) identity
        (.loadCell (.first (.var rfl)) current) (.first (.second (.var rfl)))
        (replaceStorage_evaluates account identity key value transient (.var rfl) (.var rfl))
      apply LanguageResult.bind_success .unit updated
      have latest :
          (beforeWriteStore accounts location address complete key value transient account identity environment store).read? location =
            some (world accounts) := appended_read current _
      exact .inRight (.storeCell (.first (.var rfl)) latest (.var rfl)
        (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp latest).1, rfl⟩))


def canonical (accounts : Accounts) : Accounts :=
  accounts.map fun (account, identity) =>
    ({account with address := Word.ofNatModulo (account.address.val % 2 ^ 160)}, identity)

theorem literal_evaluates (accounts : Accounts) (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (AccountState.literal accounts) (world (canonical accounts)) store := by
  induction accounts with
  | nil => exact .construct .unit
  | cons entry rest ih =>
      rcases entry with ⟨account, identity⟩
      exact .construct (.pair (.pair .word (record_evaluates account identity environment store)) ih)

theorem getStore_extension (accounts : Accounts) (address : Word) (complete : Bool)
    (environment : Core.Environment) (store : Core.Store) :
    ∃ suffix, suffix.length = 1 ∧ getStore accounts address complete environment store = store ++ suffix := by
  exact ⟨_, rfl, rfl⟩

theorem readStore_extension (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key : Word) (transient : Bool) (environment : Core.Environment) (store : Core.Store) :
    ∃ suffix, suffix.length = (if (get accounts address complete).isOk then 2 else 1) ∧
      readStore accounts location address complete key transient environment store = store ++ suffix := by
  unfold readStore
  cases obtained : get accounts address complete with
  | error reason => exact ⟨_, rfl, rfl⟩
  | ok account =>
      rcases account with ⟨account, identity⟩
      simp only [getStore, lookupStore, OrderedMapping.installedStore, WordMapping.installedStore, List.append_assoc]
      refine ⟨_, ?_, rfl⟩
      rfl

theorem readStore_preserves {store : Core.Store} {readLocation : Nat} {observed : Core.Value}
    (found : store.read? readLocation = some observed)
    (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key : Word) (transient : Bool) (environment : Core.Environment) :
    (readStore accounts location address complete key transient environment store).read? readLocation = some observed := by
  obtain ⟨suffix, _, same⟩ := readStore_extension accounts location address complete key transient environment store
  rw [same]
  exact appended_read found suffix

theorem beforeWriteStore_extension (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) (account : AccountState.Account) (identity : Nat)
    (environment : Core.Environment) (store : Core.Store) :
    ∃ suffix, suffix.length = 3 ∧
      beforeWriteStore accounts location address complete key value transient account identity environment store = store ++ suffix := by
  simp only [beforeWriteStore, insertedStore, getStore, putStore, lookupStore,
    OrderedMapping.installedStore, WordMapping.installedStore, List.append_assoc]
  refine ⟨_, ?_, rfl⟩
  rfl

theorem writeStore_written {accounts : Accounts} {location : Nat} {address : Word} {complete : Bool}
    {key value : Word} {transient : Bool} {account : AccountState.Account} {identity : Nat}
    {environment : Core.Environment} {store : Core.Store}
    (obtained : get accounts address complete = .ok (account, identity))
    (found : store.read? location = some (world accounts)) :
    (writeStore accounts location address complete key value transient environment store).read? location =
      some (world (put address (StorageSemantics.update account transient key value) identity accounts)) := by
  simp only [writeStore, obtained]
  have latest :
      (beforeWriteStore accounts location address complete key value transient account identity environment store).read? location =
        some (world accounts) := appended_read (appended_read (appended_read found _) _) _
  exact Store.write?_reads_written
    (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp latest).1, rfl⟩)

theorem writeStore_preserves {store : Core.Store} {readLocation : Nat} {observed : Core.Value}
    (found : store.read? readLocation = some observed)
    (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) (environment : Core.Environment)
    (different : readLocation ≠ location) :
    (writeStore accounts location address complete key value transient environment store).read? readLocation = some observed := by
  unfold writeStore
  cases obtained : get accounts address complete with
  | error reason => exact appended_read found _
  | ok account =>
      rcases account with ⟨account, identity⟩
      change (_[readLocation]? = some observed)
      rw [List.getElem?_set_ne (Ne.symm different)]
      exact appended_read (appended_read (appended_read found _) _) _


/-- Runtime code identities are existential representation witnesses. -/
def StateRel (source : StorageSemantics.World) (location : Nat) (store : Core.Store) : Prop :=
  ∃ accounts, accounts.map Prod.fst = source ∧ store.read? location = some (world accounts)

structure Frame (changed : Nat) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  preserved : ∀ location value, location ≠ changed →
    initial.read? location = some value → final.read? location = some value

theorem Frame.refl (changed : Nat) (store : Core.Store) : Frame changed store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem Frame.append (changed : Nat) (store suffix : Core.Store) : Frame changed store (store ++ suffix) :=
  ⟨by simp, fun _ _ _ found => appended_read found suffix⟩

theorem Frame.trans {changed : Nat} {initial middle final : Core.Store}
    (first : Frame changed initial middle) (second : Frame changed middle final) : Frame changed initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun location value different found =>
    second.preserved location value different (first.preserved location value different found)⟩

theorem Frame.write {store : Core.Store} {changed : Nat} {value : Core.Value} :
    Frame changed store (store.set changed value) := by
  constructor
  · simp
  · intro location observed different found
    change (store.set changed value)[location]? = some observed
    rw [List.getElem?_set_ne (Ne.symm different)]
    exact found

theorem readStore_frame (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key : Word) (transient : Bool) (environment : Core.Environment) (store : Core.Store) :
    Frame location store (readStore accounts location address complete key transient environment store) := by
  obtain ⟨suffix, _, same⟩ := readStore_extension accounts location address complete key transient environment store
  rw [same]
  exact Frame.append _ _ _

theorem writeStore_frame (accounts : Accounts) (location : Nat) (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool) (environment : Core.Environment) (store : Core.Store) :
    Frame location store (writeStore accounts location address complete key value transient environment store) := by
  unfold writeStore
  cases get accounts address complete with
  | error reason => exact Frame.append _ _ _
  | ok account =>
      rcases account with ⟨account, identity⟩
      obtain ⟨suffix, _, same⟩ := beforeWriteStore_extension accounts location address complete key value transient
        account identity environment store
      change Frame location store ((beforeWriteStore accounts location address complete key value transient account identity environment store).set location _)
      rw [same]
      exact (Frame.append _ _ _).trans Frame.write

theorem readStorage_preserves {environment : Core.Environment} {initial store : Core.Store}
    {worldReference addressExpr completeExpr keyExpr : Core.Expr}
    {source : StorageSemantics.World} {location : Nat} (address : Word) (complete : Bool)
    (key : Word) (transient : Bool)
    (arguments : Core.Evaluates environment initial
      (bundle [worldReference, addressExpr, completeExpr, keyExpr])
      (readArguments location address complete key) store)
    (related : StateRel source location store) :
    ∃ final, Core.Evaluates environment initial
      (AccountState.readStorage worldReference addressExpr completeExpr keyExpr transient)
      (wordResult (StorageSemantics.readStorage source address complete key transient)) final ∧
      StateRel source location final ∧ Frame location store final := by
  obtain ⟨accounts, rfl, found⟩ := related
  exact ⟨_, readStorage_evaluates accounts location address complete key transient arguments found,
    ⟨accounts, rfl, readStore_preserves found accounts location address complete key transient environment⟩,
    readStore_frame accounts location address complete key transient environment store⟩

theorem writeStorage_preserves {environment : Core.Environment} {initial store : Core.Store}
    {worldReference addressExpr completeExpr keyExpr valueExpr : Core.Expr}
    {source : StorageSemantics.World} {location : Nat} (address : Word) (complete : Bool)
    (key value : Word) (transient : Bool)
    (arguments : Core.Evaluates environment initial
      (bundle [worldReference, addressExpr, completeExpr, keyExpr, valueExpr])
      (writeArguments location address complete key value) store)
    (related : StateRel source location store) :
    ∃ final, Core.Evaluates environment initial
      (AccountState.writeStorage worldReference addressExpr completeExpr keyExpr valueExpr transient)
      (unitResult (StorageSemantics.writeStorage source address complete key value transient)) final ∧
      StateRel ((StorageSemantics.writeStorage source address complete key value transient).toOption.getD source)
        location final ∧ Frame location store final := by
  obtain ⟨accounts, rfl, found⟩ := related
  refine ⟨_, writeStorage_evaluates accounts location address complete key value transient arguments found,
    ?_, writeStore_frame accounts location address complete key value transient environment store⟩
  rw [write_source]
  cases obtained : get accounts address complete with
  | error reason =>
      refine ⟨accounts, rfl, ?_⟩
      simp only [writeStore, obtained]
      exact appended_read found _
  | ok account =>
      rcases account with ⟨account, identity⟩
      exact ⟨_, rfl, writeStore_written obtained found⟩


/-- Stateful helper calls retain the installed self reference while the body
may append helpers and update account data. -/
theorem invoke_stateful {environment captured : Core.Environment} {store final : Core.Store}
    {parameter result : Core.Ty} {body reference argument : Core.Expr} {location : Nat} {input output : Core.Value}
    (referenceEvaluated : Core.Evaluates environment store reference
      (.cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) location) store)
    (installed : WordMapping.Installed store parameter result body location captured)
    (argumentEvaluated : Core.Evaluates
      (WordMapping.closure parameter result body location captured :: environment)
      store (argument.weakenAt 0) input store)
    (bodyEvaluated : Core.Evaluates
      (input :: .cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) location :: captured)
      store body output final) :
    Core.Evaluates environment store (WordMapping.invoke parameter result reference argument) output final := by
  exact .caseRight (OptionalCell.read_success Word.zero referenceEvaluated installed)
    (.apply (.var rfl) argumentEvaluated bodyEvaluated)

theorem runHelper_stateful {environment : Core.Environment} {initial argumentStore final : Core.Store}
    {parameter result : Core.Ty} {body argument : Core.Expr} {input output : Core.Value}
    (argumentEvaluated : Core.Evaluates environment initial argument input argumentStore)
    (bodyEvaluated : Core.Evaluates
      (input :: .cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) argumentStore.length ::
        input :: environment)
      (WordMapping.installedStore argumentStore parameter result body input environment) body output final) :
    Core.Evaluates environment initial (WordMapping.runHelper parameter result body argument) output final := by
  apply Core.Evaluates.letE argumentEvaluated
  apply Core.Evaluates.letE (OptionalCell.allocate_evaluates _ _ _)
  apply Core.Evaluates.letE (bodyStore := WordMapping.installedStore argumentStore parameter result body input environment)
  · apply Core.Evaluates.storeCell (oldValue := .inLeft (WordMapping.helperType parameter result) .unit) (.var rfl)
    · simp [Store.read?]
    · exact .inRight .lambda
    · simp [Store.write?, WordMapping.installedStore, WordMapping.closure]
  · apply invoke_stateful (body := body) (captured := input :: environment) (.var rfl)
    · simp [WordMapping.Installed, WordMapping.installedStore, Store.read?]
    · simpa [Core.Expr.weakenAt] using (Core.Evaluates.var (by rfl))
    · exact bodyEvaluated

def finalize : Accounts → StorageSemantics.Words → Accounts × StorageSemantics.Words
  | [], balances => ([], balances)
  | (account, identity) :: rest, balances =>
      if account.created && account.destroyed then
        finalize rest (StorageSemantics.writeWord account.address Word.zero balances)
      else
        let (next, balances) := finalize rest balances
        ((StorageSemantics.clearTransaction account, identity) :: next, balances)

theorem finalize_source (accounts : Accounts) (balances : StorageSemantics.Words) :
    ((finalize accounts balances).1.map Prod.fst, (finalize accounts balances).2) =
      StorageSemantics.finalize (accounts.map Prod.fst) balances := by
  induction accounts generalizing balances with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨account, identity⟩
      simp only [finalize, List.map_cons, StorageSemantics.finalize]
      split
      · exact ih _
      · simpa only [List.map_cons] using congrArg
          (fun next => (StorageSemantics.clearTransaction account :: next.1, next.2)) (ih balances)

theorem clearTransaction_evaluates {environment : Core.Environment} {store : Core.Store}
    {expression : Core.Expr} (account : AccountState.Account) (identity : Nat)
    (original : Core.Evaluates environment store expression (record account identity) store) :
    Core.Evaluates environment store (AccountState.clearTransaction expression)
      (record (StorageSemantics.clearTransaction account) identity) store := by
  exact (.pair (.first original)
      (.pair (.construct .unit)
        (.pair (.first (.second (.second original)))
          (.pair (.first (.second (.second (.second original))))
            (.pair (.first (.second (.second (.second (.second original)))))
              (.pair (.first (.second (.second (.second (.second (.second original))))))
                (.pair (.first (.second (.second (.second (.second (.second (.second original)))))))
                  (.pair .bool
                    .bool))))))))

def finalizeReference (location : Nat) : Core.Value :=
  .cellRef (OptionalCell.cellType (WordMapping.helperType AccountState.finalizeParameter AccountState.type)) location

def finalizeArgument (accounts : Accounts) (balancesLocation : Nat) : Core.Value :=
  .pair (world accounts) (.cellRef WordMapping.type balancesLocation)

theorem created_evaluates {environment : Core.Environment} {store : Core.Store} {expression : Core.Expr}
    (account : AccountState.Account) (identity : Nat)
    (original : Core.Evaluates environment store expression (record account identity) store) :
    Core.Evaluates environment store (projectArgument 7 9 expression) (.bool account.created) store := by
  exact .first (.second (.second (.second (.second (.second (.second (.second original)))))))

theorem destroyed_evaluates {environment : Core.Environment} {store : Core.Store} {expression : Core.Expr}
    (account : AccountState.Account) (identity : Nat)
    (original : Core.Evaluates environment store expression (record account identity) store) :
    Core.Evaluates environment store (projectArgument 8 9 expression) (.bool account.destroyed) store := by
  exact .second (.second (.second (.second (.second (.second (.second (.second original)))))))

theorem finalizeBody_retain {captured : Core.Environment} {store final : Core.Store}
    (account : AccountState.Account) (identity : Nat) (rest next : Accounts) (balancesLocation self : Nat)
    (retained : (account.created && account.destroyed) = false)
    (installed : WordMapping.Installed store AccountState.finalizeParameter AccountState.type AccountState.finalizeBody self captured)
    (continued : Core.Evaluates
      (finalizeArgument rest balancesLocation :: finalizeReference self :: captured) store
      AccountState.finalizeBody (.inRight .word (world next)) final) :
    Core.Evaluates
      (finalizeArgument ((account, identity) :: rest) balancesLocation :: finalizeReference self :: captured) store
      AccountState.finalizeBody (.inRight .word (world ((StorageSemantics.clearTransaction account, identity) :: next))) final := by
  unfold AccountState.finalizeBody
  apply Core.Evaluates.matchData (constructor := AccountState.layout.consConstructor) (.first (.var rfl)) rfl rfl
  apply Core.Evaluates.letE (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
  cases created : account.created
  all_goals first
    | apply Core.Evaluates.ifFalse (by
        simpa [created, CodeBuilder.part, projectArgument] using
          (created_evaluates account identity
            (Core.Evaluates.second (Core.Evaluates.first (Core.Evaluates.first (Core.Evaluates.var (by rfl)))))))
    | apply Core.Evaluates.ifTrue (by
        simpa [created, CodeBuilder.part, projectArgument] using
          (created_evaluates account identity
            (Core.Evaluates.second (Core.Evaluates.first (Core.Evaluates.first (Core.Evaluates.var (by rfl)))))))
  all_goals try
    have destroyed : account.destroyed = false := by simpa only [created, Bool.true_and] using retained
    apply Core.Evaluates.ifFalse (by
      simpa [destroyed, CodeBuilder.part, projectArgument] using
        (destroyed_evaluates account identity
          (Core.Evaluates.second (Core.Evaluates.first (Core.Evaluates.first (Core.Evaluates.var (by rfl)))))))
  all_goals
    apply LanguageResult.bind_success AccountState.type
    · apply invoke_stateful (input := finalizeArgument rest balancesLocation) (.second (.second (.var rfl))) installed
      · simp [CodeBuilder.part, projectArgument, Core.Expr.weakenAt]
        change Core.Evaluates _ _
          (.pair (.second (.first (.var 1))) (.second (.first (.second (.var 1)))))
          (finalizeArgument rest balancesLocation) _
        exact .pair (.second (.first (.var rfl))) (.second (.first (.second (.var rfl))))
      · exact continued
    · exact .inRight (.construct (.pair (.pair (.first (.first (.first (.var rfl))))
        (clearTransaction_evaluates account identity (.second (.first (.first (.var rfl)))))) (.var rfl)))


def finalizeEntry (account : AccountState.Account) (identity : Nat) (rest : Accounts) : Core.Value :=
  .pair (.pair (.word account.address) (record account identity)) (world rest)

def finalizeEnvironment (account : AccountState.Account) (identity : Nat) (rest : Accounts)
    (balancesLocation self : Nat) (captured : Core.Environment) : Core.Environment :=
  let entry := finalizeEntry account identity rest
  let argument := finalizeArgument ((account, identity) :: rest) balancesLocation
  bundleValues [entry, argument, finalizeReference self] :: entry :: argument :: finalizeReference self :: captured

def burnInsertStore (account : AccountState.Account) (identity : Nat) (rest : Accounts)
    (balances : StorageSemantics.Words) (balancesLocation self : Nat)
    (captured : Core.Environment) (store : Core.Store) : Core.Store :=
  WordMapping.installedStore store WordMapping.insertParameter WordMapping.type WordMapping.insertBody
    (.pair (WordMapping.encode balances) (.pair (.word account.address) (.word Word.zero)))
    (finalizeEnvironment account identity rest balancesLocation self captured)

def burnStore (account : AccountState.Account) (identity : Nat) (rest : Accounts)
    (balances : StorageSemantics.Words) (balancesLocation self : Nat)
    (captured : Core.Environment) (store : Core.Store) : Core.Store :=
  (burnInsertStore account identity rest balances balancesLocation self captured store).set balancesLocation
    (WordMapping.encode (WordMapping.insertEntries account.address Word.zero balances))

theorem burnStore_frame (account : AccountState.Account) (identity : Nat) (rest : Accounts)
    (balances : StorageSemantics.Words) (balancesLocation self : Nat)
    (captured : Core.Environment) (store : Core.Store) :
    Frame balancesLocation store (burnStore account identity rest balances balancesLocation self captured store) :=
  (Frame.append _ _ _).trans Frame.write

theorem burnStore_balance {account : AccountState.Account} {identity : Nat} {rest : Accounts}
    {balances : StorageSemantics.Words} {balancesLocation self : Nat}
    {captured : Core.Environment} {store : Core.Store}
    (found : store.read? balancesLocation = some (WordMapping.encode balances)) :
    (burnStore account identity rest balances balancesLocation self captured store).read? balancesLocation =
      some (WordMapping.encode (WordMapping.insertEntries account.address Word.zero balances)) := by
  have current : (burnInsertStore account identity rest balances balancesLocation self captured store).read? balancesLocation =
      some (WordMapping.encode balances) := appended_read found _
  exact Store.write?_reads_written (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp current).1, rfl⟩)

theorem finalizeBody_remove {captured : Core.Environment} {store final : Core.Store}
    (account : AccountState.Account) (identity : Nat) (rest next : Accounts)
    (balances : StorageSemantics.Words) (balancesLocation self : Nat)
    (removed : (account.created && account.destroyed) = true)
    (found : store.read? balancesLocation = some (WordMapping.encode balances))
    (installed : WordMapping.Installed
      (burnStore account identity rest balances balancesLocation self captured store)
      AccountState.finalizeParameter AccountState.type AccountState.finalizeBody self captured)
    (continued : Core.Evaluates
      (finalizeArgument rest balancesLocation :: finalizeReference self :: captured)
      (burnStore account identity rest balances balancesLocation self captured store)
      AccountState.finalizeBody (.inRight .word (world next)) final) :
    Core.Evaluates
      (finalizeArgument ((account, identity) :: rest) balancesLocation :: finalizeReference self :: captured) store
      AccountState.finalizeBody (.inRight .word (world next)) final := by
  have both : account.created = true ∧ account.destroyed = true := by
    cases created : account.created <;> cases destroyed : account.destroyed <;> simp_all
  obtain ⟨created, destroyed⟩ := both
  unfold AccountState.finalizeBody
  apply Core.Evaluates.matchData (constructor := AccountState.layout.consConstructor) (.first (.var rfl)) rfl rfl
  apply Core.Evaluates.letE (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
  apply Core.Evaluates.ifTrue (by
    simpa [created, CodeBuilder.part, projectArgument] using
      (created_evaluates account identity
        (Core.Evaluates.second (Core.Evaluates.first (Core.Evaluates.first (Core.Evaluates.var (by rfl)))))))
  apply Core.Evaluates.ifTrue (by
    simpa [destroyed, CodeBuilder.part, projectArgument] using
      (destroyed_evaluates account identity
        (Core.Evaluates.second (Core.Evaluates.first (Core.Evaluates.first (Core.Evaluates.var (by rfl)))))))
  apply LanguageResult.bind_success AccountState.type
  · apply WordMapping.insert_evaluates balances account.address Word.zero
    · exact .loadCell (.second (.first (.second (.var rfl)))) found
    · exact .first (.first (.first (.var rfl)))
    · exact .word
  · have current :
        (burnInsertStore account identity rest balances balancesLocation self captured store).read? balancesLocation =
          some (WordMapping.encode balances) := appended_read found _
    apply Core.Evaluates.letE (bodyStore := burnStore account identity rest balances balancesLocation self captured store)
    · exact .storeCell (.second (.first (.second (.var rfl)))) current (.var rfl)
        (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp current).1, rfl⟩)
    · apply invoke_stateful (input := finalizeArgument rest balancesLocation) (.second (.second (.var rfl))) installed
      · simp [CodeBuilder.part, projectArgument, Core.Expr.weakenAt]
        change Core.Evaluates _ _
          (.pair (.second (.first (.var 3))) (.second (.first (.second (.var 3)))))
          (finalizeArgument rest balancesLocation) _
        exact .pair (.second (.first (.var rfl))) (.second (.first (.second (.var rfl))))
      · exact continued

theorem finalizeBody_evaluates (accounts : Accounts) (balances : StorageSemantics.Words)
    (balancesLocation self : Nat) (captured : Core.Environment) (store : Core.Store)
    (installed : WordMapping.Installed store AccountState.finalizeParameter AccountState.type AccountState.finalizeBody self captured)
    (found : store.read? balancesLocation = some (WordMapping.encode balances)) :
    ∃ final, Core.Evaluates (finalizeArgument accounts balancesLocation :: finalizeReference self :: captured) store
      AccountState.finalizeBody (.inRight .word (world (finalize accounts balances).1)) final ∧
      final.read? balancesLocation = some (WordMapping.encode (finalize accounts balances).2) ∧
      Frame balancesLocation store final := by
  induction accounts generalizing balances store with
  | nil => exact ⟨store, .matchData (.first (.var rfl)) rfl rfl (.inRight (.construct .unit)), found, Frame.refl _ _⟩
  | cons entry rest ih =>
      rcases entry with ⟨account, identity⟩
      cases removed : account.created && account.destroyed
      · obtain ⟨final, evaluated, balancesFound, frame⟩ := ih balances store installed found
        refine ⟨final, ?_, ?_, frame⟩
        · simpa only [finalize, removed, Bool.false_eq_true, ↓reduceIte] using
            finalizeBody_retain account identity rest (finalize rest balances).1 balancesLocation self removed installed evaluated
        · simpa only [finalize, removed, Bool.false_eq_true, ↓reduceIte] using balancesFound
      · have different : self ≠ balancesLocation := by
          intro same
          subst self
          change store.read? balancesLocation = some (.inRight .unit _) at installed
          rw [found] at installed
          cases balances <;> cases installed
        have firstFrame := burnStore_frame account identity rest balances balancesLocation self captured store
        have nextInstalled : WordMapping.Installed
            (burnStore account identity rest balances balancesLocation self captured store)
            AccountState.finalizeParameter AccountState.type AccountState.finalizeBody self captured :=
          firstFrame.preserved _ _ different installed
        have nextFound := burnStore_balance (account := account) (identity := identity) (rest := rest)
          (self := self) (captured := captured) found
        obtain ⟨final, evaluated, balancesFound, frame⟩ := ih
          (WordMapping.insertEntries account.address Word.zero balances) _ nextInstalled nextFound
        refine ⟨final, ?_, ?_, firstFrame.trans frame⟩
        · simpa only [finalize, removed, ↓reduceIte, writeWord_eq] using
            finalizeBody_remove account identity rest
              (finalize rest (WordMapping.insertEntries account.address Word.zero balances)).1
              balances balancesLocation self removed found nextInstalled evaluated
        · simpa only [finalize, removed, ↓reduceIte, writeWord_eq] using balancesFound


structure FinalizeFrame (worldLocation balancesLocation : Nat) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  preserved : ∀ location value, location ≠ worldLocation → location ≠ balancesLocation →
    initial.read? location = some value → final.read? location = some value

theorem finalize_evaluates {environment : Core.Environment} {initial store : Core.Store}
    {worldReference balancesReference : Core.Expr}
    (accounts : Accounts) (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat)
    (arguments : Core.Evaluates environment initial (.pair worldReference balancesReference)
      (.pair (.cellRef AccountState.type worldLocation) (.cellRef WordMapping.type balancesLocation)) store)
    (worldFound : store.read? worldLocation = some (world accounts))
    (balancesFound : store.read? balancesLocation = some (WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial (AccountState.finalize worldReference balancesReference)
      (.inRight .word .unit) final ∧
      final.read? worldLocation = some (world (finalize accounts balances).1) ∧
      final.read? balancesLocation = some (WordMapping.encode (finalize accounts balances).2) ∧
      FinalizeFrame worldLocation balancesLocation store final := by
  let argumentsValue := Core.Value.pair (.cellRef AccountState.type worldLocation) (.cellRef WordMapping.type balancesLocation)
  let input := finalizeArgument accounts balancesLocation
  let initialized := WordMapping.installedStore store AccountState.finalizeParameter AccountState.type
    AccountState.finalizeBody input (argumentsValue :: environment)
  have installed : WordMapping.Installed initialized AccountState.finalizeParameter AccountState.type
      AccountState.finalizeBody store.length (input :: argumentsValue :: environment) := by
    simp [initialized, WordMapping.Installed, WordMapping.installedStore, Store.read?]
  have initialBalance : initialized.read? balancesLocation = some (WordMapping.encode balances) := appended_read balancesFound _
  obtain ⟨bodyStore, bodyEvaluated, finalBalance, frame⟩ := finalizeBody_evaluates accounts balances
    balancesLocation store.length (input :: argumentsValue :: environment) initialized installed initialBalance
  have separate : worldLocation ≠ balancesLocation := by
    intro same
    rw [same, balancesFound] at worldFound
    cases accounts <;> cases balances <;> cases worldFound
  have retainedWorld := frame.preserved worldLocation (world accounts) separate (appended_read worldFound _)
  let final := bodyStore.set worldLocation (world (finalize accounts balances).1)
  have written : bodyStore.write? worldLocation (world (finalize accounts balances).1) = some final :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp retainedWorld).1, rfl⟩
  refine ⟨final, ?_, Store.write?_reads_written written, ?_, ?_⟩
  · unfold AccountState.finalize CodeBuilder.bind CodeBuilder.constant
    apply Core.Evaluates.letE arguments
    apply LanguageResult.bind_success .unit
    · apply runHelper_stateful
      · exact .pair (.loadCell (.first (.var rfl)) worldFound) (.second (.var rfl))
      · exact bodyEvaluated
    · exact .inRight (.storeCell (.first (.var rfl)) retainedWorld (.var rfl) written)
  · rw [Store.write?_preserves_other written (Ne.symm separate)]
    exact finalBalance
  · constructor
    · have bound : store.length ≤ initialized.length := by simp [initialized, WordMapping.installedStore]
      rw [Store.write?_preserves_length written]
      exact Nat.le_trans bound frame.length_le
    · intro location value differentWorld differentBalances found
      rw [Store.write?_preserves_other written differentWorld]
      exact frame.preserved location value differentBalances (appended_read found _)

theorem finalize_preserves {environment : Core.Environment} {initial store : Core.Store}
    {worldReference balancesReference : Core.Expr}
    {source : StorageSemantics.World} (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat)
    (arguments : Core.Evaluates environment initial (.pair worldReference balancesReference)
      (.pair (.cellRef AccountState.type worldLocation) (.cellRef WordMapping.type balancesLocation)) store)
    (related : StateRel source worldLocation store)
    (balancesFound : store.read? balancesLocation = some (WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial (AccountState.finalize worldReference balancesReference)
      (.inRight .word .unit) final ∧
      StateRel (StorageSemantics.finalize source balances).1 worldLocation final ∧
      final.read? balancesLocation = some (WordMapping.encode (StorageSemantics.finalize source balances).2) ∧
      FinalizeFrame worldLocation balancesLocation store final := by
  obtain ⟨accounts, rfl, worldFound⟩ := related
  obtain ⟨final, evaluated, worldFound, balancesFound, frame⟩ :=
    finalize_evaluates accounts balances worldLocation balancesLocation arguments worldFound balancesFound
  have source := finalize_source accounts balances
  exact ⟨final, evaluated, ⟨_, congrArg Prod.fst source, worldFound⟩,
    by simpa only [← source] using balancesFound, frame⟩

end Solcore.Frontend.RustHull.StorageCorrespondence
end
