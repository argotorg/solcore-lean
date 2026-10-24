import Solcore.Frontend.RustHull.NamedFunctionCorrespondence

/-! Actual argument-cell initialization for named Hull functions. Bundle
projection and initialized allocation use the same expressions as lowerFunction;
the source heap and Core heap retain their distinct location spaces. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

theorem projectArgument_evaluates {values : List Core.Value} {index : Nat} {value : Core.Value}
    {environment : Core.Environment} {initial final : Core.Store} {expression : Core.Expr}
    (evaluated : Core.Evaluates environment initial expression (bundleValues values) final)
    (found : values[index]? = some value) :
    Core.Evaluates environment initial (projectArgument index values.length expression) value final := by
  induction values generalizing index expression with
  | nil => simp at found
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases index with
          | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; exact evaluated
          | succ index => simp at found
      | cons next rest =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst value
              exact .first evaluated
          | succ index =>
              exact ih (.second evaluated) found

/-- This is the exact fold used by lowerFunction, with an explicit index
offset for induction through earlier argument allocations. -/
def parameterCode (total start : Nat) (types : List Core.Ty) (body : Core.Expr) : Core.Expr :=
  (types.zipIdx start).foldr (fun (type, index) body =>
    .letE (Core.OptionalCell.allocateInitialized type
      (projectArgument index total (.var index))) body) body

/-- Deterministic allocation of argument cells, retaining all existing cells
and adding the new references to the lexical environment in source order. -/
inductive ParameterCells : List Core.Ty → List Core.Value → Core.Environment → Core.Store →
    Core.Environment → Core.Store → Prop where
  | nil {environment store} : ParameterCells [] [] environment store environment store
  | cons {type types value values environment store finalEnvironment finalStore}
      (rest : ParameterCells types values
        (.cellRef (Core.OptionalCell.cellType type) store.length :: environment)
        (store ++ [.inRight .unit value]) finalEnvironment finalStore) :
      ParameterCells (type :: types) (value :: values) environment store finalEnvironment finalStore

/-- A ParameterCells derivation executes the compiler's actual allocation
fold before entering the body. It does not replace it with a host initializer. -/
theorem ParameterCells.evaluates {types : List Core.Ty} {values allValues : List Core.Value}
    {environment finalEnvironment : Core.Environment} {initial allocated final : Core.Store}
    (cells : ParameterCells types values environment initial finalEnvironment allocated)
    {start : Nat} (argument : environment[start]? = some (bundleValues allValues))
    (selected : ∀ index value, values[index]? = some value → allValues[start + index]? = some value)
    {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates finalEnvironment allocated body result final) :
    Core.Evaluates environment initial (parameterCode allValues.length start types body) result final := by
  induction cells generalizing start with
  | nil => exact evaluated
  | @cons type types value values environment store finalEnvironment finalStore rest ih =>
      simp only [parameterCode, List.zipIdx_cons, List.foldr_cons]
      apply Core.Evaluates.letE
        (Core.OptionalCell.allocateInitialized_evaluates
          (projectArgument_evaluates (.var argument) (by simpa using selected 0 value rfl)))
      apply ih (start := start + 1)
      · exact argument
      · intro index selectedValue found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using selected (index + 1) selectedValue found
      · exact evaluated

def parameterScope (arguments : List Arg) (types : List Core.Ty) (scope : Scope) : Scope :=
  (arguments.zip types).foldl (fun scope (argument, type) => scope.addLocal argument.name type) scope

/-- The actual source binder and the argument-cell allocation agree, deriving
both local environments, both heaps and the external-state invariant. -/
theorem initialize_parameters {σ : Type} {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel types sources targets) (arity : arguments.length = types.length)
    {sourceEnvironment : Semantics.Environment} {scope : Scope} {sourceState : Semantics.State σ}
    {world : World} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope Core.Renaming.id environment)
    (heapRelated : HeapRel world sourceState.heap store)
    {external : σ → Core.Store → Prop} (externalRelated : external sourceState.external store)
    (frame : ∀ state store type value, external state store →
      external state (store ++ [Core.Value.inRight type value])) :
    ∃ extension sourceEnvironment' sourceState' environment' store',
      Semantics.bindArguments arguments sources sourceEnvironment sourceState = some (sourceEnvironment', sourceState') ∧
      ParameterCells types targets environment store environment' store' ∧
      EnvironmentRel (world ++ extension) sourceEnvironment' (parameterScope arguments types scope)
        Core.Renaming.id environment' ∧
      HeapRel (world ++ extension) sourceState'.heap store' ∧
      external sourceState'.external store' := by
  induction values generalizing arguments sourceEnvironment scope sourceState world environment store with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact ⟨[], sourceEnvironment, sourceState, environment, store, rfl, .nil,
        by simpa [parameterScope] using environmentRelated, by simpa using heapRelated, externalRelated⟩
  | @cons type types source sources target targets head tail ih =>
      cases arguments with
      | nil => simp at arity
      | cons argument arguments =>
          have arity' : arguments.length = types.length := Nat.succ.inj arity
          have entry : (world ++ [(type, store.length)])[sourceState.heap.length]? = some (type, store.length) := by
            rw [← heapRelated.length_eq, List.getElem?_concat_length]
          have environment' := ((environmentRelated.extendWorld [(type, store.length)]).addLocal
            argument.name type sourceState.heap.length store.length entry)
          have heap' := heapRelated.allocate head
          have external' := frame sourceState.external store .unit target externalRelated
          obtain ⟨extension, sourceEnvironment', sourceState', environment'', store', bound,
            allocated, locals, heap, external⟩ := ih arity'
              (sourceState := (Semantics.allocate sourceState source).2)
              (sourceEnvironment := (argument.name, sourceState.heap.length) :: sourceEnvironment)
              (scope := scope.addLocal argument.name type)
              (world := world ++ [(type, store.length)])
              (environment := .cellRef (Core.OptionalCell.cellType type) store.length :: environment)
              (store := store ++ [.inRight .unit target])
              (by simpa only [Core.Renaming.lift_id] using environment')
              (by simpa only [Semantics.allocate] using heap')
              (by simpa only [Semantics.allocate] using external')
          refine ⟨[(type, store.length)] ++ extension, sourceEnvironment', sourceState', environment'', store',
            ?_, .cons allocated, ?_, ?_, external⟩
          · exact bound
          · simpa only [List.append_assoc, parameterScope, List.zip_cons_cons, List.foldl_cons] using locals
          · simpa only [List.append_assoc] using heap

end Solcore.Frontend.RustHull.Correspondence
