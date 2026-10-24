import Solcore.Frontend.RustHull.FunctionInstallationCorrespondence

/-! Argument initialization under the actual renamings used when global
closures capture administrative binders from preceding registrations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

def parameterRenaming : Nat → Core.Renaming → Core.Renaming
  | 0, mapping => mapping
  | count + 1, mapping => parameterRenaming count mapping.lift

theorem projectArgument_rename (index count : Nat) (expression : Core.Expr) (mapping : Core.Renaming) :
    (projectArgument index count expression).rename mapping =
      projectArgument index count (expression.rename mapping) := by
  induction count generalizing index expression with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          by_cases first : index = 0 <;> simp [projectArgument, first, Core.Expr.rename, ih]

theorem ParameterCells.evaluates_renamed {types : List Core.Ty} {values allValues : List Core.Value}
    {environment finalEnvironment : Core.Environment} {initial allocated final : Core.Store}
    (cells : ParameterCells types values environment initial finalEnvironment allocated)
    {start : Nat} {mapping : Core.Renaming}
    (argument : environment[mapping start]? = some (bundleValues allValues))
    (selected : ∀ index value, values[index]? = some value → allValues[start + index]? = some value)
    {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates finalEnvironment allocated
      (body.rename (parameterRenaming types.length mapping)) result final) :
    Core.Evaluates environment initial
      ((parameterCode allValues.length start types body).rename mapping) result final := by
  induction cells generalizing start mapping with
  | nil => exact evaluated
  | @cons type types value values environment store finalEnvironment finalStore rest ih =>
      have initializer : Core.Evaluates environment store
          ((projectArgument start allValues.length (.var start)).rename mapping) value store := by
        rw [projectArgument_rename]
        exact projectArgument_evaluates (.var argument) (by simpa using selected 0 value rfl)
      simp only [parameterCode, List.zipIdx_cons, List.foldr_cons, Core.Expr.rename]
      apply Core.Evaluates.letE (.newCell (.inRight initializer))
      apply ih (start := start + 1) (mapping := mapping.lift)
      · exact argument
      · intro index selectedValue found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using selected (index + 1) selectedValue found
      · exact evaluated

/-- Source argument binding and real Core allocation agree under an arbitrary
renaming of the enclosing globals. Each parameter adds the same binder on
both sides and lifts that renaming once. -/
theorem initialize_parameters_renamed {σ : Type} {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel types sources targets) (arity : arguments.length = types.length)
    {sourceEnvironment : Semantics.Environment} {scope : Scope} {sourceState : Semantics.State σ}
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world sourceState.heap store)
    {external : σ → Core.Store → Prop} (externalRelated : external sourceState.external store)
    (frame : ∀ state store type value, external state store →
      external state (store ++ [Core.Value.inRight type value])) :
    ∃ extension sourceEnvironment' sourceState' environment' store',
      Semantics.bindArguments arguments sources sourceEnvironment sourceState = some (sourceEnvironment', sourceState') ∧
      ParameterCells types targets environment store environment' store' ∧
      EnvironmentRel (world ++ extension) sourceEnvironment' (parameterScope arguments types scope)
        (parameterRenaming types.length mapping) environment' ∧
      HeapRel (world ++ extension) sourceState'.heap store' ∧
      external sourceState'.external store' := by
  induction values generalizing arguments sourceEnvironment scope sourceState world mapping environment store with
  | nil =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      exact ⟨[], sourceEnvironment, sourceState, environment, store, rfl, .nil,
        by simpa [parameterScope, parameterRenaming] using environmentRelated,
        by simpa using heapRelated, externalRelated⟩
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
              (mapping := mapping.lift)
              (environment := .cellRef (Core.OptionalCell.cellType type) store.length :: environment)
              (store := store ++ [.inRight .unit target]) environment'
              (by simpa only [Semantics.allocate] using heap')
              (by simpa only [Semantics.allocate] using external')
          refine ⟨[(type, store.length)] ++ extension, sourceEnvironment', sourceState', environment'', store',
            ?_, .cons allocated, ?_, ?_, external⟩
          · exact bound
          · simpa only [List.append_assoc, parameterScope, List.zip_cons_cons, List.foldl_cons,
              List.length_cons, parameterRenaming] using locals
          · simpa only [List.append_assoc] using heap

end Solcore.Frontend.RustHull.Correspondence
