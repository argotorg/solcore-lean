import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.LocalExpressionStoreProperties
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Frontend.RuntimeParameters

/-! Flat original lists of n+2 references, not generated nested source syntax.
Independent relations and manual Core paths fix products and costs before checking. -/
set_option autoImplicit false
namespace Tests.FrontendManyExpression
open Solcore Solcore.Frontend
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def tuple (s t : Syntax.SourceSpan) (children : List Syntax.Expr) : Syntax.Expr := ⟨s,.tuple ⟨t,children⟩⟩
private def source (s t : Syntax.SourceSpan) (name : String) (n : Nat) := tuple s t (List.replicate (n+2) (ref s name))
private def resolved (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .pair (.var id) (.var id)
  | n+1 => .pair (.var id) (resolved id n)
private def core : Nat → Core.Expr
  | 0 => .pair (.var 0) (.var 0)
  | n+1 => .pair (.var 0) (core n)
private def product (type : Core.Ty) : Nat → Core.Ty
  | 0 => .product type type
  | n+1 => .product type (product type n)
private def value (actual : Core.Value) : Nat → Core.Value
  | 0 => .pair actual actual
  | n+1 => .pair actual (value actual n)
private theorem static (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId)
    (table : LocalNameTable) (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    ResolvesLocalExpression ((name,id)::table) (source s t name n) (resolved id n) ∧
    LocalExpressionHasType ((name,id)::table) ((id,type)::context) (source s t name n) (product type n) ∧
    Resolved.Lowers (id::context.ids) (resolved id n) (core n) ∧
    Resolved.HasType ((id,type)::context) (resolved id n) (product type n) := by
  induction n with
  | zero => exact ⟨.pair (.identifier .head) (.identifier .head),
      .pair (.identifier .head .head) (.identifier .head .head), .pair (.var .head) (.var .head), .pair (.var .head) (.var .head)⟩
  | succ n ih => exact ⟨.many (.identifier .head) ih.1, .many (.identifier .head .head) ih.2.1,
      .pair (.var .head) ih.2.2.1, .pair (.var .head) ih.2.2.2⟩
private theorem checked (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId)
    (table : LocalNameTable) (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    elaborateLocalExpression? ((name,id)::table) ((id,type)::context) (source s t name n) = some (core n,product type n) :=
  let evidence := static s t name id table context type n
  elaborateLocalExpression?_complete evidence.1 evidence.2.2.1 evidence.2.2.2
private theorem costed (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId)
    (table : LocalNameTable) (env : Resolved.Environment) (actual : Core.Value) (store : Core.Store) (n : Nat) :
    LocalExpressionEvaluatesWithCost ((name,id)::table) ((id,actual)::env) store
      (source s t name n) (value actual n) store (4*n+5) := by
  induction n with
  | zero =>
      apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1) <;> exact .identifier .head .head
  | succ n ih =>
      have count : 4*(n+1)+5 = 1+(4*n+5)+3 := by omega
      rw [count]; exact .many (.identifier .head .head) ih
private theorem bound (s t : Syntax.SourceSpan) (name : String) (n : Nat) :
    localExpressionFuelBound (source s t name n) = 4*n+5 := by
  induction n with
  | zero => simp [source,tuple,ref,localExpressionFuelBound]
  | succ n ih =>
      change localExpressionFuelBound (tuple s t (ref s name :: ref s name :: ref s name :: List.replicate n (ref s name))) = _
      rw [tuple,localExpressionFuelBound]
      rw [show localExpressionFuelBound (ref s name) = 1 from by simp only [ref,localExpressionFuelBound]]
      change 1 + localExpressionFuelBound (source s t name n) + 3 = _
      rw [ih]; omega
private theorem path (actual : Core.Value) (env : Core.Environment) (store : Core.Store) (n : Nat) :
    ∀ k, Core.Steps (4*n+5) ⟨.eval (core n) (actual::env),k,store⟩ ⟨.ret (value actual n),k,store⟩ := by
  induction n with
  | zero => intro k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))
  | succ n ih =>
      intro k
      have steps := Core.Steps.cons .enterPair (.cons (.var (index := 0) rfl) (.cons .enterPairRight
        ((ih (.pairApply actual::k)).trans (.cons .applyPair .refl))))
      simpa [core,value,Nat.mul_add,Nat.add_assoc] using steps

theorem old_empty_and_binary_shapes_keep_their_distinct_costs
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (actual : Core.Value)
    (table : LocalNameTable) (context : Resolved.Context) (env : Resolved.Environment) (store : Core.Store) :
    elaborateLocalExpression? table context (tuple s t []) = some (.unit,.unit) ∧
    evaluateLocalExpressionWithCost? table env (tuple s t []) = some (.unit,1) ∧
    evaluateLocalExpressionWithCost? ((name,id)::table) ((id,actual)::env) (source s t name 0) = some (.pair actual actual,5) :=
  ⟨elaborateLocalExpression?_complete .unit .unit .unit,evaluateLocalExpressionWithCost?_complete (LocalExpressionEvaluatesWithCost.unit (store := store)),
    evaluateLocalExpressionWithCost?_complete (costed s t name id table env actual store 0)⟩

theorem arbitrary_n_plus_two_original_elements_have_independent_static_provenance
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (table : LocalNameTable)
    (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    source s t name n = tuple s t (List.replicate (n+2) (ref s name)) ∧
    ResolvesLocalExpression ((name,id)::table) (source s t name n) (resolved id n) ∧
    LocalExpressionHasType ((name,id)::table) ((id,type)::context) (source s t name n) (product type n) ∧
    elaborateLocalExpression? ((name,id)::table) ((id,type)::context) (source s t name n) = some (core n,product type n) ∧
    localExpressionFuelBound (source s t name n) = 4*n+5 :=
  ⟨rfl,(static s t name id table context type n).1,(static s t name id table context type n).2.1,
    checked s t name id table context type n,bound s t name n⟩

theorem actual_values_and_both_store_endpoints_keep_the_independently_counted_cost
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (table : LocalNameTable)
    (env : Resolved.Environment) (actual : Core.Value) (initial final replacement : Core.Store) (n : Nat) :
    evaluateLocalExpressionWithCost? ((name,id)::table) ((id,actual)::env) (source s t name n) = some (value actual n,4*n+5) ∧
    LocalExpressionEvaluatesWithCost ((name,id)::table) ((id,actual)::env) replacement (source s t name n) (value actual n) replacement (4*n+5) ∧
    (LocalExpressionEvaluatesWithCost ((name,id)::table) ((id,actual)::env) initial (source s t name n) (value actual n) final (4*n+5) ↔ final = initial) := by
  have raw := costed s t name id table env actual initial n
  have direct := evaluateLocalExpressionWithCost?_complete raw
  refine ⟨direct,raw.change_store replacement,?_⟩
  rw [localExpressionEvaluatesWithCost_iff_evaluate,direct]; simp

theorem original_scopes_and_manual_paths_determine_all_closed_fuel_thresholds
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (actual : Core.Value)
    (store : Core.Store) (n fuel : Nat) (k : List Core.Frame) :
    Core.Steps (4*n+5) ⟨.eval (core n) [actual],k,store⟩ ⟨.ret (value actual n),k,store⟩ ∧
    (Core.runStateful fuel (.initial (core n) [actual] store) = .done (value actual n) store ↔ 4*n+5 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (.initial (core n) [actual] store) = .outOfFuel checkpoint) ↔ fuel < 4*n+5) := by
  have raw := costed s t name id [] [] actual store n
  have direct := evaluateLocalExpressionWithCost?_complete raw
  have accepted := checked s t name id [] [] .word n
  have _ := raw.cost_le_fuelBound
  have _ := raw.checked_toSteps accepted rfl
  exact ⟨path actual [] store n k,
    evaluateLocalExpressionWithCost?_checked_runStateful_done_iff direct accepted rfl,
    evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff direct accepted rfl⟩

theorem arbitrary_data_environments_do_not_require_a_nominal_actual
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (nominal : Core.DataTypeId)
    (definitions : Core.DataEnvironment) (n : Nat) :
    elaborateLocalExpression? [(name,id)] [(id,.namedData nominal)] (source s t name n) = some (core n,product (.namedData nominal) n) ∧
    Core.HasType [.namedData nominal] (core n) (product (.namedData nominal) n) definitions ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) := by
  refine ⟨checked s t name id [] [] _ n,?_,?_⟩
  · induction n with
    | zero => exact .pair (.var rfl) (.var rfl)
    | succ n ih => exact .pair (.var rfl) ih
  · rintro ⟨actual,typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?,Core.DataEnvironment.lookupDataType?] at found

private def inputs (name : String) (id : Resolved.LocalId) (actual : TypedRuntimeArgument) : LocalInputs :=
  ⟨[⟨name,id,actual.type,actual.value,actual.valueTyped⟩],by simp⟩
theorem typed_actuals_keep_owner_covariance_and_unused_input_observations
    (s t : Syntax.SourceSpan) (name extra : String) (different : extra ≠ name) (id : Resolved.LocalId)
    (actual : TypedRuntimeArgument) (owner : Resolved.DeclarationId) (store : Core.Store) (n fuel : Nat)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    let original := inputs name id actual
    original.run? (4*n+5) (source s t name n) store = some (product actual.type n,.done (value actual.value n) store) ∧
    (original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).run? fuel (source s t name n) store = original.run? fuel (source s t name n) store ∧
    ((original.bindFresh owner extra .unit .unit .unit).run? fuel (source s t name n) store = some (product actual.type n,.done (value actual.value n) store) ↔
      original.run? fuel (source s t name n) store = some (product actual.type n,.done (value actual.value n) store)) := by
  dsimp
  have avoids : AvoidsLocalName extra (source s t name n) := by
    induction n with
    | zero => exact .pair (.identifier different) (.identifier different)
    | succ n ih => exact .many (.identifier different) ih
  exact ⟨LocalInputs.run?_done_iff_evaluator.mpr ⟨(static s t name id [] [] actual.type n).2.1,rfl,4*n+5,
    evaluateLocalExpressionWithCost?_complete (costed s t name id [] [] actual.value store n),Nat.le_refl _⟩,
    LocalInputs.run?_mapIds _ _ _ _ _ _,avoids.bindFresh_run_done_at_fuel_iff _ owner .unit .unit .unit⟩

theorem duplicate_rows_and_equal_optional_lookups_preserve_raw_many_results
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (actual hidden : Core.Value) (n : Nat)
    (rightTable : LocalNameTable) (rightEnv : Resolved.Environment)
    (same : ∀ key, (LocalNameTable.lookup? [(name,id),(name,id)] key).bind
      (Resolved.LocalScope.lookup? [(id,actual),(id,hidden)]) = (rightTable.lookup? key).bind rightEnv.lookup?) :
    evaluateLocalExpressionWithCost? rightTable rightEnv (source s t name n) = some (value actual n,4*n+5) :=
  (evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ same _).symm.trans
    (evaluateLocalExpressionWithCost?_complete (costed s t name id [(name,id)] [(id,hidden)] actual [] n))

private def s : Syntax.SourceSpan := ⟨⟨.main,"many.sol"⟩,237,2⟩
private def t : Syntax.SourceSpan := ⟨⟨.main,"different.sol"⟩,91,3⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Many",by decide⟩],by decide⟩⟩,7⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def atom := ref s
private def table : LocalNameTable := [("x",id 0),("y",id 1),("z",id 2),("c",id 3)]
private def env (x y z : Core.Value) (flag : Bool) : Resolved.Environment := [(id 0,x),(id 1,y),(id 2,z),(id 3,.bool flag)]
private def three := tuple s t [atom "x",atom "y",atom "z"]
private def threeCore : Core.Expr := .pair (.var 0) (.pair (.var 1) (.var 2))
private def context (type : Core.Ty) : Resolved.Context := [(id 0,type),(id 1,type),(id 2,type),(id 3,.bool)]
private theorem threeCost (x y z : Core.Value) (flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env x y z flag) store three (.pair x (.pair y z)) store 9 := by
  apply LocalExpressionEvaluatesWithCost.many (headCost := 1) (tailCost := 5)
  · exact .identifier .head .head
  · apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
    · exact .identifier (.tail (by decide) .head) (.tail (by decide) .head)
    · exact .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem threeChecked (type : Core.Ty) :
    elaborateLocalExpression? table (context type) three = some (threeCore,.product type (.product type type)) :=
  elaborateLocalExpression?_complete (.many (.identifier .head) (.pair
    (.identifier (.tail (by decide) .head)) (.identifier (.tail (by decide) (.tail (by decide) .head)))))
    (.pair (.var .head) (.pair (.var (.tail (by change id 0 ≠ id 1; decide) .head))
      (.var (.tail (by change id 0 ≠ id 2; decide) (.tail (by change id 1 ≠ id 2; decide) .head)))))
    (.pair (.var .head) (.pair (.var (.tail (by change id 0 ≠ id 1; decide) .head))
      (.var (.tail (by change id 0 ≠ id 2; decide) (.tail (by change id 1 ≠ id 2; decide) .head)))))

theorem original_order_and_explicit_association_are_not_coerced (x y z : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env x y z true) three = some (.pair x (.pair y z),9) ∧
    evaluateLocalExpressionWithCost? table (env x y z true) (tuple s t [tuple s t [atom "x",atom "y"],atom "z"]) = some (.pair (.pair x y) z,9) ∧
    Core.HasType [.word,.word,.word,.bool] (.pair (.var 2) (.pair (.var 1) (.var 0))) (.product .word (.product .word .word)) ∧
    elaborateLocalExpression? table (context .word) three ≠ some (.pair (.var 2) (.pair (.var 1) (.var 0)),.product .word (.product .word .word)) := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (threeCost x y z true store),?_,.pair (.var rfl) (.pair (.var rfl) (.var rfl)),?_⟩
  · apply evaluateLocalExpressionWithCost?_complete (initialStore := store) (finalStore := store)
    apply LocalExpressionEvaluatesWithCost.pair (leftCost := 5) (rightCost := 1)
    · apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
      · exact .identifier .head .head
      · exact .identifier (.tail (by decide) .head) (.tail (by decide) .head)
    · exact .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  · rw [threeChecked]; intro wrong; cases wrong

private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨s,.binary left ⟨t,op⟩ right⟩
private def choose (yes no : Syntax.Expr) : Syntax.Expr := ⟨s,.conditional (atom "c") s yes t no⟩
private theorem guard (x y z : Core.Value) (flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env x y z flag) store (atom "c") (.bool flag) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
theorem selected_raw_many_values_do_not_weaken_whole_boolean_or_branch_checks
    (x y z : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env x y z true) (binary .logicalAnd (atom "c") three) = some (.pair x (.pair y z),12) ∧
    evaluateLocalExpressionWithCost? table (env x y z false) (binary .logicalOr (atom "c") three) = some (.pair x (.pair y z),12) ∧
    elaborateLocalExpression? table (context .word) (binary .logicalAnd (atom "c") three) = none ∧
    evaluateLocalExpressionWithCost? table (env x y z true) (choose three (atom "missing")) = some (.pair x (.pair y z),12) ∧
    resolveLocalExpression? table (choose three (atom "missing")) = none := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (.andTrue (guard x y z true store) (threeCost x y z true store)),
    evaluateLocalExpressionWithCost?_complete (.orFalse (guard x y z false store) (threeCost x y z false store)),?_,
    evaluateLocalExpressionWithCost?_complete (.ifTrue (guard x y z true store) (threeCost x y z true store)),?_⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type,typing⟩
    cases typing with
    | logicalAnd _ rightTyped => cases rightTyped
  · simp [resolveLocalExpression?,choose,three,tuple,atom,ref,table,LocalNameTable.lookup?]

theorem missing_tail_elements_are_strict_even_when_the_head_has_a_value (x y z : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env x y z true) (tuple s t [atom "x",atom "y",atom "missing"]) = none ∧
    ¬ ∃ result cost, LocalExpressionEvaluatesWithCost table (env x y z true) store
      (tuple s t [atom "x",atom "missing",atom "z"]) result store cost := by
  constructor
  · simp [evaluateLocalExpressionWithCost?,tuple,atom,ref,table,env,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]
  · apply (evaluateLocalExpressionWithCost?_eq_none_iff store).mp
    simp [evaluateLocalExpressionWithCost?,tuple,atom,ref,table,env,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]

theorem two_pending_pairs_are_genuine_checkpoints_with_exact_residuals
    (x y z : Core.Value) (store : Core.Store) (additional : Nat) :
    Core.runStateful 7 (.initial threeCore [x,y,z,.bool true] store) = .outOfFuel ⟨.ret z,[.pairApply y,.pairApply x],store⟩ ∧
    Core.Steps 2 ⟨.ret z,[.pairApply y,.pairApply x],store⟩ (.final (.pair x (.pair y z)) store) ∧
    Core.runStateful additional ⟨.ret z,[.pairApply y,.pairApply x],store⟩ = Core.runStateful (7+additional) (.initial threeCore [x,y,z,.bool true] store) ∧
    Core.runStateful 0 ⟨.ret z,[],store⟩ = .done z store ∧
    Core.runStateful 0 ⟨.ret z,[.pairApply y,.pairApply x],store⟩ = .outOfFuel ⟨.ret z,[.pairApply y,.pairApply x],store⟩ := by
  have exhausted : Core.runStateful 7 (.initial threeCore [x,y,z,.bool true] store) = .outOfFuel ⟨.ret z,[.pairApply y,.pairApply x],store⟩ := rfl
  exact ⟨exhausted,((threeCost x y z true store).checked_residual_of_outOfFuel (threeChecked .word) rfl exhausted).2,
    Core.runStateful_resume exhausted additional,rfl,rfl⟩

theorem typed_opaque_components_and_grouping_keep_products_without_new_store_claims
    (location : Core.Location) (captured : Core.Word) (store : Core.Store) :
    let actual : TypedRuntimeArgument := ⟨.product (.cell .word) (.function .word .word),
      .pair (.cellRef .word location) (.closure .word .word (.var 1) [.word captured]),.pair .cellRef (.closure (.cons .word .nil) (.var rfl))⟩
    (inputs "x" (id 0) actual).run? 9 (source s t "x" 1) store = some (product actual.type 1,.done (value actual.value 1) store) ∧
    evaluateLocalExpressionWithCost? [("x",id 0)] [(id 0,actual.value)] ⟨t,.group (source s t "x" 1)⟩ = some (value actual.value 1,9) := by
  dsimp
  exact ⟨LocalInputs.run?_done_iff_evaluator.mpr ⟨(static s t "x" (id 0) [] [] _ 1).2.1,rfl,9,
    evaluateLocalExpressionWithCost?_complete (costed s t "x" (id 0) [] [] _ store 1),by decide⟩,
    evaluateLocalExpressionWithCost?_complete (.group (costed s t "x" (id 0) [] [] _ store 1))⟩
end Tests.FrontendManyExpression
