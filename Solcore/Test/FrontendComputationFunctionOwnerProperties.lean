import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

/-! Original f,x parameters bind in written order before arbitrary repeated
typed/inferred x binders. Header, parameters, body meaning and actual paths are
constructed independently. Structural actual typing does not validate stores. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionOwner
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def fnType (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.function s ⟨s,[named s "A"]⟩ (some ⟨s,[named s "B"]⟩)⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b),(["A"],.bool)]
private def parameters (s : Syntax.SourceSpan) : List Syntax.FunctionParameter :=
  [⟨s,.typed none ⟨s,"f"⟩ (fnType s)⟩,⟨s,.typed none ⟨s,"x"⟩ (named s "A")⟩]
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.returnStmt (some (call s))⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s "A")) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s n
private def entry (s : Syntax.SourceSpan) (n : Nat) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"ownerCovariant"⟩,none,⟨s,parameters s⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s "B"]⟩⟩,none⟩,⟨s,statements s n⟩⟩⟩
private def scope (o : Resolved.DeclarationId) (a b : Core.Ty) : Nat → LocalTypeInputs
  | 0 => (LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "x" a
  | m+1 => (scope o a b m).bindFresh o "x" a
private def code : Nat → Nat → Core.Expr
  | 0,m => .apply (.var (m+1)) (.var 0)
  | n+1,m => .letE (.var 0) (.letE (.var 0) (code n (m+2)))
private theorem functionMeaning (s : Syntax.SourceSpan) (a b : Core.Ty) : StructuralTypeDenotes (types a b) (fnType s) (.function a b) :=
  .functionReturns (.named .head) (.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head)))
private theorem header (s : Syntax.SourceSpan) (a b : Core.Ty) (n : Nat) : RuntimeFunctionHeader (types a b) (entry s n).value.signature b :=
  ⟨rfl,rfl,rfl,rfl,.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head))⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) :
    RuntimeParametersDeclare (types a b) o (parameters s) (scope o a b 0) :=
  .cons (functionMeaning s a b) (by simp) (.cons (.named .head) (by simp [LocalTypeInputs.names,LocalTypeInputs.bindFresh,LocalTypeInputs.empty]) .nil)
private theorem functionFacts (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    LocalNameTable.Lookup (scope o a b m).names "f" ⟨o,0⟩ ∧
    Resolved.LocalScope.IndexOf (scope o a b m).context.ids ⟨o,0⟩ (m+1) ∧
    Resolved.LocalScope.Lookup (scope o a b m).context ⟨o,0⟩ (.function a b) := by
  induction m with
  | zero =>
      have different := Resolved.freshLocalId_cons_fresh_ne o []
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) .head,.tail different .head,.tail different .head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId o (scope o a b m).ids ≠ ⟨o,0⟩ := by
        intro same
        have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o a b m).names.map Prod.snd := List.mem_map.mpr ⟨("f",⟨o,0⟩),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) ih.1,.tail different ih.2.1,.tail different ih.2.2⟩
private theorem argumentElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    RecursiveLocalComputationElaborates (scope o a b m).names (scope o a b m).context (ref s "x") (.var 0) a := by
  cases m <;> exact .pure (.identifier .head) (.var .head) (.var .head)
private theorem bodyElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n m : Nat) :
    RecursiveComputationReturnTreeElaborates (types a b) o (scope o a b m) ⟨s,statements s n⟩ (code n m) b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (functionFacts o a b m).1) (.var (functionFacts o a b m).2.1) (.var (functionFacts o a b m).2.2))
      (argumentElab s o a b m))
  | succ n ih =>
      exact .binding (.named .head) (argumentElab s o a b m)
        (.inferred (argumentElab s o a b (m+1)) (ih (m+2)))
private structure Actual where
  argument : TypedRuntimeArgument
  resultType : Core.Ty
  body : Core.Expr
  captured : Core.Environment
  typed : Core.ValueHasType (.closure argument.type resultType body captured) (.function argument.type resultType)
private def Actual.fn (r : Actual) : TypedRuntimeArgument := ⟨.function r.argument.type r.resultType,.closure r.argument.type r.resultType r.body r.captured,r.typed⟩
private def Actual.inputs (r : Actual) (o : Resolved.DeclarationId) :=
  (LocalInputs.empty.bindFresh o "f" r.fn.type r.fn.value r.fn.valueTyped).bindFresh o "x" r.argument.type r.argument.value r.argument.valueTyped
private def compiled (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) : CompiledRuntimeFunction := ⟨scope o a b 0,code n 0,b⟩
private def prepared (o : Resolved.DeclarationId) (r : Actual) (n : Nat) : PreparedRuntimeFunction := ⟨r.inputs o,code n 0,r.resultType⟩
private theorem compilation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) :
    RecursiveComputationFunctionCompiles (types a b) o (entry s n) (compiled o a b n) :=
  ⟨header s a b n,declared s o a b,bodyElab s o a b n 0⟩
private theorem binding (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) :
    RuntimeParametersBind (types r.argument.type r.resultType) o (parameters s) [r.fn,r.argument] (r.inputs o) :=
  .cons (functionMeaning s _ _) (by simp) (.cons (.named .head) (by simp [LocalInputs.names,LocalInputs.bindFresh,LocalInputs.empty]) .nil)
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) :=
  ⟨header s _ _ n,binding s o r,bodyElab s o _ _ n 0⟩
private def environment (o : Resolved.DeclarationId) (r : Actual) : Nat → Resolved.Environment
  | 0 => (r.inputs o).environment
  | m+1 => (Resolved.freshLocalId o (scope o r.argument.type r.resultType m).ids,r.argument.value)::environment o r m
private theorem rawFunction (o : Resolved.DeclarationId) (r : Actual) (m : Nat) :
    Resolved.LocalScope.Lookup (environment o r m) ⟨o,0⟩ r.fn.value := by
  induction m with
  | zero => exact .tail (Resolved.freshLocalId_cons_fresh_ne o []) .head
  | succ m ih =>
      refine .tail ?_ ih
      intro same
      have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o r.argument.type r.resultType m).names.map Prod.snd :=
        List.mem_map.mpr ⟨("f",⟨o,0⟩),(functionFacts o r.argument.type r.resultType m).1.mem,rfl⟩
      rw [LocalTypeInputs.names_ids] at member
      exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
private theorem rawArgument (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (m : Nat) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (scope o r.argument.type r.resultType m).names (environment o r m) store
      (ref s "x") r.argument.value store 1 := by
  cases m <;> exact .pure (.identifier .head .head)
private theorem rawCost (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n m : Nat)
    (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (scope o r.argument.type r.resultType m).names (environment o r m)
      initial ⟨s,statements s n⟩ v final (6*n+cost+5) := by
  induction n generalizing m with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact .expression (.application (.pure (.identifier (functionFacts o r.argument.type r.resultType m).1 (rawFunction o r m))) (rawArgument s o r m initial) actual)
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      refine .binding (rawArgument s o r m initial) ?_
      change RecursiveComputationReturnTreeEvaluatesWithCost o
        (("x",Resolved.freshLocalId o ((scope o r.argument.type r.resultType m).names.map Prod.snd))::(scope o r.argument.type r.resultType m).names) _ _ _ _ _ _
      rw [LocalTypeInputs.names_ids]
      refine .inferred (rawArgument s o r (m+1) initial) ?_
      simpa only [scope,LocalTypeInputs.bindFresh_names,LocalTypeInputs.bindFresh_ids,List.map_cons,
        LocalTypeInputs.names_ids,environment] using ih (m+2)
private theorem manual (r : Actual) (n m : Nat) (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) (k : List Core.Frame) :
    Core.Steps (6*n+cost+5) ⟨.eval (code n m) (List.replicate (m+1) r.argument.value++[r.fn.value]),k,initial⟩ ⟨.ret v,k,final⟩ := by
  induction n generalizing m k with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact CostStepComposition.apply (parameterType := r.argument.type) (resultType := r.resultType)
        (.cons (.var (by simp [Actual.fn])) .refl) (.cons (.var (by simp)) .refl) actual
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      simpa [code,List.replicate_succ] using CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (m+2) k))
private theorem childMap (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    {table context source core type} :
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
      RecursiveLocalComputationElaborates table context source core type :=
  recursiveLocalComputationElaborates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective)
private theorem checkerMap (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (table context source) :
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source = elaborateRecursiveLocalComputation? table context source :=
  elaborateRecursiveLocalComputation?_mapIds _ (ownerLocalIdMap_injective mapping injective) table context source
private theorem preparedSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    prepareComputationFunction? elaborateRecursiveLocalComputation? (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument]=some (prepared o r n) :=
  (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (preparation s o r n)

theorem original_records_have_independent_header_parameters_and_body
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionCompiles (types r.argument.type r.resultType) o (entry s n)
      (compiled o r.argument.type r.resultType n) ∧
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) :=
  ⟨compilation s o _ _ n,preparation s o r n⟩
theorem original_argument_order_is_reversed_exactly_once_in_actual_rows
    (o : Resolved.DeclarationId) (r : Actual) :
    (r.inputs o).bindings.map (·.name)=["x","f"] ∧
    (r.inputs o).environment.values=[r.argument.value,r.fn.value] ∧
    (r.inputs o).ids=[Resolved.freshLocalId o [⟨o,0⟩],⟨o,0⟩] ∧
    (Resolved.freshLocalId o [⟨o,0⟩]).binderIndex=1 :=
  ⟨rfl,rfl,rfl,Resolved.freshLocalId_cons_fresh_binderIndex o []⟩
theorem both_independent_record_judgments_preserve_original_source_and_actuals
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionCompiles (types r.argument.type r.resultType) (mapping o) (entry s n)
      {(compiled o r.argument.type r.resultType n) with inputs := ((scope o r.argument.type r.resultType 0).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))} ∧
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) (mapping o) (entry s n) [r.fn,r.argument]
      {(prepared o r n) with inputs := (r.inputs o).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} :=
  ⟨(computationFunctionCompiles_mapOwner_iff mapping injective (childMap mapping injective)).mpr (compilation s o _ _ n),
   (computationFunctionPrepares_mapOwner_iff mapping injective (childMap mapping injective)).mpr (preparation s o r n)⟩
theorem whole_optional_records_preserve_original_body_and_return_annotation
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    compileRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n)=
      some {(compiled o r.argument.type r.resultType n) with inputs := ((scope o r.argument.type r.resultType 0).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))} ∧
    prepareRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n) [r.fn,r.argument]=
      some {(prepared o r n) with inputs := (r.inputs o).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} := by
  constructor
  · dsimp only [compileRecursiveComputationFunction?]
    rw [compileComputationFunction?_mapOwner mapping injective _ (checkerMap mapping injective),
      (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (compilation s o r.argument.type r.resultType n)]; rfl
  · dsimp only [prepareRecursiveComputationFunction?]
    rw [prepareComputationFunction?_mapOwner mapping injective _ (checkerMap mapping injective),preparedSome s o r n]; rfl
theorem original_raw_cost_and_separately_written_literal_core_path
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) (k : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (r.inputs o).names (r.inputs o).environment
      initial (entry s n).value.body v final (6*n+cost+5) ∧
    Core.Steps (6*n+cost+5) ⟨.eval (code n 0) [r.argument.value,r.fn.value],k,initial⟩ ⟨.ret v,k,final⟩ :=
  ⟨rawCost s o r n 0 initial final v cost actual,manual r n 0 initial final v cost actual k⟩
theorem full_runner_preserves_exact_faults_checkpoints_and_final_records
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n fuel : Nat) (store : Core.Store) :
    runRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n) [r.fn,r.argument] fuel store =
      some (r.resultType,Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] store)) := by
  dsimp only [runRecursiveComputationFunction?]
  rw [runComputationFunction?_mapOwner mapping injective _ (checkerMap mapping injective)]
  unfold runComputationFunction?
  rw [preparedSome s o r n]; rfl
theorem all_fuel_thresholds_and_genuine_resumption_keep_actual_body_effects
    (r : Actual) (n : Nat) (initial final : Core.Store) (v : Core.Value) (cost fuel extra : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) :
    (Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] initial)=.done v final ↔ 6*n+cost+5≤fuel) ∧
    ((∃ cp,Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] initial)=.outOfFuel cp) ↔ fuel<6*n+cost+5) ∧
    ∀ cp,Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] initial)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (code n 0) [r.argument.value,r.fn.value] initial) :=
  ⟨(manual r n 0 initial final v cost actual []).runStateful_done_iff,
   (manual r n 0 initial final v cost actual []).runStateful_outOfFuel_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem first_initializer_finishes_in_the_old_actual_environment
    (r : Actual) (n : Nat) (store : Core.Store) (k : List Core.Frame) :
    let cp : Core.State := ⟨.ret r.argument.value,.letBody (.letE (.var 0) (code n 2)) [r.argument.value,r.fn.value]::k,store⟩
    Core.runStateful 2 ⟨.eval (code (n+1) 0) [r.argument.value,r.fn.value],k,store⟩=.outOfFuel cp ∧
    ∀ extra,Core.runStateful extra cp=Core.runStateful (2+extra) ⟨.eval (code (n+1) 0) [r.argument.value,r.fn.value],k,store⟩ := by
  have stopped : Core.runStateful 2 ⟨.eval (code (n+1) 0) [r.argument.value,r.fn.value],k,store⟩=.outOfFuel _ := rfl
  exact ⟨stopped,Core.runStateful_resume stopped⟩
private def delayed (a : Core.Ty) : Nat → Core.Expr
  | 0 => .newCell a (.var 0)
  | m+1 => .letE (.var 0) (delayed a m)
private theorem delayedTyped (a : Core.Ty) (payload : Core.CellPayload a) (m : Nat) (context : Core.Context) :
    Core.HasType (a::context) (delayed a m) (.cell a) := by
  induction m generalizing context with
  | zero => exact .newCell (.var rfl) payload
  | succ m ih => exact .letE (.var rfl) (ih (a::context))
private theorem delayedPath (a : Core.Ty) (m : Nat) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*m+3) ⟨.eval (delayed a m) (v::captured),k,store⟩ ⟨.ret (.cellRef a store.length),k,store++[v]⟩ := by
  induction m generalizing captured k with
  | zero => exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  | succ m ih =>
      have count : 3*(m+1)+3=1+(3*m+3)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::captured) k)
private def allocator (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (m : Nat) : Actual :=
  ⟨arg,.cell arg.type,delayed arg.type m,captured,.closure typed (delayedTyped arg.type payload m context)⟩
theorem actual_allocation_and_every_retained_capture_survive_owner_change
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (n m : Nat) (store : Core.Store) :
    let r := allocator arg payload captured context typed m
    runRecursiveComputationFunction? (types arg.type (.cell arg.type)) (mapping o) (entry s n) [r.fn,arg] (6*n+3*m+8) store=
      some (.cell arg.type,.done (.cellRef arg.type store.length) (store++[arg.value])) := by
  let r := allocator arg payload captured context typed m
  change runRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n)
    [r.fn,r.argument] (6*n+3*m+8) store=some (r.resultType,.done (.cellRef arg.type store.length) (store++[arg.value]))
  rw [full_runner_preserves_exact_faults_checkpoints_and_final_records mapping injective s o r n]
  congr 1
  congr 1
  exact (manual r n 0 store (store++[arg.value]) (.cellRef arg.type store.length) (3*m+3)
    (delayedPath arg.type m arg.value captured store []) []).runStateful_done_iff.mpr (by omega)
theorem a_fixed_original_declaration_has_no_source_only_actual_cost_bound
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (store : Core.Store) (bound : Nat) :
    ∃ m, bound<3*m+8 ∧
      let r := allocator arg payload captured context typed m
      RecursiveComputationReturnTreeEvaluatesWithCost o (r.inputs o).names (r.inputs o).environment
        store (entry s 0).value.body (.cellRef arg.type store.length) (store++[arg.value]) (3*m+8) := by
  refine ⟨bound,by omega,?_⟩
  simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_assoc,Nat.reduceAdd] using (original_raw_cost_and_separately_written_literal_core_path s o
    (allocator arg payload captured context typed bound) 0 store (store++[arg.value]) (.cellRef arg.type store.length) (3*bound+3)
    (delayedPath arg.type bound arg.value captured store []) []).1
end Tests.FrontendComputationFunctionOwner
