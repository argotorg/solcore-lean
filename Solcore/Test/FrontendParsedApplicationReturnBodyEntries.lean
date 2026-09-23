import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.RuntimeParameterDeclarations

/-! Original parameter-only records feed the separate return-call profile.
Independent children, actual body paths and costs precede all executable checks. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ApplicationReturnBodyEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def parsed : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "application-return-entry.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside annotation fixture")
private structure Parameters (types : TypeNameTable) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner .empty params statics
  bound : RuntimeParametersBindFrom types owner .empty params args actual
private def parameters (types : TypeNameTable) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Parameters types params args) := do
  match original : params, supplied : args with
  | [⟨s, .typed none f ft⟩, ⟨t, .typed none x xt⟩], [fv, xv] =>
      check (s.contains f.span && s.contains ft.span && t.contains x.span && t.contains xt.span &&
        decide (s.endByte ≤ t.startByte)) "original parameter spans/order changed"
      let fm ← meaning types ft; let xm ← meaning types xt
      if sameF : fm.type = fv.type then
        if sameX : xm.type = xv.type then
          if unused : x.value ∉ [f.value] then
            return ⟨(LocalTypeInputs.empty.bindFresh owner f.value fv.type).bindFresh owner x.value xv.type,
              (LocalInputs.empty.bindFresh owner f.value fv.type fv.value fv.valueTyped).bindFresh owner x.value xv.type xv.value xv.valueTyped,
              by
                rw [original]
                exact .cons (sameF ▸ fm.evidence) (by simp [LocalTypeInputs.empty_names])
                  (.cons (sameX ▸ xm.evidence) unused .nil),
              by
                rw [original, supplied]
                exact .cons (sameF ▸ fm.evidence) (by simp [LocalInputs.empty_names])
                  (.cons (sameX ▸ xm.evidence) unused .nil)⟩
          else throw (IO.userError "duplicate parameter")
        else throw (IO.userError "argument type differs")
      else throw (IO.userError "function type differs")
  | _, _ => throw (IO.userError "original parameter shape or actual arity changed")
private structure Reference (inputs : LocalInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression inputs.names source resolved
  lowered : Resolved.Lowers inputs.context.ids resolved core
  typing : Resolved.HasType inputs.context resolved type
private def reference (inputs : LocalInputs) (source : Syntax.Expr) : IO (Reference inputs source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Original (body : Syntax.Block) where
  blockSpan : Syntax.SourceSpan
  returnSpan : Syntax.SourceSpan
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : body = ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩)⟩]⟩
private def original (body : Syntax.Block) : IO (Original body) := do
  match shape : body with
  | ⟨bs, [⟨rs, .returnStmt (some ⟨s, .call f ⟨args, [x]⟩⟩)⟩]⟩ =>
      check (bs.contains rs && rs.contains s && s.contains f.span && s.contains args && args.contains x.span &&
        decide (f.span.endByte ≤ args.startByte)) "original return/call spans changed"
      return ⟨bs, rs, s, args, f, x, shape⟩
  | _ => throw (IO.userError "not original singleton return-call")
private structure Observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : Type where
  evidence : ∀ store, LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1
private def observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : IO (Observed inputs source value) := do
  match shape : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "actual row changed")
      | none => throw (IO.userError "actual name missing")
  | _ => throw (IO.userError "raw child changed")
private def delayed : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .letE (.var 0) (delayed n)
private theorem delayedTyped (n : Nat) (type : Core.Ty) (rest : Core.Context) :
    Core.HasType (type :: rest) (delayed n) type := by
  induction n generalizing rest with
  | zero => exact .var rfl
  | succ n ih => exact .letE (.var rfl) (ih _)
private theorem delayedPath (n : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (delayed n) (value :: rest), k, s⟩ ⟨.ret value, k, s⟩ := by
  induction n generalizing rest k with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have path := Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet (ih (value :: rest) k)))
      have count : 3 * (n + 1) + 1 = 3 * n + 1 + 1 + 1 + 1 := by omega
      rw [count]; exact path
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (world : Core.StoreTyping) (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (argumentTyped : Core.RuntimeValueHasType world argument.value argument.type)
    (closureTyped : Core.RuntimeValueHasType world (.closure argument.type output body captured) (.function argument.type output))
    (storeTyped : Core.StoreHasTypes world s)
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret value, k, t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped.erase⟩
  let args := [f, argument]; let types := [(["F"], f.type), (["A"], argument.type), (["R"], output)]
  let source ← parsed
  let ps ← parameters types source.value.signature.parameters.elements args
  let inputs := ps.actual
  have _ := RuntimeParametersDeclare.complete ps.declared
  have _ := RuntimeParametersBind.complete ps.bound
  have _ := RuntimeParametersBind.erase_values ps.bound
  check (decide (inputs.names = ps.statics.names ∧ inputs.context = ps.statics.context ∧
    inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
      [("x", ⟨owner, 1⟩, argument.type, argument.value), ("f", ⟨owner, 0⟩, f.type, f.value)])) "original records changed"
  let rows : PLift (inputs.environment.values = (args.map (·.value)).reverse ∧ inputs.context.values = [argument.type, f.type]) ←
    if same : inputs.environment.values = (args.map (·.value)).reverse ∧ inputs.context.values = [argument.type, f.type] then pure ⟨same⟩
    else throw (IO.userError "original projection order changed")
  have runtimeTyped : Core.RuntimeEnvironmentHasTypes world inputs.environment.values inputs.context.values := by
    rw [rows.down.1, rows.down.2]; exact .cons argumentTyped (.cons closureTyped .nil)
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have _ : RuntimeFunctionHeader types source.value.signature output := ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [clause]; exact .single (same ▸ m.evidence)⟩
          pure ()
        else throw (IO.userError "header policy changed")
      else throw (IO.userError "declared result changed")
  | _ => throw (IO.userError "original return annotation changed")
  let o ← original source.value.body
  let expression : Syntax.Expr := ⟨o.span, .call o.callee ⟨o.argumentsSpan, [o.argument]⟩⟩
  let fn ← reference inputs o.callee; let arg ← reference inputs o.argument
  if exactChildren : fn.type = f.type ∧ arg.type = argument.type ∧ fn.core = .var 1 ∧ arg.core = .var 0 then
    have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
      have e := LocalFunctionApplicationElaborates.call (span := o.span) (argumentsSpan := o.argumentsSpan)
        fn.resolution fn.lowered (exactChildren.1 ▸ fn.typing) arg.resolution arg.lowered (exactChildren.2.1 ▸ arg.typing)
      simpa only [target, expression, exactChildren.2.2.1, exactChildren.2.2.2] using e
    have elaboration : LocalApplicationReturnBodyElaborates inputs.names inputs.context source.value.body target output := by
      rw [o.shape]; exact .application child
    have typing : LocalApplicationReturnBodyHasType inputs.names inputs.context source.value.body output := by
      rw [o.shape]; exact .application child.hasType
    let fp ← observed inputs o.callee f.value; let ap ← observed inputs o.argument argument.value
    have costed : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost + 5) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        LocalFunctionApplicationEvaluatesWithCost.call (span := o.span) (argumentsSpan := o.argumentsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
    have rawBody : LocalApplicationReturnBodyEvaluates inputs.names inputs.environment s source.value.body value t := by
      rw [o.shape]; exact .application costed.erase
    have bodyCosted : LocalApplicationReturnBodyEvaluatesWithCost inputs.names inputs.environment s source.value.body value t (bodyCost + 5) := by
      rw [o.shape]; exact .application costed
    have manual (k) : Core.Steps (bodyCost + 5) ⟨.eval target inputs.environment.values, k, s⟩ ⟨.ret value, k, t⟩ := by
      rw [rows.down.1]
      exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
    have accepted := elaboration.complete
    have _ := elaborateLocalApplicationReturnBody?_sound accepted
    have _ := elaborateLocalApplicationReturnBody?_iff.mp accepted
    have _ := typing.type_unique elaboration.hasType
    have _ := elaboration.result_unique (elaborateLocalApplicationReturnBody?_iff.mpr elaboration |> elaborateLocalApplicationReturnBody?_sound)
    have _ := typing.elaborates_exact
    have _ := localApplicationReturnBodyHasType_iff_elaborates.mpr ⟨target, elaboration⟩
    have _ := elaboration.core_hasType
    have _ := elaborateLocalApplicationReturnBody?_core_hasType accepted
    have _ := elaborateLocalApplicationReturnBody?_eq_none_iff (table := inputs.names) (context := inputs.context) (body := source.value.body)
    have _ := rawBody.deterministic bodyCosted.erase
    have _ := rawBody.exists_cost
    have _ := localApplicationReturnBodyEvaluates_iff_exists_cost.mpr ⟨_, bodyCosted⟩
    have _ := bodyCosted.deterministic ((elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr (manual []))
    have _ := (elaboration.evaluates_iff inputs.sameIds).mpr (Core.steps_from_initial_sound (manual []))
    have _ := (elaboration.evaluates_iff inputs.sameIds).mp rawBody
    have _ := bodyCosted.toStepsWithContinuation elaboration inputs.sameIds [.letBody .unit []]
    have checked := LocalInputs.checkApplicationReturnBody?_iff_elaborates.mpr elaboration
    have checkEqual : inputs.checkApplicationReturnBody? source.value.body = inputs.checkApplication? expression := by
      rw [o.shape]; exact inputs.checkApplicationReturnBody?_return o.blockSpan o.returnSpan expression
    have equal (fuel store) : inputs.runApplicationReturnBody? fuel source.value.body store = inputs.runApplication? fuel expression store := by
      rw [o.shape]; exact inputs.runApplicationReturnBody?_return fuel o.blockSpan o.returnSpan expression store
    let cost := bodyCost + 5
    have done := (LocalInputs.runApplicationReturnBody?_done_iff_typed_cost).mpr ⟨typing, cost, bodyCosted, Nat.le_refl cost⟩
    have _ := LocalInputs.runApplicationReturnBody?_done_iff_typed_cost.mp done
    have _ := LocalInputs.runApplicationReturnBody?_eq_some_iff.mp done
    have childDone := (equal cost s) ▸ done
    have _ := LocalInputs.runApplication?_runtime_done_sound runtimeTyped storeTyped childDone
    have agreement : ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future t ∧
        Core.RuntimeValueHasType future value output := by
      obtain ⟨future, final, v, count, extension, st, vt, evaluated, _⟩ :=
        LocalInputs.runApplication?_runtime_has_exact_cost child.hasType runtimeTyped storeTyped
      obtain ⟨rfl, rfl, _⟩ := costed.deterministic evaluated
      exact ⟨future, extension, st, vt⟩
    have _ := agreement
    check (decide (inputs.checkApplicationReturnBody? source.value.body = some (target, output) ∧
      inputs.checkApplicationReturnBody? source.value.body = inputs.checkApplication? expression)) "static wrapper changed exact child"
    check (decide (inputs.runApplicationReturnBody? 3 source.value.body s = some (output, .outOfFuel
      ⟨.eval (.var 0) inputs.environment.values, [.applyClosure argument.type output body captured], s⟩))) "original child checkpoint changed"
    check (decide (Core.runStateful cost ⟨.eval target inputs.environment.values, [.letBody .unit []], s⟩ =
      .outOfFuel ⟨.ret value, [.letBody .unit []], t⟩)) "pending frame was treated as completed"
    for fuel in List.range (cost + 3) do
      have _ := LocalInputs.runApplicationReturnBody?_eq_none_iff (inputs := inputs) (body := source.value.body) fuel s
      have _ := (LocalInputs.runApplicationReturnBody?_eq_some_iff (fuel := fuel) (store := s)).mpr ⟨target, checked, rfl⟩
      have _ := LocalInputs.runApplication?_done_iff_of_cost child.hasType costed (fuel := fuel)
      have _ := LocalInputs.runApplication?_runtime_never_faults runtimeTyped storeTyped expression fuel output
      check ((compileRuntimeFunction? types owner source).isNone && (prepareRuntimeFunction? types owner source args).isNone &&
        (runRuntimeFunction? types owner source args fuel s).isNone && (inputs.run? fuel expression s).isNone) "return-call leaked into old endpoints"
      check (decide (inputs.runApplicationReturnBody? fuel source.value.body s = inputs.runApplication? fuel expression s ∧
        inputs.runApplicationReturnBody? fuel source.value.body s = some (output, Core.runStateful fuel (.initial target inputs.environment.values s)))) "full return/child result differs"
      match stopped : inputs.runApplicationReturnBody? fuel source.value.body s with
      | some (_, .done v final) => check (decide (cost ≤ fuel ∧ v = value ∧ final = t)) "independent cost/value/store differs"
      | some (_, .outOfFuel checkpoint) =>
          have childStopped := (equal fuel s) ▸ stopped
          have _ := LocalInputs.runApplication?_residual_of_outOfFuel costed childStopped
          check (decide (fuel < cost ∧ Core.runStateful (cost - fuel) checkpoint = .done value t)) "genuine remaining path differs"
          for additional in [0, 1, cost - fuel, cost + 2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (inputs.runApplicationReturnBody? (fuel + additional) source.value.body s =
              some (output, Core.runStateful additional checkpoint))) "genuine full-result resumption differs"
      | _ => throw (IO.userError "actual runtime typed body failed or faulted")
    for otherStore in [[], [.bool true]] do
      match stopped : inputs.runApplicationReturnBody? 3 source.value.body otherStore with
      | some (tag, .outOfFuel checkpoint) =>
          have childStopped := (equal 3 otherStore) ▸ stopped
          for additional in [0, 4, 5, cost + 2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (tag = output ∧ inputs.runApplicationReturnBody? (3 + additional) source.value.body otherStore =
              some (output, Core.runStateful additional checkpoint))) "unvalidated store full-result replay changed"
      | _ => throw (IO.userError "original call protocol lost its genuine checkpoint")
  else throw (IO.userError "independent original children changed")
end ApplicationReturnBodyEntries
open ApplicationReturnBodyEntries
def frontendParsedApplicationReturnBodyEntryTests : IO Unit := do
  for n in [0, 1, 4, 9] do
    execute ⟨.word, w 14, .word⟩ .word (delayed n) [] [] [] [] (w 14) (3 * n + 1)
      .word (.closure .nil (delayedTyped n .word [])) .nil (delayedPath n (w 14) [] [])
  for current in [3, 17] do
    have st : Core.StoreHasTypes [.word] [w current] := Core.StoreHasTypes.nil.allocate .word .word
    execute ⟨.unit, .unit, .unit⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [.word] [w current] [w current] (w current) 3
      .unit (.closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl) .word)) st
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute ⟨.word, w 9, .word⟩ (.cell .word) (.newCell .word (.var 0)) [] [.word] [w current] [w current, w 9] (.cellRef .word 1) 3
      .word (.closure .nil (.newCell (.var rfl) .word)) st (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
    execute ⟨.word, w 9, .word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
      [.word] [w current] [w 9] (w 9) 10 .word
      (.closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))) st
      (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let a : TypedRuntimeArgument := ⟨.function type type, .closure type type (.var 0) [], .closure .nil (.var rfl)⟩
    execute a a.type (.var 0) [] [] [] [] a.value 1
      (.closure .nil (.var rfl)) (.closure .nil (.var rfl)) .nil (fun _ => .cons (.var rfl) .refl)
end Tests
