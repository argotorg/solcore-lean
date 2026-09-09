import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalApplicationReturnBodyRunnerProperties
import Solcore.Frontend.LocalFunctionApplicationExactInsertionProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RuntimeApplicationFunctionFactorizationProperties

/-! Original whole-entry records are retained; only the Core caller gains a slot.
Independent actual paths fix costs and effects before insertion is used. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedApplicationInsertionEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def parsed (text : String) : IO Syntax.FunctionDecl := do
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
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) :
    IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.evidence)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return type")
  | _ => throw (IO.userError "original return shape")
private def observe (start : Core.State) (value : Core.Value) (final : Core.Store) (cost : Nat)
    (path : Core.Steps cost start (.final value final)) : IO Unit := do
  for fuel in List.range (cost+3) do
    have _ := path.runStateful_done_iff (fuel := fuel)
    match exhausted : Core.runStateful fuel start with
    | .done actual store => check (decide (cost ≤ fuel ∧ actual = value ∧ store = final)) "exact completed result"
    | .outOfFuel cp =>
        have _ := path.residual_of_outOfFuel exhausted
        check (decide (fuel < cost ∧ Core.runStateful (cost-fuel) cp = .done value final)) "each side's genuine residual"
        for additional in [0,1,cost-fuel,cost+2] do
          have _ := Core.runStateful_resume exhausted additional
          have _ := path.resumed_done_iff (additional := additional) exhausted
          check (decide (Core.runStateful additional cp = Core.runStateful (fuel+additional) start)) "full-result own-state resumption"
        if 1 < cost-fuel then
          match next : Core.runStateful 1 cp with
          | .outOfFuel nextCp =>
              have _ := Core.runStateful_resume next (cost-fuel-1)
              check (decide (Core.runStateful (cost-fuel-1) nextCp = .done value final)) "three real chunks"
          | _ => throw (IO.userError "intermediate checkpoint missing")
    | .fault _ _ => throw (IO.userError "manual successful path faulted")
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured),k,s⟩ ⟨.ret value,k,t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output,.closure argument.type output body captured,closureTyped⟩
  let args := [f,argument]; let types := [(["F"],f.type),(["A"],argument.type),(["R"],output)]
  let source ← parsed text; let ps ← parameters types source.value.signature.parameters.elements args
  let inputs := ps.actual; let h ← header types source output; let o ← original source.value.body
  let expression : Syntax.Expr := ⟨o.span,.call o.callee ⟨o.argumentsSpan,[o.argument]⟩⟩
  let fn ← reference inputs o.callee; let arg ← reference inputs o.argument
  if children : fn.type = f.type ∧ arg.type = argument.type ∧ fn.core = .var 1 ∧ arg.core = .var 0 then
    have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
      have e := LocalFunctionApplicationElaborates.call (span := o.span) (argumentsSpan := o.argumentsSpan)
        fn.resolution fn.lowered (children.1 ▸ fn.typing) arg.resolution arg.lowered (children.2.1 ▸ arg.typing)
      simpa only [target,expression,children.2.2.1,children.2.2.2] using e
    have whole : LocalApplicationReturnBodyElaborates inputs.names inputs.context source.value.body target output := by
      rw [o.shape]; exact .application child
    let prepared : PreparedRuntimeFunction := ⟨inputs,target,output⟩
    have preparation : RuntimeApplicationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,whole⟩
    have erased := preparation.compiles.parameters.result_unique ps.declared
    have _ := preparation.compiles.complete
    have _ := preparation.complete
    check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
      [("x",⟨owner,1⟩,argument.type,argument.value),("f",⟨owner,0⟩,f.type,f.value)])) "unchanged parameter-only actual record"
    let fp ← observed inputs o.callee f.value; let ap ← observed inputs o.argument argument.value
    have raw : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost+5) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        LocalFunctionApplicationEvaluatesWithCost.call (span := o.span) (argumentsSpan := o.argumentsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
    let caller := [argument.value,f.value]; let context := [argument.type,f.type]
    have manual (k) : Core.Steps (bodyCost+5) ⟨.eval target caller,k,s⟩ ⟨.ret value,k,t⟩ :=
      .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
    have rows : inputs.environment.values = caller := by
      simpa [caller,args,LocalInputs.environment,Resolved.LocalScope.values,List.map_map,Function.comp_def] using
        RuntimeParametersBind.argument_values ps.bound
    have _ := raw.deterministic ((child.evaluatesWithCost_iff_steps inputs.sameIds).mpr (by rw [rows]; exact manual []))
    have typed : Core.HasType context target output := .apply (.var rfl) (.var rfl)
    let cost := bodyCost+5
    for fuel in List.range (cost+3) do
      have _ := preparation.run_eq_body fuel s
      check (decide (runRuntimeApplicationFunction? types owner source args fuel s =
        some (output,Core.runStateful fuel (.initial target caller s)))) "original entry execution was rebuilt"
    let opaqueValue : Core.Value := .closure .unit .word (.var 1) [.word (Core.Word.ofNatModulo 99)]
    for (leading,suffix,leftTypes,rightTypes,expected,argumentIndex) in [
        ([],caller,[],context,Core.Expr.apply (.var 2) (.var 1),1),
        ([argument.value],[f.value],[argument.type],[f.type],Core.Expr.apply (.var 2) (.var 0),0),
        (caller,[],context,[],target,0)] do
      if sameCaller : leading ++ suffix = caller then
        if sameContext : leftTypes ++ rightTypes = context then
          check (decide (target.weakenAt leading.length = expected ∧ leading.length = leftTypes.length)) "independent shifted Core or cutoff"
          have originalPath : Core.Steps cost (.initial target (leading++suffix) s) (.final value t) := by
            simpa only [sameCaller,cost,Core.State.initial,Core.State.final] using manual []
          have originalEval := Core.steps_from_initial_sound originalPath
          for insertedType in [Core.Ty.namedData ⟨999⟩,.function (.namedData ⟨7⟩) (.namedData ⟨8⟩)] do
            have oldTyping : Core.HasType (leftTypes++rightTypes) target output := by rw [sameContext]; exact typed
            have newTyping := (child.core_hasType_insert_iff leftTypes rightTypes insertedType).mpr oldTyping
            have _ := (child.core_hasType_insert_iff leftTypes rightTypes insertedType).mp newTyping
          for inserted in [w 91,Core.Value.cellRef .word 999,opaqueValue] do
            have changedEval := (child.core_evaluates_insert_iff leading suffix inserted).mpr originalEval
            have _ := (child.core_evaluates_insert_iff leading suffix inserted).mp changedEval
            have _ := child.core_insertion_paths leading suffix inserted originalEval
            have changedPath := child.core_steps_insert leading suffix inserted originalPath []
            have _ := child.core_steps_reflect_insert leading suffix inserted changedPath [.letBody .unit []]
            have _ := (child.core_steps_insert_iff leading suffix inserted).mp changedPath
            have _ := (child.core_steps_insert_iff leading suffix inserted).mpr originalPath
            let oldStart := Core.State.initial target (leading++suffix) s
            let newCaller := leading ++ inserted :: suffix
            let newStart := Core.State.initial (target.weakenAt leading.length) newCaller s
            observe oldStart value t cost originalPath
            observe newStart value t cost changedPath
            let oldCp : Core.State := ⟨.eval (.var 0) caller,[.applyClosure argument.type output body captured],s⟩
            let newCp : Core.State := ⟨.eval (.var argumentIndex) newCaller,[.applyClosure argument.type output body captured],s⟩
            check (decide (Core.runStateful 3 oldStart = .outOfFuel oldCp ∧ Core.runStateful 3 newStart = .outOfFuel newCp ∧
              oldCp ≠ newCp)) "distinct saved caller checkpoints were identified"
            let entered : Core.State := ⟨.eval body (argument.value::captured),[],s⟩
            check (decide (Core.runStateful 5 oldStart = .outOfFuel entered ∧ Core.runStateful 5 newStart = .outOfFuel entered))
              "same actual body/captures did not rejoin"
        else throw (IO.userError "typing context was silently changed")
      else throw (IO.userError "caller decomposition was silently changed")
  else throw (IO.userError "independent original call changed")
end ParsedApplicationInsertionEntries
open ParsedApplicationInsertionEntries
def frontendParsedApplicationInsertionEntryTests : IO Unit := do
  for n in [0,2,5] do
    execute ⟨.word,w 14,.word⟩ .word (delayed n) [] [] [] (w 14) (3*n+1)
      (.closure .nil (delayedTyped n .word [])) (delayedPath n (w 14) [] [])
  for current in [3,17] do
    execute ⟨.word,w 14,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [w current] [w current] (w current) 3
      (.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word))
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute ⟨.word,w 14,.word⟩ (.cell .word) (.newCell .word (.var 0)) [] [w current] [w current,w 14] (.cellRef .word 1) 3
      (.closure .nil (.newCell (.var rfl) .word)) (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
    execute ⟨.word,w 14,.word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
      [w current] [w 14] (w 14) 10
      (.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word)))
      (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  for type in [Core.Ty.namedData ⟨99⟩,.product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let a : TypedRuntimeArgument := ⟨.function type type,.closure type type (.var 0) [],.closure .nil (.var rfl)⟩
    execute a a.type (.var 0) [] [] [] a.value 1 (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
end Tests
