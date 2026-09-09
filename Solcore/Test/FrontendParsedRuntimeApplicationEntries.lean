import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalApplicationReturnBodyRunnerProperties
import Solcore.Frontend.LocalInputsApplicationRuntimeProperties
import Solcore.Frontend.LocalInputsExecution
import Solcore.Frontend.RuntimeApplicationFunctionFactorizationProperties

/-! Original whole declarations and supplied values precede the new entry checks.
Independent body paths fix the expected costs, stores and exact Core. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeApplicationEntries
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
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret value, k, t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped⟩
  let args := [f, argument]; let types := [(["F"],f.type),(["A"],argument.type),(["R"],output)]
  let source ← parsed text
  let ps ← parameters types source.value.signature.parameters.elements args
  let inputs := ps.actual
  let h ← header types source output
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have namesEq : inputs.names = ps.statics.names := by rw [← LocalInputs.toTypeInputs_names, erased]
  have contextEq : inputs.context = ps.statics.context := by rw [← LocalInputs.toTypeInputs_context, erased]
  check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
    [("x",⟨owner,1⟩,argument.type,argument.value),("f",⟨owner,0⟩,f.type,f.value)])) "original parameter-only record"
  let rows : PLift (inputs.environment.values = args.reverse.map (·.value)) ←
    if same : inputs.environment.values = args.reverse.map (·.value) then pure ⟨same⟩
    else throw (IO.userError "actual values reversed other than once")
  let o ← original source.value.body
  let expression : Syntax.Expr := ⟨o.span,.call o.callee ⟨o.argumentsSpan,[o.argument]⟩⟩
  let fn ← reference inputs o.callee; let arg ← reference inputs o.argument
  if children : fn.type = f.type ∧ arg.type = argument.type ∧ fn.core = .var 1 ∧ arg.core = .var 0 then
    have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
      have e := LocalFunctionApplicationElaborates.call (span := o.span) (argumentsSpan := o.argumentsSpan)
        fn.resolution fn.lowered (children.1 ▸ fn.typing) arg.resolution arg.lowered (children.2.1 ▸ arg.typing)
      simpa only [target,expression,children.2.2.1,children.2.2.2] using e
    have bodyElaboration : LocalApplicationReturnBodyElaborates inputs.names inputs.context source.value.body target output := by
      rw [o.shape]; exact .application child
    let fp ← observed inputs o.callee f.value; let ap ← observed inputs o.argument argument.value
    have costed : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost + 5) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        LocalFunctionApplicationEvaluatesWithCost.call (span := o.span) (argumentsSpan := o.argumentsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
    have bodyCosted : LocalApplicationReturnBodyEvaluatesWithCost inputs.names inputs.environment s source.value.body value t (bodyCost + 5) := by
      rw [o.shape]; exact .application costed
    have manual (k) : Core.Steps (bodyCost + 5) ⟨.eval target inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩ := by
      rw [rows.down]; exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
    have _ := bodyCosted.deterministic ((bodyElaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr (manual []))
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,target,output⟩
    let prepared : PreparedRuntimeFunction := ⟨inputs,target,output⟩
    have compilation : RuntimeApplicationFunctionCompiles types owner source compiled :=
      ⟨h.down,ps.declared,by rw [← namesEq,← contextEq]; exact bodyElaboration⟩
    have preparation : RuntimeApplicationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,bodyElaboration⟩
    have _ := compilation.complete
    have _ := compileRuntimeApplicationFunction?_iff.mp compilation.complete
    have _ := compilation.result_unique (compileRuntimeApplicationFunction?_sound compilation.complete)
    have _ := compilation.core_hasType
    have _ := prepareRuntimeApplicationFunction?_iff.mp preparation.complete
    have _ := preparation.result_unique (prepareRuntimeApplicationFunction?_sound preparation.complete)
    have _ := preparation.core_hasType
    have _ := preparation.compiles
    have matching : args.map (·.type) = compiled.inputs.context.values.reverse := by
      change args.map (·.type) = ps.statics.context.values.reverse
      rw [← contextEq]
      simpa only [LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,
        List.map_reverse,List.reverse_reverse] using congrArg List.reverse preparation.parameters.argument_types.symm
    have _ := compilation.prepare_arguments args matching
    have _ := runtimeApplicationFunctionPrepares_toCompiled_iff.mpr ⟨compilation,matching⟩
    have _ := prepareRuntimeApplicationFunction?_factorization types owner source args
    let cost := bodyCost + 5
    have equal (fuel store) : runRuntimeApplicationFunction? types owner source args fuel store =
        inputs.runApplication? fuel expression store := by
      rw [preparation.run_eq_body, o.shape]; exact inputs.runApplicationReturnBody?_return fuel _ _ expression store
    check (decide ((compileRuntimeApplicationFunction? types owner source).map (fun c => (c.inputs.names,c.inputs.context,c.core,c.returnType)) =
      some (ps.statics.names,ps.statics.context,target,output))) "independent static record"
    check (decide ((prepareRuntimeApplicationFunction? types owner source args).map
      (fun p => (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)) =
      some (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),target,output))) "independent actual full record"
    check (decide (runRuntimeApplicationFunction? types owner source args 3 s = some (output,.outOfFuel
      ⟨.eval (.var 0) inputs.environment.values,[.applyClosure argument.type output body captured],s⟩))) "exact cp3"
    if body == .loadCell (.var 1) && captured == [.cellRef .word 0] then
      check (decide (runRuntimeApplicationFunction? types owner source args 7 [] = some (output,
        .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩))) "missing-cell fault hidden"
    for fuel in List.range (cost + 3) do
      have _ := runRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := owner) (declaration := source) (arguments := args) fuel s
      have _ := (runRuntimeApplicationFunction?_eq_some_iff (fuel := fuel) (store := s)).mpr ⟨prepared,preparation,rfl,rfl⟩
      have _ := compilation.run_eq args matching fuel s
      have _ := (LocalInputs.runApplicationReturnBody?_done_iff_typed_cost).mpr
        ⟨bodyElaboration.hasType,cost,bodyCosted,Nat.le_refl cost⟩
      check ((compileRuntimeFunction? types owner source).isNone && (prepareRuntimeFunction? types owner source args).isNone &&
        (runRuntimeFunction? types owner source args fuel s).isNone) "old whole entry changed"
      check (decide (runRuntimeApplicationFunction? types owner source args fuel s = inputs.runApplicationReturnBody? fuel source.value.body s ∧
        runRuntimeApplicationFunction? types owner source args fuel s = some (output,Core.runStateful fuel (.initial target inputs.environment.values s)))) "entry/body exact result"
      match stopped : runRuntimeApplicationFunction? types owner source args fuel s with
      | some (_, .done v final) => check (decide (cost ≤ fuel ∧ v = value ∧ final = t)) "independent terminal observation"
      | some (_, .outOfFuel checkpoint) =>
          have childStopped := (equal fuel s) ▸ stopped
          have _ := LocalInputs.runApplication?_residual_of_outOfFuel costed childStopped
          check (decide (fuel < cost ∧ Core.runStateful (cost - fuel) checkpoint = .done value t)) "genuine remainder"
          for additional in [0,1,cost-fuel,cost+2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (runRuntimeApplicationFunction? types owner source args (fuel+additional) s =
              some (output,Core.runStateful additional checkpoint))) "full entry residual transport"
      | _ => throw (IO.userError "independent successful path lost")
    for otherStore in [[],[.bool true]] do
      match stopped : runRuntimeApplicationFunction? types owner source args 3 otherStore with
      | some (tag,.outOfFuel checkpoint) =>
          have childStopped := (equal 3 otherStore) ▸ stopped
          for additional in [0,4,5,cost+2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (tag = output ∧ runRuntimeApplicationFunction? types owner source args (3+additional) otherStore =
              some (output,Core.runStateful additional checkpoint))) "unvalidated-store outcome hidden"
      | _ => throw (IO.userError "genuine cp3 lost before body")
  else throw (IO.userError "original independent call children")
private def rejected (types : TypeNameTable) (args : List TypedRuntimeArgument) (text : String) (badStatic : Bool) : IO Unit := do
  let source ← parsed text
  if badStatic then check (compileRuntimeApplicationFunction? types owner source).isNone "whole static gate"
  if badStatic && text.endsWith "{return f(x);}" then
    let ps ← parameters types source.value.signature.parameters.elements args
    check (decide (ps.actual.checkApplicationReturnBody? source.value.body = some (target,.word))) "local body success lost at whole header gate"
  have _ := compileRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := owner) (declaration := source)
  have _ := prepareRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := owner) (declaration := source) (arguments := args)
  have _ := prepareRuntimeApplicationFunction?_factorization types owner source args
  if text.endsWith "{return x;}" then
    check (decide (runRuntimeFunction? types owner source args 1 [] = some (.word,.done (w 9) []))) "old pure return success changed"
  for fuel in [0,3,20] do
    check ((prepareRuntimeApplicationFunction? types owner source args).isNone &&
      (runRuntimeApplicationFunction? types owner source args fuel []).isNone) "whole actual gate"
end ParsedRuntimeApplicationEntries
open ParsedRuntimeApplicationEntries
def frontendParsedRuntimeApplicationEntryTests : IO Unit := do
  for (n,x) in [(0,9),(0,14),(1,14),(4,14),(9,14)] do
    execute ⟨.word,w x,.word⟩ .word (delayed n) [] [] [] (w x) (3*n+1)
      (.closure .nil (delayedTyped n .word [])) (delayedPath n (w x) [] [])
  for current in [3,17] do
    execute ⟨.word,w 9,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [w current] [w current] (w current) 3
      (.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word))
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute ⟨.word,w 9,.word⟩ (.cell .word) (.newCell .word (.var 0)) [] [w current] [w current,w 9] (.cellRef .word 1) 3
      (.closure .nil (.newCell (.var rfl) .word)) (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
    execute ⟨.word,w 9,.word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
      [w current] [w 9] (w 9) 10
      (.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word)))
      (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  for type in [Core.Ty.namedData ⟨99⟩,.product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let a : TypedRuntimeArgument := ⟨.function type type,.closure type type (.var 0) [],.closure .nil (.var rfl)⟩
    execute a a.type (.var 0) [] [] [] a.value 1 (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
  execute ⟨.word,w 9,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [.bool true] [.bool true] (.bool true) 3
    (.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word))
    (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
  have _ : ¬ Core.ValueHasType (.bool true) .word := by intro impossible; cases impossible
  let f : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
  let x : TypedRuntimeArgument := ⟨.word,w 9,.word⟩
  let types : TypeNameTable := [(["F"],f.type),(["A"],.word),(["R"],.word),(["B"],.bool)]
  for args in [[],[f],[x,f],[f,⟨.bool,.bool true,.bool⟩],[f,x,x]] do rejected types args text false
  for signature in ["function invoke<T>(f:F,x:A) returns(R)","function invoke(f:F,x:A) returns()",
      "function invoke(f:F,x:A) returns(R,R)","function invoke(f:F,x:A) returns(B)","function invoke(f:F,x:A) returns(Unknown)"] do
    rejected types [f,x] (signature ++ "{return f(x);}") true
  for statements in ["return;","return x;","","return f(x);return x;","f(x);return x;","{return f(x);}","return f(f(x));"] do
    rejected types [f,x] ("function invoke(f:F,x:A) returns(R){" ++ statements ++ "}") true
end Tests
