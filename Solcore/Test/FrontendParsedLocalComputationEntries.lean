import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.LocalComputation
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RuntimeApplicationFunction

/-! Original declarations retain their two existing entry profiles. The shared
child does not introduce a mixed body or a new function endpoint. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalComputationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def target : Core.Expr := .apply (.var 1) (.var 0)
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

private def verify (inputs : LocalInputs) (source : Syntax.Expr) (core shifted : Core.Expr) (type : Core.Ty)
    (s t : Core.Store) (value : Core.Value) (cost : Nat)
    (elaboration : LocalComputationElaborates inputs.names inputs.context source core type)
    (typing : LocalComputationHasType inputs.names inputs.context source type)
    (raw : LocalComputationEvaluates inputs.names inputs.environment s source value t)
    (costed : LocalComputationEvaluatesWithCost inputs.names inputs.environment s source value t cost)
    (manual : ∀ k, Core.Steps cost ⟨.eval core inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩) : IO Unit := do
  have checked := elaborateLocalComputation?_iff.mpr elaboration
  have _ := elaborateLocalComputation?_iff.mp checked
  have _ := localComputationHasType_iff_elaborates.mp typing
  have _ := localComputationHasType_iff_elaborates.mpr ⟨core,elaboration⟩
  have coreTyped := elaboration.core_hasType
  have _ := localComputationEvaluates_iff_exists_cost.mp raw
  have _ := localComputationEvaluates_iff_exists_cost.mpr ⟨cost,costed⟩
  have evaluated := (elaboration.evaluates_iff inputs.sameIds).mp raw
  have _ := (elaboration.evaluates_iff inputs.sameIds).mpr evaluated
  have _ := costed.deterministic ((elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr (manual []))
  have _ := (elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mp costed
  have _ := costed.toStepsWithContinuation elaboration inputs.sameIds [.letBody .unit []]
  check (decide (elaborateLocalComputation? inputs.names inputs.context source = some (core,type) ∧
    core.weakenAt 0 = shifted)) "independent original and shifted Core"
  let inserted := Core.Value.cellRef .bool 999
  have _ := (elaboration.core_hasType_insert_iff [] inputs.context.values (.namedData ⟨700⟩)).mp
    ((elaboration.core_hasType_insert_iff [] inputs.context.values (.namedData ⟨700⟩)).mpr coreTyped)
  have changed := (elaboration.core_evaluates_insert_iff [] inputs.environment.values inserted).mpr evaluated
  have _ := (elaboration.core_evaluates_insert_iff [] inputs.environment.values inserted).mp changed
  have paired : ∀ k, Core.Steps cost ⟨.eval core inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩ ∧
      Core.Steps cost ⟨.eval (core.weakenAt 0) (inserted::inputs.environment.values),k,s⟩ ⟨.ret value,k,t⟩ := by
    obtain ⟨common,paths⟩ := elaboration.core_insertion_paths [] inputs.environment.values inserted evaluated
    have sameCost := ((manual []).final_unique (paths []).1).1
    exact sameCost.symm ▸ paths
  for shiftedSide in [false,true] do
    let start := if shiftedSide then Core.State.initial (core.weakenAt 0) (inserted::inputs.environment.values) s
      else Core.State.initial core inputs.environment.values s
    have path : Core.Steps cost start (.final value t) := by
      cases shiftedSide
      · exact (paired []).1
      · exact (paired []).2
    for fuel in List.range (cost+2) do
      match exhausted : Core.runStateful fuel start with
      | .done actual final => check (decide (cost ≤ fuel ∧ actual=value ∧ final=t)) "exact independent cost/value/store"
      | .outOfFuel cp =>
          have _ := path.residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted (cost-fuel)
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp = .done value t ∧
            Core.runStateful 1 cp = Core.runStateful (fuel+1) start)) "own genuine residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
  let k := [Core.Frame.letBody .unit []]
  have _ := paired k
  check (decide (Core.runStateful (cost+2) ⟨.eval core inputs.environment.values,k,s⟩ = .done .unit t ∧
    Core.runStateful (cost+2) ⟨.eval shifted (inserted::inputs.environment.values),k,s⟩ = .done .unit t))
    "retained continuation runs after the costed endpoint"
private def outcomes (call : Bool) (types : TypeNameTable) (source : Syntax.FunctionDecl)
    (args : List TypedRuntimeArgument) (core : Core.Expr) (type : Core.Ty) (store : Core.Store) (cost : Nat) : IO Unit := do
  check (if call then decide (compileRuntimeFunction? types owner source = none ∧ prepareRuntimeFunction? types owner source args = none)
    else decide (compileRuntimeApplicationFunction? types owner source = none ∧
      prepareRuntimeApplicationFunction? types owner source args = none)) "other profile's whole rejection changed"
  for fuel in List.range (cost+2) do
    let expected := some (type,Core.runStateful fuel (.initial core (args.reverse.map (·.value)) store))
    check (if call then decide (runRuntimeApplicationFunction? types owner source args fuel store = expected ∧
        runRuntimeFunction? types owner source args fuel store = none)
      else decide (runRuntimeFunction? types owner source args fuel store = expected ∧
        runRuntimeApplicationFunction? types owner source args fuel store = none)) "old whole-entry boundaries changed"
private def execute (call : Bool) (argument : TypedRuntimeArgument) (output : Core.Ty)
    (body : Core.Expr) (captured : Core.Environment) (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value::captured),k,s⟩ ⟨.ret value,k,t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output,.closure argument.type output body captured,closureTyped⟩
  let args := [f,argument]; let types := [(["F"],f.type),(["A"],argument.type),(["R"],if call then output else argument.type)]
  let source ← parsed (if call then "function invoke(f:F,x:A) returns(R){return f(x);}"
    else "function invoke(f:F,x:A) returns(R){return x;}")
  let ps ← parameters types source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source (if call then output else argument.type)
  have _ := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have rows : inputs.environment.values = [argument.value,f.value] := by
    simpa [args,LocalInputs.environment,Resolved.LocalScope.values,List.map_map,Function.comp_def] using
      RuntimeParametersBind.argument_values ps.bound
  check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
    [("x",⟨owner,1⟩,argument.type,argument.value),("f",⟨owner,0⟩,f.type,f.value)])) "one original actual parameter record"
  match shape : source.value.body with
  | ⟨bs,[⟨rs,.returnStmt (some expression)⟩]⟩ =>
      check (bs.contains rs && rs.contains expression.span) "original body/return ranges"
      if choose : call then
        match original : expression with
        | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
            check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span &&
              decide (fn.span.endByte ≤ argsSpan.startByte)) "original ordered child spans"
            let fc ← reference inputs fn; let ac ← reference inputs arg
            if same : fc.type=f.type ∧ ac.type=argument.type ∧ fc.core=.var 1 ∧ ac.core=.var 0 then
              have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
                rw [original]; simpa only [target,same.2.2.1,same.2.2.2] using LocalFunctionApplicationElaborates.call
                  (span := span) (argumentsSpan := argsSpan) fc.resolution fc.lowered (same.1 ▸ fc.typing)
                  ac.resolution ac.lowered (same.2.1 ▸ ac.typing)
              let fp ← observed inputs fn f.value; let ap ← observed inputs arg argument.value
              have costed : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost+5) := by
                rw [original]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
                  LocalFunctionApplicationEvaluatesWithCost.call (span := span) (argumentsSpan := argsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
              have whole : RuntimeApplicationFunctionPrepares types owner source args ⟨inputs,target,output⟩ :=
                ⟨by simpa [choose] using h.down,ps.bound,by rw [shape]; exact .application child⟩
              have _ := whole.complete; have _ := whole.compiles.complete
              have manual (k) : Core.Steps (bodyCost+5) ⟨.eval target inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩ := by
                rw [rows]; exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
              verify inputs expression target (.apply (.var 2) (.var 1)) output s t value (bodyCost+5)
                (.application child) (.application child.hasType) (.application costed.erase) (.application costed) manual
              outcomes true types source args target output s (bodyCost+5)
            else throw (IO.userError "fixed call children changed")
        | _ => throw (IO.userError "original root call changed")
      else
        let ac ← reference inputs expression; let ap ← observed inputs expression argument.value
        if same : ac.type=argument.type ∧ ac.core=.var 0 then
          have child : LocalComputationElaborates inputs.names inputs.context expression (.var 0) argument.type :=
            .pure ac.resolution (same.2 ▸ ac.lowered) (same.1 ▸ ac.typing)
          have whole : RuntimeFunctionPrepares types owner source args ⟨inputs,.var 0,argument.type⟩ := by
            refine ⟨by simpa [choose] using h.down,ps.bound,.single ?_⟩
            rw [LocalInputs.toTypeInputs_names,LocalInputs.toTypeInputs_context,shape]
            exact .expression ac.resolution (same.2 ▸ ac.lowered) (same.1 ▸ ac.typing)
          have _ := whole.complete; have _ := whole.compiles.complete
          verify inputs expression (.var 0) (.var 1) argument.type s s argument.value 1 child
            (.pure (ac.resolution.reflects_type (same.1 ▸ ac.typing))) (.pure (ap.evidence s).erase) (.pure (ap.evidence s))
            (fun _ => by rw [rows]; exact .cons (.var rfl) .refl)
          outcomes false types source args (.var 0) argument.type s 1
        else throw (IO.userError "fixed pure child changed")
  | _ => throw (IO.userError "original singleton return changed")
end ParsedLocalComputationEntries
open ParsedLocalComputationEntries
def frontendParsedLocalComputationEntryTests : IO Unit := do
  for argument in [TypedRuntimeArgument.mk .word (w 14) .word,⟨.unit,.unit,.unit⟩,
      ⟨.product .word .bool,.pair (w 3) (.bool false),.pair .word .bool⟩,
      ⟨.cell .word,.cellRef .word 999,.cellRef⟩,
      ⟨.function .word .word,.closure .word .word (.var 1) [w 23],.closure (.cons .word .nil) (.var rfl)⟩,
      ⟨.function (.namedData ⟨9⟩) (.namedData ⟨9⟩),.closure (.namedData ⟨9⟩) (.namedData ⟨9⟩) (.var 0) [],.closure .nil (.var rfl)⟩] do
    execute false argument argument.type (.var 0) [] [w 23] [w 23] argument.value 1
      (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
  for current in [3,17] do
    execute true ⟨.word,w 14,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [w current] [w current] (w current) 3
      (.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word))
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute true ⟨.word,w 14,.word⟩ (.cell .word) (.newCell .word (.var 0)) [] [w current] [w current,w 14] (.cellRef .word 1) 3
      (.closure .nil (.newCell (.var rfl) .word)) (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  execute true ⟨.word,w 14,.word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0] [w 3] [w 14] (w 14) 10
    (.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word)))
    (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
      (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  execute true ⟨.word,w 14,.word⟩ .word (.letE (.var 0) (.var 0)) [] [] [] (w 14) 4
    (.closure .nil (.letE (.var rfl) (.var rfl))) (fun _ => .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))
  let higher : TypedRuntimeArgument := ⟨.function (.namedData ⟨9⟩) (.namedData ⟨9⟩),
    .closure (.namedData ⟨9⟩) (.namedData ⟨9⟩) (.var 0) [],.closure .nil (.var rfl)⟩
  execute true higher higher.type (.var 0) [] [] [] higher.value 1 (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
  let source ← parsed "function invoke(f:F,x:A) returns(R){let r=f(x);return r+1;}"
  let args : List TypedRuntimeArgument := [⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩,⟨.word,w 14,.word⟩]
  let types := [(["F"],Core.Ty.function .word .word),(["A"],Core.Ty.word),(["R"],Core.Ty.word)]
  let ps ← parameters types source.value.signature.parameters.elements args
  match source.value.body.value with
  | ⟨_,.letDecl _ none (some child)⟩ :: _ =>
      check (decide (elaborateLocalComputation? ps.actual.names ps.actual.context child = some (target,.word) ∧
        prepareRuntimeFunction? types owner source args = none ∧ prepareRuntimeApplicationFunction? types owner source args = none ∧
        runRuntimeFunction? types owner source args 99 [] = none ∧ runRuntimeApplicationFunction? types owner source args 99 [] = none))
        "accepted child did not authorize a mixed whole body"
  | _ => throw (IO.userError "original mixed-body boundary changed")
end Tests
