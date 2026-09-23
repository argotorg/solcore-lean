import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RuntimeParameters
/-! Original parsed function bodies are checked against an explicit sparse caller,
not treated as newly supported whole entries. Static and raw certificates are
independent of checking; literal Core programs have separate manual paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalComputationReturnTree
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Mixed", by decide⟩], by decide⟩⟩, 51⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 90},302⟩
private def inputs (a b : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"x",id 4,a⟩,⟨"f",foreign,.function a b⟩,⟨"g",id 9,.function a .bool⟩,
  ⟨"maker",id 12,.function a (.function a b)⟩,⟨"f",id 15,.bool⟩],by change [id 4,foreign,id 9,id 12,id 15].Nodup; decide⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.unit]
private def env (a : Core.Ty) (x : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(id 4,x),(foreign,identity a),(id 9,.closure a .bool (.bool choice) [.unit]),
    (id 12,.closure a (.function a a) (.var 1) [identity a]),(id 15,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def parsed (text : String) : IO Syntax.Block := do
  let text := "function example(){" ++ text ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main,"mixed-body.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "function parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩) &&
    source.span.contains source.value.body.span) "original full function/span"
  return source.value.body
private structure Atom (i : LocalTypeInputs) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression i.names s resolved
  lowered : Resolved.Lowers i.context.ids resolved core
  typing : Resolved.HasType i.context resolved type
private def atom (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Atom i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some localId =>
          match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId with
          | some t,some n => return ⟨.var localId,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | _ => throw (IO.userError "not an atom")
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : LocalComputationElaborates i.names i.context s core type
  typing : LocalComputationHasType i.names i.context s type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "call original order/spans"
      let f ← atom i fn; let a ← atom i arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (.call f.resolution f.lowered (ft ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)),
            by rw [shape]; exact .application (.call (f.resolution.reflects_type (ft ▸ f.typing)) (a.resolution.reflects_type (same ▸ a.typing)))⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | _ =>
      let a ← atom i s
      return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing,.pure (a.resolution.reflects_type a.typing)⟩
private structure Static (ts : TypeNameTable) (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  elaboration : LocalComputationReturnTreeElaborates ts owner i b core type
  typing : LocalComputationReturnTreeHasType ts owner i b type
private def statics (ts : TypeNameTable) (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static ts i b) := do
  for statement in b.value do check (b.span.contains statement.span) "original statement span"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨rs,.returnStmt (some s)⟩]⟩ =>
      check (rs.contains s.span) "original return span"; let c ← child i s
      have _ := c.elaboration.core_fragment
      return ⟨c.core,c.type,by rw [shape]; exact .expression c.elaboration,by rw [shape]; exact .expression c.typing⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← statics ts i ⟨inner,statements⟩
      return ⟨c.core,c.type,by rw [shape]; exact .block c.elaboration,by rw [shape]; exact .block c.typing⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span) "original binding order/spans"
      if unused : name.value ∉ i.names.map Prod.fst then
        let c ← child i init; let tail ← statics ts (i.bindFresh owner name.value c.type) ⟨bs,rest⟩
        match ann : annotation with
        | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .inferred unused c.elaboration tail.elaboration,
            by rw [shape,ann]; exact .inferred unused c.typing tail.typing⟩
        | some annotationSource =>
            check (ls.contains annotationSource.span) "original annotation span"
            match written : annotationSource with
            | ⟨_,.named name none⟩ =>
                if lookup : ts.lookup? (qualifiedTypeNameKey name) = some c.type then
                  have m : StructuralTypeDenotes ts annotationSource c.type := by rw [written]; exact .named (TypeNameTable.lookup?_iff.mp lookup)
                  return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .binding m unused c.elaboration tail.elaboration,
                    by rw [shape,ann]; exact .binding m unused c.typing tail.typing⟩
                else throw (IO.userError "annotation meaning")
            | _ => throw (IO.userError "annotation shape")
      else throw (IO.userError "shadow")
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← child i s; let tail ← statics ts i ⟨bs,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.elaboration tail.elaboration,
        by rw [shape]; exact .discard c.typing tail.typing⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let c ← child i guard; let a ← statics ts i yes; let d ← statics ts i no
      if ct : c.type = .bool then
        if same : d.type = a.type then return ⟨.ifE c.core a.core d.core,a.type,
          by rw [shape]; exact .conditional (ct ▸ c.elaboration) a.elaboration (same ▸ d.elaboration),
          by rw [shape]; exact .conditional (ct ▸ c.typing) a.typing (same ▸ d.typing)⟩
        else throw (IO.userError "both arm types")
      else throw (IO.userError "Bool guard")
  | _ => throw (IO.userError "outside static fixture")
termination_by sizeOf b
private structure AtomCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, LocalExpressionEvaluatesWithCost table e store s value store 1
private def atomCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (AtomCost table e s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match found : e.lookup? localId with
          | some v => return ⟨v,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _ => throw (IO.userError "missing actual")
      | _ => throw (IO.userError "missing raw name")
  | _ => throw (IO.userError "raw atom shape")
private structure ChildCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalComputationEvaluatesWithCost table e store s value store cost
private def childCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (ChildCost table e s) := do
  match shape : s with
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← atomCost table e fn; let a ← atomCost table e arg
      match closure : f.value with
      | .closure _ _ (.var n) captured =>
          match found : (a.value::captured)[n]? with
          | some value => return ⟨value,6,fun store => by rw [shape]; exact .application (.call (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl))⟩
          | _ => throw (IO.userError "actual capture missing")
      | .closure _ _ (.bool choice) _ => return ⟨.bool choice,6,fun store => by rw [shape]; exact .application (.call (closure ▸ f.evidence store) (a.evidence store) (.cons .bool .refl))⟩
      | _ => throw (IO.userError "outside actual body fixture")
  | _ => let a ← atomCost table e s; return ⟨a.value,1,fun store => .pure (a.evidence store)⟩
private structure Cost (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalComputationReturnTreeEvaluatesWithCost owner table e store b value store cost
private def costs (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) : IO (Cost table e b) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,1,fun _ => by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some s)⟩]⟩ =>
      let c ← childCost table e s; return ⟨c.value,c.cost,fun store => by rw [shape]; exact .expression (c.evidence store)⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← costs table e ⟨inner,statements⟩; return ⟨c.value,c.cost,fun store => by rw [shape]; exact .block (c.evidence store)⟩
  | ⟨bs,⟨_,.letDecl name annotation (some init)⟩::rest⟩ =>
      let c ← childCost table e init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← costs ((name.value,fresh)::table) ((fresh,c.value)::e) ⟨bs,rest⟩
      match ann : annotation with
      | none => return ⟨tail.value,c.cost+tail.cost+2,fun store => by rw [shape,ann]; exact .inferred (c.evidence store) (tail.evidence store)⟩
      | some _ => return ⟨tail.value,c.cost+tail.cost+2,fun store => by rw [shape,ann]; exact .binding (c.evidence store) (tail.evidence store)⟩
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← childCost table e s; let tail ← costs table e ⟨bs,rest⟩
      return ⟨tail.value,c.cost+tail.cost+2,fun store => by rw [shape]; exact .discard (c.evidence store) (tail.evidence store)⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let c ← childCost table e guard
      match selected : c.value with
      | .bool true => let a ← costs table e yes; return ⟨a.value,c.cost+a.cost+2,fun store => by rw [shape]; exact .ifTrue (selected ▸ c.evidence store) (a.evidence store)⟩
      | .bool false => let a ← costs table e no; return ⟨a.value,c.cost+a.cost+2,fun store => by rw [shape]; exact .ifFalse (selected ▸ c.evidence store) (a.evidence store)⟩
      | _ => throw (IO.userError "raw Bool guard")
  | _ => throw (IO.userError "outside raw fixture")
termination_by sizeOf b
private def staticCheck (a b : Core.Ty) (text : String) (core : Core.Expr) (type : Core.Ty) (mixed : Bool) : IO Unit := do
  let source ← parsed text; let i := inputs a b; let p ← statics (types a b) i source
  have _ := elaborateLocalComputationReturnTree?_iff.mp (elaborateLocalComputationReturnTree?_iff.mpr p.elaboration)
  have _ := localComputationReturnTreeHasType_iff_elaborates.mp p.typing
  have _ := localComputationReturnTreeHasType_iff_elaborates.mpr ⟨p.core,p.elaboration⟩
  have _ := p.elaboration.core_hasType
  check (decide (p.core=core ∧ p.type=type ∧ elaborateLocalComputationReturnTree? (types a b) owner i source=some (core,type) ∧
    elaborateTypedLetReturnTree? (types a b) owner i source=(if mixed then none else some (core,type)) ∧
    (i.bindFresh owner "r" b).names.lookup? "r"=some (id 16) ∧ i.names.lookup? "f"=some foreign)) "independent Core/type/fresh/old boundary"
private def exercise (argument : TypedRuntimeArgument) (choice : Bool) (text : String) (core : Core.Expr) (type : Core.Ty)
    (value : Core.Value) (cost : Nat)
    (manual : ∀ store k, Core.Steps cost ⟨.eval core (env argument.type argument.value choice).values,k,store⟩ ⟨.ret value,k,store⟩) : IO Unit := do
  let source ← parsed text; let i := inputs argument.type argument.type; let e := env argument.type argument.value choice
  let p ← statics (types argument.type argument.type) i source; let r ← costs i.names e source
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost then
    have elaboration : LocalComputationReturnTreeElaborates (types argument.type argument.type) owner i source core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    check (decide (elaborateLocalComputationReturnTree? (types argument.type argument.type) owner i source=some (core,type))) "actual caller exact checking"
    have ids : e.ids=i.context.ids := rfl
    have fragment := elaboration.core_fragment
    have _ := fragment.weakenAt 0
    for store in [[],[Core.Value.bool true,.unit]] do
      have counted : LocalComputationReturnTreeEvaluatesWithCost owner i.names e store source value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2] using r.evidence store
      have raw := localComputationReturnTreeEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have _ := localComputationReturnTreeEvaluates_iff_exists_cost.mp raw
      have original := (elaboration.evaluates_iff ids).mp raw
      have _ := (elaboration.evaluates_iff ids).mpr original
      have _ := counted.deterministic ((elaboration.evaluatesWithCost_iff_steps ids).mpr (manual store []))
      have _ := (elaboration.evaluatesWithCost_iff_steps ids).mp counted
      let pending := [Core.Frame.letBody .unit []]
      have _ := counted.toStepsWithContinuation elaboration ids pending
      let inserted := Core.Value.closure .bool .word (.var 99) [.unit]
      have changed := (fragment.evaluates_insert_iff [] e.values inserted).mpr original
      have _ := (fragment.evaluates_insert_iff [] e.values inserted).mp changed
      have pair : ∀ k, Core.Steps cost ⟨.eval core e.values,k,store⟩ ⟨.ret value,k,store⟩ ∧
          Core.Steps cost ⟨.eval (core.weakenAt 0) (inserted::e.values),k,store⟩ ⟨.ret value,k,store⟩ := by
        obtain ⟨n,paths⟩ := fragment.insertion_paths [] e.values inserted original
        have same := ((manual store []).final_unique (paths []).1).1
        exact same.symm ▸ paths
      for shifted in [false,true] do
        let start := Core.State.initial (if shifted then core.weakenAt 0 else core) (if shifted then inserted::e.values else e.values) store
        have path : Core.Steps cost start (.final value store) := by cases shifted; exact (pair []).1; exact (pair []).2
        for fuel in List.range (cost+2) do
          match outcome : Core.runStateful fuel start with
          | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=store)) "fixed cost/value/store"
          | .outOfFuel cp =>
              have _ := path.residual_of_outOfFuel outcome
              have _ := Core.runStateful_resume outcome (cost-fuel)
              check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) start)) "genuine own checkpoint/resume"
          | .fault _ _ => throw (IO.userError "manual successful path faulted")
      check (decide (Core.runStateful cost ⟨.eval core e.values,pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "pending endpoint is not completion"
  else throw (IO.userError "independent expected result")
private theorem invoke {e : Core.Environment} {s : Core.Store} {k : List Core.Frame} {f x : Nat}
    {a b : Core.Ty} {body : Core.Expr} {captured : Core.Environment} {argument value : Core.Value}
    (fn : e[f]?=some (.closure a b body captured)) (arg : e[x]?=some argument)
    (path : Core.Steps 1 ⟨.eval body (argument::captured),k,s⟩ ⟨.ret value,k,s⟩) :
    Core.Steps 6 ⟨.eval (call f x) e,k,s⟩ ⟨.ret value,k,s⟩ :=
  .cons .enterApply (.cons (.var fn) (.cons .beginArgument (.cons (.var arg) (.cons .invokeClosure path))))
private def wrap : Nat → String → String | 0,s => s | n+1,s => "{" ++ wrap n s ++ "}"
end ParsedLocalComputationReturnTree
open ParsedLocalComputationReturnTree
def frontendParsedLocalComputationReturnTreeTests : IO Unit := do
  let bound := Core.Expr.letE (call 1 0) (.var 0)
  let higher := Core.Expr.letE (call 3 0) (call 0 1)
  let discards := Core.Expr.letE (call 1 0) (.letE (call 2 1) (call 3 2))
  let branches := Core.Expr.ifE (call 2 0) bound (call 1 0)
  have p : LocalComputationFragment (.var 0) := .pure .var
  have a : LocalComputationFragment (call 1 0) := .application .var .var
  have _ : LocalComputationFragment branches := .ifE (.application .var .var) (.letE a p) a
  let conditional := "if(g(x)){{let r:B=f(x);return r;}}else{return f(x);}"
  for a in [Core.Ty.unit,.word,.namedData ⟨7⟩,.function (.namedData ⟨8⟩) (.namedData ⟨9⟩)] do
    for b in [Core.Ty.unit,.cell .word,.namedData ⟨10⟩] do
      for (text,core,type,mixed) in [("return;",.unit,.unit,false),("return x;",.var 0,a,false),
          ("return f(x);",call 1 0,b,true),("let r=f(x);return r;",bound,b,true),("let r:B=f(x);return r;",bound,b,true),
          ("let h=maker(x);return h(x);",higher,b,true),("f(x);f(x);return f(x);",discards,b,true),(conditional,branches,b,true)] do
        for depth in [0,2,7] do staticCheck a b (wrap depth text) core type mixed
  let bare ← parsed "return;"
  match shape : bare with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
      have old : TypedLetReturnTreeElaborates [] owner (inputs .unit .unit) bare .unit .unit := by rw [shape]; exact .single .bare
      have _ := old.toLocalComputationReturnTree
  | _ => throw (IO.userError "bare original shape")
  for argument in [TypedRuntimeArgument.mk .unit .unit .unit,⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩,
      ⟨.cell .word,.cellRef .word 999,.cellRef⟩,⟨.function (.namedData ⟨9⟩) (.namedData ⟨9⟩),
        .closure (.namedData ⟨9⟩) (.namedData ⟨9⟩) (.var 0) [],.closure .nil (.var rfl)⟩] do
    for choice in [false,true] do
      exercise argument choice "return;" .unit .unit .unit 1 (fun _ _ => .cons .unit .refl)
      exercise argument choice "return x;" (.var 0) argument.type argument.value 1 (fun _ _ => .cons (.var rfl) .refl)
      for text in ["let r=f(x);return r;","let r:B=f(x);return r;"] do
        exercise argument choice (wrap 2 text) bound argument.type argument.value 9 (fun _ _ =>
          CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl))
      exercise argument choice "let h=maker(x);return h(x);" higher argument.type argument.value 14 (fun _ _ =>
        CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (invoke rfl rfl (.cons (.var rfl) .refl)))
      exercise argument choice "f(x);f(x);return f(x);" discards argument.type argument.value 22 (fun _ _ =>
        CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl))
          (CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (invoke rfl rfl (.cons (.var rfl) .refl))))
      exercise argument choice conditional branches argument.type argument.value (if choice then 17 else 14) (by
        intro s k; cases choice
        · exact CostStepComposition.ifFalse (invoke rfl rfl (.cons .bool .refl)) (invoke rfl rfl (.cons (.var rfl) .refl))
        · exact CostStepComposition.ifTrue (invoke rfl rfl (.cons .bool .refl))
            (CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)))
  for text in ["", "f(x);", "let r:B;return r;", "let x=f(x);return x;", "let r=r;return r;", "let r:Unknown=f(x);return r;",
      "let r=f(f(x));return r;", "let r=(f(x));return r;", "return x + f(x);", "{return x;}return x;",
      "if(g(x)){return x;}", "if(g(x)){return x;}else{return f(x);}return x;", "return x;f(x);"] do
    let source ← parsed text
    check (decide (elaborateLocalComputationReturnTree? (types .word .word) owner (inputs .word .word) source=none)) "whole rejection boundary"
  let arithmetic ← parsed "let r=f(x);return r + 1;"
  let arithmeticCore := Core.Expr.letE (call 1 0) (.binary .wordAdd (.var 0) (.word (Core.Word.ofNatModulo 1)))
  have arithmeticPath (s k) : Core.Steps 13 ⟨.eval arithmeticCore (env .word (.word (Core.Word.ofNatModulo 17)) true).values,k,s⟩ ⟨.ret (.word (Core.Word.ofNatModulo 18)),k,s⟩ :=
    CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons .word (.cons (.applyBinary rfl) .refl)))))
  let start := Core.State.initial arithmeticCore (env .word (.word (Core.Word.ofNatModulo 17)) true).values []
  check (decide (elaborateLocalComputationReturnTree? (types .word .word) owner (inputs .word .word) arithmetic=some (arithmeticCore,.word) ∧ Core.runStateful 13 start=.done (.word (Core.Word.ofNatModulo 18)) [])) "call result feeds pure addition"
  match cp : Core.runStateful 12 start with
  | .outOfFuel state => have _ := (arithmeticPath [] []).residual_of_outOfFuel cp; check (decide (Core.runStateful 1 state=.done (.word (Core.Word.ofNatModulo 18)) [])) "arithmetic genuine residual"
  | _ => throw (IO.userError "arithmetic premature endpoint")
  let source ← parsed "if(g(x)){return x;}else{let r:Unknown=f(x);return r;}"
  let r ← costs (inputs .word .word).names (env .word (.word (Core.Word.ofNatModulo 17)) true) source
  have _ := localComputationReturnTreeEvaluates_iff_exists_cost.mpr ⟨r.cost,r.evidence []⟩
  check (decide (r.value=.word (Core.Word.ofNatModulo 17) ∧ r.cost=9 ∧
    elaborateLocalComputationReturnTree? (types .word .word) owner (inputs .word .word) source=none)) "selected raw versus whole unknown arm"
end Tests
