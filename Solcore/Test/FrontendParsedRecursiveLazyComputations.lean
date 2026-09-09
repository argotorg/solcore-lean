import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
/-! Original lazy children retain independent static/raw certificates. Literal Core
and manual paths distinguish skipped constants from selected actual values. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveLazyComputations
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Lazy",by decide⟩],by decide⟩⟩,59⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25),("true",id 90),("false",id 91),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(id 14,a),(id 15,.bool),(id 16,.bool),(foreign,.function a a),(id 9,.function a a),(id 20,.function .bool .bool),(id 25,.function a (.function a a)),(id 90,.bool),(id 91,.bool),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def environment (a : Core.Ty) (x y : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 7,x),(id 14,y),(id 15,.bool c),(id 16,.bool d),(foreign,identity a),(id 9,identity a),(id 20,identity .bool),(id 25,.closure a (.function a a) (.var 1) [identity a]),(id 90,.bool false),(id 91,.bool true),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-lazy.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parser: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "original bytes/span"
  return s
private structure Leaf (ctx : Resolved.Context) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names s resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def leaf (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Leaf ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n => return ⟨.var localId,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "caller context row")
      | _ => throw (IO.userError "caller name")
  | _ => throw (IO.userError "identifier leaf")
private structure Static (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates names ctx s core type
  typing : RecursiveLocalComputationHasType names ctx s type
private def statics (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static ctx s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "group span"; let a ← statics ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨span,.unary ⟨opSpan,.logicalNot⟩ inner⟩ =>
      check (span.contains inner.span && span.contains opSpan && decide (span.startByte=opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+1 ∧ opSpan.endByte≤inner.span.startByte ∧ span.endByte=inner.span.endByte)) "original logical prefix bytes/order"
      let a ← statics ctx inner
      if same : a.type=.bool then return ⟨.unary .boolNot a.core,.bool,
        by rw [shape]; exact .logicalNot (same ▸ a.elaboration),by rw [shape]; exact .logicalNot (same ▸ a.typing)⟩
      else throw (IO.userError "Bool operand")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨span,.binary left ⟨opSpan,.logicalAnd⟩ right⟩ =>
      check (span.contains left.span && span.contains right.span && span.contains opSpan && decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+2 ∧ opSpan.endByte≤right.span.startByte)) "original && spans/order"
      let a ← statics ctx left; let b ← statics ctx right
      if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core b.core (.bool false),.bool,
        by rw [shape]; exact .logicalAnd (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .logicalAnd (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "both conjunction child types")
  | ⟨span,.binary left ⟨opSpan,.logicalOr⟩ right⟩ =>
      check (span.contains left.span && span.contains right.span && span.contains opSpan && decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+2 ∧ opSpan.endByte≤right.span.startByte)) "original || spans/order"
      let a ← statics ctx left; let b ← statics ctx right
      if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core (.bool true) b.core,.bool,
        by rw [shape]; exact .logicalOr (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .logicalOr (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "both disjunction child types")
  | ⟨span,.conditional guard question yes colon no⟩ =>
      check (span.contains guard.span && span.contains yes.span && span.contains no.span && span.contains question && span.contains colon &&
        decide (guard.span.endByte≤question.startByte ∧ question.endByte=question.startByte+1 ∧ question.endByte≤yes.span.startByte ∧
          yes.span.endByte≤colon.startByte ∧ colon.endByte=colon.startByte+1 ∧ colon.endByte≤no.span.startByte)) "original question/colon order"
      let g ← statics ctx guard; let a ← statics ctx yes; let b ← statics ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "whole conditional types")
  | _ => let a ← leaf ctx s; return ⟨a.core,a.type,(LocalComputationElaborates.pure a.resolution a.lowered a.typing).toRecursiveLocalComputation,.pure (a.resolution.reflects_type a.typing)⟩
termination_by sizeOf s
private structure RawLeaf (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store s value store 1
private def rawLeaf (env : Resolved.Environment) (s : Syntax.Expr) : IO (RawLeaf env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : env.lookup? localId with
          | some v => return ⟨v,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _ => throw (IO.userError "actual row")
      | _ => throw (IO.userError "actual name")
  | _ => throw (IO.userError "actual identifier")
private structure Actual (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost names env store s value store cost
private def actual (env : Resolved.Environment) (s : Syntax.Expr) : IO (Actual env s) := do
  match shape : s with
  | ⟨_,.group inner⟩ => let a ← actual env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | ⟨_,.unary ⟨_,.logicalNot⟩ inner⟩ =>
      let a ← actual env inner
      match v : a.value with
      | .bool b => return ⟨.bool (!b),a.cost+2,fun store => by rw [shape]; exact .logicalNot (v ▸ a.evidence store)⟩
      | _ => throw (IO.userError "actual Bool")
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured =>
          match found : (a.value::captured)[n]? with
          | some v => return ⟨v,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
          | _ => throw (IO.userError "actual captured index")
      | _ => throw (IO.userError "fixture body")
  | ⟨_,.binary left ⟨_,.logicalAnd⟩ right⟩ =>
      let a ← actual env left
      match value : a.value with
      | .bool false => return ⟨.bool false,a.cost+3,fun store => by rw [shape]; exact .andFalse (value ▸ a.evidence store)⟩
      | .bool true => let b ← actual env right; return ⟨b.value,a.cost+b.cost+2,fun store => by rw [shape]; exact .andTrue (value ▸ a.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual conjunction left Bool")
  | ⟨_,.binary left ⟨_,.logicalOr⟩ right⟩ =>
      let a ← actual env left
      match value : a.value with
      | .bool true => return ⟨.bool true,a.cost+3,fun store => by rw [shape]; exact .orTrue (value ▸ a.evidence store)⟩
      | .bool false => let b ← actual env right; return ⟨b.value,a.cost+b.cost+2,fun store => by rw [shape]; exact .orFalse (value ▸ a.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual disjunction left Bool")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← actual env guard
      match gv : g.value with
      | .bool true => let a ← actual env yes; return ⟨a.value,g.cost+a.cost+2,fun store => by rw [shape]; exact .ifTrue (gv ▸ g.evidence store) (a.evidence store)⟩
      | .bool false => let b ← actual env no; return ⟨b.value,g.cost+b.cost+2,fun store => by rw [shape]; exact .ifFalse (gv ▸ g.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "actual Bool")
  | _ => let a ← rawLeaf env s; return ⟨a.value,1,fun store => .pure (a.evidence store)⟩
termination_by sizeOf s
private structure Path (env : Core.Environment) (core : Core.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store k, Core.Steps cost ⟨.eval core env,k,store⟩ ⟨.ret value,k,store⟩
private def manual : (fuel : Nat) → (env : Core.Environment) → (core : Core.Expr) → IO (Path env core)
  | 0,_,_ => throw (IO.userError "manual certificate depth")
  | fuel+1,env,core => do
    match shape : core with
    | .bool b => return ⟨.bool b,1,fun _ _ => by rw [shape]; exact .cons .bool .refl⟩
    | .var n => match found : env[n]? with
      | some v => return ⟨v,1,fun _ _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | _ => throw (IO.userError "manual variable")
    | .unary op inner =>
      let a ← manual fuel env inner
      match applied : op.apply a.value with
      | some v => return ⟨v,a.cost+2,fun store k => by rw [shape]; exact CostStepComposition.unary (a.evidence store _) applied⟩
      | _ => throw (IO.userError "manual unary")
    | .apply fn arg =>
      let f ← manual fuel env fn; let a ← manual fuel env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
        | some v => return ⟨v,f.cost+a.cost+4,fun store _ => by rw [shape]; exact CostStepComposition.apply (closure ▸ f.evidence store _) (a.evidence store _) (.cons (.var found) .refl)⟩
        | _ => throw (IO.userError "manual body index")
      | _ => throw (IO.userError "manual closure")
    | .ifE guard yes no =>
      let g ← manual fuel env guard
      match gv : g.value with
      | .bool true => let a ← manual fuel env yes; return ⟨a.value,g.cost+a.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence store _) (a.evidence store k)⟩
      | .bool false => let b ← manual fuel env no; return ⟨b.value,g.cost+b.cost+2,fun store k => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence store _) (b.evidence store k)⟩
      | _ => throw (IO.userError "manual guard")
    | _ => throw (IO.userError "manual Core grammar")
private def exercise (text : String) (a : Core.Ty) (x y : Core.Value) (c d : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) (pureSource : Bool := false) : IO Unit := do
  let s ← parsed text; let env := environment a x y c d; let p ← statics (context a) s; let r ← actual env s; let m ← manual 30 env.values core
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost ∧ m.value=value ∧ m.cost=cost then
    have e : RecursiveLocalComputationElaborates names (context a) s core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr e)
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
    have _ := e.core_hasType
    check (decide (elaborateRecursiveLocalComputation? names (context a) s=some (core,type) ∧ elaborateLocalExpression? names (context a) s=(if pureSource then some (core,type) else none) ∧ elaborateLocalComputation? names (context a) s=(if pureSource then some (core,type) else none))) "new exact and original pure/old endpoint boundary"
    for store in [[],[Core.Value.bool true,.cellRef .word 91]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2.1] using r.evidence store
      have path : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,store⟩ := by simpa only [fixed.2.2.2.2.1,fixed.2.2.2.2.2] using m.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have coreRaw := (e.evaluates_iff rfl).mp raw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps rfl).mpr (path []))
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e rfl pending
      for fuel in List.range (cost+2) do
        have _ := (path []).runStateful_done_iff (fuel := fuel)
        match outcome : Core.runStateful fuel (.initial core env.values store) with
        | .done v st => check (decide (cost≤fuel ∧ v=value ∧ st=store)) "literal value/store/threshold"
        | .outOfFuel cp =>
            have _ := (path []).residual_of_outOfFuel outcome
            check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) (.initial core env.values store))) "genuine residual/full replay"
        | .fault _ _ => throw (IO.userError "fixed path fault")
      have fragment := e.core_fragment
      have _ := fragment.weakenAt 3
      for cutoff in [0,3] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading++suffix=env.values := List.take_append_drop cutoff env.values
        let inserted : Core.Value := .closure .bool .unit (.var 99) [.cellRef .word 77]
        have original : Core.Evaluates (leading++suffix) store core value store := by rw [same]; exact coreRaw
        have changed := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
        have paired : ∀ k, Core.Steps cost ⟨.eval core (leading++suffix),k,store⟩ ⟨.ret value,k,store⟩ ∧
            Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),k,store⟩ ⟨.ret value,k,store⟩ := by
          obtain ⟨n,paths⟩ := fragment.insertion_paths leading suffix inserted original
          have eqCost : n=cost := ((paths []).1.final_unique (by simpa only [same,Core.State.final] using path [])).1
          exact eqCost ▸ paths
        check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "inserted pending endpoint"
  else throw (IO.userError s!"independent certificate mismatch: {text}")
private def skippedOverlap (isOr : Bool) : IO Unit := do
  let s ← parsed (if isOr then "c || Missing" else "c && Missing")
  let env := environment .bool (.bool false) (.bool true) isOr false; let r ← actual env s
  match shape : s with
  | ⟨_,.binary left ⟨_,.logicalAnd⟩ _⟩ =>
      let a ← rawLeaf env left
      if same : a.value=.bool false then
        have old : LocalComputationEvaluatesWithCost names env [] s (.bool false) [] 4 := .pure (by rw [shape]; exact .andFalse (same ▸ a.evidence []))
        have _ := (r.evidence []).deterministic old.toRecursiveLocalComputation
      else throw (IO.userError "actual conjunction skip")
  | ⟨_,.binary left ⟨_,.logicalOr⟩ _⟩ =>
      let a ← rawLeaf env left
      if same : a.value=.bool true then
        have old : LocalComputationEvaluatesWithCost names env [] s (.bool true) [] 4 := .pure (by rw [shape]; exact .orTrue (same ▸ a.evidence []))
        have _ := (r.evidence []).deterministic old.toRecursiveLocalComputation
      else throw (IO.userError "actual disjunction skip")
  | _ => throw (IO.userError "original lazy root")
  check (decide (r.value=.bool isOr ∧ r.cost=4 ∧ elaborateRecursiveLocalComputation? names (context .bool) s=none)) "pure/new raw overlap skips unsupported source, not checking"
private def sourceCalls (fn arg : String) : Nat → String | 0 => arg | n+1 => fn++"("++sourceCalls fn arg n++")"
private def coreCalls (fn arg : Nat) : Nat → Core.Expr | 0 => .var arg | n+1 => .apply (.var fn) (coreCalls fn arg n)
end ParsedRecursiveLazyComputations
open ParsedRecursiveLazyComputations
def frontendParsedRecursiveLazyComputationTests : IO Unit := do
  for c in [false,true] do
    for d in [false,true] do
      for isOr in [false,true] do
        let value := Core.Value.bool (if isOr then c || d else c && d); let selected := c != isOr
        let text := if isOr then " || " else " && "
        let join (l r : Core.Expr) := if isOr then Core.Expr.ifE l (.bool true) r else .ifE l r (.bool false)
        exercise ("c"++text++"d") .bool (.bool c) (.bool d) c d (join (.var 2) (.var 3)) .bool value 4 true
        for depth in [1,3,9] do
          let left := coreCalls 4 0 depth; let right := coreCalls 5 1 (depth+1)
          let leftCost := 5*depth+1; let rightCost := 5*(depth+1)+1
          for groups in [0,2] do
            exercise (wrap groups (sourceCalls "f" "x" depth++text++sourceCalls "g" "y" (depth+1))) .bool (.bool c) (.bool d) c d
              (join left right) .bool value (leftCost+(if selected then rightCost+2 else 3))
          let env := environment .bool (.bool c) (.bool d) c d
          let cp : Core.State := ⟨.ret (.bool c),[.ifBranches (if isOr then .bool true else right) (if isOr then right else .bool false) env.values],[]⟩
          check (decide (Core.runStateful (leftCost+1) (.initial (join left right) env.values [])=.outOfFuel cp ∧
            Core.runStateful 1 cp=.outOfFuel ⟨.eval (if selected then right else .bool isOr) env.values,[],[]⟩ ∧
            Core.runStateful (if selected then rightCost+1 else 2) cp=.done value [])) "genuine saved ifBranches skips or enters original right"
      let f := call 4 0; let g := call 5 1; let p := call 6 2
      for (text,core,value,cost) in [
          ("f(x) && g(y) && p(c)",Core.Expr.ifE (.ifE f g (.bool false)) p (.bool false),c && d,if c then if d then 22 else 17 else 12),
          ("f(x) || g(y) || p(c)",.ifE (.ifE f (.bool true) g) (.bool true) p,c || d,if c then 12 else if d then 17 else 22),
          ("f(x) || g(y) && !p(c)",.ifE f (.bool true) (.ifE g (.unary .boolNot p) (.bool false)),c || d,if c then 9 else if d then 24 else 17),
          ("!(f(x) && g(y)) ? x : y",.ifE (.unary .boolNot (.ifE f g (.bool false))) (.var 0) (.var 1),c,if c then 19 else 14),
          ("(f(x) || g(y)) && !false",.ifE (.ifE f (.bool true) g) (.unary .boolNot (.var 9)) (.bool false),false,if c then 14 else if d then 19 else 17),
          ("(p(c) ? maker(x) : f)(y) || p(d)",.ifE (.apply (.ifE p (call 7 0) (.var 4)) (.var 1)) (.bool true) (call 6 3),d,(if c then 19 else 14)+(if d then 3 else 8))] do
        exercise text .bool (.bool c) (.bool d) c d core .bool (.bool value) cost
      exercise "true || false" .bool (.bool c) (.bool d) c d (.ifE (.var 8) (.bool true) (.var 9)) .bool (.bool true) 4 true
  for isOr in [false,true] do
    skippedOverlap isOr
    for right in ["Missing","f()","(f(x),y)"] do
      let s ← parsed ("p(c)"++(if isOr then " || " else " && ")++right)
      let r ← actual (environment .bool (.bool false) (.bool true) isOr false) s
      have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨r.cost,r.evidence []⟩
      check (decide (r.value=.bool isOr ∧ r.cost=9 ∧ elaborateRecursiveLocalComputation? names (context .bool) s=none)) "recursive skip needs no whole-source certificate"
    exercise (if isOr then "p(c) || f(x)" else "p(c) && f(x)") .bool (.word (Core.Word.ofNatModulo 23)) (.bool false) (!isOr) false
      (if isOr then .ifE (call 6 2) (.bool true) (call 4 0) else .ifE (call 6 2) (call 4 0) (.bool false)) .bool (.word (Core.Word.ofNatModulo 23)) 14
  for text in ["f(x) && p(c)","p(c) || f(x)","!(p(c) && f(x))"] do
    check ((elaborateRecursiveLocalComputation? names (context .word) (← parsed text)).isNone) "either non-Bool static child remains rejected"
end Tests
