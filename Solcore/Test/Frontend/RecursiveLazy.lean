import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.LocalComputation

/-!
# Recursive lazy tests

Recursive lazy computations, their function entries and their migrations.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveLazyComputations
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveLazyFunctionEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveLazyEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveLazyEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-lazy-entries.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) ("complete original bytes: "++text)
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte≤annotation.span.startByte)) "original parameter fields/order"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters types (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,
            by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate original parameter")
      else throw (IO.userError "original argument type mismatch")
  | _,_ => throw (IO.userError "original parameter arity")
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .bool b => return ⟨.bool b,s,1,fun _ => by rw [original]; exact .cons .bool .refl⟩
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .ifE condition yes no =>
        let c ← path n condition env s
        match cv : c.value with
        | .bool true =>
            let b ← path n yes env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifTrue (cv ▸ c.evidence _) (b.evidence _)⟩
        | .bool false =>
            let b ← path n no env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifFalse (cv ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual guard shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Certificate (Elaborates : Core.Expr → Core.Ty → Prop) (Evaluates : Core.Value → Core.Store → Nat → Prop) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : Elaborates core type
  raw : Evaluates value final cost
private abbrev Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) :=
  Certificate (RecursiveLocalComputationElaborates s.names s.context source) (RecursiveLocalComputationEvaluatesWithCost s.names env store source)
private structure Static (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates s.names s.context source core type
private def branch (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Static s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id with
          | some t,some i => return ⟨.var i,t,by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _,_ => throw (IO.userError "original static row missing")
      | none => throw (IO.userError "original static name missing")
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte≤argsSpan.startByte)) "unselected branch original call ranges"
      let f ← branch s fn; let a ← branch s arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration)⟩
          else throw (IO.userError "static branch argument differs")
      | _ => throw (IO.userError "static branch function differs")
  | _ => throw (IO.userError "outside independent static branch")
termination_by sizeOf source
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span &&
        decide (fn.span.endByte ≤ argsSpan.startByte)) "original recursive child order"
      let f ← child s env store fn; let a ← child s env f.final arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) a.final
            return ⟨.apply f.core a.core,output,b.value,b.final,f.cost+a.cost+b.cost+3,
              by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
              by rw [original]; exact .application (fv ▸ f.raw) a.raw (b.evidence [])⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | ⟨_,.binary left ⟨opSpan,op⟩ right⟩ =>
      check (source.span.contains left.span && source.span.contains right.span && source.span.contains opSpan &&
        decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte≤right.span.startByte)) "original logical children/operator order"
      let l ← child s env store left; let r ← branch s right
      if typed : l.type=.bool ∧ r.type=.bool then
        match which : op with
        | .logicalAnd =>
            have el : RecursiveLocalComputationElaborates s.names s.context source (.ifE l.core r.core (.bool false)) .bool := by
              rw [original,which]; exact .logicalAnd (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration)
            match actual : l.value with
            | .bool true =>
                let rhs ← child s env l.final right
                return ⟨.ifE l.core r.core (.bool false),.bool,rhs.value,rhs.final,l.cost+rhs.cost+2,el,by rw [original,which]; exact .andTrue (actual ▸ l.raw) rhs.raw⟩
            | .bool false => return ⟨.ifE l.core r.core (.bool false),.bool,.bool false,l.final,l.cost+3,el,by rw [original,which]; exact .andFalse (actual ▸ l.raw)⟩
            | _ => throw (IO.userError "non-Bool actual left")
        | .logicalOr =>
            have el : RecursiveLocalComputationElaborates s.names s.context source (.ifE l.core (.bool true) r.core) .bool := by
              rw [original,which]; exact .logicalOr (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration)
            match actual : l.value with
            | .bool true => return ⟨.ifE l.core (.bool true) r.core,.bool,.bool true,l.final,l.cost+3,el,by rw [original,which]; exact .orTrue (actual ▸ l.raw)⟩
            | .bool false =>
                let rhs ← child s env l.final right
                return ⟨.ifE l.core (.bool true) r.core,.bool,rhs.value,rhs.final,l.cost+rhs.cost+2,el,by rw [original,which]; exact .orFalse (actual ▸ l.raw) rhs.raw⟩
            | _ => throw (IO.userError "non-Bool actual left")
        | _ => throw (IO.userError "outside fixed lazy fixture")
      else throw (IO.userError "original logical operands are not Bool")
  | ⟨_,.identifier name⟩ =>
      let e ← branch s source
      match named : s.names.lookup? name.value with
      | some id =>
          match actual : env.lookup? id with
          | some v => return ⟨e.core,e.type,v,store,1,e.elaboration,by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | none => throw (IO.userError "original actual row missing")
      | none => throw (IO.userError "original actual name missing")
  | _ => throw (IO.userError "outside fixture expression")
termination_by sizeOf source
private abbrev Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) :=
  Certificate (RecursiveComputationReturnTreeElaborates types owner s source) (RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source)
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement spans"
  match original : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | _ => throw (IO.userError "outside original singleton return body")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) : IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧
            source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return meaning")
  | _ => throw (IO.userError "original singleton return clause")
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function lazy(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word)]
  let args := [f,g,x,y]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body; let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[y.value,x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("y",⟨owner,3⟩,y.type,y.value),("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩; let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled := ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store = some (output,Core.runStateful fuel (.initial core [y.value,x.value,g.value,f.value] store)) := by
      rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.raw b.elaboration ids []
    check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old entry remains None"
    for fuel in List.range (cost+2) do
      have _ := whole fuel s
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "whole full result/tag"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted; have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRecursiveComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "genuine saved state/residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
    return prepared
  else throw (IO.userError "independent exact Core/type")
private def reader : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.loadCell (.var 1)) [.cellRef .bool 1],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (location : Nat) : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .bool location],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arg (value : Bool) : TypedRuntimeArgument := ⟨.bool,.bool value,.bool⟩
end RecursiveLazyEntries
open RecursiveLazyEntries
def frontendParsedRecursiveLazyFunctionEntryTests : IO Unit := do
  let left := Core.Expr.apply (.var 3) (.var 1); let right := Core.Expr.apply (.var 2) (.var 0)
  let f := writer 0; let g := writer 1
  for disjunction in [false,true] do
    let source ← bodySource (if disjunction then "return f(x) || g(y);" else "return f(x) && g(y);"); let core := if disjunction then Core.Expr.ifE left (.bool true) right else .ifE left right (.bool false)
    for flag in [false,true] do
      let selected := flag != disjunction; let x := arg flag
      for rhs in [false,true] do
        discard <| verify source f g x (arg rhs) .bool core [.bool (!flag),.bool (!rhs)] [.bool flag,.bool (if selected then rhs else !rhs)] (.bool (if selected then rhs else flag)) (if selected then 32 else 18)
      discard <| verify source f reader x (arg false) .bool core [.bool (!flag),w 23] [.bool flag,w 23] (if selected then w 23 else .bool flag) (if selected then 25 else 18)
      unless selected do
        discard <| verify source f reader x (arg false) .bool core [.bool (!flag)] [.bool flag] (.bool flag) 18
    let selected := !disjunction
    discard <| verify source g f (arg selected) (arg disjunction) .bool core [.bool disjunction,.bool selected] [.bool disjunction,.bool selected] (.bool disjunction) 32
  let source ← bodySource "return f(x) && g(y);"; let core := Core.Expr.ifE left right (.bool false)
  let x := arg true; let y := arg false
  let prepared ← verify source f reader x y .bool core [.bool false,w 23] [.bool true,w 23] (w 23) 25
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],f.type),(["G"],reader.type),(["X"],.bool),(["Y"],.bool),(["R"],.bool),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [f,reader,x,y]
  let frames := [Core.Frame.ifBranches right (.bool false) env]
  let cp : Core.State := ⟨.ret (.bool true),frames,[.bool true,w 23]⟩
  check (decide (run 16 [.bool false,w 23]=some (.bool,.outOfFuel cp) ∧ Core.runStateful 9 cp=.done (w 23) [.bool true,w 23] ∧ run 25 [.bool false,w 23]=some (.bool,.done (w 23) [.bool true,w 23]))) "actual Word RHS success retains Bool entry tag after genuine ifBranches"
  let rightEnv := [y.value,.cellRef .bool 1]
  let missingCp : Core.State := ⟨.eval (.var 1) rightEnv,[.loadCellApply],[.bool true]⟩
  let missing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .bool 1),[.loadCellApply],[.bool true]⟩
  check (decide (run 23 [.bool false]=some (.bool,.outOfFuel missingCp) ∧ run 24 [.bool false]=some (.bool,missing) ∧ Core.runStateful 1 missingCp=missing ∧ runRecursiveComputationFunction? types owner source [f,reader,arg false,y] 18 [.bool true]=some (.bool,.done (.bool false) [.bool false]))) "selected missing RHS versus skipped missing RHS preserves left update"
  let badLeft : TypedRuntimeArgument := ⟨f.type,.closure .bool .bool (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 3))) [.cellRef .bool 0,.cellRef .bool 2],
    .closure (.cons .cellRef (.cons .cellRef .nil)) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
  let badEnv := [(arg true).value,x.value,g.value,badLeft.value]
  let badFrames := [Core.Frame.ifBranches right (.bool false) badEnv]; let updated := [.bool true,.bool false,w 99]
  let badCp : Core.State := ⟨.ret (.cellRef .bool 2),.loadCellApply::badFrames,updated⟩
  let bad := Core.StatefulRunResult.fault (.expectedBool (w 99)) ⟨.ret (w 99),badFrames,updated⟩
  check (decide (runRecursiveComputationFunction? types owner source [badLeft,g,x,arg true] 15 [.bool false,.bool false,w 99]=some (.bool,.outOfFuel badCp) ∧ runRecursiveComputationFunction? types owner source [badLeft,g,x,arg true] 16 [.bool false,.bool false,w 99]=some (.bool,bad) ∧ Core.runStateful 1 badCp=bad)) "non-Bool left preserves left effects and never executes right writer"
  for store in [[.bool false,w 23],[.bool false,.bool true],[.bool false],[]] do
    for fuel in List.range 34 do
      check (decide (run fuel store=some (.bool,Core.runStateful fuel (.initial core env store)))) "same prepared record retains arbitrary stores and whole tag"
      match exhausted : Core.runStateful fuel (.initial core env store) with
      | .outOfFuel residual =>
          have _ := Core.runStateful_resume exhausted 40
          check (decide (run (fuel+40) store=some (.bool,Core.runStateful 40 residual))) "all genuine checkpoints resume full outcomes"
      | _ => pure ()
  for body in ["return f(x) && missing;","return f(x) || missing;","return f(x) && 1;","return 1 || g(y);"] do
    let bad ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [f,reader,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [f,reader,x,y] 50 [.bool false,w 23]=none)) "whole unselected-name and logical operand type gates"
  let wrongReturn ← parsed "function lazy(f:F,g:G,x:X,y:Y) returns(Word){return f(x) && g(y);}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.bool) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none)) "original Bool body versus declared Word"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveLazyMigrations
/-! The three former recursive-lazy rejections retain their original source,
source file, names and ordered contexts, including foreign and duplicate rows. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveLazyMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (unary : Bool) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨if unary then "Unary" else "Binary",by split <;> decide⟩],by simp⟩⟩,if unary then 58 else 56⟩
private def id (unary : Bool) (n : Nat) : Resolved.LocalId := ⟨owner unary,n⟩
private def foreign (unary : Bool) : Resolved.LocalId :=
  ⟨{owner unary with declarationIndex := 91},302⟩
private def names (unary : Bool) : LocalNameTable :=
  if unary then [("x",id true 7),("y",id true 14),("c",id true 15),("d",id true 16),
    ("f",foreign true),("g",id true 9),("p",id true 20),("maker",id true 25),("f",id true 88)]
  else [("x",id false 7),("f",foreign false),("g",id false 9),("y",id false 14),("c",id false 15),("f",id false 88)]
private def context (unary : Bool) : Resolved.Context :=
  if unary then [(id true 7,.bool),(id true 14,.bool),(id true 15,.bool),(id true 16,.bool),
    (foreign true,.function .bool .bool),(id true 9,.function .bool .bool),(id true 20,.function .bool .bool),
    (id true 25,.function .bool (.function .bool .bool)),(foreign true,.bool)]
  else [(id false 7,.bool),(foreign false,.function .bool .bool),(id false 9,.function .bool .bool),
    (id false 14,.bool),(id false 15,.bool),(foreign false,.bool)]

private structure Static (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates table ctx s core type
  typing : RecursiveLocalComputationHasType table ctx s type

private def statics (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) :
    IO (Static table ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n =>
              have r : ResolvesLocalExpression table s (.var localId) := by
                rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
              have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
              return ⟨.var n,t,.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty,.pure (r.reflects_type ty)⟩
          | _,_ => throw (IO.userError "original ordered context")
      | _ => throw (IO.userError "original names")
  | ⟨_,.group inner⟩ =>
      let a ← statics table ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← statics table ctx fn; let a ← statics table ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.unary ⟨_,.logicalNot⟩ inner⟩ =>
      let a ← statics table ctx inner
      if same : a.type=.bool then return ⟨.unary .boolNot a.core,.bool,
        by rw [shape]; exact .logicalNot (same ▸ a.elaboration),by rw [shape]; exact .logicalNot (same ▸ a.typing)⟩
      else throw (IO.userError "Bool prefix")
  | ⟨_,.binary left ⟨_,.logicalAnd⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core b.core (.bool false),.bool,
        by rw [shape]; exact .logicalAnd (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .logicalAnd (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Bool conjunction")
  | ⟨_,.binary left ⟨_,.logicalOr⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core (.bool true) b.core,.bool,
        by rw [shape]; exact .logicalOr (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .logicalOr (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Bool disjunction")
  | _ => throw (IO.userError "migration original shape")
termination_by sizeOf s

end ParsedRecursiveLazyMigrations
open ParsedRecursiveLazyMigrations

def frontendParsedRecursiveLazyMigrationTests : IO Unit := do
  for (unary,text,expected) in [
      (false,"f(x) && g(y)",Core.Expr.ifE (.apply (.var 1) (.var 0)) (.apply (.var 2) (.var 3)) (.bool false)),
      (false,"f(x) || g(y)",.ifE (.apply (.var 1) (.var 0)) (.bool true) (.apply (.var 2) (.var 3))),
      (true,"!(f(x) && c)",.unary .boolNot (.ifE (.apply (.var 4) (.var 0)) (.var 2) (.bool false)))] do
    let file : Syntax.SourceFile := ⟨⟨.main,if unary then "recursive-unary.sol" else "recursive-binary.sol"⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
    let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
    check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original parsed source"
    let a ← statics (names unary) (context unary) s
    have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
    have _ := a.elaboration.core_hasType
    check (decide (a.core=expected ∧ a.type=.bool ∧
      elaborateRecursiveLocalComputation? (names unary) (context unary) s=some (expected,.bool) ∧
      elaborateLocalExpression? (names unary) (context unary) s=none ∧
      elaborateLocalComputation? (names unary) (context unary) s=none)) "exact new success and unchanged old rejections"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveLazyComputationProperties
/-! Fixed short-circuit source retains arbitrary actual RHS values and captures.
Only this explicitly store-free delay fixture has an unchanged final store. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveLazyComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Lazy", by decide⟩], by decide⟩⟩, 59⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "lazy.sol"⟩, 0, 1024⟩
private inductive Key | f | c | g | x
private def index : Key → Nat | .f => 0 | .c => 1 | .g => 2 | .x => 3
private def name : Key → String | .f => "f" | .c => "c" | .g => "g" | .x => "x"
private def typeOf : Key → Core.Ty | .f | .g => .function .bool .bool | _ => .bool
private def inputs : LocalTypeInputs := ⟨[⟨"f",id 0,.function .bool .bool⟩,⟨"c",id 1,.bool⟩,
  ⟨"g",id 2,.function .bool .bool⟩,⟨"x",id 3,.bool⟩], by change [id 0,id 1,id 2,id 3].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .x else .c)
  | n+1 => ⟨span,.call (ref (if side then .g else .f)) ⟨span,[calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 3 else 1)
  | n+1 => .apply (.var (if side then 2 else 0)) (callCore side n)
private def lazySource (isOr : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.binary left ⟨⟨span.source,500,502⟩,if isOr then .logicalOr else .logicalAnd⟩ right⟩
private def source (isOr : Bool) (n k : Nat) := lazySource isOr (calls false n) (calls true k)
private def core (isOr : Bool) (n k : Nat) : Core.Expr :=
  if isOr then .ifE (callCore false n) (.bool true) (callCore true k) else .ifE (callCore false n) (callCore true k) (.bool false)
private theorem oldLeaf (key : Key) :
    LocalComputationElaborates inputs.names inputs.context (ref key) (.var (index key)) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leafTyped (key : Key) :
    RecursiveLocalComputationHasType inputs.names inputs.context (ref key) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callElab (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (calls side n) (callCore side n) .bool := by
  induction n with
  | zero => cases side <;> exact (oldLeaf _).toRecursiveLocalComputation
  | succ n ih => exact .application (by cases side <;> exact (oldLeaf _).toRecursiveLocalComputation) ih
private theorem callTyped (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType inputs.names inputs.context (calls side n) .bool := by
  induction n with
  | zero => cases side <;> exact leafTyped _
  | succ n ih => exact .application (by cases side <;> exact leafTyped _) ih
private theorem elaboration (isOr : Bool) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source isOr n k) (core isOr n k) .bool := by
  cases isOr
  · exact .logicalAnd (callElab false n) (callElab true k)
  · exact .logicalOr (callElab false n) (callElab true k)
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  choice : Bool
  right : Core.Value
  leftDelay : Nat
  rightDelay : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def actual (v : Actual) : Key → Core.Value
  | .f => .closure .bool .bool (delay v.leftDelay 0) v.leftCapture
  | .c => .bool v.choice
  | .g => .closure .bool .bool (delay v.rightDelay 0) v.rightCapture
  | .x => v.right
private def env (v : Actual) : Resolved.Environment :=
  [(id 0,actual v .f),(id 1,.bool v.choice),(id 2,actual v .g),(id 3,v.right)]
private def childValue (v : Actual) (side : Bool) := if side then v.right else Core.Value.bool v.choice
private def childDelay (v : Actual) (side : Bool) := if side then v.rightDelay else v.leftDelay
private def childCapture (v : Actual) (side : Bool) := if side then v.rightCapture else v.leftCapture
private def charge (n m : Nat) := n*(3*m+5)+1
private def selected (isOr choice : Bool) := choice != isOr
private def result (isOr : Bool) (v : Actual) := if selected isOr v.choice then v.right else Core.Value.bool v.choice
private def cost (isOr : Bool) (v : Actual) (n k : Nat) :=
  charge n v.leftDelay + if selected isOr v.choice then charge k v.rightDelay+2 else 3
private theorem atomCost (v : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost inputs.names (env v) s (ref key) (actual v key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (m i : Nat) (environment : Core.Environment) (value : Core.Value) (s : Core.Store) (frames : List Core.Frame)
    (found : environment[i]? = some value) :
    Core.Steps (3*m+1) ⟨.eval (delay m i) environment,frames,s⟩ ⟨.ret value,frames,s⟩ := by
  induction m generalizing i environment frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      cases environment with
      | nil => simp at found
      | cons head rest =>
          simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i+1) (head::head::rest) frames (by simpa using found))))
private theorem callCost (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (calls side n) (childValue v side) s (charge n (childDelay v side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [calls,charge,actual,childValue] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost v .c s)
      · simpa [calls,charge,actual,childValue] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost v .x s)
  | succ n ih =>
      have count : charge (n+1) (childDelay v side) = 1+charge n (childDelay v side)+(3*childDelay v side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (.pure (by cases side <;> exact atomCost v _ s)) ih
        (delayed (childDelay v side) 0 (childValue v side::childCapture v side) (childValue v side) s [] rfl)
private theorem callPath (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (childDelay v side)) ⟨.eval (callCore side n) (env v).values,frames,s⟩ ⟨.ret (childValue v side),frames,s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n+1) (childDelay v side) = 1+charge n (childDelay v side)+(3*childDelay v side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (childDelay v side) 0 (childValue v side::childCapture v side) (childValue v side) s [] rfl)
private theorem counted (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr n k) (result isOr v) s (cost isOr v n k) := by
  cases isOr <;> cases chosen : v.choice
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay] using RecursiveLocalComputationEvaluatesWithCost.andFalse (by simpa [childValue,childDelay,chosen] using callCost v false n s)
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using RecursiveLocalComputationEvaluatesWithCost.andTrue (by simpa [childValue,childDelay,chosen] using callCost v false n s) (callCost v true k s)
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using RecursiveLocalComputationEvaluatesWithCost.orFalse (by simpa [childValue,childDelay,chosen] using callCost v false n s) (callCost v true k s)
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay] using RecursiveLocalComputationEvaluatesWithCost.orTrue (by simpa [childValue,childDelay,chosen] using callCost v false n s)
private theorem manual (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isOr v n k) ⟨.eval (core isOr n k) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  cases isOr <;> cases chosen : v.choice
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifFalse (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (.cons .bool .refl)
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifTrue (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (callPath v true k s frames)
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifFalse (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (callPath v true k s frames)
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifTrue (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (.cons .bool .refl)

theorem original_bool_static_children (isOr : Bool) (n k : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source isOr n k) = some (core isOr n k,.bool) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source isOr n k) .bool ∧ Core.HasType inputs.context.values (core isOr n k) .bool := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source isOr n k) .bool := by
    cases isOr; exact .logicalAnd (callTyped false n) (callTyped true k); exact .logicalOr (callTyped false n) (callTyped true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration isOr n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration isOr n k).core_hasType⟩

theorem actual_rhs_value_and_exact_paths (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env v) s (source isOr n k) (result isOr v) s ∧
    Core.Evaluates (env v).values s (core isOr n k) (result isOr v) s ∧
    Core.Steps (cost isOr v n k) ⟨.eval (core isOr n k) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted isOr v n k s⟩
  have fromManual := ((elaboration isOr n k).evaluatesWithCost_iff_steps (environment := env v) rfl).mpr (manual isOr v n k s [])
  exact ⟨raw,((elaboration isOr n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration isOr n k) rfl frames⟩

theorem actual_value_store_and_cost_unique (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr n k) value finalStore steps) :
    value = result isOr v ∧ finalStore = s ∧ steps = cost isOr v n k :=
  other.deterministic (counted isOr v n k s)

theorem skipped_original_rhs_has_no_raw_premise (isOr : Bool) (v : Actual) (n : Nat) (s : Core.Store)
    (skipped : Syntax.Expr) (choice : v.choice = isOr) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (lazySource isOr (calls false n) skipped) (.bool isOr) s (charge n v.leftDelay+3) := by
  cases isOr
  · exact .andFalse (by simpa [childValue,childDelay,choice] using callCost v false n s)
  · exact .orTrue (by simpa [childValue,childDelay,choice] using callCost v false n s)

theorem arbitrary_caller_insertion (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env v).values) :
    RecursiveLocalComputationFragment ((core isOr n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost isOr v n k) ⟨.eval ((core isOr n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  have fragment := (elaboration isOr n k).core_fragment
  have original := Core.steps_from_initial_sound (manual isOr v n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost isOr v n k) (.initial (core isOr n k) (leading++suffix) s) (.final (result isOr v) s) := by rw [split]; exact manual isOr v n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩

private def checkpoint (isOr : Bool) (v : Actual) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.bool v.choice),[if isOr then .ifBranches (.bool true) (callCore true k) (env v).values else .ifBranches (callCore true k) (.bool false) (env v).values],s⟩
theorem genuine_left_completed_checkpoint (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n v.leftDelay+1) (.initial (core isOr n k) (env v).values s) = .outOfFuel (checkpoint isOr v k s) := by
  have beforeChoice : Core.Steps (charge n v.leftDelay+1) (.initial (core isOr n k) (env v).values s) (checkpoint isOr v k s) := by
    cases isOr <;> exact .cons .enterIf (callPath v false n s _)
  cases isOr <;> cases chosen : v.choice
  all_goals apply Core.runStateful_outOfFuel_complete beforeChoice; apply Core.advance_next_iff.mpr; simp only [checkpoint,chosen,Bool.false_eq_true,↓reduceIte]; first | exact .chooseFalse | exact .chooseTrue

theorem all_fuels_residual_and_full_resume (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core isOr n k) (env v).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core isOr n k) (env v).values s) = .done (result isOr v) s ↔ cost isOr v n k ≤ fuel) ∧
    spent < cost isOr v n k ∧ Core.Steps (cost isOr v n k-spent) cp (.final (result isOr v) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core isOr n k) (env v).values s) := by
  have path := manual isOr v n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem selected_rhs_cost_unbounded_but_skipping_ignores_it (isOr : Bool) (limit : Nat) (value : Core.Value) (captures : Core.Environment) (s : Core.Store) :
    (∃ v : Actual, RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 1 1) value s (cost isOr v 1 1) ∧ limit < cost isOr v 1 1) ∧
    ∀ v : Actual, v.choice = isOr → ∀ k m, cost isOr {v with rightDelay := m} 1 k = charge 1 v.leftDelay+3 := by
  constructor
  · let v : Actual := ⟨!isOr,value,0,limit,[],captures⟩
    refine ⟨v,?_,?_⟩
    · simpa [result,selected,v] using counted isOr v 1 1 s
    · cases isOr <;> simp [cost,selected,charge,v] <;> omega
  · intro v choice k m; simp [cost,selected,choice]

private def body (isOr : Bool) (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source isOr n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (isOr : Bool) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isOr n k) (.letE (core isOr n k) (.var 0)) .bool :=
  .inferred (elaboration isOr n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr n k) (result isOr v) s (cost isOr v n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted isOr v n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isOr v n k+3) ⟨.eval (.letE (core isOr n k) (.var 0)) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual isOr v n k s (.letBody (.var 0) (env v).values::frames)) (.cons (.var rfl) .refl)

private theorem oldElab (isOr : Bool) :
    LocalComputationElaborates inputs.names inputs.context (source isOr 0 0) (core isOr 0 0) .bool := by
  cases oldLeaf .c with
  | pure leftResolution leftLowered leftTyped =>
      cases oldLeaf .x with
      | pure rightResolution rightLowered rightTyped =>
          cases isOr
          · exact .pure (.logicalAnd leftResolution rightResolution) (.ifE leftLowered rightLowered .bool) (.ifE leftTyped rightTyped .bool)
          · exact .pure (.logicalOr leftResolution rightResolution) (.ifE leftLowered .bool rightLowered) (.ifE leftTyped .bool rightTyped)
      | application child => cases child
  | application child => cases child
private theorem oldCost (isOr : Bool) (v : Actual) (s : Core.Store) :
    LocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 := by
  cases isOr <;> cases chosen : v.choice
  · simpa [source,lazySource,result,selected,chosen,calls] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.andFalse (by simpa [actual,chosen] using atomCost v .c s))
  · simpa [source,lazySource,result,selected,chosen,calls,actual] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.andTrue (by simpa [actual,chosen] using atomCost v .c s) (atomCost v .x s))
  · simpa [source,lazySource,result,selected,chosen,calls,actual] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.orFalse (by simpa [actual,chosen] using atomCost v .c s) (atomCost v .x s))
  · simpa [source,lazySource,result,selected,chosen,calls] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.orTrue (by simpa [actual,chosen] using atomCost v .c s))

theorem old_pure_overlap_and_original_body_embeddings (isOr : Bool) (v : Actual) (s : Core.Store) :
    LocalComputationElaborates inputs.names inputs.context (source isOr 0 0) (core isOr 0 0) .bool ∧
    LocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 ∧
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 ∧
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isOr 0 0) (.letE (core isOr 0 0) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr 0 0) (result isOr v) s 7 := by
  have new : RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 := by
    simpa [cost,charge] using counted isOr v 0 0 s
  have same := new.deterministic (oldCost isOr v s).toRecursiveLocalComputation
  have originalStatic : LocalComputationReturnTreeElaborates [] owner inputs (body isOr 0 0) (.letE (core isOr 0 0) (.var 0)) .bool :=
    .inferred (by change ¬"r" ∈ ["f","c","g","x"]; decide) (oldElab isOr)
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have originalCost : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr 0 0) (result isOr v) s 7 :=
    .inferred (oldCost isOr v s) (.expression (.pure (.identifier .head .head)))
  exact ⟨oldElab isOr,oldCost isOr v s,same.2.2 ▸ new,originalStatic.toRecursiveComputationReturnTree,originalCost.toRecursiveComputationReturnTree⟩

theorem shared_body_original_source_and_actual_cost (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body isOr n k) = some (.letE (core isOr n k) (.var 0),.bool) ∧
    Core.HasType inputs.context.values (.letE (core isOr n k) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr n k) (result isOr v) s (cost isOr v n k+3) ∧
    Core.Steps (cost isOr v n k+3) ⟨.eval (.letE (core isOr n k) (.var 0)) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab isOr n k) (environment := env v) rfl).mpr (bodyManual isOr v n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab isOr n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab isOr n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost isOr v n k s) (bodyElab isOr n k) rfl frames⟩

end Tests.FrontendRecursiveLazyComputation
end
