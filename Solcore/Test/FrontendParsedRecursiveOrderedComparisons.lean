import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
/-! Original comparison syntax has independent static/raw evidence and separate
literal Core/manual paths; actual captures and pending frames are retained. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveOrderedComparisons
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"OrderedComparisons",by decide⟩],by decide⟩⟩,62⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25),("true",id 90),("false",id 91),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(id 14,a),(id 15,.bool),(id 16,.bool),(foreign,.function a a),(id 9,.function a a),(id 20,.function .bool .bool),(id 25,.function a (.function a a)),(id 90,.bool),(id 91,.bool),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def environment (a : Core.Ty) (x y : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 7,x),(id 14,y),(id 15,.bool c),(id 16,.bool d),(foreign,identity a),(id 9,identity a),(id 20,identity .bool),(id 25,.closure a (.function a a) (.var 1) [identity a]),(id 90,.bool false),(id 91,.bool true),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def join (ge : Bool) (left right : Core.Expr) : Core.Expr :=
  let ordered := Core.Expr.letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))
  if ge then .unary .boolNot ordered else ordered
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-ordered-comparisons.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parser: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "original bytes/span"
  return s
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
  | ⟨span,.unary ⟨opSpan,op⟩ inner⟩ =>
      check (span.contains inner.span && span.contains opSpan && decide (span.startByte=opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+1 ∧ opSpan.endByte≤inner.span.startByte)) "original prefix bytes/order"
      let a ← statics ctx inner
      match which : op with
      | .logicalNot => if same : a.type=.bool then return ⟨.unary .boolNot a.core,.bool,by rw [shape,which]; exact .logicalNot (same ▸ a.elaboration),by rw [shape,which]; exact .logicalNot (same ▸ a.typing)⟩ else throw (IO.userError "Bool operand")
      | .bitNot => if same : a.type=.word then return ⟨.unary .wordNot a.core,.word,by rw [shape,which]; exact .bitNot (same ▸ a.elaboration),by rw [shape,which]; exact .bitNot (same ▸ a.typing)⟩ else throw (IO.userError "Word operand")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨span,.binary left ⟨opSpan,op⟩ right⟩ =>
      check (span.contains left.span && span.contains right.span && span.contains opSpan && decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+(if op = .less then 1 else 2) ∧ opSpan.endByte≤right.span.startByte)) "original operator width/children order"
      let a ← statics ctx left; let b ← statics ctx right
      match which : op with
      | .less => if same : a.type=.word ∧ b.type=.word then return ⟨a.core.wordLt b.core,.bool,
          by rw [shape,which]; exact .less (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .less (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Word comparison operands")
      | .greaterEqual => if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (a.core.wordLt b.core),.bool,
          by rw [shape,which]; exact .greaterEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .greaterEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Word comparison operands")
      | .logicalAnd => if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core b.core (.bool false),.bool,
          by rw [shape,which]; exact .logicalAnd (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .logicalAnd (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Bool logical operands")
      | .logicalOr => if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core (.bool true) b.core,.bool,
          by rw [shape,which]; exact .logicalOr (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),by rw [shape,which]; exact .logicalOr (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩ else throw (IO.userError "Bool logical operands")
      | _ => throw (IO.userError "outside fixed comparison fixture")
  | ⟨span,.conditional guard question yes colon no⟩ =>
      check (span.contains guard.span && span.contains yes.span && span.contains no.span && span.contains question && span.contains colon &&
        decide (guard.span.endByte≤question.startByte ∧ question.endByte=question.startByte+1 ∧ question.endByte≤yes.span.startByte ∧
          yes.span.endByte≤colon.startByte ∧ colon.endByte=colon.startByte+1 ∧ colon.endByte≤no.span.startByte)) "original question/colon order"
      let g ← statics ctx guard; let a ← statics ctx yes; let b ← statics ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "whole conditional types")
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
      | some t,some n =>
          have r : ResolvesLocalExpression names s (.var localId) := by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
          have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
          return ⟨.var n,t,(LocalComputationElaborates.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty).toRecursiveLocalComputation,.pure (r.reflects_type ty)⟩
      | _,_ => throw (IO.userError "caller row")
    | _ => throw (IO.userError "caller name")
  | _ => throw (IO.userError "outside original source fixture")
termination_by sizeOf s
private structure RawLeaf (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store s value store 1
private def rawLeaf (env : Resolved.Environment) (s : Syntax.Expr) : IO (RawLeaf env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match found : env.lookup? localId with
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
  | ⟨_,.unary ⟨_,op⟩ inner⟩ =>
      let a ← actual env inner
      match which : op, v : a.value with
      | .logicalNot,.bool b => return ⟨.bool (!b),a.cost+2,fun store => by rw [shape,which]; exact .logicalNot (v ▸ a.evidence store)⟩
      | .bitNot,.word w => return ⟨.word w.bitNot,a.cost+2,fun store => by rw [shape,which]; exact .bitNot (v ▸ a.evidence store)⟩
      | _,_ => throw (IO.userError "actual unary payload")
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
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
  | ⟨_,.binary left ⟨_,op⟩ right⟩ =>
      let a ← actual env left; let b ← actual env right
      match lv : a.value, rv : b.value with
      | .word l,.word r =>
          match which : op with
          | .less => return ⟨.bool (decide (l<r)),a.cost+b.cost+9,fun store => by rw [shape,which]; exact .less (lv ▸ a.evidence store) (rv ▸ b.evidence store)⟩
          | .greaterEqual => return ⟨.bool (!(decide (l<r))),a.cost+b.cost+11,fun store => by rw [shape,which]; exact .greaterEqual (lv ▸ a.evidence store) (rv ▸ b.evidence store)⟩
          | _ => throw (IO.userError "actual fixed operator")
      | _,_ => throw (IO.userError "actual Word comparison operands")
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
    | .binary op left right =>
      let a ← manual fuel env left; let b ← manual fuel env right
      match applied : op.apply a.value b.value with
      | some v => return ⟨v,a.cost+b.cost+3,fun store k => by rw [shape]; exact CostStepComposition.binary (a.evidence store _) (b.evidence store _) applied⟩
      | _ => throw (IO.userError "manual binary")
    | .letE bound body =>
      let a ← manual fuel env bound; let b ← manual fuel (a.value::env) body
      return ⟨b.value,a.cost+b.cost+2,fun store k => by rw [shape]; exact CostStepComposition.letE (a.evidence store _) (b.evidence store k)⟩
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
private def skippedOverlap (ge : Bool) : IO Unit := do
  let s ← parsed (if ge then "(c ? x : Missing) >= y" else "(c ? x : Missing) < y")
  let w := Core.Word.ofNatModulo; let env := environment .word (.word (w 17)) (.word (w 5)) true false; let fresh ← actual env s
  match shape : s with
  | ⟨_,.binary ⟨_,.group ⟨_,.conditional guard _ yes _ _⟩⟩ ⟨_,op⟩ right⟩ =>
      let g ← rawLeaf env guard; let l ← rawLeaf env yes; let r ← rawLeaf env right
      if same : g.value=.bool true ∧ l.value=.word (w 17) ∧ r.value=.word (w 5) then
        match which : op with
        | .less =>
            have old : LocalComputationEvaluatesWithCost names env [] s (.bool false) [] 14 := .pure (by rw [shape,which]; exact .less (.group (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence []))) (same.2.2 ▸ r.evidence []))
            have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
        | .greaterEqual =>
            have old : LocalComputationEvaluatesWithCost names env [] s (.bool true) [] 16 := .pure (by rw [shape,which]; exact .greaterEqual (.group (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence []))) (same.2.2 ▸ r.evidence []))
            have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
        | _ => throw (IO.userError "original comparison")
      else throw (IO.userError "old actual leaves")
  | _ => throw (IO.userError "original skipped conditional")
  check (decide (fresh.value=.bool ge ∧ fresh.cost=(if ge then 16 else 14) ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "pure/new ordered overlap skips unknown syntax"
private def sourceCalls (fn arg : String) : Nat → String | 0 => arg | n+1 => fn++"("++sourceCalls fn arg n++")"
private def coreCalls (fn arg : Nat) : Nat → Core.Expr | 0 => .var arg | n+1 => .apply (.var fn) (coreCalls fn arg n)
end ParsedRecursiveOrderedComparisons
open ParsedRecursiveOrderedComparisons
def frontendParsedRecursiveOrderedComparisonTests : IO Unit := do
  let w := Core.Word.ofNatModulo; let hi := 2^255; let max := Core.wordModulus-1
  for (l,r,lt,ge) in [(0,0,false,true),(0,max,true,false),(max,0,false,true),(hi,hi,false,true),
      (hi,hi-1,false,true),(hi-1,hi,true,false),(17,5,false,true),(5,17,true,false)] do
    for isGe in [false,true] do
      let token := if isGe then " >= " else " < "; let overhead := if isGe then 11 else 9; let value := if isGe then ge else lt
      exercise ("x"++token++"y") .word (.word (w l)) (.word (w r)) false false (join isGe (.var 0) (.var 1)) .bool (.bool value) (2+overhead) true
      for depth in [1,3,8] do
        let left := coreCalls 4 0 depth; let right := coreCalls 5 1 (depth+1); let lc := 5*depth+1; let rc := 5*(depth+1)+1
        for groups in [0,2] do
          exercise (wrap groups (sourceCalls "f" "x" depth++token++sourceCalls "g" "y" (depth+1))) .word (.word (w l)) (.word (w r)) false false (join isGe left right) .bool (.bool value) (lc+rc+overhead)
        let env := (environment .word (.word (w l)) (.word (w r)) false false).values
        let k := if isGe then [Core.Frame.unaryApply .boolNot] else []; let gt := Core.Expr.binary .wordGt (.var 0) (.var 1)
        let first : Core.State := ⟨.ret (.word (w l)),.letBody (.letE (right.weakenAt 0) gt) env::k,[]⟩
        let second : Core.State := ⟨.ret (.word (w r)),.letBody gt (.word (w l)::env)::k,[]⟩
        let applied : Core.State := ⟨.ret (.word (w l)),.binaryApply .wordGt (.word (w r))::k,[]⟩
        check (decide (Core.runStateful (lc+1+(if isGe then 1 else 0)) (.initial (join isGe left right) env [])=.outOfFuel first ∧
          Core.runStateful (rc+2) first=.outOfFuel second ∧ Core.runStateful 5 second=.outOfFuel applied ∧
          Core.runStateful 1 applied=(if isGe then .outOfFuel ⟨.ret (.bool lt),k,[]⟩ else .done (.bool lt) []) ∧
          Core.runStateful (if isGe then 2 else 1) applied=.done (.bool value) [])) "genuine first/second let, swapped gt and optional boolNot checkpoints"
  for isGe in [false,true] do
    skippedOverlap isGe
    let token := if isGe then " >= " else " < "; let overhead := if isGe then 11 else 9; let base := join isGe (call 4 0) (call 5 1)
    for c in [false,true] do
      for (text,core,type,value,cost) in [
          ("!(f(x)"++token++"g(y))",Core.Expr.unary .boolNot base,Core.Ty.bool,Core.Value.bool (!isGe),14+overhead),
          ("f(x)"++token++"g(y) && p(c)",.ifE base (call 6 2) (.bool false),.bool,.bool (isGe && c),if isGe then 31 else 24),
          ("f(x)"++token++"g(y) || p(c)",.ifE base (.bool true) (call 6 2),.bool,.bool (isGe || c),if isGe then 26 else 29),
          ("f(x)"++token++"g(y) ? x : y",.ifE base (.var 0) (.var 1),.word,.word (w (if isGe then 17 else 5)),15+overhead),
          ("(p(c) ? maker(x) : f)(y)"++token++"g(x)",join isGe (.apply (.ifE (call 6 2) (call 7 0) (.var 4)) (.var 1)) (call 5 0),.bool,.bool (!isGe),(if c then 25 else 20)+overhead)] do
        exercise text .word (.word (w 17)) (.word (w 5)) c false core type value cost
    exercise ("~f(x)"++token++"g(y)") .word (.word (w max)) (.word (w 0)) false false (join isGe (.unary .wordNot (call 4 0)) (call 5 1)) .bool (.bool isGe) (14+overhead)
    let s ← parsed ("(c ? f(x) : Missing)"++token++"g(y)"); let raw ← actual (environment .word (.word (w 17)) (.word (w 5)) true false) s
    have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨raw.cost,raw.evidence []⟩
    check (decide (raw.value=.bool isGe ∧ raw.cost=15+overhead ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "raw chosen call succeeds despite unselected unknown"
  for a in [Core.Ty.bool,.unit,.namedData ⟨77⟩,.cell .word,.function .word .word] do
    for text in ["f(x) < g(y)","f(x) >= g(y)"] do check ((elaborateRecursiveLocalComputation? names (context a) (← parsed text)).isNone) "value-free non-Word comparison"
  for text in ["f(x) < p(c)","p(c) >= f(x)","f(Missing) < y","x >= Missing"] do
    check ((elaborateRecursiveLocalComputation? names (context .word) (← parsed text)).isNone) "unchanged wrong-type/name/unextended boundaries"
  let precedence ← parsed "f(x) < g(y) != f(y) >= g(x)"
  check (match precedence.value with | .binary ⟨_,.binary _ ⟨_,.less⟩ _⟩ ⟨_,.notEqual⟩ ⟨_,.binary _ ⟨_,.greaterEqual⟩ _⟩ => true | _ => false) "ordered precedence above nonassociative inequality"
  for text in ["f(x) < g(y) < x","f(x) >= g(y) >= x","f(x) < g(y) >= x"] do
    let file : Syntax.SourceFile := ⟨⟨.main,"recursive-ordered-comparisons.sol"⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "nonassociative lexer")
    check (match Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) with | .ok _ next => !(tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) | .reject _ _ => true | .invariant _ => false) "nonassociative ordered rejection"
end Tests
