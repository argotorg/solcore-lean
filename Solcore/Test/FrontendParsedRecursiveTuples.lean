import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
/-! Original tuple syntax has independent static/raw evidence and separate literal
Core/manual paths. No environment typing is assumed; opaque values/captures stay literal. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveTuples
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Tuples",by decide⟩],by decide⟩⟩,64⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25),("true",id 90),("false",id 91),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(id 14,a),(id 15,.bool),(id 16,.bool),(foreign,.function a a),(id 9,.function a a),(id 20,.function .bool .bool),(id 25,.function a (.function a a)),(id 90,.bool),(id 91,.bool),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def environment (a : Core.Ty) (x y : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 7,x),(id 14,y),(id 15,.bool c),(id 16,.bool d),(foreign,identity a),(id 9,identity a),(id 20,identity .bool),(id 25,.closure a (.function a a) (.var 1) [identity a]),(id 90,.bool false),(id 91,.bool true),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def flatArity : Syntax.Expr → Nat
  | ⟨_,.group inner⟩ => flatArity inner | ⟨_,.tuple elements⟩ => elements.elements.length | _ => 0
private def tupleRanges (span tupleSpan : Syntax.SourceSpan) (elements : List Syntax.Expr) : Bool :=
  span.contains tupleSpan && elements.all (tupleSpan.contains ·.span) &&
    (elements.zip elements.tail).all (fun (a,b) => decide (a.span.endByte<b.span.startByte))
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-tuples.sol"⟩,text⟩
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
  | ⟨span,.tuple ⟨tupleSpan,[]⟩⟩ =>
      check (tupleRanges span tupleSpan []) "empty tuple spans"
      return ⟨.unit,.unit,by rw [shape]; exact .pure .unit .unit .unit,by rw [shape]; exact .pure .unit⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (tupleRanges span tupleSpan [left,right]) "original binary tuple elements"
      let a ← statics ctx left; let b ← statics ctx right
      return ⟨.pair a.core b.core,.product a.type b.type,by rw [shape]; exact .pair a.elaboration b.elaboration,by rw [shape]; exact .pair a.typing b.typing⟩
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      check (tupleRanges span tupleSpan (first::second::third::rest)) "original flat tuple elements/order"
      let a ← statics ctx first; let b ← statics ctx ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩
      return ⟨.pair a.core b.core,.product a.type b.type,by rw [shape]; exact .many a.elaboration b.elaboration,by rw [shape]; exact .many a.typing b.typing⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
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
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,1,fun _ => by rw [shape]; exact .pure .unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← actual env left; let b ← actual env right
      return ⟨.pair a.value b.value,a.cost+b.cost+3,fun store => by rw [shape]; exact .pair (a.evidence store) (b.evidence store)⟩
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      let a ← actual env first; let b ← actual env ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩
      return ⟨.pair a.value b.value,a.cost+b.cost+3,fun store => by rw [shape]; exact .many (a.evidence store) (b.evidence store)⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured => match found : (a.value::captured)[n]? with
        | some v => return ⟨v,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
        | _ => throw (IO.userError "actual captured index")
      | _ => throw (IO.userError "fixture body")
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
    | .unit => return ⟨.unit,1,fun _ _ => by rw [shape]; exact .cons .unit .refl⟩
    | .pair left right =>
      let a ← manual fuel env left; let b ← manual fuel env right
      return ⟨.pair a.value b.value,a.cost+b.cost+3,fun store _ => by rw [shape]; simpa only [Nat.add_assoc] using Core.Steps.cons .enterPair ((a.evidence store _).trans (.cons .enterPairRight ((b.evidence store _).trans (.cons .applyPair .refl))))⟩
    | .bool b => return ⟨.bool b,1,fun _ _ => by rw [shape]; exact .cons .bool .refl⟩
    | .var n => match found : env[n]? with
      | some v => return ⟨v,1,fun _ _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | _ => throw (IO.userError "manual variable")
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
private def overlap : IO Unit := do
  let s ← parsed "(c ? x : Missing,y)"; let w := Core.Word.ofNatModulo
  let env := environment .word (.word (w 17)) (.word (w 5)) true false; let fresh ← actual env s
  match shape : s with
  | ⟨_,.tuple ⟨_,[⟨_,.conditional guard _ yes _ _⟩,right]⟩⟩ =>
      let g ← rawLeaf env guard; let l ← rawLeaf env yes; let r ← rawLeaf env right
      if same : g.value=.bool true ∧ l.value=.word (w 17) ∧ r.value=.word (w 5) then
        have old : LocalComputationEvaluatesWithCost names env [] s (.pair (.word (w 17)) (.word (w 5))) [] 8 :=
          .pure (by rw [shape]; exact .pair (.ifTrue (same.1 ▸ g.evidence []) (same.2.1 ▸ l.evidence [])) (same.2.2 ▸ r.evidence []))
        have _ := (fresh.evidence []).deterministic old.toRecursiveLocalComputation
      else throw (IO.userError "old leaves")
  | _ => throw (IO.userError "original pure-overlap tuple")
  check (decide (fresh.value=.pair (.word (w 17)) (.word (w 5)) ∧ fresh.cost=8 ∧ elaborateRecursiveLocalComputation? names (context .word) s=none)) "old pure/new pair overlap despite unselected unknown"
private def foldTuple {α : Type} (empty : α) (pair : α → α → α) : List α → α
  | [] => empty | [last] => last | first::second::rest => pair first (foldTuple empty pair (second::rest))
private def sourceCalls (fn arg : String) : Nat → String | 0 => arg | n+1 => fn++"("++sourceCalls fn arg n++")"
private def coreCalls (fn arg : Nat) : Nat → Core.Expr | 0 => .var arg | n+1 => .apply (.var fn) (coreCalls fn arg n)
private structure Item where
  text : String
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
private def checkpoints (a : Core.Ty) (x y : Core.Value) (left right : Core.Expr)
    (leftValue rightValue : Core.Value) (lc rc : Nat) : IO Unit := do
  let env := (environment a x y true false).values; let store := [Core.Value.cellRef .word 37]
  let first : Core.State := ⟨.ret leftValue,[.pairRight right env],store⟩
  let second : Core.State := ⟨.ret rightValue,[.pairApply leftValue],store⟩
  check (decide (Core.runStateful (lc+1) (.initial (.pair left right) env store)=.outOfFuel first ∧
    Core.runStateful (rc+1) first=.outOfFuel second ∧ Core.runStateful 1 second=.done (.pair leftValue rightValue) store ∧
    Core.runStateful (rc+2) first=.done (.pair leftValue rightValue) store)) "genuine pairRight saved caller/opaque left and pairApply residual"
end ParsedRecursiveTuples
open ParsedRecursiveTuples
def frontendParsedRecursiveTupleTests : IO Unit := do
  let w := fun n => Core.Value.word (Core.Word.ofNatModulo n)
  let storedClosure := Core.Value.closure .word .word (.loadCell (.var 1)) [.cellRef .word 91]
  for (a,x,y) in [(Core.Ty.word,w 17,w 5),(.bool,.bool false,.bool true),(.unit,.unit,.unit),
      (.namedData ⟨77⟩,.constructed ⟨⟨77⟩,3⟩ (.cellRef .word 89),.constructed ⟨⟨77⟩,4⟩ storedClosure),
      (.cell .word,.cellRef .word 5,.cellRef .word 8),(.function .word .word,storedClosure,.closure .word .word (.var 0) [.bool false])] do
    exercise "()" a x y true false .unit .unit .unit 1 true
    for text in ["(x)","(x,)"] do
      check (match (← parsed text).value with | .group _ => true | _ => false) "singleton source is a group"
      exercise text a x y true false (.var 0) a x 1 true
    exercise "(f(f(x)),)" a x y true false (.apply (.var 4) (call 4 0)) a x 11
    exercise "(x,y,c,())" a x y true false (.pair (.var 0) (.pair (.var 1) (.pair (.var 2) .unit))) (.product a (.product a (.product .bool .unit))) (.pair x (.pair y (.pair (.bool true) .unit))) 13 true
    exercise "(f(x),g(y))" a x y true false (.pair (call 4 0) (call 5 1)) (.product a a) (.pair x y) 15
    exercise "((f(x),g(y)),c)" a x y true false (.pair (.pair (call 4 0) (call 5 1)) (.var 2)) (.product (.product a a) .bool) (.pair (.pair x y) (.bool true)) 19
    exercise "(f(x),(g(y),c))" a x y true false (.pair (call 4 0) (.pair (call 5 1) (.var 2))) (.product a (.product a .bool)) (.pair x (.pair y (.bool true))) 19
    checkpoints a x y (call 4 0) (call 5 1) x y 6 6
    for c in [false,true] do
      exercise "((p(c)?maker(x):f)(y),f(x))" a x y c false (.pair (.apply (.ifE (call 6 2) (call 7 0) (.var 4)) (.var 1)) (call 4 0)) (.product a a) (.pair y x) (if c then 28 else 23)
      exercise "(c?f(x):g(y),c)" a x y c false (.pair (.ifE (.var 2) (call 4 0) (call 5 1)) (.var 2)) (.product a .bool) (.pair (if c then x else y) (.bool c)) 13
  for length in [2,3,4,9] do
    for depth in [1,3,7] do
      let items : List Item := (List.range length).map fun i =>
        if i%4=0 then ⟨sourceCalls "f" "x" depth,coreCalls 4 0 depth,.word,w 17,5*depth+1⟩
        else if i%4=1 then ⟨sourceCalls "g" "y" (depth+1),coreCalls 5 1 (depth+1),.word,w 5,5*(depth+1)+1⟩
        else if i%4=2 then ⟨"p(c)",call 6 2,.bool,.bool true,6⟩ else ⟨"()",.unit,.unit,.unit,1⟩
      let core := foldTuple .unit Core.Expr.pair (items.map (·.core))
      let type := foldTuple .unit Core.Ty.product (items.map (·.type))
      let value := foldTuple .unit Core.Value.pair (items.map (·.value))
      let cost := (items.map (·.cost)).sum+3*(length-1)
      for trailing in [false,true] do
        for groups in [0,2] do
          let text := wrap groups ("("++String.intercalate ", " (items.map (·.text))++(if trailing then "," else "")++")")
          check (decide (flatArity (← parsed text)=length)) "original flat element count, trailing comma and outer groups"
          exercise text .word (w 17) (w 5) true false core type value cost
      match items with
      | first::rest =>
          checkpoints .word (w 17) (w 5) first.core (foldTuple .unit Core.Expr.pair (rest.map (·.core))) first.value
            (foldTuple .unit Core.Value.pair (rest.map (·.value))) first.cost ((rest.map (·.cost)).sum+3*(rest.length-1))
      | _ => throw (IO.userError "generated nonempty tuple")
  overlap
  exercise "(true,false)" .word (w 17) (w 5) true false (.pair (.var 8) (.var 9)) (.product .bool .bool) (.pair (.bool false) (.bool true)) 5 true
  let rawSource ← parsed "(f(x),c?g(y):Missing,p(c))"; let raw ← actual (environment .word (w 17) (w 5) true false) rawSource
  have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨raw.cost,raw.evidence []⟩
  check (decide (raw.value=.pair (w 17) (.pair (w 5) (.bool true)) ∧ raw.cost=27 ∧ elaborateRecursiveLocalComputation? names (context .word) rawSource=none)) "recursive chosen component versus whole missing tail"
  let base ← parsed "x"; let singleton : Syntax.Expr := ⟨base.span,.tuple ⟨base.span,[base]⟩⟩
  have noRaw {env : Resolved.Environment} {st final : Core.Store} {v : Core.Value}
      (h : RecursiveLocalComputationEvaluates names env st singleton v final) : False := by
    dsimp only [singleton] at h; cases h with | pure child => cases child
  check ((elaborateRecursiveLocalComputation? names (context .word) singleton).isNone && (resolveLocalExpression? names singleton).isNone) "manual singleton AST stays unsupported"
  for text in ["(Missing,f(x))","(f(x),Missing)","(f(x),y,Missing)","(f(c),x)","(x,x(c))",
      "(c?(x,y):x,f(x))","[f(x),y]","(f(x),y).x","(f(x),y)[x]"] do
    check ((elaborateRecursiveLocalComputation? names (context .word) (← parsed text)).isNone) "whole strict children/name/type/unextended boundaries"
  for text in ["(Missing,f(x))","(f(x),Missing)","(f(x),y,Missing)"] do
    let s ← parsed text
    let success ← try let _ ← actual (environment .word (w 17) (w 5) true false) s; pure true catch _ => pure false
    check (!success) "every tuple child is actually strict"
end Tests
