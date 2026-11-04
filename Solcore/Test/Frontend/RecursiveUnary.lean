import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RuntimeComputationFunction

/-!
# Recursive unary tests

Recursive unary computations and their function entries.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveUnaryComputations
/-! Original prefix children carry independent static/raw certificates. Fixed Core,
values and costs are checked against separately constructed continuation paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveUnaryComputations
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Unary",by decide⟩],by decide⟩⟩,58⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(id 14,a),(id 15,.bool),(id 16,.bool),(foreign,.function a a),(id 9,.function a a),(id 20,.function .bool .bool),(id 25,.function a (.function a a)),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def environment (a : Core.Ty) (x y : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 7,x),(id 14,y),(id 15,.bool c),(id 16,.bool d),(foreign,identity a),(id 9,identity a),(id 20,identity .bool),(id 25,.closure a (.function a a) (.var 1) [identity a]),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-unary.sol"⟩,text⟩
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
  | ⟨span,.unary ⟨opSpan,.bitNot⟩ inner⟩ =>
      check (span.contains inner.span && span.contains opSpan && decide (span.startByte=opSpan.startByte ∧ opSpan.endByte=opSpan.startByte+1 ∧ opSpan.endByte≤inner.span.startByte ∧ span.endByte=inner.span.endByte)) "original complement prefix bytes/order"
      let a ← statics ctx inner
      if same : a.type=.word then return ⟨.unary .wordNot a.core,.word,
        by rw [shape]; exact .bitNot (same ▸ a.elaboration),by rw [shape]; exact .bitNot (same ▸ a.typing)⟩
      else throw (IO.userError "Word operand")
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
  | _ => let a ← leaf ctx s; return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing,.pure (a.resolution.reflects_type a.typing)⟩
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
  | ⟨_,.unary ⟨_,.bitNot⟩ inner⟩ =>
      let a ← actual env inner
      match v : a.value with
      | .word w => return ⟨.word w.bitNot,a.cost+2,fun store => by rw [shape]; exact .bitNot (v ▸ a.evidence store)⟩
      | _ => throw (IO.userError "actual Word")
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var n) captured =>
          match found : (a.value::captured)[n]? with
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
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let s ← parsed text; let env := environment a x y c d; let p ← statics (context a) s; let r ← actual env s; let m ← manual 30 env.values core
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost ∧ m.value=value ∧ m.cost=cost then
    have e : RecursiveLocalComputationElaborates names (context a) s core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr e)
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
    have _ := recursiveLocalComputationHasType_iff_elaborates.mpr ⟨core,e⟩
    have _ := e.core_hasType
    check (decide (elaborateRecursiveLocalComputation? names (context a) s=some (core,type) ∧ elaborateLocalExpression? names (context a) s=none ∧ elaborateLocalComputation? names (context a) s=none)) "new exact/old None"
    for store in [[],[Core.Value.bool true,.cellRef .word 91]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2.1] using r.evidence store
      have path : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,store⟩ := by simpa only [fixed.2.2.2.2.1,fixed.2.2.2.2.2] using m.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mp raw
      have coreRaw := (e.evaluates_iff rfl).mp raw
      have _ := (e.evaluates_iff rfl).mpr coreRaw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps rfl).mpr (path []))
      have _ := (e.evaluatesWithCost_iff_steps rfl).mp counted
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
        have _ := (fragment.evaluates_insert_iff leading suffix inserted).mp changed
        have paired : ∀ k, Core.Steps cost ⟨.eval core (leading++suffix),k,store⟩ ⟨.ret value,k,store⟩ ∧
            Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),k,store⟩ ⟨.ret value,k,store⟩ := by
          obtain ⟨n,paths⟩ := fragment.insertion_paths leading suffix inserted original
          have eqCost : n=cost := ((paths []).1.final_unique (by simpa only [same,Core.State.final] using path [])).1
          exact eqCost ▸ paths
        have _ := (paired pending).2
        check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "inserted pending endpoint"
  else throw (IO.userError s!"independent certificate mismatch: {text}")
private def overlap (text : String) (a : Core.Ty) (v : Core.Value) : IO Unit := do
  let s ← parsed text; let env := environment a v v false false
  let p ← statics (context a) s; let r ← actual env s
  match shape : s with
  | ⟨_,.unary ⟨_,op⟩ inner⟩ =>
      let l ← leaf (context a) inner; let q ← rawLeaf env inner
      have compare (core type) (old : LocalComputationElaborates names (context a) s core type)
          (raw : ∀ store, LocalComputationEvaluatesWithCost names env store s r.value store 3) : IO Unit := do
        have _ := elaborateRecursiveLocalComputation?_iff.mpr old.toRecursiveLocalComputation
        have _ := elaborateRecursiveLocalComputation?_iff.mpr p.elaboration
        check (decide (p.core=core ∧ p.type=type ∧ elaborateLocalComputation? names (context a) s=some (core,type))) "old pure/new unary distinct static derivations"
        for store in [[],[Core.Value.unit]] do
          have _ := (r.evidence store).deterministic (raw store).toRecursiveLocalComputation
          check (decide (r.cost=3)) "old pure/new unary exact cost"
      match named : op with
      | .logicalNot =>
          match val : q.value with
          | .bool b =>
              if same : l.type=.bool ∧ r.value=.bool (!b) then
                compare (.unary .boolNot l.core) .bool (by rw [shape,named]; exact .pure (.logicalNot l.resolution) (.unary l.lowered) (.unary (by simpa only [Core.UnaryOp.operandType,same.1] using l.typing)))
                  (fun store => by rw [same.2,shape,named]; exact .pure (.logicalNot (val ▸ q.evidence store)))
              else throw (IO.userError "logical overlap type/value")
          | _ => throw (IO.userError "logical overlap payload")
      | .bitNot =>
          match val : q.value with
          | .word w =>
              if same : l.type=.word ∧ r.value=.word w.bitNot then
                compare (.unary .wordNot l.core) .word (by rw [shape,named]; exact .pure (.bitNot l.resolution) (.unary l.lowered) (.unary (by simpa only [Core.UnaryOp.operandType,same.1] using l.typing)))
                  (fun store => by rw [same.2,shape,named]; exact .pure (.bitNot (val ▸ q.evidence store)))
              else throw (IO.userError "complement overlap type/value")
          | _ => throw (IO.userError "complement overlap payload")
  | _ => throw (IO.userError "overlap root")
private def sourceCalls : Nat → String | 0 => "x" | n+1 => "f("++sourceCalls n++")"
private def coreCalls : Nat → Core.Expr | 0 => .var 0 | n+1 => .apply (.var 4) (coreCalls n)
private def corePrefixes (op : Core.UnaryOp) : Nat → Core.Expr → Core.Expr | 0,e => e | n+1,e => .unary op (corePrefixes op n e)
end ParsedRecursiveUnaryComputations
open ParsedRecursiveUnaryComputations
def frontendParsedRecursiveUnaryComputationTests : IO Unit := do
  let w := Core.Word.ofNatModulo; let maximum := 2^256-1
  for (token,op,a,v,opposite) in [('!',Core.UnaryOp.boolNot,Core.Ty.bool,Core.Value.bool false,Core.Value.bool true),
      ('!',.boolNot,.bool,.bool true,.bool false),('~',.wordNot,.word,.word (w 0),.word (w maximum)),
      ('~',.wordNot,.word,.word (w maximum),.word (w 0)),('~',.wordNot,.word,.word (w 17),.word (w (maximum-17)))] do
    overlap (String.singleton token++"x") a v
    for calls in [1,3,7] do
      for prefixes in [1,2,7] do
        for groups in [0,2] do
          exercise (wrap groups (String.ofList (List.replicate prefixes token)++sourceCalls calls)) a v v false false
            (corePrefixes op prefixes (coreCalls calls)) a (if prefixes%2=0 then v else opposite) (5*calls+1+2*prefixes)
    for c in [false,true] do
      for (text,core,value,cost) in [
          (String.singleton token++"(c ? f(x) : y)",Core.Expr.unary op (.ifE (.var 2) (call 4 0) (.var 1)),opposite,if c then 11 else 6),
          (String.singleton token++"maker(x)(y)",.unary op (.apply (call 7 0) (.var 1)),opposite,13),
          ("!p(c) ? f(x) : g(y)",.ifE (.unary .boolNot (call 6 2)) (call 4 0) (call 5 1),v,16)] do
        exercise text a v v c false core a value cost
    let env := environment a v v false false; let core := Core.Expr.unary op (call 4 0)
    for store in [[],[Core.Value.bool false]] do
      let cp : Core.State := ⟨.ret v,[.unaryApply op],store⟩
      check (decide (Core.runStateful 7 (.initial core env.values store)=.outOfFuel cp ∧ Core.runStateful 1 cp=.done opposite store)) "saved actual unaryApply checkpoint"
  for b in [false,true] do
    exercise "f(!g(x))" .bool (.bool b) (.bool (!b)) false false (.apply (.var 4) (.unary .boolNot (call 5 0))) .bool (.bool (!b)) 13
    for c in [false,true] do
      exercise "!f(x) ? x : y" .bool (.bool b) (.bool (!b)) c false (.ifE (.unary .boolNot (call 4 0)) (.var 0) (.var 1)) .bool (.bool false) 11
  for a in [Core.Ty.unit,.namedData ⟨77⟩,.cell .word,.function (.namedData ⟨9⟩) (.namedData ⟨11⟩)] do
    let source ← parsed "!p(c) ? f(x) : y"; let p ← statics (context a) source
    have _ := p.elaboration.core_hasType
    check (decide (p.core=.ifE (.unary .boolNot (call 6 2)) (call 4 0) (.var 1) ∧ p.type=a)) "value-free nominal/Cell/function branches"
    for text in ["!f(x)","~f(x)"] do
      check ((elaborateRecursiveLocalComputation? names (context a) (← parsed text)).isNone) "non Bool/Word recursive operand"
  for (a,text) in [(Core.Ty.word,"!f(x)"),(.bool,"~f(x)"),(.word,"~Missing"),(.bool,"!Missing"),(.word,"~f()")] do
    check ((elaborateRecursiveLocalComputation? names (context a) (← parsed text)).isNone) "wrong type/name/unsupported root"
  let rawSource ← parsed "!(c ? f(x) : Missing)"
  let raw ← actual (environment .bool (.bool false) (.bool true) true false) rawSource
  have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨raw.cost,raw.evidence []⟩
  check (decide (raw.value=.bool true ∧ raw.cost=11 ∧ elaborateRecursiveLocalComputation? names (context .bool) rawSource=none)) "raw selected success does not check missing branch"
  let skipped ← parsed "!(c ? x : Missing)"; let env := environment .bool (.bool false) (.bool true) true false; let counted ← actual env skipped
  match shape : skipped with
  | ⟨_,.unary ⟨_,.logicalNot⟩ ⟨_,.group ⟨_,.conditional guard _ yes _ _⟩⟩⟩ =>
      let g ← rawLeaf env guard; let x ← rawLeaf env yes
      if values : g.value=.bool true ∧ x.value=.bool false then
        have old : LocalComputationEvaluatesWithCost names env [] skipped (.bool true) [] 6 := .pure (by rw [shape]; exact .logicalNot (.group (.ifTrue (values.1 ▸ g.evidence []) (values.2 ▸ x.evidence []))))
        have _ := (counted.evidence []).deterministic old.toRecursiveLocalComputation
        check (decide (counted.cost=6 ∧ elaborateRecursiveLocalComputation? names (context .bool) skipped=none)) "pure/raw recursive unary overlap with unsupported skipped source"
      else throw (IO.userError "skipped raw values")
  | _ => throw (IO.userError "skipped original prefix/group")
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveUnaryFunctionEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveUnaryEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveUnaryEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-unary-entries.sol"⟩,text⟩
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
    | .unary op operand =>
        let a ← path n operand env s
        match applied : op.apply a.value with
        | some value => return ⟨value,a.final,a.cost+2,fun _ => by rw [original]; exact CostStepComposition.unary (a.evidence _) applied⟩
        | none => throw (IO.userError "manual unary payload")
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
  | _ => throw (IO.userError "outside independent static identifier")
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.group inner⟩ =>
      check (source.span.contains inner.span) "original group span"
      let a ← child s env store inner
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .group a.elaboration,by rw [original]; exact .group a.raw⟩
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
  | ⟨_,.unary ⟨opSpan,.logicalNot⟩ operand⟩ =>
      check (source.span.contains opSpan && source.span.contains operand.span && decide (opSpan.endByte≤operand.span.startByte)) "original ! prefix/operand ranges"
      let a ← child s env store operand
      if typed : a.type=.bool then
        match actual : a.value with
        | .bool b => return ⟨.unary .boolNot a.core,.bool,.bool (!b),a.final,a.cost+2,
            by rw [original]; exact .logicalNot (typed ▸ a.elaboration),by rw [original]; exact .logicalNot (actual ▸ a.raw)⟩
        | _ => throw (IO.userError "wrong actual ! payload")
      else throw (IO.userError "wrong original ! type")
  | ⟨_,.unary ⟨opSpan,.bitNot⟩ operand⟩ =>
      check (source.span.contains opSpan && source.span.contains operand.span && decide (opSpan.endByte≤operand.span.startByte)) "original ~ prefix/operand ranges"
      let a ← child s env store operand
      if typed : a.type=.word then
        match actual : a.value with
        | .word v => return ⟨.unary .wordNot a.core,.word,.word v.bitNot,a.final,a.cost+2,
            by rw [original]; exact .bitNot (typed ▸ a.elaboration),by rw [original]; exact .bitNot (actual ▸ a.raw)⟩
        | _ => throw (IO.userError "wrong actual ~ payload")
      else throw (IO.userError "wrong original ~ type")
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function unary(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word)]
  let args := [f,g,x,y]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[y.value,x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("y",⟨owner,3⟩,y.type,y.value),("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩; let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared :=
      ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled :=
      ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store =
        some (output,Core.runStateful fuel (.initial core [y.value,x.value,g.value,f.value] store)) := by
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
private def reader (t : Core.Ty) (_payload : Core.CellPayload t) (location : Nat) : TypedRuntimeArgument :=
  ⟨.function t t,.closure t t (.loadCell (.var 1)) [.cellRef t location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (t : Core.Ty) (_payload : Core.CellPayload t) (location : Nat) : TypedRuntimeArgument :=
  ⟨.function t t,.closure t t (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef t location],
    .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
end RecursiveUnaryEntries
open RecursiveUnaryEntries
def frontendParsedRecursiveUnaryFunctionEntryTests : IO Unit := do
  let f := reader .word .word 0; let g := writer .word .word 1
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩; let y : TypedRuntimeArgument := ⟨.bool,.bool false,.bool⟩
  let inner := Core.Expr.apply (.var 3) (.apply (.var 2) (.var 1))
  let core := Core.Expr.unary .wordNot inner
  let source ← bodySource "return ~f(g(x));"
  let prepared ← verify source f g x y .word core [w 23,w 99] [w 23,w 14] (.word (Core.Word.ofNatModulo 23).bitNot) 24
  for value in [Core.Word.zero,Core.Word.maximum,Core.Word.ofNatModulo 47] do
    discard <| verify source f g x y .word core [.word value,w 99] [.word value,w 14] (.word value.bitNot) 24
    discard <| verify (← bodySource "return ~~f(g(x));") f g x y .word (.unary .wordNot core) [.word value,w 99] [.word value,w 14] (.word value.bitNot.bitNot) 26
  discard <| verify source (reader .word .word 1) g x y .word core [w 23,w 99] [w 23,w 14] (.word (Core.Word.ofNatModulo 14).bitNot) 24
  discard <| verify source g f x y .word core [w 23,w 99] [w 23,w 23] (.word (Core.Word.ofNatModulo 23).bitNot) 24
  for flag in [false,true] do
    let arg : TypedRuntimeArgument := ⟨.bool,.bool (!flag),.bool⟩
    let bf := reader .bool .bool 0; let bg := writer .bool .bool 1
    discard <| verify (← bodySource "return !f(g(x));") bf bg arg y .bool (.unary .boolNot inner) [.bool flag,.bool flag] [.bool flag,.bool (!flag)] (.bool (!flag)) 24
    discard <| verify (← bodySource "return !!(f(g(x)));") bf bg arg y .bool (.unary .boolNot (.unary .boolNot inner)) [.bool flag,.bool flag] [.bool flag,.bool (!flag)] (.bool flag) 26
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],.word),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [f,g,x,y]
  let updated := [w 23,w 14]; let wrongStore := [.bool true,w 14]
  let cp : Core.State := ⟨.ret (w 23),[.unaryApply .wordNot],updated⟩
  let wrong := Core.StatefulRunResult.fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true),[.unaryApply .wordNot],wrongStore⟩
  let wrongCp : Core.State := ⟨.ret (.cellRef .word 0),[.loadCellApply,.unaryApply .wordNot],wrongStore⟩
  check (decide (run 23 [w 23,w 99]=some (.word,.outOfFuel cp) ∧ run 24 [w 23,w 99]=some (.word,.done (.word (Core.Word.ofNatModulo 23).bitNot) updated) ∧ Core.runStateful 1 cp=.done (.word (Core.Word.ofNatModulo 23).bitNot) updated)) "genuine unaryApply and one remaining transition"
  check (decide (run 22 [.bool true,w 99]=some (.word,.outOfFuel wrongCp) ∧ run 23 [.bool true,w 99]=some (.word,wrong) ∧ Core.runStateful 1 wrongCp=wrong)) "operand effects survive exact wrong-payload fault"
  let gEnv := [x.value,.cellRef .word 1]
  let suspended := [Core.Frame.storeCellValue (.var 0) gEnv,.letBody (.loadCell (.var 2)) gEnv,.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.unaryApply .wordNot]
  let missing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),suspended,[]⟩
  let missingCp : Core.State := ⟨.eval (.var 1) gEnv,suspended,[]⟩
  check (decide (run 11 []=some (.word,.outOfFuel missingCp) ∧ run 12 []=some (.word,missing) ∧ Core.runStateful 1 missingCp=missing)) "child missing-cell fault precedes unary application"
  let absentReader := reader .word .word 2
  let lateCp : Core.State := ⟨.eval (.var 1) [x.value,.cellRef .word 2],[.loadCellApply,.unaryApply .wordNot],updated⟩
  let late := Core.StatefulRunResult.fault (.invalidCellLocation 2) ⟨.ret (.cellRef .word 2),[.loadCellApply,.unaryApply .wordNot],updated⟩
  check (decide (runRecursiveComputationFunction? types owner source [absentReader,g,x,y] 21 [w 23,w 99]=some (.word,.outOfFuel lateCp) ∧ runRecursiveComputationFunction? types owner source [absentReader,g,x,y] 22 [w 23,w 99]=some (.word,late) ∧ Core.runStateful 1 lateCp=late)) "actual capture missing after argument effects keeps updated store"
  let boolSource ← bodySource "return !f(g(x));"
  let bf := reader .bool .bool 0; let bg := writer .bool .bool 1; let bx : TypedRuntimeArgument := ⟨.bool,.bool true,.bool⟩
  let bt : TypeNameTable := [(["F"],bf.type),(["G"],bg.type),(["X"],.bool),(["Y"],.bool),(["R"],.bool)]
  let boolCp : Core.State := ⟨.ret (.cellRef .bool 0),[.loadCellApply,.unaryApply .boolNot],[w 99,.bool true]⟩
  let boolFault := Core.StatefulRunResult.fault (.invalidUnaryOperand .boolNot (w 99)) ⟨.ret (w 99),[.unaryApply .boolNot],[w 99,.bool true]⟩
  check (decide (runRecursiveComputationFunction? bt owner boolSource [bf,bg,bx,y] 22 [w 99,.bool false]=some (.bool,.outOfFuel boolCp) ∧ runRecursiveComputationFunction? bt owner boolSource [bf,bg,bx,y] 23 [w 99,.bool false]=some (.bool,boolFault) ∧ Core.runStateful 1 boolCp=boolFault)) "Bool entry tag and prior effects survive actual Word payload"
  for store in [[w 23,w 99],[.bool true,w 99],[],[w 23]] do
    for fuel in List.range 27 do
      check (decide (run fuel store=some (.word,Core.runStateful fuel (.initial core env store)))) "same prepared Word/Bool/empty store preserves whole return tag"
      match exhausted : Core.runStateful fuel (.initial core env store) with
      | .outOfFuel residual =>
          have _ := Core.runStateful_resume exhausted 30
          check (decide (run (fuel+30) store=some (.word,Core.runStateful 30 residual))) "every genuine checkpoint resumes exact whole outcome"
      | _ => pure ()
  for body in ["return !f(g(x));","return ~y;","return ~missing;"] do
    let bad ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [f,g,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [f,g,x,y] 40 [w 23,w 99]=none)) "whole unary operand type/name gates"
  let wrongReturn ← parsed "function unary(f:F,g:G,x:X,y:Y) returns(Y){return ~f(g(x));}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.word) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none)) "original Word body versus declared Bool"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveUnaryComputationProperties
/-! Arbitrary original prefix/call depths retain actual delayed bodies and captures.
Store invariance below belongs only to this explicitly store-free delay fixture. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveUnaryComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Unary", by decide⟩], by decide⟩⟩, 58⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "unary.sol"⟩, 0, 1024⟩
private def ty : Bool → Core.Ty | false => .bool | true => .word
private def op : Bool → Core.UnaryOp | false => .boolNot | true => .wordNot
private def sourceOp : Bool → Syntax.UnaryOp | false => .logicalNot | true => .bitNot
private def inputs (mode : Bool) : LocalTypeInputs :=
  ⟨[⟨"f", id 0, .function (ty mode) (ty mode)⟩, ⟨"x", id 1, ty mode⟩], by change [id 0, id 1].Nodup; decide⟩
private def ref (function : Bool) : Syntax.Expr := ⟨span, .identifier ⟨span, if function then "f" else "x"⟩⟩
private def unary (mode : Bool) (child : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .unary ⟨⟨span.source, 0, 1⟩, sourceOp mode⟩ child⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref false
  | n + 1 => ⟨span, .call (ref true) ⟨span, [calls n]⟩⟩
private def callCore : Nat → Core.Expr | 0 => .var 1 | n + 1 => .apply (.var 0) (callCore n)
private def source (mode : Bool) : Nat → Nat → Syntax.Expr
  | 0, n => calls n | r + 1, n => unary mode (source mode r n)
private def core (mode : Bool) : Nat → Nat → Core.Expr
  | 0, n => callCore n | r + 1, n => .unary (op mode) (core mode r n)
private theorem oldLeaf (mode function : Bool) :
    LocalComputationElaborates (inputs mode).names (inputs mode).context (ref function)
      (.var (if function then 0 else 1)) (if function then .function (ty mode) (ty mode) else ty mode) :=
  .pure (.identifier (id := id (if function then 0 else 1)) (LocalNameTable.lookup?_iff.mp (by cases function <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases function <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases function <;> rfl)))
private theorem leafTyped (mode function : Bool) :
    RecursiveLocalComputationHasType (inputs mode).names (inputs mode).context (ref function)
      (if function then .function (ty mode) (ty mode) else ty mode) :=
  .pure (.identifier (id := id (if function then 0 else 1)) (LocalNameTable.lookup?_iff.mp (by cases function <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases function <;> rfl)))
private theorem callElab (mode : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates (inputs mode).names (inputs mode).context (calls n) (callCore n) (ty mode) := by
  induction n with
  | zero => exact (oldLeaf mode false).toRecursiveLocalComputation
  | succ n ih => exact .application (oldLeaf mode true).toRecursiveLocalComputation ih
private theorem elaboration (mode : Bool) (r n : Nat) :
    RecursiveLocalComputationElaborates (inputs mode).names (inputs mode).context (source mode r n) (core mode r n) (ty mode) := by
  induction r with
  | zero => exact callElab mode n
  | succ r ih => cases mode <;> first | exact .logicalNot ih | exact .bitNot ih
private theorem typing (mode : Bool) (r n : Nat) :
    RecursiveLocalComputationHasType (inputs mode).names (inputs mode).context (source mode r n) (ty mode) := by
  induction r with
  | zero =>
      induction n with
      | zero => exact leafTyped mode false
      | succ n ih => exact .application (leafTyped mode true) ih
  | succ r ih => cases mode <;> first | exact .logicalNot ih | exact .bitNot ih
private def delay : Nat → Nat → Core.Expr
  | 0, i => .var i | m + 1, i => .letE (.var 0) (delay m (i + 1))
private def booleanResult : Nat → Bool → Bool | 0, b => b | r + 1, b => !(booleanResult r b)
private def wordResult : Nat → Core.Word → Core.Word | 0, w => w | r + 1, w => (wordResult r w).bitNot
private def result (mode : Bool) (r : Nat) (b : Bool) (w : Core.Word) : Core.Value :=
  if mode then .word (wordResult r w) else .bool (booleanResult r b)
private def env (mode : Bool) (m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) : Resolved.Environment :=
  [(id 0, .closure (ty mode) (ty mode) (delay m 0) captures), (id 1, result mode 0 b w)]
private def charge (r n m : Nat) := 2 * r + n * (3 * m + 5) + 1
private theorem atomCost (mode function : Bool) (m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (ref function)
      (if function then .closure (ty mode) (ty mode) (delay m 0) captures else result mode 0 b w) s 1 :=
  .identifier (id := id (if function then 0 else 1)) (LocalNameTable.lookup?_iff.mp (by cases function <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases function <;> rfl))
private theorem delayed (m i : Nat) (environment : Core.Environment) (value : Core.Value) (s : Core.Store) (frames : List Core.Frame)
    (found : environment[i]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m i) environment, frames, s⟩ ⟨.ret value, frames, s⟩ := by
  induction m generalizing i environment frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      cases environment with
      | nil => simp at found
      | cons head rest =>
          simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i + 1) (head :: head :: rest) frames (by simpa using found))))
private theorem callCost (mode : Bool) (n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (calls n) (result mode 0 b w) s (charge 0 n m) := by
  induction n with
  | zero => simpa [charge, calls] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost mode false m b w captures s)
  | succ n ih =>
      have count : charge 0 (n + 1) m = 1 + charge 0 n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact .application (.pure (atomCost mode true m b w captures s)) ih
        (delayed m 0 (result mode 0 b w :: captures) (result mode 0 b w) s [] rfl)
private theorem callPath (mode : Bool) (n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge 0 n m) ⟨.eval (callCore n) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode 0 b w), frames, s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge 0 (n + 1) m = 1 + charge 0 n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _)
        (delayed m 0 (result mode 0 b w :: captures) (result mode 0 b w) s [] rfl)
private theorem counted (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode r n) (result mode r b w) s (charge r n m) := by
  induction r with
  | zero => exact callCost mode n m b w captures s
  | succ r ih =>
      have count : charge (r + 1) n m = charge r n m + 2 := by simp [charge, Nat.mul_add]; omega
      rw [count]; cases mode <;> first | exact .logicalNot ih | exact .bitNot ih
private theorem manual (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge r n m) ⟨.eval (core mode r n) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  induction r generalizing frames with
  | zero => exact callPath mode n m b w captures s frames
  | succ r ih =>
      have count : charge (r + 1) n m = charge r n m + 2 := by simp [charge, Nat.mul_add]; omega
      rw [count]; exact CostStepComposition.unary (ih _) (by cases mode <;> rfl)

theorem arbitrary_prefix_and_call_static (mode : Bool) (r n : Nat) :
    elaborateRecursiveLocalComputation? (inputs mode).names (inputs mode).context (source mode r n) = some (core mode r n, ty mode) ∧
    RecursiveLocalComputationHasType (inputs mode).names (inputs mode).context (source mode r n) (ty mode) ∧
    Core.HasType (inputs mode).context.values (core mode r n) (ty mode) :=
  ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration mode r n),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp (typing mode r n)),
    (elaboration mode r n).core_hasType⟩

theorem actual_raw_and_exact_path (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word)
    (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates (inputs mode).names (env mode m b w captures) s (source mode r n) (result mode r b w) s ∧
    Core.Evaluates (env mode m b w captures).values s (core mode r n) (result mode r b w) s ∧
    Core.Steps (charge r n m) ⟨.eval (core mode r n) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, counted mode r n m b w captures s⟩
  have fromManual := ((elaboration mode r n).evaluatesWithCost_iff_steps (environment := env mode m b w captures) rfl).mpr (manual mode r n m b w captures s [])
  exact ⟨raw, ((elaboration mode r n).evaluates_iff rfl).mp raw,
    fromManual.toStepsWithContinuation (elaboration mode r n) rfl frames⟩

theorem actual_cost_jointly_unique (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word)
    (captures : Core.Environment) (s : Core.Store) {value : Core.Value} {finalStore : Core.Store} {cost : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode r n) value finalStore cost) :
    value = result mode r b w ∧ finalStore = s ∧ cost = 2 * r + n * (3 * m + 5) + 1 :=
  other.deterministic (counted mode r n m b w captures s)

theorem pure_and_recursive_unary_overlap (mode : Bool) (m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    LocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 0) (result mode 1 b w) s 3 ∧
    RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 0) (result mode 1 b w) s 3 := by
  have old : LocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 0) (result mode 1 b w) s 3 := by
    cases mode <;> first | exact .pure (.logicalNot (atomCost false false m b w captures s)) | exact .pure (.bitNot (atomCost true false m b w captures s))
  have new := counted mode 1 0 m b w captures s
  have same := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old, same.2.2 ▸ new⟩

theorem arbitrary_caller_insertion (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading ++ suffix = (env mode m b w captures).values) :
    RecursiveLocalComputationFragment ((core mode r n).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (charge r n m) ⟨.eval ((core mode r n).weakenAt leading.length) (leading ++ inserted :: suffix), frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  have fragment := (elaboration mode r n).core_fragment
  have original := Core.steps_from_initial_sound (manual mode r n m b w captures s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (charge r n m) (.initial (core mode r n) (leading ++ suffix) s) (.final (result mode r b w) s) := by
    rw [split]; exact manual mode r n m b w captures s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length, fun frames => same ▸ (paths frames).2⟩

private def checkpoint (mode : Bool) (r : Nat) (b : Bool) (w : Core.Word) (s : Core.Store) : Core.State :=
  ⟨.ret (result mode r b w), [.unaryApply (op mode)], s⟩
theorem genuine_operand_finished_checkpoint (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    Core.runStateful (charge r n m + 1) (.initial (core mode (r + 1) n) (env mode m b w captures).values s) = .outOfFuel (checkpoint mode r b w s) := by
  have childPrefix : Core.Steps (charge r n m + 1) (.initial (core mode (r + 1) n) (env mode m b w captures).values s) (checkpoint mode r b w s) :=
    .cons .enterUnary (manual mode r n m b w captures s [.unaryApply (op mode)])
  exact Core.runStateful_outOfFuel_complete childPrefix (Core.advance_next_iff.mpr
    (Core.Transition.applyUnary (result := result mode (r + 1) b w) (by cases mode <;> rfl)))

theorem all_fuels_residual_and_full_resume (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core mode r n) (env mode m b w captures).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core mode r n) (env mode m b w captures).values s) = .done (result mode r b w) s ↔ charge r n m ≤ fuel) ∧
    spent < charge r n m ∧ Core.Steps (charge r n m - spent) cp (.final (result mode r b w) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent + additional) (.initial (core mode r n) (env mode m b w captures).values s) := by
  have path := manual mode r n m b w captures s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff, residual.1, residual.2, Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (mode : Bool) (limit : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    ∃ m, RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 1) (result mode 1 b w) s (charge 1 1 m) ∧ limit < charge 1 1 m := by
  exact ⟨limit, counted mode 1 1 limit b w captures s, by simp [charge]; omega⟩

private def body (mode : Bool) (r n : Nat) : Syntax.Block := ⟨span,
  [⟨span, .letDecl ⟨span, "r"⟩ none (some (source mode r n))⟩, ⟨span, .returnStmt (some ⟨span, .identifier ⟨span, "r"⟩⟩)⟩]⟩
private theorem bodyElab (mode : Bool) (r n : Nat) : RecursiveComputationReturnTreeElaborates [] owner (inputs mode)
    (body mode r n) (.letE (core mode r n) (.var 0)) (ty mode) :=
  .inferred (elaboration mode r n)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs mode).names (env mode m b w captures) s (body mode r n) (result mode r b w) s (charge r n m + 3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost, body, Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted mode r n m b w captures s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge r n m + 3) ⟨.eval (.letE (core mode r n) (.var 0)) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual mode r n m b w captures s (.letBody (.var 0) (env mode m b w captures).values :: frames)) (.cons (.var rfl) .refl)

theorem shared_body_original_source_and_exact_cost (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs mode) (body mode r n) = some (.letE (core mode r n) (.var 0), ty mode) ∧
    Core.HasType (inputs mode).context.values (.letE (core mode r n) (.var 0)) (ty mode) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs mode).names (env mode m b w captures) s (body mode r n) (result mode r b w) s (charge r n m + 3) ∧
    Core.Steps (charge r n m + 3) ⟨.eval (.letE (core mode r n) (.var 0)) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab mode r n) (environment := env mode m b w captures) rfl).mpr (bodyManual mode r n m b w captures s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab mode r n),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab mode r n), costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost mode r n m b w captures s) (bodyElab mode r n) rfl frames⟩

end Tests.FrontendRecursiveUnaryComputation
end
