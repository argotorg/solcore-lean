import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
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
