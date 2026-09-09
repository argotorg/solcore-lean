import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
/-! Original parsed operators have independent static/raw certificates and fixed
Core paths. Primitive expected results are supplied separately from those certificates. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveBinaryComputations
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Binary",by decide⟩],by decide⟩⟩,56⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("f",foreign),("g",id 9),("y",id 14),("c",id 15),("f",id 88)]
private def context (a : Core.Ty) : Resolved.Context := [(id 7,a),(foreign,.function a a),(id 9,.function a a),(id 14,a),(id 15,.bool),(foreign,.bool)]
private def identity : Core.Value := .closure .word .word (.var 0) [.bool true]
private def environment (x y : Core.Word) : Resolved.Environment := [(id 7,.word x),(foreign,identity),(id 9,identity),(id 14,.word y),(id 15,.bool true),(foreign,.bool false)]
private def w := Core.Word.ofNatModulo
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def wrap : Nat → String → String | 0,s => s | n+1,s => "("++wrap n s++")"
private def operator : (source : Syntax.BinaryOp) → Option {op // DirectWordBinary source op}
  | .add => some ⟨.wordAdd,.add⟩ | .subtract => some ⟨.wordSub,.subtract⟩
  | .multiply => some ⟨.wordMul,.multiply⟩ | .divide => some ⟨.wordDiv,.divide⟩
  | .modulo => some ⟨.wordMod,.modulo⟩ | .bitAnd => some ⟨.wordAnd,.bitAnd⟩
  | .bitOr => some ⟨.wordOr,.bitOr⟩ | .bitXor => some ⟨.wordXor,.bitXor⟩
  | .greater => some ⟨.wordGt,.greater⟩ | .equal => some ⟨.wordEq,.equal⟩ | _ => none
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-binary.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing")
  let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parse: {text}")
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
          | _,_ => throw (IO.userError "original typed row")
      | _ => throw (IO.userError "original name")
  | _ => throw (IO.userError "not identifier")
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
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte≤argsSpan.startByte)) "call original children"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "function type")
  | ⟨span,.binary left ⟨opSpan,sourceOp⟩ right⟩ =>
      check (span.contains left.span && span.contains right.span && span.contains opSpan &&
        decide (left.span.endByte≤opSpan.startByte ∧ opSpan.startByte<opSpan.endByte ∧ opSpan.endByte≤right.span.startByte)) "original operator span/order"
      let some ⟨op,meaning⟩ := operator sourceOp | throw (IO.userError "outside direct operators")
      let a ← statics ctx left; let b ← statics ctx right
      if both : a.type=op.leftType ∧ b.type=op.rightType then return ⟨.binary op a.core b.core,op.resultType,
        by rw [shape]; exact .binary meaning (both.1 ▸ a.elaboration) (both.2 ▸ b.elaboration),
        by rw [shape]; exact .binary meaning (both.1 ▸ a.typing) (both.2 ▸ b.typing)⟩
      else throw (IO.userError "Word operands")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← statics ctx guard; let a ← statics ctx yes; let b ← statics ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "migration conditional types")
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
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var 0) _ => return ⟨a.value,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var rfl) .refl)⟩
      | _ => throw (IO.userError "fixture actual body")
  | ⟨_,.binary left ⟨_,sourceOp⟩ right⟩ =>
      let some ⟨op,meaning⟩ := operator sourceOp | throw (IO.userError "raw operator")
      let a ← actual env left; let b ← actual env right
      match applied : op.apply a.value b.value with
      | some v => return ⟨v,a.cost+b.cost+3,fun store => by rw [shape]; exact .binary meaning (a.evidence store) (b.evidence store) applied⟩
      | _ => throw (IO.userError "primitive actual operands")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← actual env guard
      match gv : g.value with
      | .bool true =>
          let a ← actual env yes
          return ⟨a.value,g.cost+a.cost+2,fun store => by rw [shape]; exact .ifTrue (gv ▸ g.evidence store) (a.evidence store)⟩
      | .bool false =>
          let b ← actual env no
          return ⟨b.value,g.cost+b.cost+2,fun store => by rw [shape]; exact .ifFalse (gv ▸ g.evidence store) (b.evidence store)⟩
      | _ => throw (IO.userError "migration actual Bool guard")
  | _ => let a ← rawLeaf env s; return ⟨a.value,1,fun store => .pure (a.evidence store)⟩
termination_by sizeOf s
private theorem oldBinary {ctx : Resolved.Context} {span opSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (meaning : DirectWordBinary sourceOp op) (a : Leaf ctx left) (b : Leaf ctx right)
    (leftType : a.type=op.leftType) (rightType : b.type=op.rightType) :
    LocalComputationElaborates names ctx ⟨span,.binary left ⟨opSpan,sourceOp⟩ right⟩ (.binary op a.core b.core) op.resultType := by
  cases meaning <;> exact .pure (by constructor <;> first | exact a.resolution | exact b.resolution)
    (.binary a.lowered b.lowered) (.binary (by simpa only [Core.BinaryOp.leftType,leftType] using a.typing)
      (by simpa only [Core.BinaryOp.rightType,rightType] using b.typing))
private theorem oldCost {env : Resolved.Environment} {span opSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    {x y : Core.Word} {value : Core.Value} {store : Core.Store}
    (meaning : DirectWordBinary sourceOp op)
    (a : LocalExpressionEvaluatesWithCost names env store left (.word x) store 1)
    (b : LocalExpressionEvaluatesWithCost names env store right (.word y) store 1)
    (applied : op.apply (.word x) (.word y)=some value) :
    LocalExpressionEvaluatesWithCost names env store ⟨span,.binary left ⟨opSpan,sourceOp⟩ right⟩ value store 5 := by
  cases meaning <;> simp only [Core.BinaryOp.apply,Option.some.injEq] at applied <;> subst value
  case add => exact .add a b
  case subtract => exact .subtract a b
  case multiply => exact .multiply a b
  case divide => exact .divide a b
  case modulo => exact .modulo a b
  case bitAnd => exact .bitAnd a b
  case bitOr => exact .bitOr a b
  case bitXor => exact .bitXor a b
  case greater => exact .greater a b
  case equal => exact .equal a b
private def overlap (s : Syntax.Expr) (env : Resolved.Environment) : IO Unit := do
  match shape : s with
  | ⟨_,.binary left ⟨_,sourceOp⟩ right⟩ =>
      let some ⟨op,meaning⟩ := operator sourceOp | throw (IO.userError "overlap op")
      have _ := directWordBinary?_iff.mp (directWordBinary?_iff.mpr meaning)
      let a ← leaf (context .word) left; let b ← leaf (context .word) right
      let ar ← rawLeaf env left; let br ← rawLeaf env right; let r ← actual env s
      if both : a.type=op.leftType ∧ b.type=op.rightType then
        have original := oldBinary meaning a b both.1 both.2
        have oldElab : LocalComputationElaborates names (context .word) s (.binary op a.core b.core) op.resultType := by rw [shape]; exact original
        have _ := elaborateRecursiveLocalComputation?_iff.mpr oldElab.toRecursiveLocalComputation
        check (decide (elaborateLocalComputation? names (context .word) s=some (.binary op a.core b.core,op.resultType))) "old/new static overlap"
        match av : ar.value,bv : br.value with
        | .word x,.word y =>
            if applied : op.apply (.word x) (.word y)=some r.value then
              for store in [[],[Core.Value.bool false]] do
                have old : LocalComputationEvaluatesWithCost names env store s r.value store 5 := .pure (by simpa only [shape] using oldCost meaning (av ▸ ar.evidence store) (bv ▸ br.evidence store) applied)
                have _ := (r.evidence store).deterministic old.toRecursiveLocalComputation
                check (decide (r.cost=5)) "pure/binary distinct derivations same cost"
            else throw (IO.userError "overlap actual result")
        | _,_ => throw (IO.userError "overlap Word values")
      else throw (IO.userError "overlap types")
  | _ => throw (IO.userError "overlap original root")
private def exercise (text : String) (x y : Core.Word) (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (manual : ∀ store k, Core.Steps cost ⟨.eval core (environment x y).values,k,store⟩ ⟨.ret value,k,store⟩) : IO Unit := do
  let s ← parsed text; let env := environment x y; let p ← statics (context .word) s; let r ← actual env s
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost then
    have e : RecursiveLocalComputationElaborates names (context .word) s core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr e)
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
    have _ := recursiveLocalComputationHasType_iff_elaborates.mpr ⟨core,e⟩
    have _ := e.core_hasType
    check (decide (elaborateRecursiveLocalComputation? names (context .word) s=some (core,type) ∧ names.lookup? "f"=some foreign)) "fixed Core/type/first-match"
    for store in [[],[Core.Value.bool true,.word (w 71)]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2] using r.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mp raw
      have coreRaw := (e.evaluates_iff rfl).mp raw
      have _ := (e.evaluates_iff rfl).mpr coreRaw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps rfl).mpr (manual store []))
      have _ := (e.evaluatesWithCost_iff_steps rfl).mp counted
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e rfl pending
      for fuel in List.range (cost+2) do
        have _ := (manual store []).runStateful_done_iff (fuel := fuel)
        match outcome : Core.runStateful fuel (.initial core env.values store) with
        | .done v st => check (decide (cost≤fuel ∧ v=value ∧ st=store)) "literal result/threshold"
        | .outOfFuel cp =>
            have _ := (manual store []).residual_of_outOfFuel outcome
            check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) (.initial core env.values store))) "genuine checkpoint/full replay"
        | .fault _ _ => throw (IO.userError "fixed successful path fault")
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
          have fixedCost : n=cost := ((paths []).1.final_unique (by simpa only [same,env,Core.State.final] using manual store [])).1
          exact fixedCost ▸ paths
        have _ := (paired pending).2
        check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "inserted pending endpoint"
  else throw (IO.userError "independent static/raw/manual result differs")
private def vector (token : String) (op : Core.BinaryOp) (x y : Core.Word) (value : Core.Value) : IO Unit := do
  if applied : op.apply (.word x) (.word y)=some value then
    let left := Core.Expr.apply (.var 1) (call 2 0); let right := call 2 3
    let original ← parsed ("f(g(x)) "++token++" g(y)")
    check (decide (elaborateLocalExpression? names (context .word) original=none ∧ elaborateLocalComputation? names (context .word) original=none)) "all direct tags retain old nested rejection"
    have nested (store k) : Core.Steps 20 ⟨.eval (.binary op left right) (environment x y).values,k,store⟩ ⟨.ret value,k,store⟩ :=
      CostStepComposition.binary (CostStepComposition.apply (.cons (.var rfl) .refl)
        (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl))
        (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) applied
    for depth in [0,2,9] do
      exercise (wrap depth ("f(g(x)) "++token++" g(y)")) x y (.binary op left right) op.resultType value 20 nested
      exercise (wrap depth ("x "++token++" y")) x y (.binary op (.var 0) (.var 3)) op.resultType value 5
        (fun _ _ => CostStepComposition.binary (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) applied)
    overlap (← parsed ("x "++token++" y")) (environment x y)
    for store in [[],[Core.Value.unit]] do
      check (decide (Core.runStateful 12 (.initial (.binary op left right) (environment x y).values store)=
        .outOfFuel ⟨.ret (.word x),[.binaryRight op right (environment x y).values],store⟩)) "left completed before right; original saved environment"
    for a in [Core.Ty.unit,.namedData ⟨77⟩,.cell .word,.function (.namedData ⟨9⟩) (.namedData ⟨9⟩)] do
      let inner ← parsed "f(g(x))"; let c ← statics (context a) inner
      have _ := elaborateRecursiveLocalComputation?_iff.mpr c.elaboration
      check (decide (c.type=a ∧ c.core=left)) "nominal child static without actual inhabitant"
      let s ← parsed ("f(g(x)) "++token++" g(y)")
      check ((elaborateRecursiveLocalComputation? names (context a) s).isNone) "non-Word binary operands"
  else throw (IO.userError "fixed primitive expectation")
end ParsedRecursiveBinaryComputations
open ParsedRecursiveBinaryComputations
def frontendParsedRecursiveBinaryComputationTests : IO Unit := do
  for (token,op,value) in [("+",Core.BinaryOp.wordAdd,Core.Value.word (w 22)),("-",.wordSub,.word (w 12)),("*",.wordMul,.word (w 85)),
      ("/",.wordDiv,.word (w 3)),("%",.wordMod,.word (w 2)),("&",.wordAnd,.word (w 1)),("|",.wordOr,.word (w 21)),("^",.wordXor,.word (w 20)),
      (">",.wordGt,.bool true),("==",.wordEq,.bool false)] do vector token op (w 17) (w 5) value
  for (token,op,x,y,value) in [("+",Core.BinaryOp.wordAdd,Core.Word.maximum,w 1,Core.Value.word (w 0)),
      ("-",.wordSub,w 0,w 1,.word Core.Word.maximum),("*",.wordMul,Core.Word.maximum,w 2,.word (w (Core.wordModulus-2))),
      ("/",.wordDiv,w 17,w 0,.word (w 0)),("%",.wordMod,w 17,w 0,.word (w 0)),
      (">",.wordGt,w 5,w 17,.bool false),("==",.wordEq,w 17,w 17,.bool true)] do vector token op x y value
  let ternary := Core.Expr.ifE (.var 4) (call 1 0) (.var 3)
  exercise "c ? f(x) : y" (w 17) (w 5) ternary .word (.word (w 17)) 9 (fun _ _ =>
    CostStepComposition.ifTrue (.cons (.var rfl) .refl)
      (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)))
  let original ← parsed "c ? f(x) : y"
  check (decide (elaborateLocalExpression? names (context .word) original=none ∧ elaborateLocalComputation? names (context .word) original=none)) "conditional migration retains old rejection"
  for text in ["f(x) < g(y)","f(x) <= g(y)","f(x) >= g(y)","f(x) != g(y)","(f(x),y)","~f(x)","f()","f(x,y)","f(Missing) + y"] do
    let s ← parsed text
    check (decide (elaborateRecursiveLocalComputation? names (context .word) s=none ∧ elaborateLocalComputation? names (context .word) s=none)) "retained nonrecursive root boundary"
  for text in ["f(x) && g(y)","f(x) || g(y)","!f(x)"] do
    let inner ← parsed "f(x)"; let c ← statics (context .bool) inner
    check (decide (c.type=.bool)) "independent valid Bool child"
    let s ← parsed text; check ((elaborateRecursiveLocalComputation? names (context .bool) s).isNone) "lazy/unary root still pure-only"
end Tests
