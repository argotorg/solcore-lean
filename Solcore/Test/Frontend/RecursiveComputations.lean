import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeApplicationFunction
import Solcore.Frontend.DirectWordBinary
import Solcore.Core.Safety

/-!
# Recursive computation tests

Recursive computations: binary and local forms, bodies, effects, compilation and entries.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveBinaryComputations
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
  | ⟨_,.unary ⟨_,.logicalNot⟩ inner⟩ =>
      let a ← statics ctx inner
      if same : a.type=.bool then return ⟨.unary .boolNot a.core,.bool,
        by rw [shape]; exact .logicalNot (same ▸ a.elaboration),by rw [shape]; exact .logicalNot (same ▸ a.typing)⟩
      else throw (IO.userError "migration Bool operand")
  | ⟨_,.unary ⟨_,.bitNot⟩ inner⟩ =>
      let a ← statics ctx inner
      if same : a.type=.word then return ⟨.unary .wordNot a.core,.word,
        by rw [shape]; exact .bitNot (same ▸ a.elaboration),by rw [shape]; exact .bitNot (same ▸ a.typing)⟩
      else throw (IO.userError "migration Word operand")
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
      (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType,rightType] using b.typing))
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
  for (text,type,op) in [("~f(x)",Core.Ty.word,Core.UnaryOp.wordNot),("!f(x)",.bool,.boolNot)] do
    let s ← parsed text; let c ← statics (context type) s
    have _ := elaborateRecursiveLocalComputation?_iff.mpr c.elaboration
    check (decide (c.core=.unary op (call 1 0) ∧ c.type=type ∧ elaborateRecursiveLocalComputation? names (context type) s=some (.unary op (call 1 0),type) ∧
      elaborateLocalExpression? names (context type) s=none ∧ elaborateLocalComputation? names (context type) s=none)) "original unary exact success and old rejection"
  for text in ["f()","f(x,y)","f(Missing) + y"] do
    let s ← parsed text
    check (decide (elaborateRecursiveLocalComputation? names (context .word) s=none ∧ elaborateLocalComputation? names (context .word) s=none)) "retained nonrecursive root boundary"
  -- The two original Bool lazy cases now have independent positive migration coverage.
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveBinaryFunctionEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveBinaryEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveBinaryEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-binary-entries.sol"⟩,text⟩
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
    | .binary op left right =>
        let a ← path n left env s; let b ← path n right env a.final
        match applied : op.apply a.value b.value with
        | some v => return ⟨v,b.final,a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.binary (a.evidence _) (b.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive shape")
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
  | ⟨_,.binary left ⟨operatorSpan,tag⟩ right⟩ =>
      check (source.span.contains left.span && source.span.contains right.span && source.span.contains operatorSpan &&
        decide (left.span.endByte≤operatorSpan.startByte ∧ operatorSpan.endByte≤right.span.startByte)) "original binary child/operator byte order"
      let ⟨op,operator⟩ : Σ op, PLift (DirectWordBinary tag op) ←
        match tagAt : tag with
        | .subtract => pure ⟨.wordSub,⟨by rw [tagAt]; exact .subtract⟩⟩
        | .greater => pure ⟨.wordGt,⟨by rw [tagAt]; exact .greater⟩⟩
        | _ => throw (IO.userError "outside two independent operator fixtures")
      let a ← child s env store left; let b ← child s env a.final right
      if typed : a.type=op.leftType ∧ b.type=op.rightType then
        match applied : op.apply a.value b.value with
        | some v => return ⟨.binary op a.core b.core,op.resultType,v,b.final,a.cost+b.cost+3,
            by rw [original]; exact .binary operator.down (typed.1 ▸ a.elaboration) (typed.2 ▸ b.elaboration),
            by rw [original]; exact .binary operator.down a.raw b.raw applied⟩
        | none => throw (IO.userError "raw primitive has no successful cost")
      else throw (IO.userError "binary operand types differ")
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
      | none => throw (IO.userError "original name missing")
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
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let b ← tree types s env store ⟨span,statements⟩
      return ⟨b.core,b.type,b.value,b.final,b.cost,by rw [original]; exact .block b.elaboration,by rw [original]; exact .block b.raw⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child s env store e
      if unused : name.value ∉ s.names.map Prod.fst then
        let id := Resolved.freshLocalId owner s.ids
        let b ← tree types (s.bindFresh owner name.value a.type) ((id,a.value)::env) a.final ⟨span,rest⟩
        have raw : RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source b.value b.final (a.cost+b.cost+2) := by
          rw [original]; cases annotation <;> first | exact .inferred a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw) | exact .binding a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw)
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .inferred a.elaboration b.elaboration,raw⟩
        | some t =>
            let m ← meaning types t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .binding (same ▸ m.2.down) a.elaboration b.elaboration,raw⟩
            else throw (IO.userError "original binding annotation differs")
      else throw (IO.userError "shadowing is still excluded")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child s env store e; let b ← tree types s env a.final ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen e yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (s.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child s env store e
      if ct : c.type=.bool then
        let a ← tree types s env c.final yes; let b ← tree types s env c.final no
        if same : b.type=a.type then
          have el : RecursiveComputationReturnTreeElaborates types owner s source (.ifE c.core a.core b.core) a.type := by rw [original]; exact .conditional (ct ▸ c.elaboration) protection.down a.elaboration (same ▸ b.elaboration)
          match cv : c.value with
          | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,a.final,c.cost+a.cost+2,el,by rw [original]; exact .ifTrue (cv ▸ c.raw) a.raw⟩
          | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,b.final,c.cost+b.cost+2,el,by rw [original]; exact .ifFalse (cv ▸ c.raw) b.raw⟩
          | _ => throw (IO.userError "actual guard differs")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "static guard differs")
  | _ => throw (IO.userError "outside original mixed body fixture")
termination_by sizeOf source
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function recursive(f:F,g:G,x:X) returns(R){"++body++"}")
private def verify (source : Syntax.FunctionDecl) (f g x : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output),(["Word"],.word)]
  let args := [f,g,x]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
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
        some (output,Core.runStateful fuel (.initial core [x.value,g.value,f.value] store)) := by
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
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
end RecursiveBinaryEntries
open RecursiveBinaryEntries
def frontendParsedRecursiveBinaryFunctionEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  let call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
  let sub := Core.Expr.binary .wordSub (call 2 0) (call 1 0)
  let source ← bodySource "return f(x)-g(x);"
  let prepared ← verify source reader writer x .word sub [w 23] [w 14] (w 9) 26
  discard <| verify source writer reader x .word sub [w 23] [w 14] (w 0) 26
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],reader.type),(["G"],writer.type),(["X"],.word),(["R"],.word),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [reader,writer,x]
  let between : Core.State := ⟨.ret (w 23),[.binaryRight .wordSub (call 1 0) env],[w 23]⟩
  let last : Core.State := ⟨.ret (w 14),[.binaryApply .wordSub (w 23)],[w 14]⟩
  check (decide (run 9 [w 23]=some (.word,.outOfFuel between) ∧ run 25 [w 23]=some (.word,.outOfFuel last) ∧ Core.runStateful 17 between=.done (w 9) [w 14] ∧ Core.runStateful 1 last=.done (w 9) [w 14])) "original binaryRight/binaryApply saved captures/stores"
  let badLast : Core.State := ⟨.ret (w 14),[.binaryApply .wordSub (.bool true)],[w 14]⟩
  let bad := Core.StatefulRunResult.fault (.invalidBinaryOperands .wordSub (.bool true) (w 14)) badLast
  let badCp : Core.State := ⟨.ret (.cellRef .word 0),[.loadCellApply,.binaryApply .wordSub (.bool true)],[w 14]⟩
  let emptyCp : Core.State := ⟨.eval (.var 0) env,[.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.binaryRight .wordSub (call 1 0) env],[]⟩
  let empty := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.binaryRight .wordSub (call 1 0) env],[]⟩
  check (decide (run 24 [.bool true]=some (.word,.outOfFuel badCp) ∧ run 25 [.bool true]=some (.word,bad) ∧ Core.runStateful 1 badCp=bad ∧ run 4 []=some (.word,.outOfFuel emptyCp) ∧ run 8 []=some (.word,empty) ∧ Core.runStateful 4 emptyCp=empty)) "wrong payload executes right writer; faulting left prevents right"
  for s in [[w 23],[.bool true],[]] do
    for fuel in List.range 28 do
      check (decide (run fuel s=some (.word,Core.runStateful fuel (.initial sub env s)))) "same prepared full store outcomes"
      match exhausted : Core.runStateful fuel (.initial sub env s) with
      | .outOfFuel cp =>
          have _ := Core.runStateful_resume exhausted 30
          check (decide (run (fuel+30) s=some (.word,Core.runStateful 30 cp))) "fault-aware whole resumption"
      | _ => pure ()
  for body in ["let r=f(x)-g(x);return r;","let r:Word=f(x)-g(x);return r;"] do
    discard <| verify (← bodySource body) reader writer x .word (.letE sub (.var 0)) [w 23] [w 14] (w 9) 29
  discard <| verify (← bodySource "return f(g(x))-g(f(x));") reader writer x .word (.binary .wordSub (.apply (.var 2) (call 1 0)) (.apply (.var 1) (call 2 0))) [w 23] [w 14] (w 0) 47
  discard <| verify (← bodySource "f(x)-g(x);{return f(x)-x;}") reader writer x .word (.letE sub (.binary .wordSub (call 3 1) (.var 1))) [w 23] [w 14] (w 0) 40
  for old in [3,23] do
    discard <| verify (← bodySource "return f(x)>g(x);") reader writer x .bool (.binary .wordGt (call 2 0) (call 1 0)) [w old] [w 14] (.bool (old>14)) 26
    discard <| verify (← bodySource "if(f(x)>g(x)){return f(x)-x;}else{return x;}") reader writer x .word (.ifE (.binary .wordGt (call 2 0) (call 1 0)) (.binary .wordSub (call 2 0) (.var 0)) (.var 0)) [w old] [w 14] (if old>14 then w 0 else w 14) (if old>14 then 40 else 29)
  let wrongReturn ← bodySource "return f(x)>g(x);"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (.binary .wordGt (call 2 0) (call 1 0),.bool))) "independent Bool body versus declared Word"
  for bad in [wrongReturn,← bodySource "let r:Word=f(x)>g(x);return r;",← bodySource "return (f(x)>g(x))-x;"] do
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [reader,writer,x]=none ∧ runRecursiveComputationFunction? types owner bad [reader,writer,x] 80 [w 23]=none)) "return/annotation/operand type gates"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveComputationBodies
/-! Parsed bodies instantiate shared laws with independent static/raw evidence and manual Core paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment RecursiveLocalComputationEvaluatesWithCost
namespace ParsedRecursiveComputationBodies
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Shared",by decide⟩],by decide⟩⟩,54⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def inputs (a : Core.Ty) : LocalTypeInputs := ⟨[⟨"x",id 4,a⟩,⟨"f",foreign,.function a a⟩,
  ⟨"g",id 9,.function a a⟩,⟨"h",id 12,.function a a⟩,⟨"k",id 15,.function a a⟩,
  ⟨"p",id 20,.function a .bool⟩,⟨"f",id 25,.bool⟩],by change [id 4,foreign,id 9,id 12,id 15,id 20,id 25].Nodup; decide⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Word"],.word),(["A"],a),(["A"],.bool)]
private def w (n : Nat) := Core.Word.ofNatModulo n
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool false]
private def env (a : Core.Ty) (v : Core.Value) (choice : Bool) : Resolved.Environment := [(id 4,v),(foreign,identity a),(id 9,identity a),(id 12,identity a),(id 15,identity a),
    (id 20,.closure a .bool (.bool choice) [.unit]),(id 25,.bool false)]
private def parsed (text : String) : IO Syntax.Block := do
  let text := "function original(){"++text++"}"; let file : Syntax.SourceFile := ⟨⟨.main,"shared-body.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "parser")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original bytes/body"
  return source.value.body
private structure Pure (i : LocalTypeInputs) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression i.names s resolved
  lowered : Resolved.Lowers i.context.ids resolved core
  typing : Resolved.HasType i.context resolved type
private theorem one {literal : Syntax.CoreLiteral} (spelling : literal.value=.decimal "1") : WordLiteralDenotes literal (w 1) := by
  change NumericLiteralDenotes literal.value 1; rw [spelling]; exact .decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)
private def pureChild (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Pure i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some localId =>
          match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId with
          | some t,some n => return ⟨.var localId,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | ⟨_,.literal literal⟩ =>
      if spelling : literal.value=.decimal "1" then
        return ⟨.word (w 1),.word (w 1),.word,by rw [shape]; exact .wordLiteral (one spelling),.word,.word⟩
      else throw (IO.userError "fixture literal")
  | _ => throw (IO.userError "pure fixture")
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates i.names i.context s core type
  typing : RecursiveLocalComputationHasType i.names i.context s type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "original group"; let c ← child i inner
      return ⟨c.core,c.type,by rw [shape]; exact .group c.elaboration,by rw [shape]; exact .group c.typing⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte≤argsSpan.startByte)) "original call order"
      let f ← child i fn; let a ← child i arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "Function type")
  | ⟨_,.binary left ⟨_,.add⟩ right⟩ =>
      let a ← child i left; let b ← child i right
      if both : a.type=.word ∧ b.type=.word then return ⟨.binary .wordAdd a.core b.core,.word,
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType, both.1] using a.elaboration) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType, both.2] using b.elaboration),
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType, both.1] using a.typing) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType, both.2] using b.typing)⟩
      else throw (IO.userError "Word operands")
  | _ => let a ← pureChild i s; return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing,.pure (a.resolution.reflects_type a.typing)⟩
termination_by sizeOf s
private structure Static (ts : TypeNameTable) (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveComputationReturnTreeElaborates ts owner i b core type
  typing : RecursiveComputationReturnTreeHasType ts owner i b type
private def statics (ts : TypeNameTable) (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static ts i b) := do
  for statement in b.value do check (b.span.contains statement.span) "original statement span"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨rs,.returnStmt (some s)⟩]⟩ =>
      check (rs.contains s.span) "original return span"; let c ← child i s
      return ⟨c.core,c.type,by rw [shape]; exact .expression c.elaboration,by rw [shape]; exact .expression c.typing⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← statics ts i ⟨inner,statements⟩; return ⟨c.core,c.type,by rw [shape]; exact .block c.elaboration,by rw [shape]; exact .block c.typing⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span && decide (name.span.endByte≤init.span.startByte)) "original binding order/spans"
      if unused : name.value ∉ i.names.map Prod.fst then
        let c ← child i init; let tail ← statics ts (i.bindFresh owner name.value c.type) ⟨bs,rest⟩
        match ann : annotation with
        | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .inferred c.elaboration tail.elaboration,
            by rw [shape,ann]; exact .inferred c.typing tail.typing⟩
        | some annotationSource =>
            check (ls.contains annotationSource.span && decide (name.span.endByte≤annotationSource.span.startByte ∧ annotationSource.span.endByte≤init.span.startByte)) "original annotation order/span"
            match written : annotationSource with
            | ⟨_,.named name none⟩ =>
                if lookup : ts.lookup? (qualifiedTypeNameKey name) = some c.type then
                  have m : StructuralTypeDenotes ts annotationSource c.type := by rw [written]; exact .named (TypeNameTable.lookup?_iff.mp lookup)
                  return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .binding m c.elaboration tail.elaboration,
                    by rw [shape,ann]; exact .binding m c.typing tail.typing⟩
                else throw (IO.userError "annotation meaning")
            | _ => throw (IO.userError "annotation shape")
      else throw (IO.userError "shadow")
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← child i s; let tail ← statics ts i ⟨bs,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.elaboration tail.elaboration,
        by rw [shape]; exact .discard c.typing tail.typing⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child i guard; let a ← statics ts i yes; let d ← statics ts i no
      if valid : c.type=.bool ∧ d.type=a.type then return ⟨.ifE c.core a.core d.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ c.elaboration) protection.down a.elaboration (valid.2 ▸ d.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ c.typing) protection.down a.typing (valid.2 ▸ d.typing)⟩
      else throw (IO.userError "Bool guard/whole arms")
  | _ => throw (IO.userError "outside static fixture")
termination_by sizeOf b
private structure PureCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalExpressionEvaluatesWithCost table e store s value store cost
private def pureCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (PureCost table e s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match found : e.lookup? localId with
          | some v => return ⟨v,1,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _ => throw (IO.userError "actual row")
      | _ => throw (IO.userError "actual name")
  | ⟨_,.literal literal⟩ =>
      if spelling : literal.value=.decimal "1" then
        return ⟨.word (w 1),1,fun _ => by rw [shape]; exact .wordLiteral (one spelling)⟩
      else throw (IO.userError "literal")
  | ⟨_,.binary left ⟨_,.add⟩ right⟩ =>
      let a ← pureCost table e left; let b ← pureCost table e right
      match av : a.value, bv : b.value with
      | .word x,.word y => return ⟨.word (x.add y),a.cost+b.cost+3,fun store => by rw [shape]; exact .add (av ▸ a.evidence store) (bv ▸ b.evidence store)⟩
      | _,_ => throw (IO.userError "actual Word operands")
  | _ => throw (IO.userError "raw pure fixture")
termination_by sizeOf s
private structure ChildCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost table e store s value store cost
private def childCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (ChildCost table e s) := do
  match shape : s with
  | ⟨_,.group inner⟩ => let c ← childCost table e inner; return ⟨c.value,c.cost,fun store => by rw [shape]; exact .group (c.evidence store)⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← childCost table e fn; let a ← childCost table e arg
      match closure : f.value with
      | .closure _ _ (.var n) captured =>
          match found : (a.value::captured)[n]? with
          | some value => return ⟨value,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
          | _ => throw (IO.userError "actual capture")
      | .closure _ _ (.bool choice) _ => return ⟨.bool choice,f.cost+a.cost+4,fun store => by rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons .bool .refl)⟩
      | _ => throw (IO.userError "actual body")
  | _ => let c ← pureCost table e s; return ⟨c.value,c.cost,fun store => .pure (c.evidence store)⟩
termination_by sizeOf s
private structure Cost (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table e store b value store cost
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
private def staticCheck (a : Core.Ty) (text : String) (core : Core.Expr) (type : Core.Ty) (old : Bool := false) : IO Unit := do
  let source ← parsed text; let i := inputs a; let p ← statics (types a) i source
  have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mp ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr p.elaboration)
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp p.typing
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,p.elaboration⟩
  have _ := ComputationReturnTreeElaborates.core_hasType core_hasType p.elaboration
  let oldResult := if old then some (core,type) else none
  check (decide (elaborateComputationReturnTree? elaborateLocalComputation? (types a) owner i source=oldResult ∧
    elaborateLocalComputationReturnTree? (types a) owner i source=oldResult ∧ p.core=core ∧ p.type=type ∧ elaborateRecursiveComputationReturnTree? (types a) owner i source=some (core,type) ∧
    (i.bindFresh owner "r" a).names.lookup? "r"=some (id 26) ∧
    ((i.bindFresh owner "r" a).bindFresh owner "z" a).names.lookup? "z"=some (id 27) ∧ i.names.lookup? "f"=some foreign)) "static exact Core/type/fresh/first match"
private def exercise (a : Core.Ty) (argument : Core.Value) (choice : Bool) (text : String) (core : Core.Expr)
    (value : Core.Value) (cost : Nat) (manual : ∀ store k, Core.Steps cost ⟨.eval core (env a argument choice).values,k,store⟩ ⟨.ret value,k,store⟩) : IO Unit := do
  let source ← parsed text; let i := inputs a; let e := env a argument choice
  let p ← statics (types a) i source; let r ← costs i.names e source
  if fixed : p.core=core ∧ r.value=value ∧ r.cost=cost then
    have certificate : RecursiveComputationReturnTreeElaborates (types a) owner i source core p.type := by simpa only [fixed.1] using p.elaboration
    have ids : e.ids=i.context.ids := rfl
    have fragment := ComputationReturnTreeElaborates.core_fragment (ChildElab := RecursiveLocalComputationElaborates) (F := RecursiveLocalComputationFragment) core_fragment weakenAt certificate
    have _ := ComputationBodyFragment.weakenAt (F := RecursiveLocalComputationFragment) weakenAt fragment 1
    for store in [[],[Core.Value.bool true,.unit]] do
      have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner i.names e store source value store cost := by simpa only [fixed.2.1,fixed.2.2] using r.evidence store
      have raw := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨_,counted⟩
      have _ := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) recursiveLocalComputationEvaluates_iff_exists_cost).mp raw
      have correspondence := ComputationReturnTreeElaborates.evaluates_iff (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (F := RecursiveLocalComputationFragment) core_fragment weakenAt evaluates_insert_iff evaluates_iff certificate ids
      have original := correspondence.mp raw; have _ := correspondence.mpr original
      have exactCost := ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (F := RecursiveLocalComputationFragment) core_fragment weakenAt evaluates_insert_iff evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost insertion_paths toStepsWithContinuation certificate ids
      have _ := ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost) deterministic counted (exactCost.mpr (manual store []))
      have _ := exactCost.mp counted
      let pending := [Core.Frame.letBody .unit []]
      have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (F := RecursiveLocalComputationFragment) core_fragment weakenAt insertion_paths toStepsWithContinuation counted certificate ids pending
      let inserted := Core.Value.cellRef (.namedData ⟨99⟩) 404
      have changed := (ComputationBodyFragment.evaluates_insert_iff (F := RecursiveLocalComputationFragment) evaluates_insert_iff fragment [] e.values inserted).mpr original
      have _ := (ComputationBodyFragment.evaluates_insert_iff (F := RecursiveLocalComputationFragment) evaluates_insert_iff fragment [] e.values inserted).mp changed
      have pair : ∀ k, Core.Steps cost ⟨.eval core e.values,k,store⟩ ⟨.ret value,k,store⟩ ∧ Core.Steps cost ⟨.eval (core.weakenAt 0) (inserted::e.values),k,store⟩ ⟨.ret value,k,store⟩ := by
        obtain ⟨n,paths⟩ := ComputationBodyFragment.insertion_paths (F := RecursiveLocalComputationFragment) insertion_paths fragment [] e.values inserted original
        have same := ((manual store []).final_unique (paths []).1).1
        exact same.symm ▸ paths
      for shifted in [false,true] do
        let start := Core.State.initial (if shifted then core.weakenAt 0 else core) (if shifted then inserted::e.values else e.values) store
        have path : Core.Steps cost start (.final value store) := by cases shifted; exact (pair []).1; exact (pair []).2
        for fuel in List.range (cost+2) do
          match outcome : Core.runStateful fuel start with
          | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=store)) "fixed result"
          | .outOfFuel cp =>
              have _ := path.residual_of_outOfFuel outcome
              check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) start)) "genuine residual/full replay"
          | .fault _ _ => throw (IO.userError "manual successful path fault")
      check (decide (Core.runStateful cost ⟨.eval core e.values,pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "pending endpoint"
  else throw (IO.userError "independent expected result")
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def nested (f g x : Nat) : Core.Expr := .apply (.var f) (call g x)
private theorem invoke {e : Core.Environment} {s : Core.Store} {k : List Core.Frame} {f : Nat} {arg : Core.Expr} {n : Nat}
    {a b : Core.Ty} {body : Core.Expr} {captured : Core.Environment} {x v : Core.Value}
    (fn : e[f]?=some (.closure a b body captured)) (argument : Core.Steps n ⟨.eval arg e,.applyClosure a b body captured::k,s⟩ ⟨.ret x,.applyClosure a b body captured::k,s⟩)
    (actual : Core.Steps 1 (.initial body (x::captured) s) (.final v s)) :
    Core.Steps (1+n+1+3) ⟨.eval (.apply (.var f) arg) e,k,s⟩ ⟨.ret v,k,s⟩ := CostStepComposition.apply (.cons (.var fn) .refl) argument actual
private def wrap : Nat → String → String | 0,s => s | n+1,s => "{"++wrap n s++"}"
end ParsedRecursiveComputationBodies
open ParsedRecursiveComputationBodies
def frontendParsedRecursiveComputationBodyTests : IO Unit := do
  let bound := Core.Expr.letE (nested 1 2 0) (.var 0)
  let branches := Core.Expr.ifE (nested 5 2 0) bound (.letE (.var 0) (.var 0))
  let branchText := "if(p(g(x))){let t:A=f(g(x));return t;}else{let t=x;return t;}"
  for a in [Core.Ty.unit,.word,.namedData ⟨7⟩,.cell .word,.function (.namedData ⟨8⟩) (.namedData ⟨9⟩)] do
    for depth in [0,2,11] do
      for (text,core,type,old) in [("return;",.unit,.unit,true),("return x;",.var 0,a,true),("let r:A=f(x);return r;",.letE (call 1 0) (.var 0),a,true),
          ("return ((f(g(x))));",nested 1 2 0,a,false),("let r:A=f(g(x));return r;",bound,a,false),
          ("let r=f(g(x));return r;",bound,a,false),(branchText,branches,a,false)] do
        staticCheck a (wrap depth text) core type old
  for choice in [false,true] do
    exercise .word (.word (w 17)) choice "return;" .unit .unit 1 (fun _ _ => .cons .unit .refl)
    exercise .word (.word (w 17)) choice "return ((f(g(x))));" (nested 1 2 0) (.word (w 17)) 11 (fun _ _ =>
      invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl))
    exercise .word (.word (w 17)) choice branchText branches (.word (w 17)) (if choice then 27 else 17) (by
      intro s k; cases choice
      · exact CostStepComposition.ifFalse (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons .bool .refl)) (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
      · exact CostStepComposition.ifTrue (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons .bool .refl)) (CostStepComposition.letE (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)))
  let mixed := "let r:Word=f(g(x)); {h(k(r)); let z=r; return z+1;}"
  let core := Core.Expr.letE (nested 1 2 0) (.letE (nested 4 5 0) (.letE (.var 1) (.binary .wordAdd (.var 0) (.word (w 1)))))
  staticCheck .word mixed core .word
  exercise .word (.word (w 17)) true mixed core (.word (w 18)) 34 (fun _ _ =>
    CostStepComposition.letE (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl))
      (CostStepComposition.letE (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl))
        (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons .word (.cons (.applyBinary rfl) .refl))))))))
  for text in ["if(p(g(x))){return x;}else{let r:Unknown=x;return r;}"] do
    let body ← parsed text; let r ← costs (inputs .word).names (env .word (.word (w 17)) true) body
    have _ := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨_,r.evidence []⟩
    check (decide (r.value=.word (w 17) ∧ r.cost=14 ∧ elaborateRecursiveComputationReturnTree? (types .word) owner (inputs .word) body=none)) "raw success/whole unknown"
  staticCheck .word "return f(g(x))+1;" (.binary .wordAdd (nested 1 2 0) (.word (w 1))) .word
  for text in ["","f(g(x));","{return x;}return x;","let r=r;return r;","if(p(g(x))){return x;}"] do
    let body ← parsed text
    check (decide (elaborateRecursiveComputationReturnTree? (types .word) owner (inputs .word) body=none ∧
      elaborateComputationReturnTree? elaborateLocalComputation? (types .word) owner (inputs .word) body=none ∧ elaborateLocalComputationReturnTree? (types .word) owner (inputs .word) body=none)) "retained rejection boundary"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveComputationBodyEffects
/-! Original function records supply actual inputs to a new body profile only.
Independent source certificates and transition scripts retain literal captures and effects. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveBodyEffects
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveBodyEffects",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-body-effects.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "complete original bytes"
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) :
    IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
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
-- A bounded fixture script constructs transitions; it never calls the machine runner.
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
    | .bool b => return ⟨.bool b,s,1,fun _ => by rw [original]; exact .cons .bool .refl⟩
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
    | .newCell t (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef t s.length,s++[v],3,fun _ => by rw [original]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "manual allocation value")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : RecursiveLocalComputationElaborates s.names s.context source core type
  raw : RecursiveLocalComputationEvaluatesWithCost s.names env store source value final cost
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.group inner⟩ =>
      check (source.span.contains inner.span) "original group range"
      let c ← child s env store inner
      return ⟨c.core,c.type,c.value,c.final,c.cost,by rw [original]; exact .group c.elaboration,by rw [original]; exact .group c.raw⟩
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
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
      | none => throw (IO.userError "original name missing")
  | _ => throw (IO.userError "outside fixture expression")
termination_by sizeOf source
private structure Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : RecursiveComputationReturnTreeElaborates types owner s source core type
  raw : RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source value final cost
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement spans"
  match original : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
      return ⟨.unit,.unit,.unit,store,1,by rw [original]; exact .bare,by rw [original]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let b ← tree types s env store ⟨span,statements⟩
      return ⟨b.core,b.type,b.value,b.final,b.cost,by rw [original]; exact .block b.elaboration,by rw [original]; exact .block b.raw⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child s env store e
      if unused : name.value ∉ s.names.map Prod.fst then
        let id := Resolved.freshLocalId owner s.ids
        let b ← tree types (s.bindFresh owner name.value a.type) ((id,a.value)::env) a.final ⟨span,rest⟩
        have raw : RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source b.value b.final (a.cost+b.cost+2) := by
          rw [original]; cases annotation <;> first | exact .inferred a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw) | exact .binding a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw)
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .inferred a.elaboration b.elaboration,raw⟩
        | some t =>
            let m ← meaning types t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .binding (same ▸ m.2.down) a.elaboration b.elaboration,raw⟩
            else throw (IO.userError "original binding annotation differs")
      else throw (IO.userError "shadowing is still excluded")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child s env store e; let b ← tree types s env a.final ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen e yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (s.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child s env store e; if ct : c.type=.bool then
        let a ← tree types s env c.final yes; let b ← tree types s env c.final no
        if same : b.type=a.type then
          have el : RecursiveComputationReturnTreeElaborates types owner s source (.ifE c.core a.core b.core) a.type := by rw [original]; exact .conditional (ct ▸ c.elaboration) protection.down a.elaboration (same ▸ b.elaboration)
          match cv : c.value with
          | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,a.final,c.cost+a.cost+2,el,by rw [original]; exact .ifTrue (cv ▸ c.raw) a.raw⟩
          | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,b.final,c.cost+b.cost+2,el,by rw [original]; exact .ifFalse (cv ▸ c.raw) b.raw⟩
          | _ => throw (IO.userError "actual guard differs")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "static guard differs")
  | _ => throw (IO.userError "outside original mixed body fixture")
termination_by sizeOf source
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
private def verify (body : String) (f g x : TypedRuntimeArgument) (output : Core.Ty)
    (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) (missing := false) : IO Unit := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output),(["Word"],.word)]
  let source ← parsed ("function recursive(f:F,g:G,x:X) returns(R){"++body++"}"); let args := [f,g,x]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let env := inputs.environment.values; let manual ← path 100 core env s
  have _ := h.down
  have _ : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  check (decide (env=[x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.core=core ∧ b.type=output ∧ b.value=value ∧ b.final=final ∧ b.cost=cost ∧
    manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent Core/type/value/store/cost"
  have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr b.elaboration
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,b.elaboration⟩
  have _ := b.elaboration.core_hasType RecursiveLocalComputationElaborates.core_hasType
  have raw := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := RecursiveLocalComputationEvaluates)
    recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨_,b.raw⟩
  have closed := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.raw b.elaboration ids []
  have reflected := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.elaboration ids).mpr closed
  have _ := ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationEvaluatesWithCost.deterministic b.raw reflected
  have _ := (ComputationReturnTreeElaborates.evaluates_iff (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff b.elaboration ids).mp raw
  check (decide (elaborateRecursiveComputationReturnTree? types owner inputs.toTypeInputs source.value.body=some (core,output) ∧
    compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "new body exact Some/old whole None"
  for fuel in List.range (cost+2) do
    check (decide (runRuntimeComputationFunction? types owner source args fuel s=none)) "no recursive whole entry"
    match exhausted : Core.runStateful fuel (.initial core env s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact actual completion"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel exhausted
        have _ := Core.runStateful_resume exhausted 2
        check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
          Core.runStateful 2 cp=Core.runStateful (fuel+2) (.initial core env s))) "genuine saved state/residual/full resume"
    | .fault _ _ => throw (IO.userError "independent successful path faulted")
  if missing then
    let cp : Core.State := ⟨.eval (.apply (.var 1) (.var 0)) env,[.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.letBody (.var 0) env],[]⟩
    let fault := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.letBody (.var 0) env],[]⟩
    check (decide (Core.runStateful 4 (.initial core env [])=.outOfFuel cp ∧
      Core.runStateful 13 (.initial core env [])=fault ∧ Core.runStateful 9 cp=fault)) "typed rows preserve full missing-store checkpoint/fault"
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def delay : Nat → Core.Expr | 0 => .var 0 | n+1 => .letE (.var 0) (delay n)
private theorem delayTyped (n : Nat) (ctx : Core.Context) (found : ctx[0]?=some .word) : Core.HasType ctx (delay n) .word := by
  induction n generalizing ctx with | zero => exact .var found | succ n ih => exact .letE (.var found) (ih _ rfl)
end RecursiveBodyEffects
open RecursiveBodyEffects
def frontendParsedRecursiveComputationBodyEffectsTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  let identity : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
  let nested (f g x : Nat) : Core.Expr := .apply (.var f) (.apply (.var g) (.var x))
  for old in [3,23] do
    for ann in ["",":Word"] do
      verify ("let r"++ann++"=((f(g(x))));{return r;}") reader writer x .word (.letE (nested 2 1 0) (.var 0)) [w old] [w 14] (w 14) 25
    verify "f(g(x));{f(g(x));return x;}" reader writer x .word (.letE (nested 2 1 0) (.letE (nested 3 2 1) (.var 2))) [w old] [w 14] (w 14) 49
    check (decide (Core.runStateful 24 (.initial (.letE (nested 2 1 0) (.letE (nested 3 2 1) (.var 2))) [x.value,writer.value,reader.value] [w old])=
      .outOfFuel ⟨.eval (.letE (nested 3 2 1) (.var 2)) [w 14,x.value,writer.value,reader.value],[],[w 14]⟩)) "actual hidden slot retains captured reader and updated store"
    let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl))⟩
    let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word,.closure (.cell .word) .word (.loadCell (.var 0)) [],.closure .nil (.loadCell (.var rfl))⟩
    verify "let r=f(g(x));return r;" load alloc x .word (.letE (nested 2 1 0) (.var 0)) [w old] [w old,w 14] (w 14) 18
    for choice in [false,true] do
      let guard : TypedRuntimeArgument := ⟨.function .word .bool,.closure .word .bool (.letE (.storeCell (.var 1) (.var 0)) (.bool choice)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) .bool)⟩
      verify "if(f(g(x))){g(x);return x;}else{return x;}" guard identity x .word (.ifE (nested 2 1 0) (.letE (.apply (.var 1) (.var 0)) (.var 1)) (.var 0)) [w old] [w 14] (w 14) (if choice then 29 else 21)
    let maker : TypedRuntimeArgument := ⟨.function .word reader.type,.closure .word reader.type (.var 1) [reader.value],.closure (.cons reader.valueTyped .nil) (.var rfl)⟩
    verify "let h=f(x);return h(g(x));" maker writer x .word (.letE (.apply (.var 2) (.var 0)) (nested 0 2 1)) [w old] [w 14] (w 14) 30
    verify "f(g(x));return f;" reader writer x reader.type (.letE (nested 2 1 0) (.var 3)) [w old] [w 14] reader.value 25
    verify "f(g(x));return;" reader writer x .unit (.letE (nested 2 1 0) .unit) [w old] [w 14] .unit 25
  for n in [0,2,5,13] do
    let delayed : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (delay n) [],.closure .nil (delayTyped n _ rfl)⟩
    verify "let r=f(g(x));return r;" identity delayed x .word (.letE (nested 2 1 0) (.var 0)) [] [] (w 14) (3*n+14)
  for captured in [9,31] do
    let constant : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w captured],.closure (.cons .word .nil) (.var rfl)⟩
    verify "let r=f(g(x));return r;" constant identity x .word (.letE (nested 2 1 0) (.var 0)) [] [] (w captured) 14
  verify "let r=f(g(x));return r;" reader identity x .word (.letE (nested 2 1 0) (.var 0)) [.bool true] [.bool true] (.bool true) 16 true
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveComputationCompilation
/-! Whole original declarations have independent annotation, parameter and body
certificates. The nominal matrix supplies no values; three actual smokes run separately. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveComputationCompilation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CompileRecursive", by decide⟩], by decide⟩⟩, n⟩
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def text (body : String) := "function example(f:F,g:G,x:A) returns(R){" ++ body ++ "}"
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"compile-recursive.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing")
  let .ok source next := Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"original declaration parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "whole original span"
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte ≤ source.value.body.span.startByte)) "original header before body"
  return source
private structure Meaning (ts : TypeNameTable) (s : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes ts s type
private def meaning (ts : TypeNameTable) (s : Syntax.TypeExpr) : IO (Meaning ts s) := do
  match shape : s with
  | ⟨_,.named name none⟩ =>
      match found : ts.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | _ => throw (IO.userError "missing annotation")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [a]⟩ => let m ← meaning ts a; return ⟨m.type,by rw [shape]; exact .single m.evidence⟩
  | ⟨_,.tuple [a,b]⟩ =>
      let x ← meaning ts a; let y ← meaning ts b
      return ⟨.product x.type y.type,by rw [shape]; exact .pair x.evidence y.evidence⟩
  | _ => throw (IO.userError "outside annotation fixture")
termination_by sizeOf s
private structure Declared (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (ps : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom ts o i ps inputs
private def declare (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (ps : List Syntax.FunctionParameter) : IO (Declared ts o i ps) := do
  match shape : ps with
  | [] => return ⟨i,by rw [shape]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte ≤ annotation.span.startByte)) "parameter original order"
      let m ← meaning ts annotation
      if unused : name.value ∉ i.names.map Prod.fst then
        let tail ← declare ts o (i.bindFresh o name.value m.type) rest
        return ⟨tail.inputs,by rw [shape]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "non-runtime parameter")
private structure Header (ts : TypeNameTable) (s : Syntax.FunctionSignature) where
  type : Core.Ty
  evidence : RuntimeFunctionHeader ts s type
private def header (ts : TypeNameTable) (s : Syntax.FunctionSignature) : IO (Header ts s) := do
  if policy : s.genericParameters = none ∧ s.whereClause = none ∧ s.modifiers.publicMarker = none ∧ s.modifiers.payableMarker = none then
    match shape : s.returnsClause with
    | none => return ⟨.unit,⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [shape]; exact .absent⟩⟩
    | some ⟨_,⟨_,[a]⟩⟩ =>
        let m ← meaning ts a
        return ⟨m.type,⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [shape]; exact .single m.evidence⟩⟩
    | _ => throw (IO.userError "return annotation shape")
  else throw (IO.userError "whole header policy")
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
      | some id =>
          match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
          | some t,some n => return ⟨.var id,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | ⟨_,.literal literal⟩ =>
      if spelling : literal.value=.decimal "1" then
        have denoted : WordLiteralDenotes literal (Core.Word.ofNatModulo 1) := by
          change NumericLiteralDenotes literal.value 1; rw [spelling]
          exact .decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)
        return ⟨.word (Core.Word.ofNatModulo 1),.word (Core.Word.ofNatModulo 1),.word,by rw [shape]; exact .wordLiteral denoted,.word,.word⟩
      else throw (IO.userError "migration literal")
  | _ => throw (IO.userError "not fixture atom")
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveLocalComputationElaborates i.names i.context s core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "original group"; let c ← child i inner
      return ⟨c.core,c.type,by rw [shape]; exact .group c.evidence⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "call spans/order"
      let f ← child i fn; let a ← child i arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.binary left ⟨_,.add⟩ right⟩ =>
      let a ← child i left; let b ← child i right
      if both : a.type=.word ∧ b.type=.word then return ⟨.binary .wordAdd a.core b.core,.word,
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType, both.1] using a.evidence) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType, both.2] using b.evidence)⟩
      else throw (IO.userError "migration Word operands")
  | _ => let a ← atom i s; return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing⟩
termination_by sizeOf s
private structure Body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveComputationReturnTreeElaborates ts o i b core type
private def body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (b : Syntax.Block) : IO (Body ts o i b) := do
  for s in b.value do check (b.span.contains s.span) "original statement span"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨rs,.returnStmt (some s)⟩]⟩ =>
      check (rs.contains s.span) "return span"; let c ← child i s
      return ⟨c.core,c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← body ts o i ⟨inner,statements⟩; return ⟨c.core,c.type,by rw [shape]; exact .block c.evidence⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span && decide (name.span.endByte ≤ init.span.startByte)) "binding spans/order"
      if unused : name.value ∉ i.names.map Prod.fst then
        let c ← child i init; let tail ← body ts o (i.bindFresh o name.value c.type) ⟨bs,rest⟩
        match ann : annotation with
        | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .inferred c.evidence tail.evidence⟩
        | some a =>
            check (ls.contains a.span && decide (a.span.endByte ≤ init.span.startByte)) "annotation before initializer"
            let m ← meaning ts a
            if same : m.type = c.type then return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .binding (same ▸ m.evidence) c.evidence tail.evidence⟩
            else throw (IO.userError "initializer annotation mismatch")
      else throw (IO.userError "shadowing")
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← child i s; let tail ← body ts o i ⟨bs,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.evidence tail.evidence⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child i guard; let a ← body ts o i yes; let d ← body ts o i no
      if ct : c.type = .bool then
        if same : d.type = a.type then return ⟨.ifE c.core a.core d.core,a.type,by rw [shape]; exact .conditional (ct ▸ c.evidence) protection.down a.evidence (same ▸ d.evidence)⟩
        else throw (IO.userError "arm types")
      else throw (IO.userError "guard type")
  | _ => throw (IO.userError "outside body fixture")
termination_by sizeOf b
private def table (a b r : Core.Ty) : TypeNameTable := [(["F"],.function a b),(["F"],.bool),
  (["G"],.function a a),(["A"],a),(["B"],b),(["R"],r),(["Unit"],.unit),(["Word"],.word),(["mod","F"],.function a b)]
private abbrev rowEq : DecidableEq LocalTypeBinding := fun a b =>
  decidable_of_iff ((a.name,a.id,a.type)=(b.name,b.id,b.type)) (by cases a; cases b; simp)
attribute [local instance] rowEq
private abbrev inputEq : DecidableEq LocalTypeInputs := fun a b =>
  decidable_of_iff (a.bindings=b.bindings) ⟨by cases a; cases b; intro h; cases h; rfl,fun h => congrArg LocalTypeInputs.bindings h⟩
attribute [local instance] inputEq
private abbrev compiledEq : DecidableEq CompiledRuntimeFunction := fun a b =>
  decidable_of_iff ((a.inputs,a.core,a.returnType)=(b.inputs,b.core,b.returnType)) (by cases a; cases b; simp)
attribute [local instance] compiledEq
private def fields (c : CompiledRuntimeFunction) := (c.inputs.names,c.inputs.context,c.core,c.returnType)
private structure Ready (ts : TypeNameTable) (o : Resolved.DeclarationId) where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  evidence : RecursiveComputationFunctionCompiles ts o source compiled
private def positive (a b r : Core.Ty) (o : Resolved.DeclarationId) (sourceText : String)
    (expectedCore : Core.Expr) (oldProfile : Bool := false) : IO (Ready (table a b r) o) := do
  let ts := table a b r; let s ← parsed sourceText
  let ps ← declare ts o .empty s.value.signature.parameters.elements; let h ← header ts s.value.signature
  let c ← body ts o ps.inputs s.value.body
  if exactResult : h.type = r ∧ c.type = r ∧ c.core = expectedCore then
    let compiled : CompiledRuntimeFunction := ⟨ps.inputs,expectedCore,r⟩
    have e : RecursiveComputationFunctionCompiles ts o s compiled := ⟨by simpa only [compiled,exactResult.1] using h.evidence,
      ps.evidence,by simpa only [compiled,exactResult.2.1,exactResult.2.2] using c.evidence⟩
    let expectedInputs := ((LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "g" (.function a a)).bindFresh o "x" a
    let expected : CompiledRuntimeFunction := ⟨expectedInputs,expectedCore,r⟩
    have accepted := (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr e
    have _ := ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType ((compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp accepted).body
    check (decide (compiled = expected ∧ compileRecursiveComputationFunction? ts o s = some expected)) "independent full record/Core/return"
    check (decide (compileComputationFunction? elaborateLocalComputation? ts o s=(if oldProfile then some expected else none) ∧
      compileRuntimeComputationFunction? ts o s=(if oldProfile then some expected else none))) "old-child generic/old252 full Option"
    let wrong : CompiledRuntimeFunction := ⟨ps.inputs,.letE .unit (expectedCore.weakenAt 0),r⟩
    have _ : Core.HasType ps.inputs.context.values wrong.core r := .letE .unit
      (by simpa only [Core.Context.insertAt] using (ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType e.body).weakenAt (inserted := .unit) 0)
    if different : (compileRecursiveComputationFunction? ts o s).map fields ≠ some (fields wrong) then
      have _ : ¬ RecursiveComputationFunctionCompiles ts o s wrong := by
        intro other; exact different (congrArg (Option.map fields) ((compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr other))
      pure ()
    else throw (IO.userError "same-typed wrong Core acquired exact provenance")
    return ⟨s,compiled,e⟩
  else throw (IO.userError "independent body/declared return differs")
private structure Bound (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom ts o i ps args inputs
private def bindActual (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Bound ts o i ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨i,by rw [shape,supplied]; exact .nil⟩
  | ⟨_,.typed none name annotation⟩::rest,arg::tail =>
      let m ← meaning ts annotation
      if same : m.type = arg.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let b ← bindActual ts o (i.bindFresh o name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨b.inputs,by rw [shape,supplied]; exact .cons (same ▸ m.evidence) unused b.evidence⟩
        else throw (IO.userError "actual duplicate")
      else throw (IO.userError "actual type")
  | _,_ => throw (IO.userError "actual arity")
private def smoke (x : TypedRuntimeArgument) (annotation : String) : IO Unit := do
  let o := owner 4; let core := Core.Expr.letE (.apply (.var 2) (call 1 0)) (.var 0)
  let ready ← positive x.type x.type x.type o ("function example(f:F,g:G,x:"++annotation++") returns("++annotation++"){let r=f(g(x));return r;}") core
  let ts := table x.type x.type x.type
  let f : TypedRuntimeArgument := ⟨.function x.type x.type,.closure x.type x.type (.var 0) [],.closure .nil (.var rfl)⟩
  let g := f; let args := [f,g,x]; let actual ← bindActual ts o .empty ready.source.value.signature.parameters.elements args
  let c ← body ts o actual.inputs.toTypeInputs ready.source.value.body
  if fixed : c.core=core ∧ c.type=x.type ∧ ready.compiled.returnType=x.type then
    let prepared : PreparedRuntimeFunction := ⟨actual.inputs,core,x.type⟩
    have e : RecursiveComputationFunctionPrepares ts o ready.source args prepared := ⟨by simpa only [prepared,fixed.2.2] using ready.evidence.header,
      actual.evidence,by simpa only [prepared,fixed.1,fixed.2.1] using c.evidence⟩
    have accepted := (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr e
    have _ := (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp accepted
    check (decide (prepared.toCompiled=ready.compiled ∧ prepared.inputs.environment.values=[x.value,g.value,f.value] ∧
      prepared.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
        [("x",⟨o,2⟩,x.type,x.value),("g",⟨o,1⟩,g.type,g.value),("f",⟨o,0⟩,f.type,f.value)])) "same actual record/one reverse/parameter-only"
    have manual (s k) : Core.Steps 14 ⟨.eval core [x.value,g.value,f.value],k,s⟩ ⟨.ret x.value,k,s⟩ :=
      CostStepComposition.letE (CostStepComposition.apply (.cons (.var rfl) .refl)
        (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)
    for store in [[],[Core.Value.bool false]] do
      for fuel in List.range 16 do
        have _ := (manual store []).runStateful_done_iff (fuel := fuel)
        have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? ts o ready.source args fuel store
        check (decide (runRecursiveComputationFunction? ts o ready.source args fuel store=some (x.type,Core.runStateful fuel (.initial core [x.value,g.value,f.value] store)) ∧
          runRuntimeComputationFunction? ts o ready.source args fuel store=none)) "new full result/old nested None"
      check (decide (runRecursiveComputationFunction? ts o ready.source args 14 store=some (x.type,.done x.value store))) "manual value/cost/store"
      match runRecursiveComputationFunction? ts o ready.source args 13 store with
      | some (_, .outOfFuel cp) => check (decide (Core.runStateful 1 cp=.done x.value store)) "genuine cp13/residual1"
      | _ => throw (IO.userError "missing genuine checkpoint")
    for supplied in [args,[],[f,g],[f,x,g],args++[⟨.unit,.unit,.unit⟩],[f,g,⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩,⟨.unit,.unit,.unit⟩]] do
      have _ := prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? ts o ready.source supplied
      check (decide ((prepareRecursiveComputationFunction? ts o ready.source supplied).map PreparedRuntimeFunction.toCompiled=
        if supplied.map (·.type)=args.map (·.type) then some ready.compiled else none)) "full Option/Unit not omitted/product not flattened"
  else throw (IO.userError "original actual body differs")
private def rejected (sourceText : String) (localSuccess : Bool) (location : Syntax.Parser.FunctionLocation := .module) (b : Core.Ty := .word) : IO Unit := do
  let ts := table .word b .word; let o := owner 4; let s ← parsed sourceText location
  if localSuccess then
    let fixed := ((LocalTypeInputs.empty.bindFresh o "f" (.function .word .word)).bindFresh o "g" (.function .word .word)).bindFresh o "x" .word
    let c ← body ts o fixed s.value.body
    check (decide (c.core = .letE (.apply (.var 2) (call 1 0)) (.var 0) ∧ c.type = .word ∧
      elaborateRecursiveComputationReturnTree? ts o fixed s.value.body = some (c.core,c.type))) "body-only success under separate valid caller"
  check ((compileRecursiveComputationFunction? ts o s).isNone) "invalid whole declaration compiled"
end ParsedRecursiveComputationCompilation
open ParsedRecursiveComputationCompilation
def frontendParsedRecursiveComputationCompilationTests : IO Unit := do
  let types : List Core.Ty := [.unit,.word,.cell .word,.product .word .unit,.namedData ⟨77⟩,.function (.namedData ⟨9⟩) (.namedData ⟨9⟩)]
  for o in [owner 0,owner 41] do
    for a in types do
      for b in types do
        let nested := Core.Expr.apply (.var 2) (call 1 0)
        for (bodyText,core,old) in [("let r=f(g(x));return r;",.letE nested (.var 0),false),
            ("let r:B=((f(g(x))));{return r;}",.letE nested (.var 0),false),
            ("f(g(x));return f(g(x));",.letE nested (.apply (.var 3) (call 2 1)),false),
            ("return f(x);",call 2 0,true),("let r=f(x);return r;",.letE (call 2 0) (.var 0),true)] do
          let _ ← positive a b b o (text bodyText) core old
        let _ ← positive a (.function a b) b o (text "let h=f(g(x));return h(g(x));") (.letE nested (.apply (.var 0) (call 2 1)))
        let _ ← positive a b a o (text "return x;") (.var 0) true
      let _ ← positive a .bool a o (text "if(f(g(x))){{let t=x;return t;}}else{return x;}") (.ifE (.apply (.var 2) (call 1 0)) (.letE (.var 0) (.var 0)) (.var 0))
      let _ ← positive a .unit .unit o "function example(f:mod.F,g:G,x:(A)) returns(()){let r:B=f(g(x));return r;}" (.letE (.apply (.var 2) (call 1 0)) (.var 0))
  smoke ⟨.unit,.unit,.unit⟩ "()"
  smoke ⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩ "Word"
  smoke ⟨.product .word .unit,.pair (.word (Core.Word.ofNatModulo 17)) .unit,.pair .word .unit⟩ "(Word,())"
  let suffix := "{let r=f(g(x));return r;}"
  for head in ["function example<T>(f:F,g:G,x:A) returns(R)","function example(f:F,g:G,x:A) returns(R) where A: Eq",
      "function example(f:F,g:G,x:A)","function example(f:F,g:G,x:A) returns(Unit)",
      "function example(f:F,g:G,x:A) returns()","function example(f:F,g:G,x:A) returns(R,R)",
      "function example(f:F,g:G,x:A) returns(Missing)","function example(comptime f:F,g:G,x:A) returns(R)",
      "function example(f:F,g:G,x:Missing) returns(R)","function example(f:F,g:G,f:A) returns(R)"] do rejected (head++suffix) true
  for marker in ["public","payable"] do rejected ("function example(f:F,g:G,x:A) "++marker++" returns(R)"++suffix) true .contract
  let _ ← positive .word .word .word (owner 4) (text "return f(g(x))+1;") (.binary .wordAdd (.apply (.var 2) (call 1 0)) (.word (Core.Word.ofNatModulo 1)))
  for b in ["let r;return x;","let r=f(g(x));return f(r,x);",
      "{let r=f(g(x));}return r;","return f(g(x));return x;","let r:Missing=f(g(x));return r;"] do rejected (text b) false
  rejected (text "if(f(g(x))){return x;}else{{let r:Missing=x;return r;}}") false .module .bool
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveComputationEntries
/-! Original declaration records feed a separate recursive expression profile.
No recursive whole entry is introduced; fixed Core paths are independent scripts. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveComputationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveActual",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-actual.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "complete original bytes"
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) :
    IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
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
-- A bounded fixture script constructs transitions; it never calls the machine runner.
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
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .newCell t (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef t s.length,s++[v],3,fun _ => by rw [original]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "manual allocation value")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  id : Resolved.LocalId
  index : Nat
  type : Core.Ty
  value : Core.Value
  resolution : ResolvesLocalExpression s.names source (.var id)
  lowered : Resolved.Lowers s.context.ids (.var id) (.var index)
  typing : Resolved.HasType s.context (.var id) type
  raw : LocalExpressionEvaluatesWithCost s.names env store source value store 1
private def leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Leaf s env store source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨id,i,t,v,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual)⟩
          | _,_,_ => throw (IO.userError "independent original row missing")
      | none => throw (IO.userError "independent original name missing")
  | _ => throw (IO.userError "fixture leaf is not identifier")
private structure Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : RecursiveLocalComputationElaborates s.names s.context source core type
  raw : RecursiveLocalComputationEvaluatesWithCost s.names env store source value final cost
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.group inner⟩ =>
      check (source.span.contains inner.span) "original group range"
      let c ← child s env store inner
      return ⟨c.core,c.type,c.value,c.final,c.cost,by rw [original]; exact .group c.elaboration,by rw [original]; exact .group c.raw⟩
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
  | _ =>
      let a ← leaf s env store source
      return ⟨.var a.index,a.type,a.value,store,1,.pure a.resolution a.lowered a.typing,.pure a.raw⟩
termination_by sizeOf source
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
private def verify (sourceText : String) (f g x : TypedRuntimeArgument) (output : Core.Ty)
    (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat)
    (legacy : Bool := false) (missing : Bool := false) : IO Unit := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output)]
  let source ← parsed ("function recursive(f:F,g:G,x:X) returns(R){return "++sourceText++";}"); let args := [f,g,x]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source output
  let [⟨returnSpan,.returnStmt (some expression)⟩] := source.value.body.value | throw (IO.userError "original return shape")
  check (source.value.body.span.contains returnSpan && returnSpan.contains expression.span) "original expression inside return"
  let b ← child inputs.toTypeInputs inputs.environment s expression; let env := inputs.environment.values
  let manual ← path 100 core [x.value,g.value,f.value] s
  have _ : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have _ := h.down
  have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  check (decide (env=[x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.core=core ∧ b.type=output ∧ b.value=value ∧ b.final=final ∧ b.cost=cost ∧
    manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent Core/type/value/store/cost"
  have accepted := elaborateRecursiveLocalComputation?_iff.mpr b.elaboration
  have _ := elaborateRecursiveLocalComputation?_iff.mp accepted
  have typed := recursiveLocalComputationHasType_iff_elaborates.mpr ⟨_,b.elaboration⟩
  have _ := recursiveLocalComputationHasType_iff_elaborates.mp typed
  have _ := b.elaboration.core_hasType
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,b.raw⟩
  have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mp raw
  have evaluated := (b.elaboration.evaluates_iff ids).mp raw
  have _ := (b.elaboration.evaluates_iff ids).mpr evaluated
  have closed := b.raw.toStepsWithContinuation b.elaboration ids []
  have _ := b.raw.toStepsWithContinuation b.elaboration ids [.letBody .unit []]
  have _ := b.raw.deterministic ((b.elaboration.evaluatesWithCost_iff_steps ids).mpr closed)
  have _ := (b.elaboration.evaluatesWithCost_iff_steps ids).mp b.raw
  let inserted : Core.Value := .cellRef (.namedData ⟨99⟩) 72
  let leading := env.take 1; let suffix := env.drop 1
  have splitEnv : leading++suffix=env := List.take_append_drop 1 env
  have fragment := b.elaboration.core_fragment
  have _ := fragment.weakenAt 1
  have evalSplit : Core.Evaluates (leading++suffix) s b.core b.value b.final := by rw [splitEnv]; exact evaluated
  have insertedEvaluation := (fragment.evaluates_insert_iff leading suffix inserted).mpr evalSplit
  have _ := (fragment.evaluates_insert_iff leading suffix inserted).mp insertedEvaluation
  have shifted : Core.Steps b.cost (.initial (b.core.weakenAt leading.length) (leading++inserted::suffix) s) (.final b.value b.final) := by
    obtain ⟨pairedCost,paired⟩ := fragment.insertion_paths leading suffix inserted evalSplit
    have sameCost : pairedCost=b.cost := (closed.final_unique (by simpa only [splitEnv,env,Core.State.final] using (paired []).1)).1.symm
    exact sameCost ▸ (paired []).2
  check (decide (elaborateRecursiveLocalComputation? inputs.names inputs.context expression=some (core,output))) "new expression only"
  unless legacy do check (decide (elaborateLocalComputation? inputs.names inputs.context expression=none ∧
    elaborateLocalComputationReturnTree? types owner inputs.toTypeInputs source.value.body=none ∧
    compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none ∧
    compileRuntimeApplicationFunction? types owner source=none)) "old child/body/whole entry remains narrow"
  for fuel in List.range (cost+2) do
    unless legacy do check (decide (runRuntimeComputationFunction? types owner source args fuel s=none)) "no new whole runner"
    for item in ([⟨Core.State.initial b.core env s,⟨closed⟩⟩,
        ⟨.initial (b.core.weakenAt leading.length) (leading++inserted::suffix) s,⟨shifted⟩⟩] :
        List (Σ start : Core.State, PLift (Core.Steps b.cost start (.final b.value b.final)))) do
      let start := item.1; have cert := item.2.down
      match exhausted : Core.runStateful fuel start with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "fixed completion threshold"
      | .outOfFuel cp =>
          have _ := cert.residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
            Core.runStateful 2 cp=Core.runStateful (fuel+2) start)) "each genuine checkpoint/full residual/resume"
      | .fault _ _ => throw (IO.userError "independently successful source faulted")
  if legacy then
    match shape : expression with
    | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
        let a ← leaf inputs.toTypeInputs inputs.environment s fn; let z ← leaf inputs.toTypeInputs inputs.environment s arg
        match ft : a.type, fv : a.value with
        | .function input result,.closure _ _ body captured =>
            if same : z.type=input then
              let p ← path 100 body (z.value::captured) s
              have old : LocalComputationElaborates inputs.toTypeInputs.names inputs.toTypeInputs.context expression (.apply (.var a.index) (.var z.index)) result := by rw [shape]; exact .application (.call a.resolution a.lowered (ft ▸ a.typing) z.resolution z.lowered (same ▸ z.typing))
              have oldCost : LocalComputationEvaluatesWithCost inputs.toTypeInputs.names inputs.environment s expression p.value p.final (1+1+p.cost+3) := by rw [shape]; exact .application (.call (fv ▸ a.raw) z.raw (p.evidence []))
              have _ := old.toRecursiveLocalComputation
              have _ := b.raw.deterministic oldCost.toRecursiveLocalComputation
            else throw (IO.userError "legacy argument")
        | _,_ => throw (IO.userError "legacy Function")
    | _ => throw (IO.userError "legacy root")
  if missing then
    let cp : Core.State := ⟨.eval (.apply (.var 1) (.var 0)) env,[.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0]],[]⟩
    let fault := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩
    check (decide (Core.runStateful 3 (.initial core env [])=.outOfFuel cp ∧ Core.runStateful 12 (.initial core env [])=fault ∧
      Core.runStateful 9 cp=fault)) "same original typed rows do not ensure allocated store"
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def delay : Nat → Core.Expr | 0 => .var 0 | n+1 => .letE (.var 0) (delay n)
private theorem delayTyped (n : Nat) (ctx : Core.Context) (found : ctx[0]?=some .word) : Core.HasType ctx (delay n) .word := by
  induction n generalizing ctx with | zero => exact .var found | succ n ih => exact .letE (.var found) (ih _ rfl)
end RecursiveComputationEntries
open RecursiveComputationEntries
def frontendParsedRecursiveComputationEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  let identity : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
  let nested : Core.Expr := .apply (.var 2) (.apply (.var 1) (.var 0))
  let computed : Core.Expr := .apply (.apply (.var 2) (.var 0)) (.apply (.var 1) (.var 0))
  for old in [3,23] do
    for expression in ["f(g(x))","((f))(((g(x))))","((f(g(x))))"] do
      verify expression reader writer x .word nested [w old] [w 14] (w 14) 22
    verify "f(g(x))" writer reader x .word nested [w old] [w old] (w old) 22
    let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl))⟩
    let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word,.closure (.cell .word) .word (.loadCell (.var 0)) [],.closure .nil (.loadCell (.var rfl))⟩
    verify "f(g(x))" load alloc x .word nested [w old] [w old,w 14] (w 14) 15
    let maker : TypedRuntimeArgument := ⟨.function .word reader.type,.closure .word reader.type (.var 1) [reader.value],.closure (.cons reader.valueTyped .nil) (.var rfl)⟩
    verify "(f(x))(g(x))" maker writer x .word computed [w old] [w 14] (w 14) 27
    let effectMaker : TypedRuntimeArgument := ⟨.function .word reader.type,
      .closure .word reader.type (.letE (.storeCell (.var 1) (.var 2)) (.var 4)) [.cellRef .word 0,w 7,reader.value],
      .closure (.cons .cellRef (.cons .word (.cons reader.valueTyped .nil))) (.letE (.storeCell (.var rfl) (.var rfl)) (.var rfl))⟩
    verify "((f(x)))((g(x)))" effectMaker writer x .word computed [w old] [w 14] (w 14) 34
    let env := [x.value,writer.value,effectMaker.value]
    check (decide (Core.runStateful 14 (.initial computed env [w old])=.outOfFuel ⟨.ret reader.value,[.applyArgument (.apply (.var 1) (.var 0)) env],[w 7]⟩ ∧
      Core.runStateful 30 (.initial computed env [w old])=.outOfFuel ⟨.ret (w 14),[.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0]],[w 14]⟩)) "observable callee then argument stores/captures"
  for n in [0,2,5,13] do
    let delayed : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (delay n) [],.closure .nil (delayTyped n _ rfl)⟩
    verify "f(g(x))" identity delayed x .word nested [] [] (w 14) (3*n+11)
  for captured in [9,31] do
    let constant : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w captured],.closure (.cons .word .nil) (.var rfl)⟩
    verify "f(g(x))" constant identity x .word nested [] [] (w captured) 11
  verify "f(g(x))" reader identity x .word nested [.bool true] [.bool true] (.bool true) 13 false true
  verify "f(x)" reader identity x .word (.apply (.var 2) (.var 0)) [w 23] [w 23] (w 23) 8 true
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveLocalComputation
/-! Original syntax carries independent static and raw evidence. Value-free
nominal cases are separate from actual values and their hand-written Core paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveLocalComputation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Recursive",by decide⟩],by decide⟩⟩,53⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("f",foreign),("g",id 9),("maker",id 12),("y",id 14),("c",id 15),("p",id 20),("f",id 88)]
private def context (a b c : Core.Ty) : Resolved.Context := [(id 7,a),(foreign,.function b c),(id 9,.function a b),
  (id 12,.function a (.function a b)),(id 14,a),(id 15,.bool),(id 20,.function (.product a .unit) b),(foreign,.bool)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.bool true]
private def environment (a : Core.Ty) (x y : Core.Value) : Resolved.Environment := [(id 7,x),(foreign,identity a),
  (id 9,identity a),(id 12,.closure a (.function a a) (.var 1) [identity a]),(id 14,y),(id 15,.bool true),
  (id 20,.closure (.product a .unit) a (.first (.var 0)) []),(foreign,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def grouped : Nat → String → String | 0,s => s | n+1,s => "(" ++ grouped n s ++ ")"
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-computation.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError s!"parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) "original full expression span"
  return source
private structure Pure (ctx : Resolved.Context) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names s resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def pureChild (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Pure ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n => return ⟨.var localId,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | ⟨_,.group inner⟩ =>
      let a ← pureChild ctx inner; return ⟨a.resolved,a.core,a.type,by rw [shape]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,by rw [shape]; exact .unit,.unit,.unit⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (span.contains tupleSpan && tupleSpan.contains left.span && tupleSpan.contains right.span && decide (left.span.endByte ≤ right.span.startByte)) "tuple child spans/order"
      let a ← pureChild ctx left; let b ← pureChild ctx right
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [shape]; exact .pair a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← pureChild ctx left; let b ← pureChild ctx right
      if atWord : a.type = .word then
        if btWord : b.type = .word then return ⟨.binary .wordSub a.resolved b.resolved,.binary .wordSub a.core b.core,.word,
          by rw [shape]; exact .subtract a.resolution b.resolution,.binary a.lowered b.lowered,
          .binary (show Resolved.HasType ctx a.resolved .word from atWord ▸ a.typing) (show Resolved.HasType ctx b.resolved .word from btWord ▸ b.typing)⟩
        else throw (IO.userError "right Word")
      else throw (IO.userError "left Word")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← pureChild ctx guard; let a ← pureChild ctx yes; let b ← pureChild ctx no
      if gt : g.type = .bool then
        if same : b.type = a.type then return ⟨.ifE g.resolved a.resolved b.resolved,.ifE g.core a.core b.core,a.type,
          by rw [shape]; exact .conditional g.resolution a.resolution b.resolution,
          .ifE g.lowered a.lowered b.lowered,.ifE (gt ▸ g.typing) a.typing (same ▸ b.typing)⟩
        else throw (IO.userError "whole arms")
      else throw (IO.userError "Bool guard")
  | _ => throw (IO.userError "outside independent pure fixture")
termination_by sizeOf s
private structure Static (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates names ctx s core type
  typing : RecursiveLocalComputationHasType names ctx s type
private def statics (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static ctx s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span && decide (span.startByte < inner.span.startByte ∧ inner.span.endByte < span.endByte)) "original group not erased from AST"
      let c ← statics ctx inner
      return ⟨c.core,c.type,by rw [shape]; exact .group c.elaboration,by rw [shape]; exact .group c.typing⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "original call children/spans/order"
      let f ← statics ctx fn; let a ← statics ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "function type")
  | ⟨_,.binary left ⟨_,.add⟩ right⟩ =>
      let a ← statics ctx left; let b ← statics ctx right
      if both : a.type=.word ∧ b.type=.word then return ⟨.binary .wordAdd a.core b.core,.word,
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType, both.1] using a.elaboration) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType, both.2] using b.elaboration),
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType, both.1] using a.typing) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType, both.2] using b.typing)⟩
      else throw (IO.userError "migration Word operands")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← statics ctx guard; let a ← statics ctx yes; let b ← statics ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "migration conditional types")
  | _ => let p ← pureChild ctx s; return ⟨p.core,p.type,.pure p.resolution p.lowered p.typing,.pure (p.resolution.reflects_type p.typing)⟩
termination_by sizeOf s
private def staticCheck (a b c : Core.Ty) (text : String) (core : Core.Expr) (type : Core.Ty) (old : Bool := false) : IO Unit := do
  let s ← parsed text; let ctx := context a b c; let p ← statics ctx s
  have _ := elaborateRecursiveLocalComputation?_iff.mp (elaborateRecursiveLocalComputation?_iff.mpr p.elaboration)
  have _ := recursiveLocalComputationHasType_iff_elaborates.mp p.typing
  have _ := recursiveLocalComputationHasType_iff_elaborates.mpr ⟨p.core,p.elaboration⟩
  have _ := p.elaboration.core_hasType
  check (decide (p.core = core ∧ p.type = type ∧ elaborateRecursiveLocalComputation? names ctx s = some (core,type) ∧
    elaborateLocalComputation? names ctx s = (if old then some (core,type) else none) ∧
    names.lookup? "f" = some foreign ∧ ctx.lookup? foreign = some (.function b c))) "exact independent static result or old boundary"
private structure PureCost (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store s value store cost
private def pureCost (env : Resolved.Environment) (s : Syntax.Expr) : IO (PureCost env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : env.lookup? localId with
          | some v => return ⟨v,1,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _ => throw (IO.userError "actual row missing")
      | _ => throw (IO.userError "actual name missing")
  | ⟨_,.group inner⟩ =>
      let a ← pureCost env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | _ => throw (IO.userError "outside actual pure fixture")
termination_by sizeOf s
private structure Actual (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost names env store s value store cost
private def actual (env : Resolved.Environment) (s : Syntax.Expr) : IO (Actual env s) := do
  match shape : s with
  | ⟨_,.group inner⟩ =>
      let a ← actual env inner; return ⟨a.value,a.cost,fun store => by rw [shape]; exact .group (a.evidence store)⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← actual env fn; let a ← actual env arg
      match closure : f.value with
      | .closure _ _ (.var index) captured =>
          match found : (a.value::captured)[index]? with
          | some v => return ⟨v,f.cost+a.cost+1+3,fun store => by
              rw [shape]; exact .application (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl)⟩
          | _ => throw (IO.userError "actual body index")
      | _ => throw (IO.userError "outside independent actual body")
  | _ => let p ← pureCost env s; return ⟨p.value,p.cost,fun store => .pure (p.evidence store)⟩
termination_by sizeOf s
private def exercise (type : Core.Ty) (x y : Core.Value) (text : String) (core : Core.Expr) (value : Core.Value) (cost : Nat)
    (manual : ∀ store k, Core.Steps cost ⟨.eval core (environment type x y).values,k,store⟩ ⟨.ret value,k,store⟩)
    (legacyPure : Bool := false) : IO Unit := do
  let s ← parsed text; let ctx := context type type type; let env := environment type x y
  let p ← statics ctx s; let r ← actual env s
  if exactResult : p.core = core ∧ p.type = type ∧ r.value = value ∧ r.cost = cost then
    have e : RecursiveLocalComputationElaborates names ctx s core type := by simpa only [exactResult.1,exactResult.2.1] using p.elaboration
    have ids : env.ids = ctx.ids := rfl
    have fragment := e.core_fragment
    have _ := fragment.weakenAt 3
    for store in [[],[.bool true,.word (Core.Word.ofNatModulo 71)]] do
      have counted : RecursiveLocalComputationEvaluatesWithCost names env store s value store cost := by simpa only [exactResult.2.2.1,exactResult.2.2.2] using r.evidence store
      have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mp raw
      have coreRaw := (e.evaluates_iff ids).mp raw
      have _ := (e.evaluates_iff ids).mpr coreRaw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps ids).mpr (manual store []))
      have _ := (e.evaluatesWithCost_iff_steps ids).mp counted
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e ids pending
      if legacyPure then
        let old ← pureChild ctx s; let oldCost ← pureCost env s
        have oldElab : LocalComputationElaborates names ctx s old.core old.type := .pure old.resolution old.lowered old.typing
        have oldCounted : LocalComputationEvaluatesWithCost names env store s oldCost.value store oldCost.cost := .pure (oldCost.evidence store)
        have _ := elaborateRecursiveLocalComputation?_iff.mpr oldElab.toRecursiveLocalComputation
        have _ := counted.deterministic oldCounted.toRecursiveLocalComputation
        check (decide (old.core = core ∧ old.type = type ∧ elaborateLocalComputation? names ctx s = some (core,type))) "pure/group overlap or old success changed"
      for fuel in List.range (cost+2) do
        have _ := (manual store []).runStateful_done_iff (fuel := fuel)
        match Core.runStateful fuel (.initial core env.values store) with
        | .done v t => check (decide (cost ≤ fuel ∧ v = value ∧ t = store)) "literal actual result/cost"
        | .outOfFuel cp => check (decide (fuel < cost ∧ Core.runStateful (cost-fuel) cp = .done value store)) "genuine checkpoint residual"
        | .fault _ _ => throw (IO.userError "actual smoke fault")
      for cutoff in [0,1,3,8] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading ++ suffix = env.values := List.take_append_drop cutoff env.values
        for inserted in [Core.Value.cellRef .word 99,.closure .bool .word (.var 19) [.unit]] do
          have original : Core.Evaluates (leading ++ suffix) store core value store := by rw [same]; exact coreRaw
          have changed := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
          have _ := (fragment.evaluates_insert_iff leading suffix inserted).mp changed
          have paired : ∀ k, Core.Steps cost ⟨.eval core (leading++suffix),k,store⟩ ⟨.ret value,k,store⟩ ∧
              Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading++inserted::suffix),k,store⟩ ⟨.ret value,k,store⟩ := by
            obtain ⟨n,paths⟩ := fragment.insertion_paths leading suffix inserted original
            have fixedCost : n = cost := ((paths []).1.final_unique (by simpa only [same,env,Core.State.final] using manual store [])).1
            exact fixedCost ▸ paths
          have _ := (paired pending).2
          check (decide (Core.runStateful cost ⟨.eval (core.weakenAt cutoff) (leading++inserted::suffix),pending,store⟩ =
            .outOfFuel ⟨.ret value,pending,store⟩)) "inserted caller pending endpoint"
  else throw (IO.userError "independent static/raw/manual expectations disagree")
private theorem invoke {env : Core.Environment} {fn arg : Core.Expr} {a b : Core.Ty} {body : Core.Expr}
    {captured : Core.Environment} {v result : Core.Value} {fc ac : Nat}
    (f : ∀ store k, Core.Steps fc ⟨.eval fn env,k,store⟩ ⟨.ret (.closure a b body captured),k,store⟩)
    (x : ∀ store k, Core.Steps ac ⟨.eval arg env,k,store⟩ ⟨.ret v,k,store⟩)
    (resultPath : ∀ store, Core.Steps 1 (.initial body (v::captured) store) (.final result store)) :
    ∀ store k, Core.Steps (fc+ac+1+3) ⟨.eval (.apply fn arg) env,k,store⟩ ⟨.ret result,k,store⟩ :=
  fun store _ => CostStepComposition.apply (f store _) (x store _) (resultPath store)
end ParsedRecursiveLocalComputation
open ParsedRecursiveLocalComputation
def frontendParsedRecursiveLocalComputationTests : IO Unit := do
  for a in [Core.Ty.unit,.word,.namedData ⟨7⟩,.function (.namedData ⟨8⟩) (.namedData ⟨9⟩)] do
    for b in [Core.Ty.bool,.unit,.namedData ⟨11⟩] do
      for c in [Core.Ty.word,.cell .word,.function (.namedData ⟨12⟩) (.namedData ⟨13⟩)] do
        for depth in [0,3,17,40] do
          for (s,core,t) in [("f(g(x))",.apply (.var 1) (call 2 0),c),
              ("(maker(x))(y)",.apply (call 3 0) (.var 4),b),
              ("f((maker(x))(y))",.apply (.var 1) (.apply (call 3 0) (.var 4)),c),
              ("f(p((x,())))",.apply (.var 1) (.apply (.var 6) (.pair (.var 0) .unit)),c),
              ("(c ? f : f)(g(c ? x : y))",.apply (.ifE (.var 5) (.var 1) (.var 1)) (.apply (.var 2) (.ifE (.var 5) (.var 0) (.var 4))),c)] do
            staticCheck a b c (grouped depth s) core t
        staticCheck a b c "((x))" (.var 0) a true
        staticCheck a b c "g(x)" (call 2 0) b true
  staticCheck .word .word .word "f(g(x - y))" (.apply (.var 1) (.apply (.var 2) (.binary .wordSub (.var 0) (.var 4)))) .word
  for (type,x,y) in [(Core.Ty.unit,Core.Value.unit,Core.Value.unit),(.word,.word (Core.Word.ofNatModulo 17),.word (Core.Word.ofNatModulo 5))] do
    let leaf (index : Nat) (v : Core.Value) (found : (environment type x y).values[index]? = some v) :
        ∀ store k, Core.Steps 1 ⟨.eval (.var index) (environment type x y).values,k,store⟩ ⟨.ret v,k,store⟩ := fun _ _ => .cons (.var found) .refl
    let gx := invoke (leaf 2 (identity type) rfl) (leaf 0 x rfl) (fun _ => .cons (.var rfl) .refl)
    let fx := invoke (leaf 1 (identity type) rfl) gx (fun _ => .cons (.var rfl) .refl)
    let maker := invoke (leaf 3 (.closure type (.function type type) (.var 1) [identity type]) rfl) (leaf 0 x rfl) (fun _ => .cons (.var rfl) .refl)
    let applied := invoke maker (leaf 4 y rfl) (fun _ => .cons (.var rfl) .refl)
    exercise type x y "((x))" (.var 0) x 1 (leaf 0 x rfl) true
    exercise type x y "g(x)" (call 2 0) x 6 gx
    for depth in [0,5,23] do
      exercise type x y (grouped depth "f(g(x))") (.apply (.var 1) (call 2 0)) x 11 fx
      exercise type x y (grouped depth "(maker(x))(y)") (.apply (call 3 0) (.var 4)) y 11 applied
    exercise type x y "f((maker(x))(y))" (.apply (.var 1) (.apply (call 3 0) (.var 4))) y 16
      (invoke (leaf 1 (identity type) rfl) applied (fun _ => .cons (.var rfl) .refl))
  staticCheck .word .word .word "f(g(x)) + x" (.binary .wordAdd (.apply (.var 1) (call 2 0)) (.var 0)) .word
  staticCheck .word .word .word "c ? f(g(x)) : x" (.ifE (.var 5) (.apply (.var 1) (call 2 0)) (.var 0)) .word
  for text in ["!g(x)","f()","f(x,y)","f(g(Missing))",
      "x(y)","f(c)","g(c ? x : Missing)","(lam(z: Word){return z;})(x)"] do
    let s ← parsed text
    check ((elaborateRecursiveLocalComputation? names (context .word .word .word) s).isNone) "outside recursive-call profile"
  let sourceText := "function example(f:F,g:F,x:A) returns(A){return f(g(x));}"
  let file : Syntax.SourceFile := ⟨⟨.main,"unchanged-entry.sol"⟩,sourceText⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "whole lexer")
  let .ok decl next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "whole parser")
  let ts : TypeNameTable := [(["F"],.function .word .word),(["A"],.word)]
  let some inputs := declareRuntimeParameters? ts owner decl.value.signature.parameters.elements | throw (IO.userError "valid original parameters")
  let [⟨_,.returnStmt (some expression)⟩] := decl.value.body.value | throw (IO.userError "original singleton body")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (interpretRuntimeFunctionHeader? ts decl.value.signature = some .word) &&
    decide (inputs.names = [("x",⟨owner,2⟩),("g",⟨owner,1⟩),("f",⟨owner,0⟩)] ∧ inputs.context =
      [(⟨owner,2⟩,.word),(⟨owner,1⟩,.function .word .word),(⟨owner,0⟩,.function .word .word)] ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context expression = some (.apply (.var 2) (call 1 0),.word)) &&
    (elaborateLocalComputationReturnTree? ts owner inputs decl.value.body).isNone &&
    (compileRuntimeFunction? ts owner decl).isNone && (compileRuntimeApplicationFunction? ts owner decl).isNone &&
    (compileRuntimeComputationFunction? ts owner decl).isNone) "valid original header/rows and recursive child did not retain old body/entry boundary"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveBinaryComputationProperties
/-! Symbolic original binary operands and actual delayed closure bodies.
Primitive success is supplied independently; checking never supplies raw values. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveBinaryComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Binary", by decide⟩], by decide⟩⟩, 56⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "binary.sol"⟩, 0, 1024⟩
private def operatorSpan : Syntax.SourceSpan := ⟨span.source, 500, 501⟩
private def inputs : LocalTypeInputs := ⟨[⟨"f", id 0, .function .word .word⟩, ⟨"x", id 1, .word⟩,
  ⟨"g", id 2, .function .word .word⟩, ⟨"y", id 3, .word⟩], by decide⟩
private def fn (side : Bool) := if side then "g" else "f"
private def seed (side : Bool) := if side then "y" else "x"
private def fi (side : Bool) := if side then 2 else 0
private def xi (side : Bool) := if side then 3 else 1
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (seed side)
  | n + 1 => ⟨span, .call (ref (fn side)) ⟨span, [calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (xi side)
  | n + 1 => .apply (.var (fi side)) (callCore side n)
private def source (sourceOp : Syntax.BinaryOp) (n k : Nat) : Syntax.Expr :=
  ⟨span, .binary (calls false n) ⟨operatorSpan, sourceOp⟩ (calls true k)⟩
private def core (op : Core.BinaryOp) (n k : Nat) : Core.Expr := .binary op (callCore false n) (callCore true k)
private def body (sourceOp : Syntax.BinaryOp) (n k : Nat) : Syntax.Block :=
  ⟨span, [⟨span, .letDecl ⟨span, "r"⟩ none (some (source sourceOp n k))⟩, ⟨span, .returnStmt (some (ref "r"))⟩]⟩
private def bodyCore (op : Core.BinaryOp) (n k : Nat) : Core.Expr := .letE (core op n k) (.var 0)
private theorem leaf (side : Bool) (function : Bool) :
    LocalComputationElaborates inputs.names inputs.context (ref (if function then fn side else seed side))
      (.var (if function then fi side else xi side)) (if function then .function .word .word else .word) := by
  let index := if function then fi side else xi side
  exact .pure (resolved := .var (id index)) (.identifier (LocalNameTable.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases side <;> cases function <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
private theorem callsElab (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (calls side n) (callCore side n) .word := by
  induction n with
  | zero => exact (leaf side false).toRecursiveLocalComputation
  | succ n ih => exact .application (leaf side true).toRecursiveLocalComputation ih
private theorem callsTyped (side : Bool) (n : Nat) : RecursiveLocalComputationHasType inputs.names inputs.context (calls side n) .word := by
  have atom (function : Bool) : RecursiveLocalComputationHasType inputs.names inputs.context
      (ref (if function then fn side else seed side)) (if function then .function .word .word else .word) :=
    .pure (.identifier (id := id (if function then fi side else xi side))
      (LocalNameTable.lookup?_iff.mp (by cases side <;> cases function <;> rfl))
      (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
  induction n with
  | zero => exact atom false
  | succ n ih => exact .application (atom true) ih
private theorem elaboration {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source sourceOp n k) (core op n k) op.resultType :=
  .binary operator (by cases operator <;> exact callsElab false n) (by cases operator <;> exact callsElab true k)
private theorem bodyElab {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body sourceOp n k) (bodyCore op n k) op.resultType :=
  .inferred (elaboration operator n k) (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private structure Actual where
  x : Core.Word
  y : Core.Word
  m : Nat
  t : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def value (a : Actual) (side : Bool) : Core.Value := .word (if side then a.y else a.x)
private def depth (a : Actual) (side : Bool) := if side then a.t else a.m
private def capture (a : Actual) (side : Bool) := if side then a.rightCapture else a.leftCapture
private def closure (a : Actual) (side : Bool) : Core.Value := .closure .word .word (delay (depth a side) 0) (capture a side)
private def env (a : Actual) : Resolved.Environment := [(id 0, closure a false), (id 1, value a false), (id 2, closure a true), (id 3, value a true)]
private def charge (n m : Nat) := n * (3 * m + 5) + 1
private def cost (a : Actual) (n k : Nat) := charge n a.m + charge k a.t + 3
private theorem delayed (m index : Nat) (v : Core.Value) (rest : Core.Environment) (s : Core.Store) (frames : List Core.Frame)
    (found : (v :: rest)[index]? = some v) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (v :: rest), frames, s⟩ ⟨.ret v, frames, s⟩ := by
  induction m generalizing index rest frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (v :: rest) frames (by simpa using found))))
private theorem callsCost (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (calls side n) (value a side) s (charge n (depth a side)) := by
  have atom (function : Bool) : LocalComputationEvaluatesWithCost inputs.names (env a) s
      (ref (if function then fn side else seed side)) (if function then closure a side else value a side) s 1 :=
    .pure (.identifier (id := id (if function then fi side else xi side))
      (LocalNameTable.lookup?_iff.mp (by cases side <;> cases function <;> rfl))
      (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
  induction n with
  | zero => simpa [charge, calls] using (atom false).toRecursiveLocalComputation
  | succ n ih =>
      have count : charge (n + 1) (depth a side) = 1 + charge n (depth a side) + (3 * depth a side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact .application (atom true).toRecursiveLocalComputation ih (delayed (depth a side) 0 (value a side) (capture a side) s [] rfl)
private theorem callsPath (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval (callCore side n) (env a).values, frames, s⟩ ⟨.ret (value a side), frames, s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n + 1) (depth a side) = 1 + charge n (depth a side) + (3 * depth a side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _) (delayed (depth a side) 0 (value a side) (capture a side) s [] rfl)
private theorem counted {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op)
    (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source sourceOp n k) result s (cost a n k) :=
  .binary operator (callsCost a false n s) (callsCost a true k s) applied
private theorem manual {op : Core.BinaryOp} (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) :
    Core.Steps (cost a n k) ⟨.eval (core op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ :=
  CostStepComposition.binary (callsPath a false n s _) (callsPath a true k s _) applied

theorem original_operator_and_whole_static {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    directWordBinary? sourceOp = some op ∧
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source sourceOp n k) = some (core op n k, op.resultType) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source sourceOp n k) op.resultType ∧
    Core.HasType inputs.context.values (core op n k) op.resultType := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source sourceOp n k) op.resultType :=
    .binary operator (by cases operator <;> exact callsTyped false n) (by cases operator <;> exact callsTyped true k)
  exact ⟨directWordBinary?_iff.mpr operator, elaborateRecursiveLocalComputation?_iff.mpr (elaboration operator n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed), (elaboration operator n k).core_hasType⟩

theorem raw_and_exact_core_agree {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env a) s (source sourceOp n k) result s ∧
    Core.Evaluates (env a).values s (core op n k) result s ∧
    Core.Steps (cost a n k) ⟨.eval (core op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ := by
  have raw : RecursiveLocalComputationEvaluates inputs.names (env a) s (source sourceOp n k) result s :=
    .binary operator (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, callsCost a false n s⟩)
      (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, callsCost a true k s⟩) applied
  have exactCost := ((elaboration operator n k).evaluatesWithCost_iff_steps (environment := env a) rfl).mpr
    (manual a n k s result applied [])
  exact ⟨raw, ((elaboration operator n k).evaluates_iff rfl).mp raw,
    exactCost.toStepsWithContinuation (elaboration operator n k) rfl frames⟩

theorem independent_actual_cost_unique {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result)
    {other : Core.Value} {finalStore : Core.Store} {otherCost : Nat}
    (otherEvaluation : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source sourceOp n k) other finalStore otherCost) :
    other = result ∧ finalStore = s ∧ otherCost = n * (3 * a.m + 5) + k * (3 * a.t + 5) + 5 := by
  obtain ⟨sameValue, sameStore, sameCost⟩ := otherEvaluation.deterministic (counted operator a n k s result applied)
  exact ⟨sameValue, sameStore, by simp only [cost, charge] at sameCost; omega⟩

theorem arbitrary_inserted_slot_preserves_paths {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading ++ suffix = (env a).values) :
    RecursiveLocalComputationFragment ((core op n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost a n k) ⟨.eval ((core op n k).weakenAt leading.length) (leading ++ inserted :: suffix), frames, s⟩
      ⟨.ret result, frames, s⟩ := by
  have fragment := (elaboration operator n k).core_fragment
  have original := Core.steps_from_initial_sound (manual a n k s result applied [])
  rw [← split] at original
  have transported := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
  have reflected := (fragment.evaluates_insert_iff leading suffix inserted).mp transported
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted reflected
  have known : Core.Steps (cost a n k) (.initial (core op n k) (leading ++ suffix) s) (.final result s) := by
    rw [split]; exact manual a n k s result applied []
  have sameCost := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length, fun frames => sameCost ▸ (paths frames).2⟩

private def between (a : Actual) (op : Core.BinaryOp) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (value a false), [.binaryRight op (callCore true k) (env a).values], s⟩
private def pending (a : Actual) (op : Core.BinaryOp) (s : Core.Store) : Core.State :=
  ⟨.ret (value a true), [.binaryApply op (value a false)], s⟩
theorem genuine_operand_checkpoints (a : Actual) (op : Core.BinaryOp) (n k : Nat) (s : Core.Store)
    (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result) :
    Core.runStateful (charge n a.m + 1) (.initial (core op n k) (env a).values s) = .outOfFuel (between a op k s) ∧
    Core.runStateful (charge n a.m + charge k a.t + 2) (.initial (core op n k) (env a).values s) = .outOfFuel (pending a op s) := by
  constructor
  · apply Core.runStateful_outOfFuel_complete (next := ⟨.eval (callCore true k) (env a).values, [.binaryApply op (value a false)], s⟩)
    · simpa [Core.State.initial, core, between, depth, Nat.add_comm] using Core.Steps.cons .enterBinary (callsPath a false n s [.binaryRight op (callCore true k) (env a).values])
    · exact Core.advance_next_iff.mpr .enterBinaryRight
  · apply Core.runStateful_outOfFuel_complete (next := .final result s)
    · simpa [Core.State.initial, core, pending, depth, Nat.add_assoc, Nat.add_left_comm] using Core.Steps.cons .enterBinary
        ((callsPath a false n s [.binaryRight op (callCore true k) (env a).values]).trans
          (.cons .enterBinaryRight (callsPath a true k s [.binaryApply op (value a false)])))
    · exact Core.advance_next_iff.mpr (.applyBinary applied)

theorem all_fuels_and_full_checkpoint_resume (a : Actual) (op : Core.BinaryOp) (n k : Nat) (s : Core.Store)
    (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result)
    (fuel spent additional : Nat) (checkpoint : Core.State)
    (exhausted : Core.runStateful spent (.initial (core op n k) (env a).values s) = .outOfFuel checkpoint) :
    (Core.runStateful fuel (.initial (core op n k) (env a).values s) = .done result s ↔ cost a n k ≤ fuel) ∧
    spent < cost a n k ∧ Core.Steps (cost a n k - spent) checkpoint (.final result s) ∧
    Core.runStateful additional checkpoint = Core.runStateful (spent + additional) (.initial (core op n k) (env a).values s) := by
  have path := manual a n k s result applied []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff, residual.1, residual.2, Core.runStateful_resume exhausted additional⟩

theorem inferred_original_body_static {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body sourceOp n k) = some (bodyCore op n k, op.resultType) ∧
    RecursiveComputationReturnTreeHasType [] owner inputs (body sourceOp n k) op.resultType ∧
    Core.HasType inputs.context.values (bodyCore op n k) op.resultType := by
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab operator n k),
    (computationReturnTreeHasType_iff_elaborates (ChildHasType := RecursiveLocalComputationHasType)
      (ChildElab := RecursiveLocalComputationElaborates) recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_, bodyElab operator n k⟩,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab operator n k)⟩

private theorem bodyCounted {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op)
    (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body sourceOp n k) result s (cost a n k + 3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost, body, ref, Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted operator a n k s result applied)
    (.expression (.pure (.identifier .head .head)))
private theorem bodyManual {op : Core.BinaryOp} (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) :
    Core.Steps (cost a n k + 3) ⟨.eval (bodyCore op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ := by
  simpa [bodyCore, Nat.add_assoc] using CostStepComposition.letE (manual a n k s result applied (.letBody (.var 0) (env a).values :: frames))
    (Core.Steps.cons (.var rfl) .refl)

theorem shared_body_transports_actual_cost {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) (fuel : Nat) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body sourceOp n k) result s (cost a n k + 3) ∧
    Core.Steps (cost a n k + 3) ⟨.eval (bodyCore op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ ∧
    (Core.runStateful fuel (.initial (bodyCore op n k) (env a).values s) = .done result s ↔ cost a n k + 3 ≤ fuel) := by
  have reflected := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab operator n k) (environment := env a) rfl).mpr
      (bodyManual a n k s result applied [])
  exact ⟨reflected, ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
    (bodyCounted operator a n k s result applied) (bodyElab operator n k) rfl frames,
    (bodyManual a n k s result applied []).runStateful_done_iff⟩

theorem fixed_source_actual_body_cost_is_unbounded (limit : Nat) (x y : Core.Word) (s : Core.Store) :
    ∃ a : Actual, RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s
      (body .add 1 1) (.word (x + y)) s (cost a 1 1 + 3) ∧ limit < cost a 1 1 + 3 := by
  let a : Actual := ⟨x, y, limit, 0, [], []⟩
  refine ⟨a, bodyCounted .add a 1 1 s (.word (x + y)) rfl, ?_⟩
  simp [cost, charge, a]; omega

theorem pending_continuation_is_not_a_safety_claim (s : Core.Store) :
    Core.Steps 5 ⟨.eval (core .wordGt 0 0) (env ⟨.zero, .zero, 0, 0, [], []⟩).values, [.unaryApply .wordNot], s⟩
      ⟨.ret (.bool false), [.unaryApply .wordNot], s⟩ ∧
    Core.runStateful 0 ⟨.ret (.bool false), [.unaryApply .wordNot], s⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool false)) ⟨.ret (.bool false), [.unaryApply .wordNot], s⟩ :=
  ⟨manual ⟨.zero, .zero, 0, 0, [], []⟩ 0 0 s (.bool false) rfl [.unaryApply .wordNot], rfl⟩

end Tests.FrontendRecursiveBinaryComputation
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveComputationBodyProperties
/-! Independent original mixed-body evidence instantiates the separate child
contracts. Hidden Core binders do not become source names or actual captures. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveComputationBody
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Shared", by decide⟩], by decide⟩⟩, 54⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def xid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def cid : Resolved.LocalId := ⟨owner, 2⟩
private def gid : Resolved.LocalId := ⟨owner, 8⟩
private def rid : Resolved.LocalId := ⟨owner, 18⟩
private def inputs (a : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x", xid, a⟩, ⟨"f", fid, .function a a⟩, ⟨"c", cid, .bool⟩, ⟨"f", gid, .unit⟩], by change [xid, fid, cid, gid].Nodup; decide⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Payload"], a)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "shared-body.sol"⟩, 254, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref "x"
  | n + 1 => ⟨span, .call (ref "f") ⟨span, [calls n]⟩⟩
private def callCore : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .apply (.var 1) (callCore n)
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def tail : List Syntax.Statement := [⟨span, .expression (ref "r") true⟩,
  ⟨span, .ifThen (ref "c") (returned "r") (some (returned "x"))⟩]
private def body (annotated : Bool) (n : Nat) : Syntax.Block :=
  ⟨span, [⟨span, .block (⟨span, .letDecl ⟨span, "r"⟩ (if annotated then some annotation else none) (some (calls n))⟩ :: tail)⟩]⟩
private def tailCore : Core.Expr := .letE (.var 0) (.ifE (.var 4) (.var 1) (.var 2))
private def core (n : Nat) : Core.Expr := .letE (callCore n) tailCore
private theorem childElab (n : Nat) (a : Core.Ty) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (calls n) (callCore n) a := by
  induction n with
  | zero => exact .pure (.identifier .head) (.var .head) (.var .head)
  | succ n ih => exact .application (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head))
      (.var (.tail (by change xid ≠ fid; decide) .head)) (.var (.tail (by change xid ≠ fid; decide) .head))) ih
private theorem tailElab (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) owner ((inputs a).bindFresh owner "r" a) ⟨span, tail⟩ tailCore a := by
  have branch : RecursiveComputationReturnTreeElaborates (types a) owner ((inputs a).bindFresh owner "r" a)
      ⟨span, [⟨span, .ifThen (ref "c") (returned "r") (some (returned "x"))⟩]⟩ (.ifE (.var 3) (.var 0) (.var 1)) a := by
    exact .conditional (.pure (.identifier (.tail (by change "r" ≠ "c"; decide) (.tail (by change "x" ≠ "c"; decide) (.tail (by change "f" ≠ "c"; decide) .head))))
      (.var (.tail (by change rid ≠ cid; decide) (.tail (by change xid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) .head))))
      (.var (.tail (by change rid ≠ cid; decide) (.tail (by change xid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) .head)))))
      (computationBlockPreservesNames_iff.mp (by simp only [returned, computationBlockPreservesNames]))
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
      (.expression (.pure (.identifier (.tail (by change "r" ≠ "x"; decide) .head)) (.var (.tail (by change rid ≠ xid; decide) .head))
        (.var (.tail (by change rid ≠ xid; decide) .head))))
  have first : RecursiveLocalComputationElaborates ((inputs a).bindFresh owner "r" a).names
      ((inputs a).bindFresh owner "r" a).context (ref "r") (.var 0) a := .pure (.identifier .head) (.var .head) (.var .head)
  simpa [tail, tailCore, Core.Expr.weakenAt] using ComputationReturnTreeElaborates.discard first branch
private theorem provenance (annotated : Bool) (n : Nat) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) (body annotated n) (core n) a := by
  cases annotated
  · exact .block (.inferred (childElab n a) (tailElab a))
  · exact .block (.binding (.named .head) (childElab n a) (tailElab a))
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def env (m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) : Resolved.Environment :=
  [(xid, value), (fid, .closure .unit .unit (delay m 0) captures), (cid, .bool flag), (gid, .unit)]
private def charge (n m : Nat) : Nat := n * (3 * m + 5) + 1
private theorem delayed (m index : Nat) (value : Core.Value) (rest : Core.Environment) (store : Core.Store)
    (k : List Core.Frame) (found : (value :: rest)[index]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (value :: rest), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction m generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (value :: rest) k (by simpa using found))))
private theorem childCost (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs .unit).names (env m value captures flag) store (calls n) value store (charge n m) := by
  induction n with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .pure (.identifier .head .head)
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact .application (.pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head))) ih (delayed m 0 value captures store [] rfl)
private theorem childPath (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m) ⟨.eval (callCore n) (env m value captures flag).values, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing k with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) (delayed m 0 value captures store [] rfl)
private theorem tailCost (m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (("r", rid) :: (inputs .unit).names)
      ((rid, value) :: env m value captures flag) store ⟨span, tail⟩ value store 7 := by
  refine ComputationReturnTreeEvaluatesWithCost.discard (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (expressionCost := 1) (tailCost := 4) (middleStore := store) (discardedValue := value) ?_ ?_
  · exact .pure (.identifier .head .head)
  cases flag
  · refine ComputationReturnTreeEvaluatesWithCost.ifFalse (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      (middleStore := store) (conditionCost := 1) (branchCost := 1) ?_ ?_
    · exact .pure (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
        (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    · exact .expression (.pure (.identifier (.tail (by decide) .head) (.tail (by decide) .head)))
  · refine ComputationReturnTreeEvaluatesWithCost.ifTrue (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      (middleStore := store) (conditionCost := 1) (branchCost := 1) ?_ ?_
    · exact .pure (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
        (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    · exact .expression (.pure (.identifier .head .head))
private theorem counted (annotated : Bool) (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m value captures flag)
      store (body annotated n) value store (charge n m + 9) := by
  cases annotated <;> apply ComputationReturnTreeEvaluatesWithCost.block
  · exact .inferred (childCost n m value captures flag store) (tailCost m value captures flag store)
  · exact .binding (childCost n m value captures flag store) (tailCost m value captures flag store)
private theorem manual (n m : Nat) (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m + 9) ⟨.eval (core n) (env m value captures flag).values, k, store⟩ ⟨.ret value, k, store⟩ := by
  have tailPath : Core.Steps 7 ⟨.eval tailCore (value :: (env m value captures flag).values), k, store⟩ ⟨.ret value, k, store⟩ := by
    cases flag <;> exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet
      (.cons .enterIf (.cons (.var rfl) (.cons (by constructor) (.cons (.var rfl) .refl))))))
  simpa [core, Nat.add_assoc] using CostStepComposition.letE (childPath n m value captures flag store _) tailPath

theorem independent_original_body_and_actual_cost (annotated : Bool) (n m : Nat) (a : Core.Ty)
    (value : Core.Value) (captures : Core.Environment) (flag : Bool) (store : Core.Store) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) (body annotated n) (core n) a ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m value captures flag)
      store (body annotated n) value store (charge n m + 9) ∧
    ∀ k, Core.Steps (charge n m + 9) ⟨.eval (core n) (env m value captures flag).values, k, store⟩ ⟨.ret value, k, store⟩ :=
  ⟨provenance annotated n a, counted annotated n m value captures flag store, manual n m value captures flag store⟩

theorem independent_static_contracts (annotated : Bool) (n : Nat) (a : Core.Ty) :
    elaborateRecursiveComputationReturnTree? (types a) owner (inputs a) (body annotated n) = some (core n, a) ∧
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a) (body annotated n) a ∧
    Core.HasType (inputs a).context.values (core n) a :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (provenance annotated n a),
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_, provenance annotated n a⟩,
    (provenance annotated n a).core_hasType RecursiveLocalComputationElaborates.core_hasType⟩

theorem sparse_foreign_ids_and_first_spelling (a : Core.Ty) :
    Resolved.freshLocalId owner (inputs a).ids = rid ∧
    (inputs a).names.lookup? "f" = some fid ∧ ((inputs a).bindFresh owner "r" a).ids = rid :: (inputs a).ids := by
  exact ⟨rfl, rfl, rfl⟩

theorem raw_cost_without_runtime_typing (annotated : Bool) (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluates owner (inputs .unit).names (env m v cap flag) s (body annotated n) v s ∧
    ∀ w t c, RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m v cap flag) s (body annotated n) w t c →
      v = w ∧ s = t ∧ charge n m + 9 = c := by
  have known := counted annotated n m v cap flag s
  exact ⟨(computationReturnTreeEvaluates_iff_exists_cost recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨_, known⟩,
    fun _ _ _ other => ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationEvaluatesWithCost.deterministic known other⟩

theorem separate_child_execution_laws (annotated : Bool) (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    Core.Evaluates (env m v cap flag).values s (core n) v s ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m v cap flag) s (body annotated n) v s (charge n m + 9) ∧
    ∀ k, Core.Steps (charge n m + 9) ⟨.eval (core n) (env m v cap flag).values, k, s⟩ ⟨.ret v, k, s⟩ := by
  have e := provenance annotated n .unit
  have rawIff := ComputationReturnTreeElaborates.evaluates_iff (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff e (environment := env m v cap flag) rfl
    (initialStore := s) (finalStore := s) (value := v)
  have costIff := ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation e (environment := env m v cap flag) rfl
    (initialStore := s) (finalStore := s) (value := v) (cost := charge n m + 9)
  exact ⟨rawIff.mp (raw_cost_without_runtime_typing annotated n m v cap flag s).1,
    costIff.mpr (manual n m v cap flag s []), fun k =>
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
        (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
        RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (counted annotated n m v cap flag s) e rfl k⟩

theorem arbitrary_inserted_value_and_kept_prefix (n m : Nat) (v inserted : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store)
    (leading suffix : Core.Environment) (split : leading ++ suffix = (env m v cap flag).values) :
    ComputationBodyFragment RecursiveLocalComputationFragment ((core n).weakenAt leading.length) ∧
    (Core.Evaluates (leading ++ inserted :: suffix) s ((core n).weakenAt leading.length) v s ↔ Core.Evaluates (leading ++ suffix) s (core n) v s) ∧
    ∀ k, Core.Steps (charge n m + 9) ⟨.eval ((core n).weakenAt leading.length) (leading ++ inserted :: suffix), k, s⟩ ⟨.ret v, k, s⟩ := by
  have fragment := ComputationReturnTreeElaborates.core_fragment (ChildElab := RecursiveLocalComputationElaborates) (F := RecursiveLocalComputationFragment)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt (provenance false n .unit)
  have original : Core.Steps (charge n m + 9) (.initial (core n) (leading ++ suffix) s) (.final v s) := split ▸ manual n m v cap flag s []
  obtain ⟨actual, paths⟩ := ComputationBodyFragment.insertion_paths RecursiveLocalComputationFragment.insertion_paths fragment leading suffix inserted (Core.steps_from_initial_sound original)
  have same := (original.final_unique (paths []).1).1
  exact ⟨fragment.weakenAt RecursiveLocalComputationFragment.weakenAt _,
    fragment.evaluates_insert_iff RecursiveLocalComputationFragment.evaluates_insert_iff leading suffix inserted,
    fun k => same.symm ▸ (paths k).2⟩

theorem all_fuel_and_genuine_checkpoint (n m fuel spent : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store)
    (checkpoint : Core.State) (genuine : Core.runStateful spent (.initial (core n) (env m v cap flag).values s) = .outOfFuel checkpoint) :
    (Core.runStateful fuel (.initial (core n) (env m v cap flag).values s) = .done v s ↔ charge n m + 9 ≤ fuel) ∧
    Core.Steps (charge n m + 9 - spent) checkpoint (.final v s) ∧
    ∀ additional, Core.runStateful additional checkpoint = Core.runStateful (spent + additional) (.initial (core n) (env m v cap flag).values s) :=
  ⟨(manual n m v cap flag s []).runStateful_done_iff, ((manual n m v cap flag s []).residual_of_outOfFuel genuine).2,
    Core.runStateful_resume genuine⟩

private def oldBody : Syntax.Block := ⟨span, [⟨span, .expression ⟨span, .tuple ⟨span, []⟩⟩ true⟩, ⟨span, .returnStmt none⟩]⟩
theorem old_exact_evidence_embeds_unchanged (a : Core.Ty) (environment : Resolved.Environment) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) oldBody (.letE .unit .unit) .unit ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a).names environment s oldBody .unit s 4 := by
  have old : LocalComputationReturnTreeElaborates (types a) owner (inputs a) oldBody (.letE .unit .unit) .unit := by
    simpa [oldBody, Core.Expr.weakenAt] using LocalComputationReturnTreeElaborates.discard
      (blockSpan := span) (statementSpan := span) (types := types a) (owner := owner) (inputs := inputs a)
      (.pure (.unit (span := span) (tupleSpan := span)) .unit .unit) (.bare (returnSpan := span))
  have actual : LocalComputationReturnTreeEvaluatesWithCost owner (inputs a).names environment s oldBody .unit s 4 := .discard (.pure .unit) .bare
  exact ⟨old.toRecursiveComputationReturnTree, actual.toRecursiveComputationReturnTree⟩

theorem same_typed_core_is_not_provenance (annotated : Bool) (n : Nat) (a : Core.Ty) :
    Core.HasType (inputs a).context.values (.var 0) a ∧
    ¬ RecursiveComputationReturnTreeElaborates (types a) owner (inputs a) (body annotated n) (.var 0) a := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have bad := (elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr forged
  change elaborateRecursiveComputationReturnTree? (types a) owner (inputs a) (body annotated n) = some (.var 0, a) at bad
  rw [(independent_static_contracts annotated n a).1] at bad
  cases bad

theorem missing_annotation_is_static_not_raw (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs .unit) (body true n) = none ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m v cap flag) s (body true n) v s (charge n m + 9) := by
  refine ⟨?_, counted true n m v cap flag s⟩
  simp [elaborateRecursiveComputationReturnTree?, body, elaborateComputationReturnTree?, inputs,
    LocalTypeInputs.names, annotation, interpretStructuralType?, TypeNameTable.lookup?]

private def checkpoint (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) : Core.State :=
  ⟨.ret (.closure .unit .unit (delay m 0) cap),
    [.applyArgument (callCore n) (env m v cap flag).values, .letBody tailCore (env m v cap flag).values], s⟩
theorem actual_checkpoint_before_nested_argument (n m : Nat) (v : Core.Value) (cap : Core.Environment) (flag : Bool) (s : Core.Store) :
    Core.runStateful 3 (.initial (core (n + 1)) (env m v cap flag).values s) = .outOfFuel (checkpoint n m v cap flag s) ∧
    Core.Steps (charge (n + 1) m + 9 - 3) (checkpoint n m v cap flag s) (.final v s) ∧
    ∀ additional, Core.runStateful additional (checkpoint n m v cap flag s) =
      Core.runStateful (3 + additional) (.initial (core (n + 1)) (env m v cap flag).values s) := by
  have genuine : Core.runStateful 3 (.initial (core (n + 1)) (env m v cap flag).values s) = .outOfFuel (checkpoint n m v cap flag s) := rfl
  exact ⟨genuine, ((manual (n + 1) m v cap flag s []).residual_of_outOfFuel genuine).2, Core.runStateful_resume genuine⟩

theorem same_source_has_no_capture_body_cost_bound (limit : Nat) (s : Core.Store) :
    ∃ m, RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .unit).names (env m .unit [] true) s (body false 1) .unit s (charge 1 m + 9) ∧
      limit < charge 1 m + 9 := by
  exact ⟨limit, counted false 1 limit .unit [] true s, by simp [charge]; omega⟩

theorem continuation_endpoint_is_not_a_safety_claim (n m : Nat) (s : Core.Store) :
    Core.Steps (charge n m + 9) ⟨.eval (core n) (env m .unit [] true).values, [.unaryApply .wordNot], s⟩
      ⟨.ret .unit, [.unaryApply .wordNot], s⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], s⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], s⟩ :=
  ⟨manual n m .unit [] true s _, rfl⟩

end Tests.FrontendRecursiveComputationBody
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveLocalComputationProperties
/-! Original grouped call spines have independent source and machine proofs.
Static types, actual tags, captures and inserted caller slots stay separate. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveLocalComputation
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Recursive", by decide⟩], by decide⟩⟩, 53⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def xid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def gid : Resolved.LocalId := ⟨owner, 2⟩
private def names : LocalNameTable := [("f", fid), ("x", xid), ("f", gid)]
private def context (a : Core.Ty) : Resolved.Context := [(xid, a), (fid, .function a a), (gid, .unit), (fid, .unit)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive.sol"⟩, 253, 3⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def source (s t : Syntax.SourceSpan) : Nat → Syntax.Expr
  | 0 => ref s "x"
  | n + 1 => ⟨s, .call ⟨t, .group (ref s "f")⟩ ⟨t, [⟨s, .group (source s t n)⟩]⟩⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .apply (.var 1) (core n)
private theorem provenance (n : Nat) (a : Core.Ty) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationElaborates names (context a) (source s t n) (core n) a := by
  induction n with
  | zero => exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head)) (.var .head) (.var .head)
  | succ n ih =>
      exact .application (.group (.pure (.identifier .head)
        (.var (.tail (by change xid ≠ fid; decide) .head)) (.var (.tail (by change xid ≠ fid; decide) .head)))) (.group ih)
private theorem typing (n : Nat) (a : Core.Ty) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationHasType names (context a) (source s t n) a := by
  induction n with
  | zero => exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head)
  | succ n ih => exact .application (.group (.pure (.identifier .head (.tail (by change xid ≠ fid; decide) .head)))) (.group ih)
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def environment (m : Nat) (value : Core.Value) (captured : Core.Environment) : Resolved.Environment :=
  [(xid, value), (fid, .closure .unit .unit (delay m 0) captured), (gid, .unit), (fid, .bool false)]
private def charge (n m : Nat) : Nat := n * (3 * m + 5) + 1
private theorem bodyRaw (m index : Nat) (value : Core.Value) (rest : Core.Environment) (store : Core.Store)
    (found : (value :: rest)[index]? = some value) :
    Core.Evaluates (value :: rest) store (delay m index) value store := by
  induction m generalizing index rest with
  | zero => exact .var found
  | succ m ih => exact .letE (.var rfl) (ih (index + 1) (value :: rest) (by simpa using found))
private theorem bodyPath (m index : Nat) (value : Core.Value) (rest : Core.Environment) (store : Core.Store)
    (k : List Core.Frame) (found : (value :: rest)[index]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (value :: rest), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction m generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (value :: rest) k (by simpa using found))))
private theorem raw (n m : Nat) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationEvaluates names (environment m value captured) store (source s t n) value store := by
  induction n with
  | zero => exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head)
  | succ n ih =>
      exact .application (.group (.pure (.identifier .head (.tail (by change xid ≠ fid; decide) .head))))
        (.group ih) (bodyRaw m 0 value captured store rfl)
private theorem counted (n m : Nat) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store (source s t n) value store (charge n m) := by
  induction n with
  | zero =>
      simp only [charge, Nat.zero_mul, Nat.zero_add]
      exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head)
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact .application (.group (.pure (.identifier .head (.tail (by change xid ≠ fid; decide) .head)))) (.group ih)
        (bodyPath m 0 value captured store [] rfl)
private theorem manual (n m : Nat) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m) ⟨.eval (core n) (environment m value captured).values, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing k with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) (bodyPath m 0 value captured store [] rfl)

theorem arbitrary_depth_preserves_original_spans_and_independent_evidence
    (n m : Nat) (a : Core.Ty) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationElaborates names (context a) (source s t n) (core n) a ∧
    RecursiveLocalComputationHasType names (context a) (source s t n) a ∧
    RecursiveLocalComputationEvaluates names (environment m value captured) store (source s t n) value store ∧
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source s t n) value store (charge n m) ∧
    ∀ k, Core.Steps (charge n m) ⟨.eval (core n) (environment m value captured).values, k, store⟩ ⟨.ret value, k, store⟩ :=
  ⟨provenance n a s t, typing n a s t, raw n m value captured store s t,
    counted n m value captured store s t, manual n m value captured store⟩

theorem exact_static_provenance_rejects_another_same_typed_core (n : Nat) (a : Core.Ty) :
    elaborateRecursiveLocalComputation? names (context a) (source span span (n + 1)) = some (core (n + 1), a) ∧
    Core.HasType (context a).values (core (n + 1)) a ∧ Core.HasType (context a).values (.var 0) a ∧
    (∃ expected, RecursiveLocalComputationElaborates names (context a) (source span span (n + 1)) expected a) ∧
    ¬ RecursiveLocalComputationElaborates names (context a) (source span span (n + 1)) (.var 0) a := by
  have accepted := elaborateRecursiveLocalComputation?_iff.mpr (provenance (n + 1) a span span)
  refine ⟨accepted, (provenance (n + 1) a span span).core_hasType, .var rfl,
    recursiveLocalComputationHasType_iff_elaborates.mp (typing (n + 1) a span span), ?_⟩
  intro other
  have impossible := accepted.symm.trans (elaborateRecursiveLocalComputation?_iff.mpr other)
  cases impossible

theorem supplied_raw_cost_reflects_exact_core_without_runtime_typing
    (n m : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    (∃ cost, RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source span span n) value store cost) ∧
    Core.Evaluates (environment m value captured).values store (core n) value store ∧
    (RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source span span n) value store (charge n m) ↔
      Core.Steps (charge n m) (.initial (core n) (environment m value captured).values store) (.final value store)) ∧
    ∀ k, Core.Steps (charge n m) ⟨.eval (core n) (environment m value captured).values, k, store⟩ ⟨.ret value, k, store⟩ :=
  ⟨recursiveLocalComputationEvaluates_iff_exists_cost.mp (raw n m value captured store span span),
    ((provenance n .word span span).evaluates_iff rfl).mp (raw n m value captured store span span),
    (provenance n .word span span).evaluatesWithCost_iff_steps rfl,
    fun k => (counted n m value captured store span span).toStepsWithContinuation (provenance n .word span span) rfl k⟩

theorem all_other_successes_have_the_independent_value_store_and_cost
    (n m : Nat) (value other : Core.Value) (captured : Core.Environment) (store final : Core.Store) (cost : Nat)
    (otherPath : RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store (source span span n) other final cost) :
    value = other ∧ store = final ∧ charge n m = cost :=
  (counted n m value captured store span span).deterministic otherPath

private def checkpoint (n m : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.eval (core n) (environment m value captured).values, [.applyClosure .unit .unit (delay m 0) captured], store⟩
theorem every_fuel_observes_the_independent_exact_cost
    (n m fuel : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    (Core.runStateful fuel (.initial (core (n + 1)) (environment m value captured).values store) = .done value store ↔ charge (n + 1) m ≤ fuel) ∧
    ((∃ cp, Core.runStateful fuel (.initial (core (n + 1)) (environment m value captured).values store) = .outOfFuel cp) ↔ fuel < charge (n + 1) m) :=
  ⟨(manual (n + 1) m value captured store []).runStateful_done_iff,
    (manual (n + 1) m value captured store []).runStateful_outOfFuel_iff⟩

theorem genuine_nested_argument_checkpoint_keeps_its_residual_and_frames
    (n m additional : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    Core.runStateful 3 (.initial (core (n + 1)) (environment m value captured).values store) = .outOfFuel (checkpoint n m value captured store) ∧
    Core.Steps (charge (n + 1) m - 3) (checkpoint n m value captured store) (.final value store) ∧
    Core.runStateful additional (checkpoint n m value captured store) =
      Core.runStateful (3 + additional) (.initial (core (n + 1)) (environment m value captured).values store) := by
  have stopped : Core.runStateful 3 (.initial (core (n + 1)) (environment m value captured).values store) =
      .outOfFuel (checkpoint n m value captured store) := by cases n <;> rfl
  exact ⟨stopped, ((manual (n + 1) m value captured store []).residual_of_outOfFuel stopped).2,
    Core.runStateful_resume stopped additional⟩

theorem arbitrary_caller_insertion_has_one_manual_cost_before_all_continuations
    (n m : Nat) (value inserted : Core.Value) (captured leading suffix : Core.Environment) (store : Core.Store)
    (split : leading ++ suffix = (environment m value captured).values) :
    Core.Evaluates (leading ++ inserted :: suffix) store ((core n).weakenAt leading.length) value store ∧
    Core.Evaluates (leading ++ suffix) store (core n) value store ∧
    ∃ cost, cost = charge n m ∧ ∀ k,
      Core.Steps cost ⟨.eval (core n) (leading ++ suffix), k, store⟩ ⟨.ret value, k, store⟩ ∧
      Core.Steps cost ⟨.eval ((core n).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret value, k, store⟩ := by
  have fragment := (provenance n .word span span).core_fragment
  have original := split ▸ Core.steps_from_initial_sound (manual n m value captured store [])
  have insertedEvaluation := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
  have recovered := (fragment.evaluates_insert_iff leading suffix inserted).mp insertedEvaluation
  obtain ⟨cost, paths⟩ := fragment.insertion_paths leading suffix inserted recovered
  exact ⟨insertedEvaluation, recovered, cost, ((paths []).1.final_unique (split ▸ manual n m value captured store [])).1, paths⟩

theorem syntactic_recursive_fragment_and_weakening_need_no_scoping (i j cutoff : Nat) :
    RecursiveLocalComputationFragment (.apply (.var i) (.apply (.var j) (.var i))) ∧
    RecursiveLocalComputationFragment ((Core.Expr.apply (.var i) (.apply (.var j) (.var i))).weakenAt cutoff) := by
  have fragment : RecursiveLocalComputationFragment (.apply (.var i) (.apply (.var j) (.var i))) :=
    .application (.pure .var) (.application (.pure .var) (.pure .var))
  exact ⟨fragment, fragment.weakenAt cutoff⟩

theorem insertion_preserves_a_pending_endpoint_not_its_safety (inserted : Core.Value) (store : Core.Store) :
    Core.Steps 11 ⟨.eval ((core 2).weakenAt 0) (inserted :: (environment 0 .unit []).values), [.unaryApply .wordNot], store⟩
      ⟨.ret .unit, [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], store⟩ := by
  obtain ⟨_, _, cost, rfl, paths⟩ := arbitrary_caller_insertion_has_one_manual_cost_before_all_continuations
    2 0 .unit inserted [] [] (environment 0 .unit []).values store rfl
  exact ⟨(paths _).2, rfl⟩

theorem pure_and_recursive_group_derivations_reconcile_the_same_actual_cost
    (m : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ value store 1 ∧
    ∀ other final cost, RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ other final cost → other = value ∧ final = store ∧ cost = 1 := by
  have purePath : RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ value store 1 := .pure (.group (.identifier (.tail (by decide) .head) .head))
  have recursivePath : RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ value store 1 := .group (.pure (.identifier (.tail (by decide) .head) .head))
  exact ⟨purePath, fun _ _ _ alternative => alternative.deterministic recursivePath⟩

theorem old_successes_embed_but_old_nested_call_rejection_remains (a : Core.Ty) (m : Nat)
    (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    RecursiveLocalComputationElaborates names (context a) (source span span 1) (core 1) a ∧
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source span span 1) value store (charge 1 m) ∧
    elaborateLocalComputation? names (context a) (source span span 2) = none := by
  have old : LocalComputationElaborates names (context a) (source span span 1) (core 1) a :=
    .application (.call (.group (.identifier .head)) (.var (.tail (by change xid ≠ fid; decide) .head))
      (.var (.tail (by change xid ≠ fid; decide) .head)) (.group (.identifier (.tail (by decide) .head))) (.var .head) (.var .head))
  have oldCost : LocalComputationEvaluatesWithCost names (environment m value captured)
      store (source span span 1) value store (charge 1 m) := by
    have count : charge 1 m = 1 + 1 + (3 * m + 1) + 3 := by simp [charge]; omega
    rw [count]
    exact .application (.call (.group (.identifier .head (.tail (by change xid ≠ fid; decide) .head)))
      (.group (.identifier (.tail (by decide) .head) .head)) (bodyPath m 0 value captured store [] rfl))
  refine ⟨old.toRecursiveLocalComputation, oldCost.toRecursiveLocalComputation, ?_⟩
  simp [elaborateLocalComputation?, elaborateLocalFunctionApplication?, source, elaborateLocalExpression?, resolveLocalExpression?]

private def computed : Syntax.Expr := ⟨span, .call (source span span 1) ⟨span, [⟨span, .tuple ⟨span, []⟩⟩]⟩⟩
theorem a_computed_callee_invokes_its_literal_captured_body (captured : Core.Value) (store : Core.Store) :
    let returned := Core.Value.closure .unit .unit (.var 1) [captured]
    RecursiveLocalComputationElaborates names (context (.function .unit .unit)) computed (.apply (core 1) .unit) .unit ∧
    RecursiveLocalComputationEvaluatesWithCost names (environment 0 returned []) store computed captured store 11 ∧
    ∀ k, Core.Steps 11 ⟨.eval (.apply (core 1) .unit) (environment 0 returned []).values, k, store⟩ ⟨.ret captured, k, store⟩ := by
  let returned := Core.Value.closure .unit .unit (.var 1) [captured]
  have body : Core.Steps 1 (.initial (.var 1) [.unit, captured] store) (.final captured store) := .cons (.var rfl) .refl
  refine ⟨.application (provenance 1 (.function .unit .unit) span span) (.pure .unit .unit .unit),
    .application (counted 1 0 returned [] store span span) (.pure .unit) body, ?_⟩
  intro k
  exact CostStepComposition.apply (manual 1 0 returned [] store _) (.cons .unit .refl) body

theorem nominal_static_paths_do_not_manufacture_an_argument (n : Nat) (nominal : Core.DataTypeId) :
    RecursiveLocalComputationHasType names (context (.namedData nominal)) (source span span n) (.namedData nominal) ∧
    Core.ValueHasType (.closure (.namedData nominal) (.namedData nominal) (.var 0) [])
      (.function (.namedData nominal) (.namedData nominal)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨typing n _ span span, .closure .nil (.var rfl), ?_⟩
  rintro ⟨value, typed⟩; cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def skipped : Syntax.Expr :=
  ⟨span, .group ⟨span, .conditional (ref span "x") span (ref span "f") span
    ⟨span, .call (ref span "missing") ⟨span, [source span span 2]⟩⟩⟩⟩
theorem pure_group_overlap_preserves_unselected_unsupported_source (value : Core.Value) (store : Core.Store) :
    let env : Resolved.Environment := [(xid, .bool true), (fid, value), (gid, .unit), (fid, .unit)]
    RecursiveLocalComputationEvaluates names env store skipped value store ∧
    RecursiveLocalComputationEvaluatesWithCost names env store skipped value store 4 ∧
    elaborateRecursiveLocalComputation? names (context .bool) skipped = none := by
  refine ⟨.pure (.group (.ifTrue (.identifier (.tail (by decide) .head) .head)
    (.identifier .head (.tail (by decide) .head)))),
    .group (.pure (.ifTrue (conditionCost := 1) (branchCost := 1)
      (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head)))), ?_⟩
  simp [elaborateRecursiveLocalComputation?, skipped, ref, elaborateLocalExpression?,
    resolveLocalExpression?, names, LocalNameTable.lookup?]

end Tests.FrontendRecursiveLocalComputation
end
