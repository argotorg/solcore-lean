import Solcore.Frontend.ClosedSource
import Solcore.Frontend.StrictWordBinary
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Syntax.Parser.Term

/- Actual parsed grouped references, fourteen operator spellings, five unsigned
Word pairs and two separate raw/Core stores. Original closed and local-cost
witnesses are constructed before running either machine. No data gate, runtime
typing of opaque tails, source/Core closure identity or parser proof is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedClosedStrictWordBinary
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedStrictWord",by decide⟩],by decide⟩⟩,300⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex:=903}
private def fid : Resolved.LocalId := ⟨foreign,700⟩
private def names : LocalNameTable := [("x",sid 7),("y",sid 31),("x",fid)]
private def opaqueCore : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite,.cellRef .word 700]
private def rawRows (p : RuntimeValue) (a b : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(sid 0,p),(sid 7,.word a),(sid 31,.word b),(sid 7,.unit),(fid,p)]
private def coreRows (a b : Core.Word) : Resolved.Environment :=
  [(sid 7,.word a),(sid 31,.word b),(sid 7,opaqueCore),(fid,.cellRef .word 900)]
private def context : Resolved.Context := [(sid 7,.word),(sid 31,.word),(sid 7,.unit),(fid,.unit)]
private def range (file : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨file.id,a,b⟩
private def leaf (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def binary (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat) : Syntax.Expr :=
  ⟨range f 1 (w+5),.binary (leaf (range f 1 2) "x") ⟨range f 3 (w+3),op⟩
    (leaf (range f (w+4) (w+5)) "y")⟩
private def source (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat) : Syntax.Expr :=
  ⟨range f 0 (w+6),.group (binary f op w)⟩
private def overhead : Syntax.BinaryOp → Nat
  | .notEqual | .lessEqual => 5
  | .less => 9
  | .greaterEqual => 11
  | _ => 3
private def primitive (op : Syntax.BinaryOp) (a b : Core.Word) :
    Option {value : Core.Value // StrictWordBinaryDenotes op a b value} :=
  match op with
  | .add => some ⟨.word (a.add b),.add⟩
  | .subtract => some ⟨.word (a.sub b),.subtract⟩
  | .multiply => some ⟨.word (a.mul b),.multiply⟩
  | .divide => some ⟨.word (a.udiv b),.divide⟩
  | .modulo => some ⟨.word (a.umod b),.modulo⟩
  | .bitAnd => some ⟨.word (a.bitAnd b),.bitAnd⟩
  | .bitOr => some ⟨.word (a.bitOr b),.bitOr⟩
  | .bitXor => some ⟨.word (a.bitXor b),.bitXor⟩
  | .greater => some ⟨.bool (decide (a>b)),.greater⟩
  | .less => some ⟨.bool (decide (a<b)),.less⟩
  | .equal => some ⟨.bool (a==b),.equal⟩
  | .notEqual => some ⟨.bool (!(a==b)),.notEqual⟩
  | .lessEqual => some ⟨.bool (!(decide (a>b))),.lessEqual⟩
  | .greaterEqual => some ⟨.bool (!(decide (a<b))),.greaterEqual⟩
  | .logicalAnd | .logicalOr => none
private theorem original (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (p : RuntimeValue) (store : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner names (rawRows p a b) store
      (source f op w) (RuntimeValue.ofCore value) store := by
  exact .group (.strictWordBinary (.reference .head (.tail (by decide) .head))
    (.reference (.tail (by change "x" ≠ "y"; decide) .head)
      (.tail (by decide) (.tail (by decide) .head))) meaning)
private theorem costed (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (store : Core.Store) : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (source f op w) value store (2+overhead op) := by
  have l : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (leaf (range f 1 2) "x") (.word a) store 1 := .identifier .head .head
  have r : LocalExpressionEvaluatesWithCost names (coreRows a b) store
      (leaf (range f (w+4) (w+5)) "y") (.word b) store 1 :=
    .identifier (.tail (by change "x" ≠ "y"; decide) .head) (.tail (by decide) .head)
  apply LocalExpressionEvaluatesWithCost.group
  cases meaning with
  | add => exact .add l r
  | subtract => exact .subtract l r
  | multiply => exact .multiply l r
  | divide => exact .divide l r
  | modulo => exact .modulo l r
  | bitAnd => exact .bitAnd l r
  | bitOr => exact .bitOr l r
  | bitXor => exact .bitXor l r
  | greater => exact .greater l r
  | less => exact .less l r
  | equal => exact .equal l r
  | notEqual => exact .notEqual l r
  | lessEqual => exact .lessEqual l r
  | greaterEqual => exact .greaterEqual l r
private theorem cutoff (f : Syntax.SourceFile) (op : Syntax.BinaryOp) (w : Nat)
    (a b : Core.Word) (value : Core.Value) (meaning : StrictWordBinaryDenotes op a b value)
    (p : RuntimeValue) (store : List RuntimeValue) : ∀ n,
    evaluateClosedSourceExpression? n owner names (rawRows p a b) store (source f op w) =
      if 3 ≤ n then some (RuntimeValue.ofCore value,store) else none := by
  cases meaning <;> intro n
  all_goals
    by_cases high : 3 ≤ n
    · have split : n=(n-3)+3 := by omega
      rw [split]
      simp [source,binary,leaf,evaluateClosedSourceExpression?,evaluateStrictWordBinary?,
        names,rawRows,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,fid,foreign]
    · have small : n=0 ∨ n=1 ∨ n=2 := by omega
      rcases small with rfl | rfl | rfl
      all_goals simp [source,binary,leaf,evaluateClosedSourceExpression?]
private theorem image {captured store src value}
    (original : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ a st, ClosedSourceExpressionEvaluates owner names captured store src a st ↔ a=value ∧ st=store := by
  intro a st; constructor
  · exact fun h => h.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original
private theorem coreImage {e s c v k} (h : Core.Steps k (.initial c e s) (.final v s)) (fuel a st) :
    Core.runStateful fuel (.initial c e s) = .done a st ↔ a=v ∧ st=s ∧ k≤fuel := by
  constructor
  · intro run
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run)
      (Core.steps_from_initial_sound h)
    exact ⟨rfl,rfl,h.runStateful_done_iff.mp run⟩
  · rintro ⟨rfl,rfl,enough⟩; exact h.runStateful_done_iff.mpr enough
private def closedLane {captured store src value} (d : Nat)
    (orig : ClosedSourceExpressionEvaluates owner names captured store src value store)
    (cut : ∀ n, evaluateClosedSourceExpression? n owner names captured store src =
      if d≤n then some (value,store) else none) : IO Unit := do
  proof orig
  for n in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? n owner names captured store src with
    | none =>
      have below : n<d := by
        by_cases enough : d≤n
        · have eq := cut n; rw [run,if_pos enough] at eq; cases eq
        · omega
      proof below; check (n<d) "closed exact depth rejection"
    | some (actual,finalStore) =>
      have endpoints : actual=value ∧ finalStore=store := by
        by_cases enough : d≤n
        · have eq := cut n; rw [run,if_pos enough] at eq; exact Prod.mk.inj (Option.some.inj eq)
        · have eq := cut n; rw [run,if_neg enough] at eq; cases eq
      have witness := (image orig actual finalStore).mpr endpoints
      proof endpoints; proof witness; proof ((image orig actual finalStore).mp witness)
      check (n≥d) "closed full actual endpoints proved at sufficient depth"
private def exercise (f : Syntax.SourceFile) (src : Syntax.Expr) (op : Syntax.BinaryOp) (w : Nat)
    (shape : src=source f op w) (a b : Core.Word) (p : RuntimeValue)
    (rawStore : List RuntimeValue) (coreStore : Core.Store) : IO Unit := do
  let some ⟨value,meaning⟩ := primitive op a b | throw (IO.userError "strict primitive constructor")
  have orig : ClosedSourceExpressionEvaluates owner names (rawRows p a b) rawStore src
      (RuntimeValue.ofCore value) rawStore := by rw [shape]; exact original f op w a b value meaning p rawStore
  have lc : LocalExpressionEvaluatesWithCost names (coreRows a b) coreStore src value coreStore
      (2+overhead op) := by rw [shape]; exact costed f op w a b value meaning coreStore
  proof orig; proof lc
  have cut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p a b) rawStore src =
      if 3≤n then some (RuntimeValue.ofCore value,rawStore) else none := by
    intro n; rw [shape]; exact cutoff f op w a b value meaning p rawStore n
  let inner := match src.value with | .group child => child | _ => src
  have innerShape : inner=binary f op w := by simp only [inner,shape,source]
  have innerOrig : ClosedSourceExpressionEvaluates owner names (rawRows p a b) rawStore inner
      (RuntimeValue.ofCore value) rawStore := by
    rw [innerShape]
    exact .strictWordBinary (.reference .head (.tail (by decide) .head))
      (.reference (.tail (by change "x" ≠ "y"; decide) .head)
        (.tail (by decide) (.tail (by decide) .head))) meaning
  have innerCut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p a b) rawStore inner =
      if 2≤n then some (RuntimeValue.ofCore value,rawStore) else none := by
    intro n
    have h := cutoff f op w a b value meaning p rawStore (n+1)
    rw [source,evaluateClosedSourceExpression?] at h
    have bound : (3≤n+1) ↔ (2≤n) := by omega
    simpa only [innerShape,bound] using h
  closedLane 2 innerOrig innerCut
  closedLane 3 orig cut
  match checked : elaborateLocalExpression? names context src with
  | none => throw (IO.userError "whole actual source checking")
  | some (core,ty) =>
    have aligned : (coreRows a b).ids=context.ids := rfl
    have steps := lc.checked_toSteps checked aligned
    have paths : ∀ continuation, Core.Steps (2+overhead op)
        ⟨.eval core (coreRows a b).values,continuation,coreStore⟩
        ⟨.ret value,continuation,coreStore⟩ := by
      obtain ⟨resolved,resolution,lowering,_⟩ := elaborateLocalExpression?_sound checked
      exact lc.toStepsWithContinuation resolution (aligned ▸ lowering)
    proof steps; proof paths
    let k := 2+overhead op
    for fuel in [0,k-1,k,k+3] do
      match run : Core.runStateful fuel (.initial core (coreRows a b).values coreStore) with
      | .done actual finalStore =>
        have endpoints := (coreImage steps fuel actual finalStore).mp run
        proof endpoints; proof ((coreImage steps fuel actual finalStore).mpr endpoints)
        check (actual==value && finalStore==coreStore && fuel≥k) "Core full actual endpoints and cost"
      | .outOfFuel suspended =>
        have below := steps.runStateful_outOfFuel_iff.mp ⟨suspended,run⟩
        proof below; proof (steps.runStateful_outOfFuel_iff.mpr below)
        check (fuel<k) "Core exact exhaustion"
      | _ => throw (IO.userError "independently costed Core expression stuck")
private def parsedCase (op : Syntax.BinaryOp) (spelling : String) : IO Nat := do
  let text := "(x "++spelling++" y)"
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-strict-word.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "strict Word lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile file) "EOF, diagnostics, full source ownership"
    let w := spelling.utf8ByteSize
    match actualShape : src with
    | ⟨gs,.group ⟨bs,.binary ⟨ls,.identifier ⟨ln,"x"⟩⟩ ⟨os,actualOp⟩ ⟨rs,.identifier ⟨rn,"y"⟩⟩⟩⟩ =>
      if exactFields : gs=range file 0 (w+6) ∧ bs=range file 1 (w+5) ∧ ls=range file 1 2 ∧
          ln=range file 1 2 ∧ os=range file 3 (w+3) ∧ actualOp=op ∧
          rs=range file (w+4) (w+5) ∧ rn=range file (w+4) (w+5) then
        have shape : src=source file op w := by
          rcases exactFields with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
          exact actualShape
        check (src==source file op w && [gs,bs,ls,ln,os,rs,rn].all (fun r => r.isValidFor file))
          "whole handwritten AST and all seven actual ranges"
        let inert := leaf (range file 0 (w+6)) "opaque-unused"
        let p := RuntimeValue.sourceClosure inert foreign [("x",fid)] [(fid,.unit)]
        let pairs : List (Core.Word × Core.Word) := [(Core.Word.zero,Core.Word.zero),
          (Core.Word.ofNatModulo 7,Core.Word.ofNatModulo 3),(Core.Word.maximum,Core.Word.ofNatModulo 1),
          (Core.Word.ofNatModulo 1,Core.Word.maximum),(Core.Word.ofNatModulo (2^255),Core.Word.zero)]
        let mut count := 0
        for (a,b) in pairs do
          for (rawStore,coreStore) in [([],[]),
            ([p,RuntimeValue.ofCore opaqueCore,.hostFunction .storageWrite,.cellRef .word 701],
             [opaqueCore,.hostFunction .storageWrite,.cellRef .word 901,.unit])] do
            exercise file src op w shape a b p rawStore coreStore
            count := count+1
        return count
      else throw (IO.userError "complete actual AST differs from handwritten tree and all ranges")
    | _ => throw (IO.userError "actual grouped binary references")
  | _ => throw (IO.userError "strict Word parser")
end Tests.ParsedClosedStrictWordBinary
open Tests.ParsedClosedStrictWordBinary in
def Tests.frontendParsedClosedStrictWordBinaryTests : IO Unit := do
  let mut count := 0
  for (op,spelling) in [(.add,"+"),(.subtract,"-"),(.multiply,"*"),(.divide,"/"),(.modulo,"%"),
    (.bitAnd,"&"),(.bitOr,"|"),(.bitXor,"^"),(.greater,">"),(.less,"<"),(.equal,"=="),
    (.notEqual,"!="),(.lessEqual,"<="),(.greaterEqual,">=")] do
    count := count + (← parsedCase op spelling)
  check (count==140) "all fourteen operators, five Word pairs, two stores completed"
