import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RuntimeComputationFunction

/-!
# Recursive conditional tests

Recursive conditional computations and their function entries.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveConditionalComputations
/-! Original ternaries carry independent static/raw certificates. Literal Core,
values and costs are supplied separately, then checked against hand-built paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveConditionalComputations
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Conditional",by decide⟩],by decide⟩⟩,57⟩
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
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-conditional.sol"⟩,text⟩
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
  | ⟨_,.unary ⟨_,.bitNot⟩ inner⟩ =>
      let a ← statics ctx inner
      if same : a.type=.word then return ⟨.unary .wordNot a.core,.word,
        by rw [shape]; exact .bitNot (same ▸ a.elaboration),by rw [shape]; exact .bitNot (same ▸ a.typing)⟩
      else throw (IO.userError "migration Word operand")
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
private def overlap (c : Bool) : IO Unit := do
  let s ← parsed "c ? x : y"; let env := environment .word (.word (Core.Word.ofNatModulo 17)) (.word (Core.Word.ofNatModulo 5)) c false
  match shape : s with
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← leaf (context .word) guard; let a ← leaf (context .word) yes; let b ← leaf (context .word) no
      let gr ← rawLeaf env guard; let ar ← rawLeaf env yes; let br ← rawLeaf env no; let r ← actual env s
      let recursive ← statics (context .word) s
      if valid : g.type=.bool ∧ b.type=a.type then
        have old : LocalComputationElaborates names (context .word) s (.ifE g.core a.core b.core) a.type := by
          rw [shape]; exact .pure (.conditional g.resolution a.resolution b.resolution) (.ifE g.lowered a.lowered b.lowered) (.ifE (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing))
        have _ := elaborateRecursiveLocalComputation?_iff.mpr old.toRecursiveLocalComputation
        have _ := elaborateRecursiveLocalComputation?_iff.mpr recursive.elaboration
        check (decide (recursive.core=.ifE (.var 2) (.var 0) (.var 1) ∧ recursive.type=.word ∧
          elaborateLocalComputation? names (context .word) s=some (.ifE (.var 2) (.var 0) (.var 1),.word))) "old pure/new conditional distinct static overlap"
        for store in [[],[Core.Value.unit]] do
          if gv : gr.value=.bool c then
            have oldRaw : ∃ value, LocalComputationEvaluatesWithCost names env store s value store 4 := by
              cases c with
              | true => exact ⟨ar.value,.pure (by rw [shape]; exact .ifTrue (gv ▸ gr.evidence store) (ar.evidence store))⟩
              | false => exact ⟨br.value,.pure (by rw [shape]; exact .ifFalse (gv ▸ gr.evidence store) (br.evidence store))⟩
            have _ : r.cost=4 := by obtain ⟨_,oldCost⟩ := oldRaw; exact ((r.evidence store).deterministic oldCost.toRecursiveLocalComputation).2.2
            check (decide (r.cost=4)) "pure/recursive exact cost"
          else throw (IO.userError "original actual guard")
      else throw (IO.userError "overlap type")
  | _ => throw (IO.userError "overlap root")
end ParsedRecursiveConditionalComputations
open ParsedRecursiveConditionalComputations
def frontendParsedRecursiveConditionalComputationTests : IO Unit := do
  let nested := Core.Expr.apply (.var 4) (call 5 0)
  let templates (a : Core.Ty) := [("c ? f(g(x)) : g(y)",.ifE (.var 2) nested (call 5 1),a),
    ("p(c) ? f(g(x)) : y",.ifE (call 6 2) nested (.var 1),a),
    ("c ? x : d ? f(x) : g(y)",.ifE (.var 2) (.var 0) (.ifE (.var 3) (call 4 0) (call 5 1)),a),
    ("(p(c) ? maker(x) : maker(y))(y)",.apply (.ifE (call 6 2) (call 7 0) (call 7 1)) (.var 1),a),
    ("p(c) ? maker(x) : f",.ifE (call 6 2) (call 7 0) (.var 4),.function a a)]
  for a in [Core.Ty.word,.unit,.namedData ⟨77⟩,.cell .word,.function (.namedData ⟨9⟩) (.namedData ⟨11⟩)] do
    for depth in [0,3,17] do
      for (text,core,type) in templates a do
        let s ← parsed (wrap depth text); let p ← statics (context a) s
        have _ := p.elaboration.core_hasType
        check (decide (p.core=core ∧ p.type=type ∧ elaborateRecursiveLocalComputation? names (context a) s=some (core,type) ∧ names.lookup? "f"=some foreign ∧ (context a).lookup? foreign=some (.function a a))) "value-free original type/first match"
  for (a,x,y) in [(Core.Ty.word,Core.Value.word (Core.Word.ofNatModulo 17),Core.Value.word (Core.Word.ofNatModulo 5)),(.unit,.unit,.unit)] do
    for c in [false,true] do
      for d in [false,true] do
        for depth in [0,3] do
          for ((text,core,type),value,cost) in (templates a).zip [(if c then x else y,if c then 14 else 9),(if c then x else y,if c then 19 else 9),
              (if c || d then x else y,if c then 4 else 12),(y,19),(identity a,if c then 14 else 9)] do
            exercise (wrap depth text) a x y c d core type value cost
  for c in [false,true] do
    overlap c
    let x := Core.Value.word (Core.Word.ofNatModulo 17); let y := Core.Value.word (Core.Word.ofNatModulo 5)
    let env := environment .word x y c true
    let core := Core.Expr.ifE (call 6 2) nested (.var 1)
    for store in [[],[Core.Value.unit]] do
      let cp : Core.State := ⟨.ret (.bool c),[.ifBranches nested (.var 1) env.values],store⟩
      check (decide (Core.runStateful 7 (.initial core env.values store)=.outOfFuel cp ∧
        Core.runStateful 1 cp=.outOfFuel ⟨.eval (if c then nested else .var 1) env.values,[],store⟩ ∧
        Core.runStateful (if c then 12 else 2) cp=.done (if c then x else y) store)) "actual saved conditional frame/next choice/residual"
  let unarySource ← parsed "~(c ? f(x) : y)"; let unaryStatic ← statics (context .word) unarySource
  let unaryCore := Core.Expr.unary .wordNot (.ifE (.var 2) (call 4 0) (.var 1))
  have _ := elaborateRecursiveLocalComputation?_iff.mpr unaryStatic.elaboration
  check (decide (unaryStatic.core=unaryCore ∧ unaryStatic.type=.word ∧ elaborateRecursiveLocalComputation? names (context .word) unarySource=some (unaryCore,.word) ∧
    elaborateLocalExpression? names (context .word) unarySource=none ∧ elaborateLocalComputation? names (context .word) unarySource=none)) "original unary conditional exact success and old rejection"
  for text in ["c ? f(x) : c","x ? f(x) : y","c ? f(x) : Missing","c ? Missing : f(x)","c ? f(x) : f(c)","c ? f(x) : f()"] do
    let s ← parsed text; check ((elaborateRecursiveLocalComputation? names (context .word) s).isNone) "whole branch/guard/profile rejection"
  for text in ["c ? f(x) : Missing","c ? f(x) : c","c ? f(x) : f()"] do
    let s ← parsed text; let r ← actual (environment .word (.word (Core.Word.ofNatModulo 17)) (.word (Core.Word.ofNatModulo 5)) true false) s
    have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨r.cost,r.evidence []⟩
    check (decide (r.value=.word (Core.Word.ofNatModulo 17) ∧ r.cost=9)) "selected-only raw success does not type the unselected branch"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveConditionalFunctionEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveConditionalEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveConditionalEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-conditional-entries.sol"⟩,text⟩
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
  | ⟨_,.conditional condition question yes colon no⟩ =>
      check (source.span.contains question && source.span.contains colon && source.span.contains condition.span && source.span.contains yes.span && source.span.contains no.span &&
        decide (condition.span.endByte≤question.startByte ∧ question.endByte≤yes.span.startByte ∧ yes.span.endByte≤colon.startByte ∧ colon.endByte≤no.span.startByte)) "original question/colon and three child order"
      let c ← child s env store condition; let a ← branch s yes; let b ← branch s no
      if typed : c.type=.bool ∧ b.type=a.type then
        have el : RecursiveLocalComputationElaborates s.names s.context source (.ifE c.core a.core b.core) a.type := by
          rw [original]; exact .conditional (typed.1 ▸ c.elaboration) a.elaboration (typed.2 ▸ b.elaboration)
        match cv : c.value with
        | .bool true =>
            let selected ← child s env c.final yes
            return ⟨.ifE c.core a.core b.core,a.type,selected.value,selected.final,c.cost+selected.cost+2,el,by rw [original]; exact .ifTrue (cv ▸ c.raw) selected.raw⟩
        | .bool false =>
            let selected ← child s env c.final no
            return ⟨.ifE c.core a.core b.core,a.type,selected.value,selected.final,c.cost+selected.cost+2,el,by rw [original]; exact .ifFalse (cv ▸ c.raw) selected.raw⟩
        | _ => throw (IO.userError "actual guard has no successful raw cost")
      else throw (IO.userError "static conditional types differ")
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function conditional(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
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
private def guardReader : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.loadCell (.var 1)) [.cellRef .bool 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def guardWriter : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .bool 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def writer : TypedRuntimeArgument := ⟨.function .bool .word,.closure .bool .word (.letE (.storeCell (.var 1) (.var 2)) (.loadCell (.var 2))) [.cellRef .word 1,w 14],
  .closure (.cons .cellRef (.cons .word .nil)) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
end RecursiveConditionalEntries
open RecursiveConditionalEntries
def frontendParsedRecursiveConditionalFunctionEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.bool,.bool true,.bool⟩; let y : TypedRuntimeArgument := ⟨.word,w 23,.word⟩
  let call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
  let core := Core.Expr.ifE (call 3 1) (call 2 1) (.var 0)
  let source ← bodySource "return f(x)?g(x):y;"
  let prepared ← verify source guardReader writer x y .word core [.bool true,w 99] [.bool true,w 14] (w 14) 25
  discard <| verify source guardReader writer x y .word core [.bool false,w 99] [.bool false,w 99] (w 23) 11
  discard <| verify source guardReader writer x y .word core [.bool false] [.bool false] (w 23) 11
  for choice in [false,true] do
    let arg : TypedRuntimeArgument := ⟨.bool,.bool choice,.bool⟩
    discard <| verify source guardWriter writer arg y .word core [.bool (!choice),w 99] [.bool choice,if choice then w 14 else w 99] (if choice then w 14 else w 23) (if choice then 32 else 18)
  let alternate : TypedRuntimeArgument := ⟨writer.type,.closure .bool .word (.letE (.storeCell (.var 1) (.var 2)) (.loadCell (.var 2))) [.cellRef .word 1,w 23],.closure (.cons .cellRef (.cons .word .nil)) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
  for choice in [false,true] do
    let selected := if choice then writer.value else alternate.value; let word := if choice then w 14 else w 23
    discard <| verify (← bodySource "return f(x)?g:y;") guardReader writer x alternate writer.type (.ifE (call 3 1) (.var 2) (.var 0)) [.bool choice] [.bool choice] selected 11
    discard <| verify (← bodySource "return (f(x)?g:y)(x);") guardReader writer x alternate .word (.apply (.ifE (call 3 1) (.var 2) (.var 0)) (.var 1)) [.bool choice,w 99] [.bool choice,word] word 25
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],guardReader.type),(["G"],writer.type),(["X"],.bool),(["Y"],.word),(["R"],.word),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [guardReader,writer,x,y]
  let frames := [Core.Frame.ifBranches (call 2 1) (.var 0) env]
  for choice in [false,true] do
    let store := [.bool choice,w 99]; let cp : Core.State := ⟨.ret (.bool choice),frames,store⟩
    let selected : Core.State := ⟨.eval (if choice then call 2 1 else .var 0) env,[],store⟩
    check (decide (run 9 store=some (.word,.outOfFuel cp) ∧ run 10 store=some (.word,.outOfFuel selected) ∧ Core.runStateful 1 cp=.outOfFuel selected)) "genuine ifBranches and exact selection after resumption"
  let wrong := Core.StatefulRunResult.fault (.expectedBool (w 99)) ⟨.ret (w 99),frames,[w 99,w 23]⟩
  let wrongCp : Core.State := ⟨.ret (.cellRef .bool 0),.loadCellApply::frames,[w 99,w 23]⟩
  let empty := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .bool 0),.loadCellApply::frames,[]⟩
  let emptyCp : Core.State := ⟨.eval (.var 1) env,.applyClosure .bool .bool (.loadCell (.var 1)) [.cellRef .bool 0]::frames,[]⟩
  let selectedEnv := [.bool true,.cellRef .word 1,w 14]
  let selectedFrames := [Core.Frame.storeCellValue (.var 2) selectedEnv,.letBody (.loadCell (.var 2)) selectedEnv]
  let branchFault := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),selectedFrames,[.bool true]⟩
  let branchCp : Core.State := ⟨.eval (.var 1) selectedEnv,selectedFrames,[.bool true]⟩
  check (decide (run 8 [w 99,w 23]=some (.word,.outOfFuel wrongCp) ∧ run 9 [w 99,w 23]=some (.word,wrong) ∧ Core.runStateful 1 wrongCp=wrong ∧ run 4 []=some (.word,.outOfFuel emptyCp) ∧ run 8 []=some (.word,empty) ∧ Core.runStateful 4 emptyCp=empty)) "wrong or missing guard blocks both branches"
  check (decide (run 17 [.bool true]=some (.word,.outOfFuel branchCp) ∧ run 18 [.bool true]=some (.word,branchFault) ∧ Core.runStateful 1 branchCp=branchFault ∧ run 11 [.bool false]=some (.word,.done (w 23) [.bool false]))) "selected branch fault versus unselected missing-cell success"
  let effectCp : Core.State := ⟨.ret (.bool true),[.ifBranches (call 2 1) (.var 0) [y.value,x.value,writer.value,guardWriter.value]],[.bool true]⟩
  check (decide (runRecursiveComputationFunction? types owner source [guardWriter,writer,x,y] 16 [.bool false]=some (.word,.outOfFuel effectCp) ∧ runRecursiveComputationFunction? types owner source [guardWriter,writer,x,y] 25 [.bool false]=some (.word,branchFault) ∧ Core.runStateful 9 effectCp=branchFault)) "guard update survives resumed selected-branch fault"
  for s in [[.bool true,w 99],[.bool false],[w 99,w 23],[],[.bool true]] do
    for fuel in List.range 34 do
      check (decide (run fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared record full values/stores/fault tags"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .outOfFuel cp =>
          have _ := Core.runStateful_resume exhausted 40
          check (decide (run (fuel+40) s=some (.word,Core.runStateful 40 cp))) "all genuine residual states resume whole outcomes"
      | _ => pure ()
  for body in ["return f(x)?g(x):missing;","return f(x)?g(x):x;","return y?g(x):y;"] do
    let bad ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [guardReader,writer,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [guardReader,writer,x,y] 50 [.bool true,w 99]=none)) "whole unselected-name/branch-type/guard-type gates"
  let wrongReturn ← parsed "function conditional(f:F,g:G,x:X,y:Y) returns(X){return f(x)?g(x):y;}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.word) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none)) "independent Word body versus declared Bool"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveConditionalComputationProperties
/-! Original conditional children have independent static and actual certificates.
Only the selected actual branch contributes a path or a cost. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveConditionalComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Conditional", by decide⟩], by decide⟩⟩, 57⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "conditional.sol"⟩, 0, 1024⟩
private inductive Key | p | x | f | g | y | c
private def index : Key → Nat | .p => 0 | .x => 1 | .f => 2 | .g => 3 | .y => 4 | .c => 5
private def name : Key → String | .p => "p" | .x => "x" | .f => "f" | .g => "g" | .y => "y" | .c => "c"
private def typeOf (a : Core.Ty) : Key → Core.Ty | .p => .function a .bool | .f | .g => .function a a | .c => .bool | _ => a
private def inputs (a : Core.Ty) : LocalTypeInputs := ⟨[⟨"p", id 0, .function a .bool⟩, ⟨"x", id 1, a⟩,
  ⟨"f", id 2, .function a a⟩, ⟨"g", id 3, .function a a⟩, ⟨"y", id 4, a⟩, ⟨"c", id 5, .bool⟩], by
    change [id 0, id 1, id 2, id 3, id 4, id 5].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span, .identifier ⟨span, name key⟩⟩
private def call (fn arg : Syntax.Expr) : Syntax.Expr := ⟨span, .call fn ⟨span, [arg]⟩⟩
private def branch (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .y else .x)
  | n + 1 => call (ref (if side then .g else .f)) (branch side n)
private def branchCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 4 else 1)
  | n + 1 => .apply (.var (if side then 3 else 2)) (branchCore side n)
private def conditional (guard yes no : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional guard ⟨span.source, 400, 401⟩ yes ⟨span.source, 700, 701⟩ no⟩
private def source (n k : Nat) := conditional (call (ref .p) (ref .x)) (branch false n) (branch true k)
private def core (n k : Nat) := Core.Expr.ifE (.apply (.var 0) (.var 1)) (branchCore false n) (branchCore true k)
private theorem oldLeaf (a : Core.Ty) (key : Key) :
    LocalComputationElaborates (inputs a).names (inputs a).context (ref key) (.var (index key)) (typeOf a key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leaf (a : Core.Ty) (key : Key) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (ref key) (.var (index key)) (typeOf a key) :=
  (oldLeaf a key).toRecursiveLocalComputation
private theorem leafTyped (a : Core.Ty) (key : Key) :
    RecursiveLocalComputationHasType (inputs a).names (inputs a).context (ref key) (typeOf a key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem branchElab (a : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (branch side n) (branchCore side n) a := by
  induction n with
  | zero => cases side <;> exact leaf a _
  | succ n ih => exact .application (by cases side <;> exact leaf a _) ih
private theorem branchTyped (a : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType (inputs a).names (inputs a).context (branch side n) a := by
  induction n with
  | zero => cases side <;> exact leafTyped a _
  | succ n ih => exact .application (by cases side <;> exact leafTyped a _) ih
private theorem elaboration (a : Core.Ty) (n k : Nat) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (source n k) (core n k) a :=
  .conditional (.application (leaf a .p) (leaf a .x)) (branchElab a false n) (branchElab a true k)
private def delay : Nat → Nat → Core.Expr
  | 0, i => .var i
  | n + 1, i => .letE (.var 0) (delay n (i + 1))
private structure Actual where
  choice : Bool
  x : Core.Value
  y : Core.Value
  guardDelay : Nat
  leftDelay : Nat
  rightDelay : Nat
  guardCapture : Core.Environment
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def actual (a : Core.Ty) (v : Actual) : Key → Core.Value
  | .p => .closure a .bool (delay v.guardDelay 1) (.bool v.choice :: v.guardCapture)
  | .f => .closure a a (delay v.leftDelay 0) v.leftCapture
  | .g => .closure a a (delay v.rightDelay 0) v.rightCapture
  | .x => v.x | .y => v.y | .c => .bool v.choice
private def env (a : Core.Ty) (v : Actual) : Resolved.Environment :=
  [(id 0, actual a v .p), (id 1, v.x), (id 2, actual a v .f), (id 3, actual a v .g), (id 4, v.y), (id 5, .bool v.choice)]
private def branchValue (v : Actual) (side : Bool) := if side then v.y else v.x
private def branchDelay (v : Actual) (side : Bool) := if side then v.rightDelay else v.leftDelay
private def branchCapture (v : Actual) (side : Bool) := if side then v.rightCapture else v.leftCapture
private def charge (n m : Nat) := n * (3 * m + 5) + 1
private def guardCost (v : Actual) := 3 * v.guardDelay + 6
private def cost (v : Actual) (n k : Nat) := guardCost v + (if v.choice then charge n v.leftDelay else charge k v.rightDelay) + 2
private def result (v : Actual) := if v.choice then v.x else v.y
private theorem atomCost (a : Core.Ty) (v : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs a).names (env a v) s (ref key) (actual a v key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (n i : Nat) (environment : Core.Environment) (value : Core.Value) (s : Core.Store) (frames : List Core.Frame)
    (found : environment[i]? = some value) :
    Core.Steps (3 * n + 1) ⟨.eval (delay n i) environment, frames, s⟩ ⟨.ret value, frames, s⟩ := by
  induction n generalizing i environment frames with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      cases environment with
      | nil => simp at found
      | cons head rest =>
          simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i + 1) (head :: head :: rest) frames (by simpa using found))))
private theorem branchCosted (a : Core.Ty) (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (branch side n) (branchValue v side) s (charge n (branchDelay v side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [charge, branch, branchValue, actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a v .x s)
      · simpa [charge, branch, branchValue, actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a v .y s)
  | succ n ih =>
      have count : charge (n + 1) (branchDelay v side) = 1 + charge n (branchDelay v side) + (3 * branchDelay v side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact .application (.pure (by cases side <;> exact atomCost a v _ s)) ih
        (delayed (branchDelay v side) 0 (branchValue v side :: branchCapture v side) (branchValue v side) s [] rfl)
private theorem branchPath (a : Core.Ty) (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (branchDelay v side)) ⟨.eval (branchCore side n) (env a v).values, frames, s⟩ ⟨.ret (branchValue v side), frames, s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var (value := branchValue v side) (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n + 1) (branchDelay v side) = 1 + charge n (branchDelay v side) + (3 * branchDelay v side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (branchDelay v side) 0 (branchValue v side :: branchCapture v side) (branchValue v side) s [] rfl)
private theorem guardCosted (a : Core.Ty) (v : Actual) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (call (ref .p) (ref .x)) (.bool v.choice) s (guardCost v) := by
  have count : guardCost v = 1 + 1 + (3 * v.guardDelay + 1) + 3 := by simp [guardCost]; omega
  rw [count]; exact .application (.pure (atomCost a v .p s)) (.pure (atomCost a v .x s))
    (delayed v.guardDelay 1 (v.x :: .bool v.choice :: v.guardCapture) (.bool v.choice) s [] rfl)
private theorem guardPath (a : Core.Ty) (v : Actual) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (guardCost v) ⟨.eval (.apply (.var 0) (.var 1)) (env a v).values, frames, s⟩ ⟨.ret (.bool v.choice), frames, s⟩ := by
  have count : guardCost v = 1 + 1 + (3 * v.guardDelay + 1) + 3 := by simp [guardCost]; omega
  rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (delayed v.guardDelay 1 (v.x :: .bool v.choice :: v.guardCapture) (.bool v.choice) s [] rfl)
private theorem counted (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (source n k) (result v) s (cost v n k) := by
  cases chosen : v.choice
  · simpa [source, conditional, cost, result, chosen, branchValue, branchDelay] using RecursiveLocalComputationEvaluatesWithCost.ifFalse
      (chosen ▸ guardCosted a v s) (branchCosted a v true k s)
  · simpa [source, conditional, cost, result, chosen, branchValue, branchDelay] using RecursiveLocalComputationEvaluatesWithCost.ifTrue
      (chosen ▸ guardCosted a v s) (branchCosted a v false n s)
private theorem manual (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost v n k) ⟨.eval (core n k) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  cases chosen : v.choice
  · simpa [core, cost, result, chosen, branchValue, branchDelay] using CostStepComposition.ifFalse
      (chosen ▸ guardPath a v s (.ifBranches (branchCore false n) (branchCore true k) (env a v).values :: frames)) (branchPath a v true k s frames)
  · simpa [core, cost, result, chosen, branchValue, branchDelay] using CostStepComposition.ifTrue
      (chosen ▸ guardPath a v s (.ifBranches (branchCore false n) (branchCore true k) (env a v).values :: frames)) (branchPath a v false n s frames)

theorem arbitrary_type_original_three_children (a : Core.Ty) (n k : Nat) :
    elaborateRecursiveLocalComputation? (inputs a).names (inputs a).context (source n k) = some (core n k, a) ∧
    RecursiveLocalComputationHasType (inputs a).names (inputs a).context (source n k) a ∧
    Core.HasType (inputs a).context.values (core n k) a := by
  have typed : RecursiveLocalComputationHasType (inputs a).names (inputs a).context (source n k) a :=
    .conditional (.application (leafTyped a .p) (leafTyped a .x)) (branchTyped a false n) (branchTyped a true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration a n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),
    (elaboration a n k).core_hasType⟩

theorem arbitrary_actual_selected_path (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates (inputs a).names (env a v) s (source n k) (result v) s ∧
    Core.Evaluates (env a v).values s (core n k) (result v) s ∧
    Core.Steps (cost v n k) ⟨.eval (core n k) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  have guard := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, guardCosted a v s⟩
  have raw : RecursiveLocalComputationEvaluates (inputs a).names (env a v) s (source n k) (result v) s := by
    cases chosen : v.choice
    · simpa [source, conditional, result, chosen, branchValue] using RecursiveLocalComputationEvaluates.ifFalse
        (chosen ▸ guard) (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, branchCosted a v true k s⟩)
    · simpa [source, conditional, result, chosen, branchValue] using RecursiveLocalComputationEvaluates.ifTrue
        (chosen ▸ guard) (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, branchCosted a v false n s⟩)
  have costed := ((elaboration a n k).evaluatesWithCost_iff_steps (environment := env a v) rfl).mpr (manual a v n k s [])
  exact ⟨raw, ((elaboration a n k).evaluates_iff rfl).mp raw, costed.toStepsWithContinuation (elaboration a n k) rfl frames⟩

theorem actual_cost_unique_without_unselected_charge (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (source n k) value finalStore steps) :
    value = result v ∧ finalStore = s ∧ steps = guardCost v + (if v.choice then charge n v.leftDelay else charge k v.rightDelay) + 2 :=
  other.deterministic (counted a v n k s)

theorem unselected_depth_does_not_contribute (v : Actual) (n k ignored : Nat) :
    (v.choice = true → cost v n k = cost v n ignored) ∧
    (v.choice = false → cost v n k = cost v ignored k) := by
  constructor <;> intro chosen <;> simp [cost, chosen]

theorem unselected_source_is_not_a_raw_premise (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store)
    (skipped : Syntax.Expr) (chosen : v.choice = true) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s
      (conditional (call (ref .p) (ref .x)) (branch false n) skipped) v.x s (guardCost v + charge n v.leftDelay + 2) :=
  .ifTrue (chosen ▸ guardCosted a v s) (branchCosted a v false n s)

theorem pure_and_recursive_conditional_overlap (a : Core.Ty) (v : Actual) (s : Core.Store) :
    LocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 ∧
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 := by
  have old : LocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 := by
    cases chosen : v.choice
    · simp [conditional, result, chosen]; exact .pure (.ifFalse (by simpa [actual, chosen] using atomCost a v .c s) (atomCost a v .y s))
    · simp [conditional, result, chosen]; exact .pure (.ifTrue (by simpa [actual, chosen] using atomCost a v .c s) (atomCost a v .x s))
  have new : RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 := by
    cases chosen : v.choice
    · simp [conditional, result, chosen]; exact .ifFalse (.pure (by simpa [actual, chosen] using atomCost a v .c s)) (.pure (atomCost a v .y s))
    · simp [conditional, result, chosen]; exact .ifTrue (.pure (by simpa [actual, chosen] using atomCost a v .c s)) (.pure (atomCost a v .x s))
  have equality := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old, equality.2.2 ▸ new⟩

theorem arbitrary_caller_insertion (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading ++ suffix = (env a v).values) :
    RecursiveLocalComputationFragment ((core n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost v n k) ⟨.eval ((core n k).weakenAt leading.length) (leading ++ inserted :: suffix), frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  have fragment := (elaboration a n k).core_fragment
  have original := Core.steps_from_initial_sound (manual a v n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost v n k) (.initial (core n k) (leading ++ suffix) s) (.final (result v) s) := by rw [split]; exact manual a v n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length, fun frames => same ▸ (paths frames).2⟩

private def checkpoint (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.bool v.choice), [.ifBranches (branchCore false n) (branchCore true k) (env a v).values], s⟩
theorem actual_guard_checkpoint (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (guardCost v + 1) (.initial (core n k) (env a v).values s) = .outOfFuel (checkpoint a v n k s) := by
  have guardPrefix : Core.Steps (guardCost v + 1) (.initial (core n k) (env a v).values s) (checkpoint a v n k s) :=
    .cons .enterIf (guardPath a v s [.ifBranches (branchCore false n) (branchCore true k) (env a v).values])
  cases chosen : v.choice
  · exact Core.runStateful_outOfFuel_complete guardPrefix (Core.advance_next_iff.mpr (by simpa [checkpoint, chosen] using Core.Transition.chooseFalse (thenBranch := branchCore false n) (elseBranch := branchCore true k) (environment := (env a v).values) (continuation := []) (store := s)))
  · exact Core.runStateful_outOfFuel_complete guardPrefix (Core.advance_next_iff.mpr (by simpa [checkpoint, chosen] using Core.Transition.chooseTrue (thenBranch := branchCore false n) (elseBranch := branchCore true k) (environment := (env a v).values) (continuation := []) (store := s)))

theorem all_fuels_genuine_residual_and_full_resume (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core n k) (env a v).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core n k) (env a v).values s) = .done (result v) s ↔ cost v n k ≤ fuel) ∧
    spent < cost v n k ∧ Core.Steps (cost v n k - spent) cp (.final (result v) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent + additional) (.initial (core n k) (env a v).values s) := by
  have path := manual a v n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff, residual.1, residual.2, Core.runStateful_resume exhausted additional⟩

theorem same_source_actual_guard_cost_is_unbounded (a : Core.Ty) (limit : Nat) (x y : Core.Value) (s : Core.Store) :
    ∃ v : Actual, RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (source 1 1) x s (cost v 1 1) ∧ limit < cost v 1 1 := by
  let v : Actual := ⟨true, x, y, limit, 0, 0, [], [], []⟩
  refine ⟨v, counted a v 1 1 s, ?_⟩
  simp [cost, guardCost, charge, v]; omega

private def body (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span, .letDecl ⟨span, "r"⟩ none (some (source n k))⟩, ⟨span, .returnStmt (some ⟨span, .identifier ⟨span, "r"⟩⟩)⟩]⟩
private theorem bodyElab (a : Core.Ty) (n k : Nat) : RecursiveComputationReturnTreeElaborates [] owner (inputs a)
    (body n k) (.letE (core n k) (.var 0)) a :=
  .inferred (elaboration a n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCosted (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a).names (env a v) s (body n k) (result v) s (cost v n k + 3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost, body, Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted a v n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost v n k + 3) ⟨.eval (.letE (core n k) (.var 0)) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual a v n k s (.letBody (.var 0) (env a v).values :: frames)) (.cons (.var rfl) .refl)

theorem shared_body_exact_source_and_cost (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs a) (body n k) = some (.letE (core n k) (.var 0), a) ∧
    Core.HasType (inputs a).context.values (.letE (core n k) (.var 0)) a ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a).names (env a v) s (body n k) (result v) s (cost v n k + 3) ∧
    Core.Steps (cost v n k + 3) ⟨.eval (.letE (core n k) (.var 0)) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab a n k) (environment := env a v) rfl).mpr (bodyManual a v n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab a n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab a n k), costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCosted a v n k s) (bodyElab a n k) rfl frames⟩

end Tests.FrontendRecursiveConditionalComputation
end
