import Solcore.Syntax.Parser.Function
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalComputation
import Solcore.Core.FuelResumptionProperties
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
