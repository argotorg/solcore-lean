import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Core.FuelResumptionProperties
/-! Original preparation, literal source costs and separate Core paths precede
function checkpoint safety. Actual aliased captures share one supplied world.
The typed caller itself allocates/writes and returns a different result type. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedFunctionCheckpointWorlds
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"FunctionCheckpointWorlds",by decide⟩],by decide⟩⟩,142⟩
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def fBody : Core.Expr := .letE (.newCell .word (.var 0)) (.binary .wordAdd (.loadCell (.var 2)) (.word (Core.Word.ofNatModulo 1)))
private def allocator (l m : Nat) : Core.Value := .closure .word .word fBody [.cellRef .word l,reader m]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def second : Core.Expr := .letE (.apply (.var 4) (.var 1)) (.var 0)
private def first : Core.Expr := .letE (.apply (.var 2) (.var 0)) second
private def core : Core.Expr := .letE (.apply (.var 2) (.var 0)) first
private def caller : Core.Expr := .letE (.storeCell (.var 1) (.word (Core.Word.ofNatModulo 7))) (.loadCell (.var 1))
private def pending : List Core.Frame := [.newCellApply .word,.letBody caller [.cellRef .word 0],.pairApply (.bool true)]
private theorem pendingTyped : Core.ContinuationHasType [.word,.word] pending .word (.product .bool .word) :=
  .cons .newCellApply (.cons (.letBody (.cons (.cellRef rfl) .nil)
    (.letE (.storeCell (.var rfl) .word) (.loadCell (.var rfl)))) (.cons (.pairApply .bool) .nil))
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function checkpoint(f:function(Word) returns(Word),g:function(Word) returns(Word),x:Word) returns(Word){let x:Word=f(x);g(x);let x=f(x);return x;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"function-checkpoint-worlds.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple results⟩; return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.core (r.core.weakenAt 0),r.type,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,i.bindings.length⟩ ∧ i.names.lookup? "x"=some ⟨owner,if i.bindings.length=3 then 2 else 3⟩)) "fresh3/4 retains original x2/3; discard creates no source ID"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private def bind (i : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Σ o, PLift (RuntimeParametersBindFrom types owner i ps args o)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨i,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨_,.typed none name annotation⟩::rest,arg::tail =>
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let r ← bind (i.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨r.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused r.2.down⟩⟩
        else throw (IO.userError "duplicate actual binding")
      else throw (IO.userError "ordered actual type")
  | _,_ => throw (IO.userError "actual arity")
private structure Preparation (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RecursiveComputationFunctionPrepares types owner source args ⟨inputs,core,.word⟩
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Preparation source args) := do
  let rows ← bind .empty source.value.signature.parameters.elements args; let b ← body rows.1.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have _ := rows.2.down.erase_values
          return ⟨rows.1,⟨h,rows.2.down,by simpa only [same.2.1,same.2.2] using b.evidence⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core and original return annotation")
  | _ => throw (IO.userError "outer return")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.word word) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l, written : s.write? l (.word word) with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons .word (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual caller missing write")
      | _ => throw (IO.userError "manual caller reference")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def arguments (f g : Core.Value) : IO (List TypedRuntimeArgument) :=
  [f,g,w 14].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "literal supplied values and captures"; return a
    | none => throw (IO.userError "structural actual argument")
private theorem storeWorld {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.RuntimeStoreHasTypes world store) : world=store.map Core.Value.type :=
  typed.world_eq
private def verify (l m a r : Nat) : IO Unit := do
  let f := allocator l m; let g := writer m; let s := [w 41,w 99]; let env : Core.Environment := [w 14,g,f]
  let allocated := s++[w 14]; let written := if m=0 then [w a,w 99,w 14] else [w 41,w a,w 14]
  let bodyStore := written++[w a]; let callerStore := bodyStore++[w r]; let finalStore := w 7::callerStore.tail
  let source ← parsed; let args ← arguments f g; let p ← prepare source args
  let manual ← path 80 core env s; let extra ← path 30 caller [.cellRef .word 4,.cellRef .word 0] callerStore
  let raw ← rawBody p.inputs.names p.inputs.environment s source.value.body
  if fixed : p.inputs.environment.values=env ∧ manual.value=w r ∧ manual.final=bodyStore ∧ manual.cost=56 ∧
      raw.value=w r ∧ raw.final=bodyStore ∧ raw.cost=56 ∧ extra.value=w r ∧ extra.final=finalStore ∧ extra.cost=10 then
    have ⟨ev,mv,ms,mc,rv,rs,rc,xv,xs,xc⟩ := fixed
    have literal (k) : Core.Steps 56 ⟨.eval core env,k,s⟩ ⟨.ret (w r),k,bodyStore⟩ := by simpa only [mv,ms,mc] using manual.evidence k
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner p.inputs.names p.inputs.environment s source.value.body (w r) bodyStore 56 := by simpa only [rv,rs,rc] using raw.evidence
    have sourcePath (k) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using counted) p.evidence.body (by simpa only [LocalInputs.toTypeInputs_context] using p.inputs.sameIds) k
    have aligned (k) : Core.Steps 56 ⟨.eval core p.inputs.environment.values,k,s⟩ ⟨.ret (w r),k,bodyStore⟩ := by rw [ev]; exact literal k
    have _ := (sourcePath []).final_unique (aligned [])
    have finishing : Core.Steps 13 ⟨.ret (w r),pending,bodyStore⟩ (.final (.pair (.bool true) (w r)) finalStore) := by
      have path : Core.Steps 10 ⟨.eval caller [.cellRef .word 4,.cellRef .word 0],[.pairApply (.bool true)],callerStore⟩ ⟨.ret (w r),[.pairApply (.bool true)],finalStore⟩ := by simpa only [xv,xs,xc] using extra.evidence [.pairApply (.bool true)]
      have length : bodyStore.length=4 := by simp [bodyStore,written]; split <;> rfl
      have staged : Core.Steps 11 ⟨.eval caller [.cellRef .word bodyStore.length,.cellRef .word 0],[.pairApply (.bool true)],callerStore⟩ (.final (.pair (.bool true) (w r)) finalStore) := by simpa only [length,Core.State.final,Nat.reduceAdd] using path.trans (.cons .applyPair .refl)
      exact .cons .applyNewCell (.cons .bindLet staged)
    let start : Core.State := ⟨.eval core env,pending,s⟩
    have whole : Core.Steps 69 start (.final (.pair (.bool true) (w r)) finalStore) := (literal pending).trans finishing
    if validated : validateRuntimeInputs [.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have safe := p.evidence.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped
      have exactSafe : Core.StateHasType start (.product .bool .word) ∧
          (∀ fuel error state, Core.runStateful fuel start≠.fault error state) ∧
          ∀ {fuel cp}, Core.runStateful fuel start=.outOfFuel cp → Core.StateHasType cp (.product .bool .word) ∧
            ∀ more error state, Core.runStateful more cp≠.fault error state := by simpa only [ev] using safe
      for fuel in List.range 71 do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "original prepared runner remains separate from typed caller"
        match exhausted : Core.runStateful fuel start with
        | .done v t => check (decide (69≤fuel ∧ v=.pair (.bool true) (w r) ∧ t=finalStore)) "caller returns Bool times Word after its own effects"
        | .fault error state => False.elim (exactSafe.2.1 fuel error state exhausted)
        | .outOfFuel cp =>
            have _ := exactSafe.2.2 exhausted
            have saved := p.evidence.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped (by simpa only [ev] using exhausted)
            have terminal : ∃ savedWorld future, Core.WorldExtends [.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧
                Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future finalStore ∧ future[0]?=some .word := by
              obtain ⟨savedWorld,ext,stored,further⟩ := saved
              obtain ⟨future,growth,typed⟩ := further (whole.residual_of_outOfFuel exhausted).2
              exact ⟨savedWorld,future,ext,stored,growth,typed,(ext.trans growth).lookup rfl⟩
            have _ := terminal
            check (decide (fuel<69 ∧ Core.runStateful (69-fuel) cp=.done (.pair (.bool true) (w r)) finalStore)) "all genuine saved states complete from actual stored state"
            for more in [0,1,13,69] do
              have _ := Core.runStateful_resume exhausted more
              check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) start)) "full resumption, not re-preparation"
              match again : Core.runStateful more cp with
              | .outOfFuel next =>
                  have chain : ∃ savedWorld future, Core.WorldExtends [.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future next.store := by
                    obtain ⟨savedWorld,ext,stored,further⟩ := saved
                    obtain ⟨future,growth,typed⟩ := further (Core.runStateful_outOfFuel_sound again).1
                    exact ⟨savedWorld,future,ext,stored,growth,typed⟩
                  have _ := chain
              | .done _ _ => pure ()
              | .fault error state => False.elim ((exactSafe.2.2 exhausted).2 more error state again)
      let xenv := w a::env; let hidden := w a::xenv
      let cpA : Core.State := ⟨.ret (.cellRef .word 2),.letBody (.binary .wordAdd (.loadCell (.var 2)) (.word (Core.Word.ofNatModulo 1))) [w 14,.cellRef .word l,reader m]::.letBody first env::pending,allocated⟩
      let cpW : Core.State := ⟨.ret .unit,.letBody (.loadCell (.var 2)) [w a,.cellRef .word m]::.letBody second xenv::pending,written⟩
      let cpB : Core.State := ⟨.ret (.cellRef .word 3),.letBody (.binary .wordAdd (.loadCell (.var 2)) (.word (Core.Word.ofNatModulo 1))) [w a,.cellRef .word l,reader m]::.letBody (.var 0) hidden::pending,bodyStore⟩
      let cpC : Core.State := ⟨.ret (.cellRef .word 4),[.letBody caller [.cellRef .word 0],.pairApply (.bool true)],callerStore⟩
      let cpD : Core.State := ⟨.ret .unit,[.letBody (.loadCell (.var 1)) [.cellRef .word 4,.cellRef .word 0],.pairApply (.bool true)],finalStore⟩
      for (spent,cp) in [(10,cpA),(31,cpW),(46,cpB),(56,⟨.ret (w r),pending,bodyStore⟩),(57,cpC),(64,cpD)] do
        if exhausted : Core.runStateful spent start=.outOfFuel cp then
          have actualWorld : Core.WorldExtends [.word,.word] (cp.store.map Core.Value.type) ∧ Core.RuntimeStoreHasTypes (cp.store.map Core.Value.type) cp.store := by
            obtain ⟨world,ext,typed,_⟩ := p.evidence.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped (by simpa only [ev] using exhausted)
            simpa only [storeWorld typed] using And.intro ext typed
          have _ := actualWorld
          check (decide (Core.runStateful (69-spent) cp=.done (.pair (.bool true) (w r)) finalStore)) "literal original captures, discard slot and caller frames"
        else throw (IO.userError "literal checkpoint")
      if links : Core.runStateful 10 start=.outOfFuel cpA ∧ Core.runStateful 21 cpA=.outOfFuel cpW ∧ Core.runStateful 15 cpW=.outOfFuel cpB ∧ Core.runStateful 11 cpB=.outOfFuel cpC ∧ Core.runStateful 7 cpC=.outOfFuel cpD then
        have worlds : Core.WorldExtends [.word,.word] [.word,.word,.word] ∧ Core.RuntimeStoreHasTypes [.word,.word,.word] cpA.store ∧ Core.RuntimeStoreHasTypes [.word,.word,.word] cpW.store ∧
            Core.RuntimeStoreHasTypes [.word,.word,.word,.word] cpB.store ∧ Core.WorldExtends [.word,.word,.word] [.word,.word,.word,.word,.word] ∧ Core.RuntimeStoreHasTypes [.word,.word,.word,.word,.word] cpC.store ∧ Core.RuntimeStoreHasTypes [.word,.word,.word,.word,.word] cpD.store := by
          obtain ⟨world,ext,stored,further⟩ := p.evidence.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType runtime.1 runtime.2 pendingTyped (by simpa only [ev] using links.1)
          have initialWorld : world=[.word,.word,.word] := storeWorld stored
          subst world
          have aw := (Core.runStateful_outOfFuel_sound links.2.1).1
          have ab := aw.trans (Core.runStateful_outOfFuel_sound links.2.2.1).1
          have ac := ab.trans (Core.runStateful_outOfFuel_sound links.2.2.2.1).1
          have ad := ac.trans (Core.runStateful_outOfFuel_sound links.2.2.2.2).1
          obtain ⟨_,_,tw⟩ := further aw; obtain ⟨_,_,tb⟩ := further ab; obtain ⟨future,growth,tc⟩ := further ac; obtain ⟨_,_,td⟩ := further ad
          rw [storeWorld tc] at growth
          rw [storeWorld stored] at stored; rw [storeWorld tw] at tw; rw [storeWorld tb] at tb; rw [storeWorld tc] at tc; rw [storeWorld td] at td
          by_cases same : m=0
          all_goals simp [cpW,cpB,cpC,cpD,finalStore,callerStore,bodyStore,written,same,w,Core.Value.type] at tw tb tc td growth ⊢
          all_goals exact ⟨ext,stored,tw,tb,growth,tc,td⟩
        have _ := worlds
      else throw (IO.userError "independent further paths 21/15/11/7")
    else throw (IO.userError "actual argument/capture/store common world")
  else throw (IO.userError "independent original raw56/Core56/caller10 expectations")
end ParsedFunctionCheckpointWorlds
open ParsedFunctionCheckpointWorlds in
def frontendParsedFunctionCheckpointWorldTests : IO Unit := do
  for (l,m,a,r) in [(0,0,42,43),(1,0,100,100),(1,1,100,101)] do verify l m a r
end Tests
