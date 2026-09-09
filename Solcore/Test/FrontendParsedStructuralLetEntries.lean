import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Original structural let annotations reach existing entries without new steps.
Independent annotation/raw-body evidence and fixed Core paths determine all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace StructuralLetEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralLetEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "structural-let-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def bindingTypes (types : TypeNameTable) (source : Syntax.Block) : IO (List Core.Ty) := do
  match source with
  | ⟨span, ⟨_, .letDecl _ (some sourceType) (some _)⟩ :: rest⟩ =>
      let meaning ← annotation types sourceType
      let tail ← bindingTypes types ⟨span, rest⟩
      return meaning.type :: tail
  | ⟨_, [⟨_, .ifThen _ yes (some no)⟩]⟩ =>
      return (← bindingTypes types yes) ++ (← bindingTypes types no)
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => return []
  | _ => throw (IO.userError "original annotated body shape changed")
termination_by sizeOf source
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (written : List Core.Ty) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  assertTrue (decide ((← bindingTypes types source.value.body) = written)) "independent written let annotation order/types changed"
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader types source.value.signature declared.type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, declared.meaning⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
    pure ()
  else throw (IO.userError "independent header policy rejected")
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError ("structural parameter entry did not compile: " ++ content))
  let original ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name sourceType := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains sourceType.span)
      "original parameter range changed"
    let meaning ← annotation types sourceType
    pure (name.value, meaning.type)
  let names := original.map Prod.fst
  assertTrue (decide (original.map Prod.snd = arguments.map (·.type))) "independent original parameter types changed"
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (original.map Prod.snd).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "structural arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "adapter flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid structural parameter gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid structural parameter gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid structural parameter gate exposed a checkpoint"
end StructuralLetEntries
open StructuralLetEntries

def frontendParsedStructuralLetEntryTests : IO Unit := do
  for annotation in ["()", "(())", "((),)"] do
    let source ← check [] ("function unit() returns(()){let u: " ++ annotation ++ "=();return u;}") []
      (.letE .unit (.var 0)) .unit .unit 4
      (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl)))) [.unit]
    for store in stores do
      assertTrue (decide (runRuntimeFunction? [] owner source [] 2 store =
        some (.unit, .outOfFuel ⟨.ret .unit, [.letBody (.var 0) []], store⟩))) "Unit binding checkpoint lost its tail"
  let _ ← check [(["Unit"],.word)] "function notReserved() returns(()){let u: ()=();return u;}" []
    (.letE .unit (.var 0)) .unit .unit 4
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl)))) [.unit]
  for n in [0,9,Core.wordModulus - 1] do
    for choice in [false,true] do
      let args := [wordArg n,boolArg choice]
      let ptype := Core.Ty.product .word .bool
      let pvalue := Core.Value.pair (w n) (.bool choice)
      let _ ← check types "function single(x: Word,c: Bool) returns(Word){let y: ((Word,))=x;return y;}" args
        (.letE (.var 1) (.var 0)) .word (w n) 4
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))) [.word]
      for annotation in ["(Word,Bool)", "((Word,),(Bool,))", "(Word,Bool,)"] do
        let _ ← check types ("function pair(x: Word,c: Bool) returns((Word,Bool)){let p: " ++ annotation ++ "=(x,c);return p;}") args
          (.letE (.pair (.var 1) (.var 0)) (.var 0)) ptype pvalue 8
          (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
            (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl)))))))) [ptype]
      let unused ← check types "function strict(x: Word,c: Bool) returns(Word){let unused: (Word,Bool)=(x,c);return x;}" args
        (.letE (.pair (.var 1) (.var 0)) (.var 2)) .word (w n) 8
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl)))))))) [ptype]
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner unused args 6 store =
          some (.word, .outOfFuel ⟨.ret pvalue, [.letBody (.var 2) [.bool choice,w n]], store⟩)))
          "unused structural initializer stopped executing strictly"
      let _ ← check types "function nested(x: Word,c: Bool) returns(((Word,Bool),())){let p: (Word,Bool)=(x,c);let q: ((Word,Bool),())=(p,());return q;}" args
        (.letE (.pair (.var 1) (.var 0)) (.letE (.pair (.var 0) .unit) (.var 0))) (.product ptype .unit) (.pair pvalue .unit) 15
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl)
          (.cons .applyPair (.cons .bindLet (.cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
            (.cons .unit (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl))))))))))))))) [ptype,.product ptype .unit]
      let _ ← check types "function arms(x: Word,c: Bool) returns((Word,Bool)){if(c){let p: (Word,Bool)=(x,c);return p;}else{let u: ()=();let p: (Word,Bool)=(x,c);return p;}}" args
        (.ifE (.var 0) (.letE (.pair (.var 1) (.var 0)) (.var 0)) (.letE .unit (.letE (.pair (.var 2) (.var 1)) (.var 0))))
        ptype pvalue (if choice then 11 else 14)
        (by
          intro store k
          cases choice
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet (.cons .unit (.cons .bindLet (.cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))))))))
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl)))))))))))) [ptype,.unit,ptype]
      for declaration in ["function mismatch(x: Word,c: Bool){let p: (Word,Bool)=();return ();}",
          "function order(x: Word,c: Bool){let p: (Bool,Word)=(x,c);return ();}",
          "function association(x: Word,c: Bool){let p: (Word,(Bool,()))=((x,c),());return ();}",
          "function unknown(x: Word,c: Bool){let p: (Word,Missing)=(x,c);return ();}",
          "function many(x: Word,c: Bool){let p: (Word,Bool,Word)=(x,c);return ();}",
          "function self(x: Word,c: Bool){let p: (Word,Bool)=p;return ();}",
          "function forward(x: Word,c: Bool){let p: (Word,Bool)=q;let q: (Word,Bool)=(x,c);return ();}",
          "function shadow(x: Word,c: Bool){let x: (Word)=x;return ();}",
          "function sibling(x: Word,c: Bool) returns((Word,Bool)){if(c){let p: (Word,Bool)=(x,c);return p;}else{return p;}}"] do
        rejected types (← parsed declaration) args
  let selected ← parsed "function skipped(x: Word,c: Bool) returns(Word){if(c){return x;}else{let bad: (Missing,())=(x,());return x;}}"
  let names : LocalNameTable := [("c",⟨owner,1⟩),("x",⟨owner,0⟩)]
  let env : Resolved.Environment := [(⟨owner,1⟩,.bool true),(⟨owner,0⟩,w 9)]
  for store in stores do
    let original ← body names env store selected.value.body
    assertTrue (decide (original.value = w 9 ∧ original.cost = 4 ∧
      evaluateTypedLetReturnTreeWithCost? owner names env selected.value.body = some (w 9,4))) "raw selected path changed"
  rejected types selected [wordArg 9,boolArg true]
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w 7],.closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArg : TypedRuntimeArgument := ⟨.product cell.type closure.type,.pair cell.value closure.value,.pair cell.valueTyped closure.valueTyped⟩
  let _ ← check types "function opaque(p: (Cell,Fn)) returns((Cell,Fn)){let q: (Cell,Fn)=p;return q;}" [opaqueArg]
    (.letE (.var 0) (.var 0)) opaqueArg.type opaqueArg.value 4
    (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))) [opaqueArg.type]
  let nominal ← parsed "function nominal(p: (N,())) returns((N,())){let q: (N,())=p;return q;}"
  let nominalTypes := (["N"],Core.Ty.namedData ⟨91⟩) :: types
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.letE (.var 0) (.var 0),.product (.namedData ⟨91⟩) .unit))) "static let required a nominal inhabitant"
  rejected nominalTypes nominal [wordArg 9]
end Tests
