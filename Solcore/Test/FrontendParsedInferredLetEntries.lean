import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Original missing annotations remain missing through checked recursive entries.
Independent annotation/raw-body evidence and fixed Core paths determine all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace InferredLetEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"InferredLetEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def unitArg : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pairArg (left right : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product left.type right.type,.pair left.value right.value,.pair left.valueTyped right.valueTyped⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "inferred-let-entry.sol"⟩, content }
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
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let head ← expression table env store first
      let tail ← expression table env store ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
      return ⟨.pair head.value tail.value, head.cost + tail.cost + 3, by rw [sourceAt]; exact .many head.costed tail.costed⟩
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← expression table env store yes
          return ⟨child.value,guard.cost + child.cost + 2,by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← expression table env store no
          return ⟨child.value,guard.cost + child.cost + 2,by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent conditional guard not Boolean")
  | _ => throw (IO.userError "expression outside independent tuple script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name optionalType (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by
        rw [sourceAt]; cases optionalType with
        | none => exact .inferred first.costed second.costed
        | some _ => exact .binding first.costed second.costed⟩
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
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← annotation types first
      let tail ← annotation types ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [atSource]; exact .many head.meaning tail.meaning⟩
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
private def bindingTypes (types : TypeNameTable) (source : Syntax.Block) : IO (List (Option Core.Ty)) := do
  match source with
  | ⟨span, ⟨letSpan, .letDecl name optionalType (some initializer)⟩ :: rest⟩ =>
      assertTrue (span.contains letSpan && letSpan.contains name.span && letSpan.contains initializer.span &&
        decide (name.span.endByte ≤ initializer.span.startByte)) "original inferred binding ranges/order changed"
      let written : Option Core.Ty ← match optionalType with
        | none => pure none
        | some sourceType => do
            assertTrue (letSpan.contains sourceType.span) "original written annotation range changed"
            let meaning ← annotation types sourceType
            pure (some meaning.type)
      return written :: (← bindingTypes types ⟨span, rest⟩)
  | ⟨_, [⟨_, .ifThen _ yes (some no)⟩]⟩ =>
      return (← bindingTypes types yes) ++ (← bindingTypes types no)
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => return []
  | _ => throw (IO.userError "original annotated body shape changed")
termination_by sizeOf source
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (written : List (Option Core.Ty)) : IO Syntax.FunctionDecl := do
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
end InferredLetEntries
open InferredLetEntries
def frontendParsedInferredLetEntryTests : IO Unit := do
  let _ ← check [] "function unit(){let u=();return u;}" [] (.letE .unit (.var 0)) .unit .unit 4
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) (.refl))))) [none]
  let _ ← check [(["Word"],.bool)] "function alias(x: Word) returns(Word){let z=x;return z;}" [boolArg true]
    (.letE (.var 0) (.var 0)) .bool (.bool true) 4 (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))) [none]
  for n in [0,9,Core.Word.maximum.val] do
    for choice in [false,true] do
      let args := [wordArg n,boolArg choice,wordArg 17]
      let _ ← check types "function mixed(x: Word,c: Bool,y: Word) returns(Word){let a=x;let b: Word=a;let d=b;return d;}"
        args (.letE (.var 2) (.letE (.var 0) (.letE (.var 0) (.var 0)))) .word (w n) 10
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))))))))) [none,some .word,none]
      let strict ← check types "function strict(x: Word,c: Bool,y: Word) returns(Word){let p=(x,y);return x;}"
        args (.letE (.pair (.var 2) (.var 0)) (.var 3)) .word (w n) 8
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))) [none]
      for store in stores do
        let saved : Core.State := ⟨.ret (.pair (w n) (w 17)),[.letBody (.var 3) [w 17,.bool choice,w n]],store⟩
        assertTrue (decide (runRuntimeFunction? types owner strict args 6 store = some (.word,.outOfFuel saved) ∧
          Core.runStateful 2 saved = .done (w n) store)) "unused initializer or actual residual let work disappeared"
      let _ ← check types "function product(x: Word,c: Bool,y: Word) returns((Word,Bool,Word)){let p=(x,c,y);return p;}"
        args (.letE (.pair (.var 2) (.pair (.var 1) (.var 0))) (.var 0))
        (.product .word (.product .bool .word)) (.pair (w n) (.pair (.bool choice) (w 17))) 12
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))))))) [none]
      let _ ← check types "function branch(x: Word,c: Bool,y: Word) returns(Word){if(c){let z=x;return z;}else{return y;}}"
        args (.ifE (.var 1) (.letE (.var 2) (.var 0)) (.var 0)) .word (if choice then w n else w 17)
        (if choice then 7 else 4) (by
          intro store k; cases choice
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) (.refl))))
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl)))))))) [none]
      for content in ["function bad(x: Word,c: Bool,y: Word) returns(Word){let p=missing;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p=p;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let x=x;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p=(x,missing);return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p: (Word,Bool)=(x,y);return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){if(c){let p=x;return p;}else{let p=missing;return p;}}"] do
        rejected types (← parsed content) args
  let captured : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w 7],
    .closure (.cons .word .nil) (.var rfl)⟩
  let packedOpaque := pairArg (pairArg ⟨.cell .word,.cellRef .word 999,.cellRef⟩ captured) unitArg
  let _ ← check types "function opaque(p:((Cell,Fn),())) returns(((Cell,Fn),())){let q=p;return q;}"
    [packedOpaque] (.letE (.var 0) (.var 0)) packedOpaque.type packedOpaque.value 4 (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))) [none]
  let nominalTypes : TypeNameTable := [(["N"],.namedData ⟨91⟩)]
  let nominal ← parsed "function nominal(x:N) returns(N){let z=x;return z;}"
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.letE (.var 0) (.var 0),.namedData ⟨91⟩))) "nominal static inference required an actual inhabitant"
  rejected nominalTypes nominal [wordArg 9]
end Tests
