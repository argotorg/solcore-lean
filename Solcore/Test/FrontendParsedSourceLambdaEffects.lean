import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope
import Solcore.Syntax.Parser.Term

set_option autoImplicit false
namespace Tests
namespace ParsedSourceLambdaEffects
open Solcore Solcore.Frontend
private abbrev Store := List RuntimeValue
private abbrev Captures := Resolved.LocalScope RuntimeValue
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def w (n : Nat) : RuntimeValue := .word ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def savedOwner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"SourceLambdaCallbacks",by decide⟩],by decide⟩⟩,153⟩
private def sid (index : Nat) : Resolved.LocalId := ⟨savedOwner,index⟩
private def callerOwner : Resolved.DeclarationId := {savedOwner with declarationIndex:=154}
private def cid (index : Nat) : Resolved.LocalId := ⟨callerOwner,index⟩
private def foreign : Resolved.LocalId := ⟨{savedOwner with declarationIndex:=900},700⟩
private def savedNames : LocalNameTable := [("x",sid 7),("r",sid 31),("x",foreign),("extra",sid 2)]
private def savedCaptured : Captures :=
  [(sid 32,.bool false),(sid 31,.cellRef .word 0),(sid 7,w 5),(sid 31,w 99),(foreign,.unit)]
private def callerNames : LocalNameTable := [("fetch",cid 7),("argument",cid 900),("r",cid 42)]
private def callerCaptured (source : Syntax.Expr) (argument : RuntimeValue) : Captures :=
  [(cid 900,argument),(cid 7,.sourceClosure source savedOwner savedNames savedCaptured),(cid 42,.cellRef .word 999)]
private theorem fresh : Resolved.freshLocalId savedOwner (savedNames.map Prod.snd) = sid 32 := by decide
private structure Original (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def original : (source : Syntax.Expr) → Option (Original source)
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ _ body⟩ => some ⟨name,body,.inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ body⟩ => some ⟨name,body,.typed⟩
  | _ => none
private def emptyCall (spelling : String) (source : Syntax.Expr) : Bool :=
  match source.value with
  | .call ⟨_,.identifier name⟩ ⟨_,[]⟩ => name.value == spelling
  | _ => false
private def touchReadSyntax (body : Syntax.Block) : Bool :=
  match body.value with
  | [⟨_,.expression touch true⟩,⟨_,.returnStmt (some ⟨_,.tuple ⟨_,
      [⟨_,.identifier parameter⟩,⟨_,.call ⟨_,.identifier load⟩ ⟨_,[⟨_,.identifier reference⟩]⟩⟩]⟩⟩)⟩] =>
      emptyCall "touch" touch && parameter.value == "x" && load.value == "load" && reference.value == "r"
  | _ => false

/- Independently supplied, deliberately limited callback semantics for these original calls.
They are neither the new relation recursively closed nor a canonical/general source evaluator. -/
private inductive Child (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Captures) :
    Store → Syntax.Expr → RuntimeValue → Store → Prop where
  | fetch {store source value target} (callSyntax : emptyCall "fetch" source = true)
      (named : LocalNameTable.Lookup names "fetch" target) (found : Resolved.LocalScope.Lookup captured target value) :
      Child owner names captured store source value (store ++ [.unit])
  | argument {store source value target} (callSyntax : emptyCall "argument" source = true)
      (named : LocalNameTable.Lookup names "argument" target) (found : Resolved.LocalScope.Lookup captured target value) :
      Child owner names captured store source value (store.set 0 (w 41))
private inductive Body (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Captures) :
    Store → Syntax.Block → RuntimeValue → Store → Prop where
  | touchRead {store source parameterId referenceId argument location value}
      (bodySyntax : touchReadSyntax source = true)
      (parameterName : LocalNameTable.Lookup names "x" parameterId)
      (parameter : Resolved.LocalScope.Lookup captured parameterId argument)
      (referenceName : LocalNameTable.Lookup names "r" referenceId)
      (reference : Resolved.LocalScope.Lookup captured referenceId (.cellRef .word location))
      (read : (store ++ [.bool true])[location]? = some value) :
      Body owner names captured store source (.pair argument value) (store ++ [.bool true])
private def noChild (_ : Resolved.DeclarationId) (_ : LocalNameTable) (_ : Captures)
    (_ : Store) (_ : Syntax.Expr) (_ : RuntimeValue) (_ : Store) : Prop := False
private def noBody (_ : Resolved.DeclarationId) (_ : LocalNameTable) (_ : Captures)
    (_ : Store) (_ : Syntax.Block) (_ : RuntimeValue) (_ : Store) : Prop := False
private theorem create (source : Syntax.Expr) (header : Original source) (store : Store) :
    SourceLambdaEvaluates noChild noBody savedOwner savedNames savedCaptured store source
      (.sourceClosure source savedOwner savedNames savedCaptured) store := .creation header.shape
private theorem call (source callee argument : Syntax.Expr) (header : Original source)
    (parameter : header.name.value = "x") (bodySyntax : touchReadSyntax header.body = true)
    (fetch : emptyCall "fetch" callee = true) (arg : emptyCall "argument" argument = true)
    (value : RuntimeValue) (span argumentsSpan : Syntax.SourceSpan) :
    SourceLambdaEvaluates Child Body callerOwner callerNames (callerCaptured source value)
      [w 23] ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ (.pair value (w 41)) [w 41,.unit,.bool true] := by
  have first : Child callerOwner callerNames (callerCaptured source value) [w 23] callee
      (.sourceClosure source savedOwner savedNames savedCaptured) [w 23,.unit] :=
    .fetch fetch .head (.tail (by decide) .head)
  have second : Child callerOwner callerNames (callerCaptured source value) [w 23,.unit] argument value [w 41,.unit] :=
    .argument arg (.tail (by decide) .head) .head
  have third : Body savedOwner (("x",sid 32)::savedNames) ((sid 32,value)::savedCaptured)
      [w 41,.unit] header.body (.pair value (w 41)) [w 41,.unit,.bool true] :=
    .touchRead bodySyntax .head .head (.tail (by decide) (.tail (by decide) .head))
      (.tail (by decide) (.tail (by decide) .head)) rfl
  exact .call header.shape first second (by simpa only [parameter,fresh] using third)
private theorem exact_rows (value : RuntimeValue) :
    ((("x",sid 32)::savedNames).map Prod.snd) = [sid 32,sid 7,sid 31,foreign,sid 2] ∧
    (((sid 32,value)::savedCaptured).map Prod.fst) = [sid 32,sid 32,sid 31,sid 7,sid 31,foreign] ∧
    Resolved.LocalScope.Lookup ((sid 32,value)::savedCaptured) (sid 32) value := ⟨rfl,rfl,.head⟩

private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"source-lambda-callbacks.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide
        (source.span=Syntax.SourceSpan.fullFile file ∧ next.diagnostics.length=diagnostics)) "complete original Expr and diagnostics"
      if text="lam(x:comptime<A>)->comptime<B>{return x;}" then
        let [⟨diagnosticSpan,.constraintViolation .comptimeTypeInParameter⟩] := next.diagnostics
          | throw (IO.userError "actual comptime parameter diagnostic")
        check (decide (diagnosticSpan=⟨file.id,6,17⟩)) "diagnostics do not replace the preserved raw parameter syntax"
      if let .lambda keyword parameters returns body := source.value then
        check (source.span.contains keyword && source.span.contains parameters.span &&
          source.span.contains body.span && parameters.elements.all (fun p => parameters.span.contains p.span) &&
          returns.toList.all (fun annotation => source.span.contains annotation.span) &&
          body.value.all (fun statement => body.span.contains statement.span)) "all original lambda subranges"
      return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private def inspectShape (text : String) (expected : Bool) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics
  match original source with
  | some header =>
      check expected "independent original unary shape"
      have decoded := sourceUnaryLambdaShape?_iff.mpr header.shape
      have _ : SourceUnaryLambdaShape source header.name header.body := sourceUnaryLambdaShape?_iff.mp decoded
      check (sourceUnaryLambdaShape? source == some (header.name,header.body)) "exact original name/body decoder"
      have created := create source header [w 5]
      have retained := (SourceLambdaEvaluates.creation_iff header.shape).mp created
      have _ := (SourceLambdaEvaluates.creation_iff (ChildEval:=noChild) (BodyEval:=noBody) header.shape).mpr retained
      check (decide (([w 5] : Store).map RuntimeValue.toCore? = [some (.word ⟨5,by decide⟩)]))
        "creation with empty body/child relations and unchanged actual store"
  | none => check (!expected && (sourceUnaryLambdaShape? source).isNone) "outside this unary shape only, not a language fault"
private def inspectCall (source callSource : Syntax.Expr) (value : RuntimeValue) : IO Unit := do
  let some header := original source | throw (IO.userError "saved original unary source")
  have generated := create source header [w 5]
  have _ := (SourceLambdaEvaluates.creation_iff header.shape).mp generated
  check (decide ((([w 5] : Store).map RuntimeValue.toCore?) ≠ ([w 23] : Store).map RuntimeValue.toCore?))
    "the same saved closure data is invoked with a different store, not a stored heap snapshot"
  match shape : callSource with
  | ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
      if parameter : header.name.value = "x" then
        if bodySyntax : touchReadSyntax header.body = true then
          if fetch : emptyCall "fetch" callee = true then
            if arg : emptyCall "argument" argument = true then
              have evaluated := call source callee argument header parameter bodySyntax fetch arg value span argumentsSpan
              have decomposed := SourceLambdaEvaluates.call_iff.mp evaluated
              have rebuilt := SourceLambdaEvaluates.call_iff.mpr decomposed
              have _ : SourceLambdaEvaluates Child Body callerOwner callerNames (callerCaptured source value)
                  [w 23] callSource (.pair value (w 41)) [w 41,.unit,.bool true] := by
                rw [shape]; exact rebuilt
              have rows := exact_rows value
              check (decide ((((sid 32,value)::savedCaptured).map Prod.fst)=
                [sid 32,sid 32,sid 31,sid 7,sid 31,foreign])) "actual parameter prepended; old colliding capture remains"
              have _ : Resolved.LocalScope.Lookup ((sid 32,value)::savedCaptured) (sid 32) value := rows.2.2
              check (decide (savedOwner ≠ callerOwner ∧
                Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)=sid 32 ∧
                Resolved.freshLocalId callerOwner (callerNames.map Prod.snd)=cid 901)) "saved owner and names-only freshness"
              check (decide (([w 23,.unit] : Store).map RuntimeValue.toCore?=
                [some (.word ⟨23,by decide⟩),some .unit] ∧
                ([w 41,.unit] : Store).map RuntimeValue.toCore?=
                [some (.word ⟨41,by decide⟩),some .unit] ∧
                ([w 41,.unit,.bool true] : Store).map RuntimeValue.toCore?=
                [some (.word ⟨41,by decide⟩),some .unit,some (.bool true)])) "distinct callee, argument and body store effects"
              check (decide (value.toCore?=none ∧ (RuntimeValue.pair value (w 41)).toCore?=none))
                "actual nonprojectable argument/result passed directly, never projected by the raw rules"
            else throw (IO.userError "argument callback syntax")
          else throw (IO.userError "callee callback syntax")
        else throw (IO.userError "independent saved original body syntax")
      else throw (IO.userError "original parameter spelling")
  | _ => throw (IO.userError "original unary outer call")
end ParsedSourceLambdaEffects

open ParsedSourceLambdaEffects in
/-- Original source rules consume supplied callback witnesses; no closed evaluator or typing claim. -/
def frontendParsedSourceLambdaEffectTests : IO Unit := do
  inspectShape "lam(x){return x;}" true
  inspectShape "lam(x:A)->B{let x:A=x;return saved;}" true
  inspectShape "lam(x,)->A{return saved;}" true
  inspectShape "lam(){return saved;}" false
  inspectShape "lam(x,y){return x;}" false
  inspectShape "lam(comptime x:A){return x;}" false
  inspectShape "lam(comptime){return comptime;}" true 1
  inspectShape "lam(comptime:A){return comptime;}" true 1
  inspectShape "lam(comptime x){return x;}" false 1
  inspectShape "lam(x){let ;}" true 1
  inspectShape "lam(x:Missing)->Missing{return absent;}" true
  inspectShape "lam(x){return lam(y){return x;};}" true
  inspectShape "saved" false
  inspectShape "saved(x)" false
  inspectShape "(lam(x){return x;})" false
  inspectShape "let" false 2
  let staged := "lam(x:comptime<A>)->comptime<B>{return x;}"
  inspectShape staged true 1
  let stagedSource ← parsed staged 1
  let .lambda _ ⟨_,[⟨_,.typed none _ ⟨_,.comptime _ _ _⟩⟩]⟩ _ _ := stagedSource.value
    | throw (IO.userError "unmarked comptime type is raw uninterpreted data, not staging admission")
  let text := "lam(x:Unknown)->comptime<B>{touch();return (x,load(r));}"
  inspectShape text true
  let source ← parsed text
  let callSource ← parsed "fetch()(argument())"
  let payloadSource ← parsed "lam(){return saved;}"
  let value := Solcore.Frontend.RuntimeValue.sourceClosure payloadSource callerOwner [] [(sid 99,.bool true)]
  inspectCall source callSource value
  inspectCall source callSource (.coreClosure .bool .unit (.var 99) [value,.cellRef .word 700])

end Tests
