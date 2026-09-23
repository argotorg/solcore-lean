import Solcore.Syntax.Parser.Function
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation

/-! Original parsed preparation failures remain absent under owner transport.
Selected raw body success does not repair a header, parameter list or branch. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationFunctionOwnerBoundaries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"FunctionOwnerBoundary",by decide⟩],by decide⟩⟩,136⟩
private def mapping (o : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {o with declarationIndex := o.declarationIndex+17}
private theorem injective : Function.Injective mapping := by
  rintro ⟨a,n⟩ ⟨b,m⟩ same; simpa [mapping] using same
private def relabel := ownerLocalIdMap mapping
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective mapping injective
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Word"],.bool)]
private def word : Core.Value := .word (Core.Word.ofNatModulo 14)
private def wordArg : TypedRuntimeArgument := ⟨.word,word,.word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool,.bool b,.bool⟩
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"function-owner-boundary.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"parser: {text}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) &&
    source.span.contains source.value.signature.span && source.span.contains source.value.body.span &&
    source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original complete function and header/body ranges"
  return source
private def compiledRows (c : CompiledRuntimeFunction) :=
  (c.inputs.bindings.map (fun r => (r.name,r.id,r.type)),c.core,c.returnType)
private def preparedRows (p : PreparedRuntimeFunction) :=
  (p.inputs.bindings.map (fun r => (r.name,r.id,r.type,r.value)),p.core,p.returnType)
private def rejected (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument)
    (compiles : Bool := false) : IO Unit := do
  let oldCompile := compileRecursiveComputationFunction? types owner source
  let nextCompile := compileRecursiveComputationFunction? types (mapping owner) source
  have compileLaw := compileComputationFunction?_mapOwner mapping injective elaborateRecursiveLocalComputation?
    (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner source
  have prepareLaw := prepareComputationFunction?_mapOwner mapping injective elaborateRecursiveLocalComputation?
    (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner source args
  check (oldCompile.isSome==compiles) "value-free compilation must be classified separately from bad actual arguments"
  check (decide (nextCompile.map compiledRows = (oldCompile.map (fun c =>
    {c with inputs := c.inputs.mapIds relabel relabel_injective})).map compiledRows)) "all compiled rows/Core/type retained"
  have _ := congrArg (Option.map compiledRows) compileLaw
  match absent : prepareRecursiveComputationFunction? types owner source args with
  | some _ => throw (IO.userError "original preparation unexpectedly accepted")
  | none =>
      have absentMapped : prepareRecursiveComputationFunction? types (mapping owner) source args=none := by
        change prepareComputationFunction? _ _ _ _ _ = _
        rw [prepareLaw]
        change (prepareRecursiveComputationFunction? types owner source args).map _ = none
        rw [absent]; rfl
      have noOriginal : ¬ ∃ p, RecursiveComputationFunctionPrepares types owner source args p := by
        rintro ⟨p,h⟩
        have impossible := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr h
        change prepareRecursiveComputationFunction? types owner source args=some p at impossible
        rw [absent] at impossible; cases impossible
      have noMapped : ¬ ∃ p, RecursiveComputationFunctionPrepares types (mapping owner) source args p := by
        rintro ⟨p,h⟩
        have impossible := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr h
        change prepareRecursiveComputationFunction? types (mapping owner) source args=some p at impossible
        rw [absentMapped] at impossible; cases impossible
      have _ := noOriginal; have _ := noMapped
      check (decide ((prepareRecursiveComputationFunction? types (mapping owner) source args).map preparedRows=none))
        "no mapped complete prepared record"
      for store in [[],[Core.Value.bool false,.cellRef .word 700,word]] do
        for fuel in [0,1,4,25] do
          have _ := runComputationFunction?_mapOwner mapping injective elaborateRecursiveLocalComputation?
            (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner source args fuel store
          have originalNone : runRecursiveComputationFunction? types owner source args fuel store=none := by
            simp only [runRecursiveComputationFunction?,runComputationFunction?,absent,bind,Option.bind_none]
          have _ := originalNone
          check (decide (runRecursiveComputationFunction? types owner source args fuel store=none ∧
            runRecursiveComputationFunction? types (mapping owner) source args fuel store=none))
            "preparation absence is None, never a runtime fault or exhausted state"
  match absent : compileRecursiveComputationFunction? types owner source with
  | none =>
      have _ : ¬ ∃ c, RecursiveComputationFunctionCompiles types owner source c := by
        rintro ⟨c,h⟩
        have impossible := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr h
        change compileRecursiveComputationFunction? types owner source=some c at impossible
        rw [absent] at impossible; cases impossible
      check nextCompile.isNone "compile absence retained"
  | some _ => pure ()
private structure Atom (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ st, RecursiveLocalComputationEvaluatesWithCost names env st s value st 1
private def atom (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Expr) : IO (Atom names env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match found : env.lookup? localId with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .pure (.identifier
          (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _ => throw (IO.userError "original raw row")
    | _ => throw (IO.userError "original raw name")
  | _ => throw (IO.userError "raw identifier fixture")
private structure Raw (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ st, RecursiveComputationReturnTreeEvaluatesWithCost owner names env st s value st cost
private def raw (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Block) : IO (Raw names env s) := do
  check (s.value.all fun statement => s.span.contains statement.span) "original raw statement ranges"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ =>
      let a ← atom names env expression
      return ⟨a.value,1,fun st => by rw [shape]; exact .expression (a.evidence st)⟩
  | ⟨span,⟨_,.letDecl name annotation (some init)⟩::rest⟩ =>
      let a ← atom names env init
      let fresh := Resolved.freshLocalId owner (names.map Prod.snd)
      let b ← raw ((name.value,fresh)::names) ((fresh,a.value)::env) ⟨span,rest⟩
      return ⟨b.value,1+b.cost+2,fun st => by
        rw [shape]; cases annotation with
        | none => exact .inferred (a.evidence st) (b.evidence st)
        | some _ => exact .binding (a.evidence st) (b.evidence st)⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let a ← atom names env condition
      match selected : a.value with
      | .bool true =>
          let b ← raw names env yes
          return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifTrue (selected ▸ a.evidence st) (b.evidence st)⟩
      | .bool false =>
          let b ← raw names env no
          return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifFalse (selected ▸ a.evidence st) (b.evidence st)⟩
      | _ => throw (IO.userError "original raw condition")
  | _ => throw (IO.userError "raw body fixture")
termination_by sizeOf s
private def rawOnly (text : String) (yesCost noCost : Nat) (yesValue noValue : Core.Value) : IO Unit := do
  let source ← parsed text
  let names : LocalNameTable := [("c",⟨owner,1⟩),("x",⟨owner,0⟩)]
  for choice in [false,true] do
    let env : Resolved.Environment := [(⟨owner,1⟩,.bool choice),(⟨owner,0⟩,word)]
    let original ← raw names env source.value.body
    if same : original.cost=(if choice then yesCost else noCost) ∧ original.value=(if choice then yesValue else noValue) then
      have _ : ∀ st, RecursiveComputationReturnTreeEvaluatesWithCost owner names env st source.value.body
          (if choice then yesValue else noValue) st (if choice then yesCost else noCost) := by
        simpa only [same.1,same.2] using original.evidence
      rejected source [wordArg,boolArg choice]
    else throw (IO.userError "independent selected original raw value/cost")
end ParsedComputationFunctionOwnerBoundaries
open ParsedComputationFunctionOwnerBoundaries in
def frontendParsedComputationFunctionOwnerBoundaryTests : IO Unit := do
  let identity ← parsed "function identity(x:Word)returns(Word){return x;}"
  for args in [[],[wordArg,wordArg],[boolArg true]] do rejected identity args true
  let noArgs ← parsed "function empty(){return;}"
  rejected noArgs [wordArg] true
  for (text,args) in [
      ("function duplicate(x:Word,x:Word)returns(Word){return x;}",[wordArg,wordArg]),
      ("function compile(comptime x:Word)returns(Word){return x;}",[wordArg]),
      ("function unknown(x:Missing)returns(Word){return x;}",[wordArg]),
      ("function mismatch(x:Word)returns(Bool){return x;}",[wordArg]),
      ("function absent(x:Word){return x;}",[wordArg]),
      ("function unknownReturn(x:Word)returns(Missing){return x;}",[wordArg]),
      ("function emptyReturn(x:Word)returns(){return x;}",[wordArg]),
      ("function many(x:Word)returns(Word,Bool){return x;}",[wordArg]),
      ("function generic<T>(x:Word)returns(Word){return x;}",[wordArg]),
      ("function constrained(x:Word)returns(Word)where Word:Eq{return x;}",[wordArg]),
      ("function missing(x:Word)returns(Word){return missing;}",[wordArg])] do
    rejected (← parsed text) args
  for text in ["function publicOnly(x:Word)public returns(Word){return x;}",
      "function payableOnly(x:Word)payable returns(Word){return x;}"] do
    rejected (← parsed text .contract) [wordArg]
  rawOnly "function unknownBranch(x:Word,c:Bool)returns(Word){if(c){return x;}else{let x:Missing=x;return x;}}" 4 7 word word
  rawOnly "function exposed(x:Word,c:Bool)returns(Word){if(c){let x=x;return x;}else{return x;}}" 7 4 word word
  rawOnly "function branches(x:Word,c:Bool)returns(Word){if(c){return c;}else{return x;}}" 4 4 (.bool true) word
end Tests
