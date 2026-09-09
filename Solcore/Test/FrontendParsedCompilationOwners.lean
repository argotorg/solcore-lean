import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionCompilationOwnerProperties
import Solcore.Frontend.TerminalReturnTree

/-! Compilation owner laws are consumed without constructing runtime arguments.
Nominal and mixed type-only declarations retain exact Core/type projections;
their identity-bearing rows change, while written names and order do not. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def baseOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"CompilationOwners", by decide⟩], by decide⟩⟩, 4⟩
private def owners : List Resolved.DeclarationId :=
  [baseOwner, { baseOwner with declarationIndex := 52 },
    ⟨⟨.main, ⟨[⟨"OtherModule", by decide⟩], by decide⟩⟩, 4⟩]
private def shiftOwner (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { owner with declarationIndex := owner.declarationIndex + 17 }
private theorem shiftOwnerInjective : Function.Injective shiftOwner := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; simp_all [shiftOwner]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pair"], .product .word .bool), (["Choice"], .sum .word .bool), (["Pkg", "Flag"], .bool)]
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)
private def projection (compiled : CompiledRuntimeFunction) : Core.Expr × Core.Ty × List Core.Ty :=
  (compiled.core, compiled.returnType, compiled.inputs.context.values)

/-- The finite parsed grid below consumes an unrestricted owner theorem. There
are no argument values, inhabitation hypotheses, or successful-check premises. -/
private theorem arbitraryOwnerProjections (table : TypeNameTable)
    (left right : Resolved.DeclarationId) (source : Syntax.FunctionDecl) :
    (compileRuntimeFunction? table left source).map projection =
      (compileRuntimeFunction? table right source).map projection :=
  compileRuntimeFunction?_owner_projection_eq table left right source

private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-compilation-owners.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkProjections (source : Syntax.FunctionDecl)
    (expected : Option (Core.Expr × Core.Ty × List Core.Ty)) : IO Unit := do
  for left in owners do
    for right in owners do
      have _ := arbitraryOwnerProjections types left right source
      let first := (compileRuntimeFunction? types left source).map projection
      let second := (compileRuntimeFunction? types right source).map projection
      assertTrue (decide (first = second ∧ first = expected))
        "owner change altered complete Option projection or hid unexpected rejection/acceptance"
      match compileRuntimeFunction? types left source, compileRuntimeFunction? types right source with
      | some first, some second =>
          assertTrue (decide (first.inputs.names.map Prod.fst = second.inputs.names.map Prod.fst ∧
            first.inputs.ids.map (·.binderIndex) = second.inputs.ids.map (·.binderIndex)))
            "source spellings, row order, or binder indices changed"
          if left != right && !first.inputs.bindings.isEmpty then
            assertTrue (decide (first.inputs.ids ≠ second.inputs.ids ∧ first.inputs.names ≠ second.inputs.names ∧
              first.inputs.context ≠ second.inputs.context)) "distinct owners were erased from identity-bearing data"
      | none, none => pure ()
      | _, _ => throw (IO.userError "one-sided compilation failure")

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (core : Core.Expr) (returnType : Core.Ty) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError s!"{content}: expected complete declaration")
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "unexpected static parameter shape")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span &&
      parameter.span.contains annotation.span) "canonical parameter spans changed"
    pure name.value
  assertTrue (names.length == parameterTypes.length) "static parameter count changed"
  checkProjections source (some (core, returnType, parameterTypes.reverse))
  for owner in owners do
    match compiledAtOwner : compileRuntimeFunction? types owner source with
    | none => throw (IO.userError "value-free compilation unexpectedly failed")
    | some compiled =>
        let provenance := compileRuntimeFunction?_sound compiledAtOwner
        have _ := provenance.core_hasType
        let expectedRows := ((names.zip parameterTypes).zipIdx.map fun (entry, index) =>
          (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2)).reverse
        assertTrue (decide (rows compiled.inputs = expectedRows ∧
          compiled.inputs.context.values = parameterTypes.reverse ∧
          Core.infer? parameterTypes.reverse core = some returnType ∧
          elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body =
            some (core, returnType))) "static rows, open Core typing, or original whole body changed"
        let mapping := ownerLocalIdMap shiftOwner
        let injective := ownerLocalIdMap_injective shiftOwner shiftOwnerInjective
        let mapped := compiled.inputs.mapIds mapping injective
        let declaredMapped := provenance.parameters.map_owner shiftOwner shiftOwnerInjective
        let compiledMapped := provenance.mapOwner shiftOwner shiftOwnerInjective
        have _ := declaredMapped.complete
        have _ := compiledMapped.complete
        assertTrue (decide (mapped.ids = compiled.inputs.ids.map mapping ∧
          mapped.names = LocalNameTable.mapIds mapping compiled.inputs.names ∧
          mapped.context = Resolved.LocalScope.mapIds mapping compiled.inputs.context ∧
          mapped.context.values = compiled.inputs.context.values ∧
          mapped.names.map Prod.fst = names.reverse)) "type-only map failed to retain source spelling/type order"
        assertTrue (decide ((declareRuntimeParameters? types (shiftOwner owner)
          source.value.signature.parameters.elements).map rows = some (rows mapped)))
          "independent declaration covariance changed the exact mapped rows"
        let some shifted := compileRuntimeFunction? types (shiftOwner owner) source
          | throw (IO.userError "injective owner map lost independent compilation")
        assertTrue (decide (rows shifted.inputs = rows mapped ∧ projection shifted = projection compiled))
          "compiled evidence covariance changed the mapped inputs, exact Core, or return contract"
        let identityMapped := compiled.inputs.mapIds id (fun _ _ same => same)
        let twice := mapped.mapIds mapping injective
        let composed := compiled.inputs.mapIds (mapping ∘ mapping) (injective.comp injective)
        assertTrue (decide (rows identityMapped = rows compiled.inputs ∧ rows twice = rows composed))
          "type-only identity or composition changed rows"
        if !compiled.inputs.bindings.isEmpty then
          assertTrue (decide (mapped.ids ≠ compiled.inputs.ids ∧
            mapped.ids.map (·.binderIndex) = compiled.inputs.ids.map (·.binderIndex)))
            "owner relabeling was trivial or changed source positions"

private def rejected (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed? content location | throw (IO.userError s!"{content}: semantic rejection did not fully parse")
  checkProjections source none
  for owner in owners do
    assertTrue (compileRuntimeFunction? types owner source).isNone "owner change enabled a rejected whole declaration"

private def terminalBlock : IO Unit := do
  let some source ← parsed? "function nested(){{return;}}"
    | throw (IO.userError "original terminal wrapper did not parse")
  checkProjections source (some (.unit, .unit, []))
  for owner in owners do
    match atBody : source.value.body with
    | ⟨outerSpan, [⟨innerSpan, .block [⟨returnSpan, .returnStmt none⟩]⟩]⟩ =>
        have _ : TypedLetReturnTreeElaborates types owner .empty source.value.body .unit .unit := by
          rw [atBody]; exact .block (.single .bare)
        assertTrue (outerSpan.contains innerSpan && innerSpan.contains returnSpan &&
          decide (outerSpan.startByte < innerSpan.startByte ∧ innerSpan.endByte < outerSpan.endByte))
          "original inner block range changed"
    | _ => throw (IO.userError "original lexical wrapper AST changed")
    let some compiled := compileRuntimeFunction? types owner source
      | throw (IO.userError "terminal block lost owner-independent compilation")
    assertTrue (decide (compiled.core = .unit ∧ compiled.returnType = .unit ∧ rows compiled.inputs = []) &&
      (elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body).isNone)
      "wrapper introduced a parameter row or widened the old tree adapter"
    have _ (definitions : Core.DataEnvironment) : Core.HasType [] .unit .unit definitions := .unit
    have _ := arbitraryOwnerProjections types owner (shiftOwner owner) source

def frontendParsedCompilationOwnersTests : IO Unit := do
  terminalBlock
  accepted "function bare(){return;}" [] .unit .unit
  accepted "function literal() returns (Word){return 7;}" [] (.word (Core.Word.ofNatModulo 7)) .word
  accepted "function opaque(x: Opaque) returns (Opaque){return x;}" [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  accepted "function unused(x: Opaque){return;}" [.namedData ⟨91⟩] .unit .unit
  for body in ["{return c ? x : y;}", "{if(c){return x;}else{return y;}}"] do
    accepted ("function nominal(c: Bool,x: Opaque,y: Opaque) returns (Opaque)" ++ body)
      [.bool, .namedData ⟨91⟩, .namedData ⟨91⟩] (.ifE (.var 2) (.var 1) (.var 0)) (.namedData ⟨91⟩)
  accepted "function units(c: Bool){if(c){return;}else{return;}}" [.bool] (.ifE (.var 0) .unit .unit) .unit
  accepted "function nested(c: Bool){if(c){if(c){return;}else{return;}}else{return;}}"
    [.bool] (.ifE (.var 0) (.ifE (.var 0) .unit .unit) .unit) .unit
  accepted "function alias(c: Pkg /* same spelling */ . Flag,x: Word,y: Word,) returns (Word){if(c){return x / y;}else{return x % y;}}"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordDiv (.var 1) (.var 0))
      (.binary .wordMod (.var 1) (.var 0))) .word
  let pool : List (String × Core.Ty) := [("Bool", .bool), ("Word", .word), ("Unit", .unit),
    ("Cell", .cell .word), ("Fn", .function .bool .bool), ("Opaque", .namedData ⟨91⟩),
    ("Pair", .product .word .bool), ("Choice", .sum .word .bool)]
  for arity in [1, 2, 4, 6, 8] do
    let inputs := pool.take arity
    let parameters := String.intercalate ", " (inputs.zipIdx.map fun (row, index) => s!"p{index}: {row.1}")
    for (selected, index) in inputs.zipIdx do
      accepted (s!"function position({parameters}) returns ({selected.1})" ++ "{return " ++ s!"p{index};" ++ "}")
        (inputs.map Prod.snd) (.var (arity - 1 - index)) selected.2
  -- Return-clause arity belongs to static header policy; supplied-argument arity does not.
  for content in ["function absent(){return 7;}", "function mismatch() returns (Bool){return 7;}",
      "function empty() returns (){return;}", "function many() returns (Word,Bool){return 7;}",
      "function unknown() returns (Unknown){return;}", "function generic<T>(){return;}",
      "function constrained() where Word: Eq {return;}", "function duplicate(x: Bool,x: Bool){return;}",
      "function duplicate(x: Word,y: Bool,x: Opaque){return;}", "function staged(comptime x: Bool){return;}",
      "function unknown(x: Unknown){return;}", "function unsupported(x: Word<Bool>){return;}",
      "function emptyBody(){}", "function extra(){return;return;}",
      "function call(f: Fn) returns (Bool){return f();}",
      "function missing(c: Bool,x: Opaque) returns (Opaque){return c ? x : missing;}",
      "function missing(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}",
      "function wrong(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return 0;}}",
      "function wrong(c: Word,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}",
      "function noElse(c: Bool){if(c){return;}}", "function extra(c: Bool){if(c){return;}else{return;}return;}"] do
    rejected content
  for content in ["function publicOnly() public {return;}", "function payableOnly() payable {return;}"] do
    rejected content .contract
  -- Missing annotations are parser failures, not type-only argument-guard failures.
  for content in ["", "function missing(x){return;}", "function missing(x:){return;}", "function f()",
      "function f(){return;", "function f(){return 7}", "function f(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "malformed, diagnosed, or incompletely consumed declaration accepted"

end Tests
