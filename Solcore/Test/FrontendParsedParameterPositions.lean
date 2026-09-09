import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeParameterDeclarationReferenceProperties
import Solcore.Frontend.RuntimeFunctionCompilationOwnerProperties

/-! Actual parsed parameter lookups justify reversed Core indices without
runtime arguments. Same-type positions, nominal types, owner composition and
out-of-range subtraction retain their distinct static contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owners : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"StaticPositions", by decide⟩], by decide⟩⟩, 4⟩,
    ⟨⟨.main, ⟨[⟨"OtherPositions", by decide⟩], by decide⟩⟩, 4⟩]
private def shiftOwner (offset : Nat) (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { owner with declarationIndex := owner.declarationIndex + offset }
private theorem shiftInjective (offset : Nat) : Function.Injective (shiftOwner offset) := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; simp_all [shiftOwner]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)

private theorem desiredPosition {table : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare table owner parameters inputs) {index : Nat}
    {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier} {annotation : Syntax.TypeExpr}
    {type : Core.Ty} (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes table annotation type) :
    index < parameters.length ∧ inputs.bindings[parameters.length - 1 - index]? =
      some { name := name.value, id := ⟨owner, index⟩, type } ∧
      LocalNameTable.Lookup inputs.names name.value ⟨owner, index⟩ ∧
      Resolved.LocalScope.Lookup inputs.context ⟨owner, index⟩ type ∧
      Resolved.LocalScope.IndexOf inputs.context.ids ⟨owner, index⟩ (parameters.length - 1 - index) := by
  obtain ⟨bounded, actualType, actualMeaning, rowAt, named, typed, indexed⟩ := declared.position parameterAt
  have same := actualMeaning.type_unique meaning.structural
  cases same
  exact ⟨bounded, rowAt, named, typed, indexed⟩

private theorem noOutsideWitness {table : TypeNameTable} {owner : Resolved.DeclarationId}
    {parameters : List Syntax.FunctionParameter} {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare table owner parameters inputs) (index : Nat)
    (outside : parameters.length ≤ index) :
    ¬ ∃ span name annotation, parameters[index]? = some ⟨span, .typed none name annotation⟩ := by
  rintro ⟨span, name, annotation, parameterAt⟩
  exact Nat.not_lt_of_ge outside (declared.position parameterAt).1

private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-static-positions.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkOutside {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs} (declared : RuntimeParametersDeclare types owner parameters inputs) : IO Unit := do
  for index in [parameters.length, parameters.length + 1, parameters.length + 17] do
    if outside : parameters.length ≤ index then
      have _ := noOutsideWitness declared index outside
      assertTrue (decide (parameters[index]? = none ∧ parameters.length - 1 - index = 0 ∧
        inputs.context.lookup? ⟨owner, index⟩ = none ∧
        Resolved.LocalScope.index? inputs.ids ⟨owner, index⟩ = none))
        "saturated subtraction fabricated an out-of-range parameter, type lookup, or Core index"
    else throw (IO.userError "outside fixture was in range")

private def checkSelected (source : Syntax.FunctionDecl) (index : Nat) (expectedType : Core.Ty)
    {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    (declared : RuntimeParametersDeclare types owner source.value.signature.parameters.elements inputs) : IO Unit := do
  let parameters := source.value.signature.parameters.elements
  let count := parameters.length
  have _ := declared.rows.arity
  have _ := declared.bindings_length
  have _ := declared.names_nodup
  have _ := declared.generated_ids
  assertTrue (decide (inputs.bindings.length = count ∧ (inputs.names.map Prod.fst).Nodup ∧
    inputs.ids = (List.range count).reverse.map (fun index => (⟨owner, index⟩ : Resolved.LocalId))))
    "empty-start layout changed arity, unique spellings, or generated identities"
  match parameterAt : parameters[index]? with
  | some ⟨parameterSpan, .typed none name annotation⟩ =>
      if interpreted : interpretTypeName? types annotation = some expectedType then
        let meaning := interpretTypeName?_sound interpreted
        have _ := declared.rows.row_at parameterAt
        have _ := desiredPosition declared parameterAt meaning
        let coreIndex := count - 1 - index
        assertTrue (decide (index < count ∧ inputs.bindings[coreIndex]?.map
          (fun row => (row.name, row.id, row.type)) = some (name.value, ⟨owner, index⟩, expectedType) ∧
          inputs.names.lookup? name.value = some ⟨owner, index⟩ ∧
          inputs.context.lookup? ⟨owner, index⟩ = some expectedType ∧
          Resolved.LocalScope.index? inputs.context.ids ⟨owner, index⟩ = some coreIndex))
          "actual source lookup lost its exact reversed row or first-match position"
        match bodyAt : source.value.body with
        | ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨expressionSpan, .identifier reference⟩)⟩]⟩ =>
            if sameName : reference.value = name.value then
              have _ := declared.reference_resolves_at parameterAt expressionSpan reference.span
              have _ := declared.reference_elaborates_at parameterAt meaning expressionSpan reference.span
              have returned := declared.reference_return_elaborates_at parameterAt meaning
                blockSpan returnSpan expressionSpan reference.span
              have ownReturn : ReturnBodyElaborates inputs.names inputs.context source.value.body
                  (.var coreIndex) expectedType := by
                simpa only [bodyAt, ← sameName] using returned
              have _ := ownReturn.complete
              let expression : Syntax.Expr := ⟨expressionSpan, .identifier reference⟩
              assertTrue (decide (resolveLocalExpression? inputs.names expression = some (.var ⟨owner, index⟩) ∧
                elaborateLocalExpression? inputs.names inputs.context expression = some (.var coreIndex, expectedType) ∧
                elaborateReturnBody? inputs.names inputs.context source.value.body = some (.var coreIndex, expectedType) ∧
                Core.infer? inputs.context.values (.var coreIndex) = some expectedType))
                "own parsed identifier or return did not retain exact positional Core/type"
              assertTrue (source.span.contains parameterSpan && parameterSpan.contains name.span &&
                blockSpan.contains returnSpan && returnSpan.contains expressionSpan && expressionSpan.contains reference.span)
                "source spelling/position witnesses were replaced"
              if 1 < count then
                let wrongIndex := (coreIndex + 1) % count
                assertTrue (decide (wrongIndex ≠ coreIndex ∧
                  Resolved.LocalScope.index? inputs.ids ⟨owner, index⟩ ≠ some wrongIndex ∧
                  elaborateLocalExpression? inputs.names inputs.context expression ≠ some (.var wrongIndex, expectedType)))
                  "same-type or in-range alternative index replaced the actual source position"
            else throw (IO.userError "parsed return named a different source parameter")
        | _ => throw (IO.userError "positive fixture did not retain its own singleton identifier return")
      else throw (IO.userError "actual parameter annotation did not denote the desired type")
  | _ => throw (IO.userError "selected source position lacked its actual typed-none parameter")
  checkOutside declared

private def checkText (content : String) (index : Nat) (parameterTypes : List Core.Ty)
    (expectedType : Core.Ty) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError "complete positional declaration did not parse")
  for owner in owners do
    match accepted : declareRuntimeParameters? types owner source.value.signature.parameters.elements with
    | none => throw (IO.userError "type-only parameter declaration failed")
    | some inputs =>
        let declared := declareRuntimeParameters?_sound accepted
        assertTrue (decide (inputs.context.values = parameterTypes.reverse)) "static type order changed"
        checkSelected source index expectedType declared
        let first := shiftOwner 7
        let second := shiftOwner 11
        let once := declared.map_owner first (shiftInjective 7)
        let twice := once.map_owner second (shiftInjective 11)
        let composed := declared.map_owner (second ∘ first) ((shiftInjective 11).comp (shiftInjective 7))
        checkSelected source index expectedType twice
        checkSelected source index expectedType composed
        let firstInputs := inputs.mapIds (ownerLocalIdMap first) (ownerLocalIdMap_injective first (shiftInjective 7))
        let twiceInputs := firstInputs.mapIds (ownerLocalIdMap second) (ownerLocalIdMap_injective second (shiftInjective 11))
        let composedInputs := inputs.mapIds (ownerLocalIdMap (second ∘ first))
          (ownerLocalIdMap_injective (second ∘ first) ((shiftInjective 11).comp (shiftInjective 7)))
        have _ := inputs.mapIds_comp (ownerLocalIdMap first) (ownerLocalIdMap second)
          (ownerLocalIdMap_injective first (shiftInjective 7)) (ownerLocalIdMap_injective second (shiftInjective 11))
        assertTrue (decide (rows twiceInputs = rows composedInputs ∧ inputs.ids ≠ twiceInputs.ids ∧
          inputs.names.map Prod.fst = twiceInputs.names.map Prod.fst)) "composed owner transport changed spelling/order"
        let some compiled := compileRuntimeFunction? types owner source
          | throw (IO.userError "valid own positional return did not compile")
        assertTrue (decide (compiled.core = .var (parameterTypes.length - 1 - index) ∧
          compiled.returnType = expectedType ∧ rows compiled.inputs = rows inputs)) "whole compilation replaced source correspondence"

def frontendParsedParameterPositionTests : IO Unit := do
  let pool : List (String × Core.Ty) := [("Opaque", .namedData ⟨91⟩), ("Word", .word), ("Bool", .bool),
    ("Cell", .cell .word), ("Fn", .function .bool .bool), ("Opaque", .namedData ⟨91⟩), ("Word", .word), ("Unit", .unit)]
  for arity in [1, 2, 3, 5, 8] do
    let selectedTypes := pool.take arity
    let parameters := String.intercalate ", " (selectedTypes.zipIdx.map fun (row, index) => s!"p{index}: {row.1}")
    for (selected, index) in selectedTypes.zipIdx do
      checkText (s!"function pick({parameters}) returns ({selected.1})" ++ " { return " ++ s!"p{index};" ++ " }")
        index (selectedTypes.map Prod.snd) selected.2
  checkText "function same(x: Opaque,y: Opaque) returns (Opaque){return x;}" 0
    [.namedData ⟨91⟩, .namedData ⟨91⟩] (.namedData ⟨91⟩)
  let nominalContext : Core.Context := [.namedData ⟨91⟩, .namedData ⟨91⟩]
  assertTrue (decide (Core.infer? nominalContext (.var 0) = some (.namedData ⟨91⟩) ∧
    Core.infer? nominalContext (.var 1) = some (.namedData ⟨91⟩) ∧ 2 - 1 - 2 = 0))
    "same types or saturated subtraction must not justify a source position"
  let some empty ← parsed? "function empty(){return;}" | throw (IO.userError "empty declaration did not parse")
  for owner in owners do
    match accepted : declareRuntimeParameters? types owner empty.value.signature.parameters.elements with
    | some _inputs => checkOutside (declareRuntimeParameters?_sound accepted)
    | none => throw (IO.userError "empty static parameters rejected")
  for (content, parametersAccepted) in [
      ("function duplicate(x: Word,x: Word){return;}", false),
      ("function duplicate(x: Word,y: Bool,x: Opaque){return;}", false),
      ("function unknown(x: Unknown){return;}", false), ("function staged(comptime x: Word){return;}", false),
      ("function missing(x: Opaque) returns (Opaque){return missing;}", true),
      ("function wrong(x: Opaque) returns (Word){return x;}", true),
      ("function call(f: Fn) returns (Bool){return f();}", true),
      ("function skipped(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}", true)] do
    let some source ← parsed? content | throw (IO.userError "semantic rejection did not fully parse")
    for owner in owners do
      assertTrue ((declareRuntimeParameters? types owner source.value.signature.parameters.elements).isSome == parametersAccepted)
        "whole-body rejection was confused with parameter declaration rejection"
      assertTrue (compileRuntimeFunction? types owner source).isNone "valid parameter layout certified an invalid whole body/contract"
  for content in ["", "function missing(x){return;}", "function missing(x:){return;}",
      "function f()", "function f(x: Word){return x;} trailing"] do
    assertTrue (← parsed? content).isNone "missing annotations or incomplete source became static parameter evidence"

end Tests
