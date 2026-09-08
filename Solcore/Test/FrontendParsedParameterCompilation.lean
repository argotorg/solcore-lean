import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionParameterCompilationProperties
import Solcore.Frontend.RuntimeFunctionConditionalParameterCompilationProperties

/-! Whole parsed entries consume all six positional compilation interfaces.
Actual source lookups and shapes fix open Core without argument inhabitants;
equal typing alone cannot certify a different source position or arm order. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owners : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"PositionalCompilation", by decide⟩], by decide⟩⟩, 7⟩,
    ⟨⟨.main, ⟨[⟨"OtherCompilation", by decide⟩], by decide⟩⟩, 53⟩]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Alias"], .namedData ⟨91⟩), (["Flag"], .bool)]
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)

private structure SelectedParameter (parameters : List Syntax.FunctionParameter) (index : Nat)
    (type : Core.Ty) where
  span : Syntax.SourceSpan
  name : Syntax.Identifier
  annotation : Syntax.TypeExpr
  atPosition : parameters[index]? = some ⟨span, .typed none name annotation⟩
  meaning : TypeNameDenotes types annotation type

private def selected (parameters : List Syntax.FunctionParameter) (index : Nat) (type : Core.Ty) :
    IO (SelectedParameter parameters index type) := do
  match atPosition : parameters[index]? with
  | some ⟨span, .typed none name annotation⟩ =>
      if interpreted : interpretTypeName? types annotation = some type then
        return ⟨span, name, annotation, atPosition, interpretTypeName?_sound interpreted⟩
      else throw (IO.userError "actual parameter annotation did not have the desired meaning")
  | _ => throw (IO.userError "actual source position was not a typed-none parameter")

private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-positional-compilation.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")

private def checkResult {owner : Resolved.DeclarationId} {source : Syntax.FunctionDecl}
    {inputs : LocalTypeInputs} {core : Core.Expr} {type : Core.Ty}
    (forward : RuntimeFunctionCompiles types owner source { inputs, core, returnType := type })
    (success : compileRuntimeFunction? types owner source = some { inputs, core, returnType := type })
    (inverse : ∀ compiled, RuntimeFunctionCompiles types owner source compiled →
      compiled.core = core ∧ compiled.returnType = type)
    (parameterTypes : List Core.Ty) (wrongCore : Core.Expr) : IO Unit := do
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError "independently proved whole entry did not compile")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      have _ := inverse compiled provenance
      have _ := forward.result_unique provenance
      have _ : compiled = { inputs, core, returnType := type } :=
        Option.some.inj (accepted.symm.trans success)
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
        rows compiled.inputs = rows inputs ∧ compiled.inputs.context.values = parameterTypes.reverse ∧
        Core.infer? parameterTypes.reverse core = some type)) "exact whole-entry record or open Core type changed"
      if different : wrongCore ≠ core then
        assertTrue (Core.infer? parameterTypes.reverse wrongCore == some type)
          "wrong-position fixture was not independently equally typed"
        have excluded : ¬ RuntimeFunctionCompiles types owner source
            { inputs, core := wrongCore, returnType := type } := by
          intro wrong
          exact different (inverse _ wrong).1
        have _ := excluded
        assertTrue (decide (compiled.core ≠ wrongCore)) "equally typed wrong Core acquired source provenance"

private def single (content : String) (index : Nat) (parameterTypes : List Core.Ty)
    (type : Core.Ty) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError "singleton fixture did not fully parse")
  let parameter ← selected source.value.signature.parameters.elements index type
  match bodyAt : source.value.body with
  | ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, spelling⟩⟩)⟩]⟩ =>
      if sameName : spelling = parameter.name.value then
        have bodyShape : source.value.body = ⟨blockSpan,
            [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, parameter.name.value⟩⟩)⟩]⟩ := by
          simpa only [sameName] using bodyAt
        assertTrue (source.span.contains parameter.span && parameter.span.contains parameter.name.span &&
          blockSpan.contains returnSpan && span.contains nameSpan) "own singleton source positions changed"
        for owner in owners do
          match declaredAt : declareRuntimeParameters? types owner source.value.signature.parameters.elements with
          | none => throw (IO.userError "whole parameter declaration failed")
          | some inputs =>
              let declared := declareRuntimeParameters?_sound declaredAt
              if headerAt : interpretRuntimeFunctionHeader? types source.value.signature = some type then
                let header := interpretRuntimeFunctionHeader?_iff.mp headerAt
                let forward := runtimeFunction_parameter_compiles declared parameter.atPosition parameter.meaning header bodyShape
                let success := compileRuntimeFunction?_parameter declared parameter.atPosition parameter.meaning header bodyShape
                let coreIndex := parameterTypes.length - 1 - index
                let wrongIndex := ((List.range parameterTypes.length).find? fun candidate =>
                  candidate != coreIndex && Core.infer? parameterTypes.reverse (.var candidate) == some type).getD coreIndex
                checkResult forward success (fun _ provenance => provenance.parameter_return_core
                  parameter.atPosition parameter.meaning bodyShape) parameterTypes (.var wrongIndex)
              else throw (IO.userError "whole singleton header failed")
      else throw (IO.userError "singleton reference did not name the selected parameter")
  | _ => throw (IO.userError "singleton fixture lost its exact identifier-return shape")

private def conditional (content : String) (conditionIndex thenIndex elseIndex : Nat)
    (parameterTypes : List Core.Ty) (type : Core.Ty) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError "conditional fixture did not fully parse")
  let parameters := source.value.signature.parameters.elements
  let condition ← selected parameters conditionIndex .bool
  let thenParameter ← selected parameters thenIndex type
  let elseParameter ← selected parameters elseIndex type
  match bodyAt : source.value.body with
  | ⟨blockSpan, [⟨ifSpan, .ifThen ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionSpelling⟩⟩
      ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenSpelling⟩⟩)⟩]⟩
      (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseSpelling⟩⟩)⟩]⟩)⟩]⟩ =>
      if sameCondition : conditionSpelling = condition.name.value then
        if sameThen : thenSpelling = thenParameter.name.value then
          if sameElse : elseSpelling = elseParameter.name.value then
            have bodyShape : source.value.body = ⟨blockSpan, [⟨ifSpan,
                .ifThen ⟨conditionSpan, .identifier ⟨conditionNameSpan, condition.name.value⟩⟩
                ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt
                  (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenParameter.name.value⟩⟩)⟩]⟩
                (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt
                  (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseParameter.name.value⟩⟩)⟩]⟩)⟩]⟩ := by
              simpa only [sameCondition, sameThen, sameElse] using bodyAt
            assertTrue (source.span.contains condition.span && source.span.contains thenParameter.span &&
              source.span.contains elseParameter.span && conditionSpan.contains conditionNameSpan &&
              thenSpan.contains thenNameSpan && elseSpan.contains elseNameSpan) "own conditional source positions changed"
            for owner in owners do
              match declaredAt : declareRuntimeParameters? types owner parameters with
              | none => throw (IO.userError "whole conditional parameters failed")
              | some inputs =>
                  let declared := declareRuntimeParameters?_sound declaredAt
                  if headerAt : interpretRuntimeFunctionHeader? types source.value.signature = some type then
                    let header := interpretRuntimeFunctionHeader?_iff.mp headerAt
                    let forward := runtimeFunction_conditional_parameters_compiles declared condition.atPosition
                      thenParameter.atPosition elseParameter.atPosition condition.meaning thenParameter.meaning elseParameter.meaning header bodyShape
                    let success := compileRuntimeFunction?_conditional_parameters declared condition.atPosition
                      thenParameter.atPosition elseParameter.atPosition condition.meaning thenParameter.meaning elseParameter.meaning header bodyShape
                    let count := parameterTypes.length
                    checkResult forward success (fun _ provenance => provenance.conditional_parameters_core
                      condition.atPosition thenParameter.atPosition elseParameter.atPosition condition.meaning
                      thenParameter.meaning elseParameter.meaning bodyShape) parameterTypes
                      (.ifE (.var (count - 1 - conditionIndex)) (.var (count - 1 - elseIndex)) (.var (count - 1 - thenIndex)))
                  else throw (IO.userError "whole conditional header failed")
          else throw (IO.userError "else reference changed its source parameter")
        else throw (IO.userError "then reference changed its source parameter")
      else throw (IO.userError "condition reference changed its source parameter")
  | _ => throw (IO.userError "conditional fixture lost its exact terminal shape")

private def parameterText (annotations : List String) : String :=
  String.intercalate ", " (annotations.zipIdx.map fun (annotation, index) => s!"p{index}: {annotation}")
private def conditionalText (annotations : List String) (condition thenIndex elseIndex : Nat)
    (returnAnnotation : String) : String :=
  s!"function select({parameterText annotations}) returns ({returnAnnotation})" ++
    "{if(" ++ s!"p{condition}" ++ "){return " ++ s!"p{thenIndex};" ++ "}else{return " ++ s!"p{elseIndex};" ++ "}}"

private def rejected (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed? content location | throw (IO.userError s!"semantic rejection did not fully parse: {content}")
  for owner in owners do
    match rejectedAt : compileRuntimeFunction? types owner source with
    | some _ => throw (IO.userError "a selected parameter bypassed a whole-entry obligation")
    | none =>
        have _ := compileRuntimeFunction?_eq_none_iff.mp rejectedAt
        pure ()

def frontendParsedParameterCompilationTests : IO Unit := do
  let pool : List (String × Core.Ty) := [("Opaque", .namedData ⟨91⟩), ("Word", .word), ("Bool", .bool),
    ("Unit", .unit), ("Cell", .cell .word), ("Fn", .function .bool .bool)]
  for arity in [1, 2, 4, 6] do
    let parameters := pool.take arity
    for (parameter, index) in parameters.zipIdx do
      single (s!"function pick({parameterText (parameters.map Prod.fst)}) returns ({parameter.1})" ++
        "{return " ++ s!"p{index};" ++ "}") index (parameters.map Prod.snd) parameter.2
  single "function aliases(x: Opaque,y: Alias) returns (Alias){return x;}" 0
    [.namedData ⟨91⟩, .namedData ⟨91⟩] (.namedData ⟨91⟩)
  for arity in [1, 2, 3, 4] do
    for condition in List.range arity do
      for thenIndex in List.range arity do
        for elseIndex in List.range arity do
          conditional (conditionalText (List.replicate arity "Bool") condition thenIndex elseIndex "Flag")
            condition thenIndex elseIndex (List.replicate arity .bool) .bool
  for condition in List.range 4 do
    let annotations := (List.range 4).map fun index => if index == condition then "Flag" else if index % 2 == 0 then "Opaque" else "Alias"
    let parameterTypes := (List.range 4).map fun index => if index == condition then Core.Ty.bool else .namedData ⟨91⟩
    for thenIndex in (List.range 4).filter (· != condition) do
      for elseIndex in (List.range 4).filter (· != condition) do
        conditional (conditionalText annotations condition thenIndex elseIndex "Alias")
          condition thenIndex elseIndex parameterTypes (.namedData ⟨91⟩)
  for (annotation, type) in pool do
    conditional (conditionalText [annotation, "Bool", annotation] 1 0 2 annotation)
      1 0 2 [type, .bool, type] type
  -- Valid ternary-return syntax is outside the exact terminal-if premise, not rejected.
  let some ternary ← parsed? "function ternary(c: Bool,x: Opaque,y: Alias) returns (Opaque){return c ? x : y;}"
    | throw (IO.userError "valid out-of-profile body did not parse")
  for owner in owners do
    let some compiled := compileRuntimeFunction? types owner ternary
      | throw (IO.userError "exact theorem body shape became an unintended compiler restriction")
    assertTrue (decide (compiled.core = .ifE (.var 2) (.var 1) (.var 0) ∧
      compiled.returnType = .namedData ⟨91⟩)) "valid ternary-return compilation changed"
  let some nested ← parsed? "function nested(c: Bool,x: Opaque) returns (Opaque){if(c){if(c){return x;}else{return x;}}else{return x;}}"
    | throw (IO.userError "valid recursive body did not parse")
  for owner in owners do
    assertTrue (decide ((compileRuntimeFunction? types owner nested).map (fun result => (result.core, result.returnType)) =
      some (.ifE (.var 1) (.ifE (.var 1) (.var 0) (.var 0)) (.var 0), .namedData ⟨91⟩)))
      "exact one-level theorem premise became a recursive compiler restriction"
  for content in ["function generic<T>(x: Opaque) returns (Opaque){return x;}",
      "function mismatch(x: Opaque) returns (Word){return x;}", "function absent(x: Opaque){return x;}",
      "function empty(x: Opaque) returns (){return x;}", "function many(x: Opaque) returns (Opaque,Opaque){return x;}",
      "function duplicate(x: Opaque,x: Opaque) returns (Opaque){return x;}",
      "function hidden(x: Opaque,y: Unknown) returns (Opaque){return x;}",
      "function staged(x: Opaque,comptime y: Word) returns (Opaque){return x;}",
      "function missing(x: Opaque) returns (Opaque){return missing;}",
      "function wrong(c: Word,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}",
      "function wrong(c: Bool,x: Opaque,y: Word) returns (Opaque){if(c){return x;}else{return y;}}",
      "function skipped(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}",
      "function noElse(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}}",
      "function extra(x: Opaque) returns (Opaque){return x;return x;}",
      "function extra(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}return x;}",
      "function armExtra(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;return x;}}"] do
    rejected content
  rejected "function publicOnly(x: Opaque) public returns (Opaque){return x;}" .contract
  for content in ["function missing(x){return x;}", "function missing(x:){return x;}",
      "function f(x: Word) returns (Word){return x}", "function f(x: Word){return x;} trailing"] do
    assertTrue (← parsed? content).isNone "malformed or partially consumed declaration became whole-entry evidence"

end Tests
