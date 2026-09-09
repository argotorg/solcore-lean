import Solcore.Syntax.Parser.Function
import Solcore.Frontend.StructuralTypeTableProperties
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Complete types carry independent meaning. One structural return annotation
and parameters now execute; initialized-let annotations remain named-only. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedStructuralTypes
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "structural-type.sol"⟩, content⟩
private def parsed? (content : String) : IO (Option Syntax.TypeExpr) := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file content) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "complete original type range changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "type parser invariant")
private def parsed (content : String) : IO Syntax.TypeExpr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete type: {content}")
  return source
private structure Certificate (table : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes table source type
private def certify (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Certificate table source) := do
  match sourceAt : source with
  | ⟨_, .named name none⟩ =>
      match found : table.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent name missing")
      | some type => return ⟨type, by rw [sourceAt]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← certify table child
      return ⟨inner.type, by rw [sourceAt]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← certify table left
      let second ← certify table right
      return ⟨.product first.type second.type, by rw [sourceAt]; exact .pair first.meaning second.meaning⟩
  | _ => throw (IO.userError "outside independent structural certificate")
termination_by sizeOf source
private def checked (content : String) (table : TypeNameTable) (expected : Core.Ty) : IO Syntax.TypeExpr := do
  let source ← parsed content
  let independent ← certify table source
  assertTrue (decide (independent.type = expected)) "independent ordered type differs from fixture"
  have accepted := independent.meaning.complete
  have _ := interpretStructuralType?_sound accepted
  have _ := interpretStructuralType?_iff.mpr independent.meaning
  have _ := independent.meaning.type_unique (interpretStructuralType?_sound accepted)
  assertTrue (decide (interpretStructuralType? table source = some expected)) "structural interpretation differs from fixture"
  match source.value with
  | .named _ none =>
      assertTrue (decide (interpretTypeName? table source = some expected)) "named-only compatibility changed"
  | _ => assertTrue (interpretTypeName? table source).isNone "old named-only scope silently broadened"
  let otherSpan : Syntax.SourceSpan := ⟨⟨.external "unrelated", "raw"⟩, 92, 1⟩
  have _ := interpretStructuralType?_span table source otherSpan
  assertTrue (decide (interpretStructuralType? table { source with span := otherSpan } = some expected)) "meaning required outer range validity"
  let extras : TypeNameTable := [(["Word"], .unit), (["Unknown"], .bool)]
  have extended := independent.meaning.extend_types (TypeNameTable.Extends.append_right table extras)
  have _ := interpretStructuralType?_some_of_extends (TypeNameTable.Extends.append_right table extras) accepted
  assertTrue (decide (interpretStructuralType? (table ++ extras) source = some expected)) "later duplicates overrode an accepted nested leaf"
  have _ := extended.complete
  return source
private def table : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["PairAlias"], .product .word .bool), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word)]
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TypeGate", by decide⟩], by decide⟩⟩, 23⟩
private def w : TypedRuntimeArgument := ⟨.word, .word (Core.Word.ofNatModulo 9), .word⟩
private def b : TypedRuntimeArgument := ⟨.bool, .bool true, .bool⟩
private def u : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def p : TypedRuntimeArgument := ⟨.product .word .bool, .pair w.value b.value, .pair .word .bool⟩
private def declaration (content : String) : IO Syntax.FunctionDecl := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "entry lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file content) lexed)
    | throw (IO.userError "complete gate declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && lexed.diagnostics.isEmpty &&
    decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "gate source lost original completion or range"
  return source
private def oldGateRejected (content : String) (arguments : List TypedRuntimeArgument)
    (expected : Core.Ty) : IO Unit := do
  let source ← declaration content
  let annotations := source.value.signature.parameters.elements.filterMap (fun parameter =>
    match parameter.value with | .typed none _ annotation => some annotation | _ => none)
  let annotations := annotations ++ (source.value.signature.returnsClause.map (·.types.elements)).getD []
  let annotations := annotations ++ source.value.body.value.filterMap (fun statement =>
    match statement.value with | .letDecl _ (some annotation) _ => some annotation | _ => none)
  let structural := annotations.filter fun annotation => match annotation.value with | .tuple _ => true | _ => false
  let [annotation] := structural | throw (IO.userError "expected one original structural annotation")
  let independent ← certify table annotation
  assertTrue (decide (independent.type = expected ∧ interpretStructuralType? table annotation = some expected))
    "new structural meaning did not come from the original declaration annotation"
  have _ := independent.meaning.complete
  assertTrue (interpretTypeName? table annotation).isNone "old annotation adapter broadened"
  assertTrue (compileRuntimeFunction? table owner source).isNone "old static declaration gate broadened"
  assertTrue (prepareRuntimeFunction? table owner source arguments).isNone "old argument gate broadened"
  assertTrue (evaluateRuntimeFunctionWithCost? table owner source arguments).isNone "old direct entry gate broadened"
  for store in [[], [w.value, .cellRef .word 99]] do
    for fuel in [0, 1, 40] do
      assertTrue (runRuntimeFunction? table owner source arguments fuel store).isNone "rejected gate exposed execution"
private structure Raw (names : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost names env store source value store cost
private def raw (names : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Raw names env store source) := do
  match sourceAt : source with
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .identifier name⟩ =>
      match named : names.lookup? name.value with
      | none => throw (IO.userError "independent source name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← raw names env store left
      let second ← raw names env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "outside independent migrated return script")
termination_by sizeOf source
private structure Declared (initial : LocalTypeInputs) (parameters : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom table owner initial parameters inputs
private def declared (initial : LocalTypeInputs) (parameters : List Syntax.FunctionParameter) :
    IO (Declared initial parameters) := do
  match parametersAt : parameters with
  | [] => return ⟨initial, by rw [parametersAt]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest =>
      let certificate ← certify table annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declared (initial.bindFresh owner name.value certificate.type) rest
        return ⟨tail.inputs, by rw [parametersAt]; exact .cons certificate.meaning unused tail.evidence⟩
      else throw (IO.userError "original parameter spelling repeated")
  | _ => throw (IO.userError "unsupported original parameter shape")
private def checkedReturn (content : String) (arguments : List TypedRuntimeArgument)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (path : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (structuralReturn : Bool := true) : IO Unit := do
  let source ← declaration content
  let returnsMeaning : PLift (RuntimeReturnTypeDenotes table source.value.signature.returnsClause type) ←
    match returnsAt : source.value.signature.returnsClause with
    | none =>
        if same : type = .unit then pure ⟨by rw [returnsAt, same]; exact .absent⟩
        else throw (IO.userError "absent return must have Unit type")
    | some ⟨_, ⟨_, [annotation]⟩⟩ =>
        let independent ← certify table annotation
        if same : independent.type = type then
          if structuralReturn then
            assertTrue (interpretTypeName? table annotation).isNone "old named-only type adapter broadened"
          pure ⟨by rw [returnsAt]; exact .single (same ▸ independent.meaning)⟩
        else throw (IO.userError "independent structural return type differs from fixture")
    | _ => throw (IO.userError "expected exactly one return annotation")
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader table source.value.signature type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, returnsMeaning.down⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
  else throw (IO.userError "independent header policy not satisfied")
  let independent ← declared .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete independent.evidence
  if !structuralReturn then
    for parameter in source.value.signature.parameters.elements do
      let .typed none _ annotation := parameter.value | throw (IO.userError "parameter shape changed")
      assertTrue (interpretTypeName? table annotation).isNone "old named-only parameter meaning broadened"
  let expectedNames ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name _ := parameter.value | throw (IO.userError "parameter shape changed")
    pure name.value
  let expected := (expectedNames.zip arguments).zipIdx.map fun (entry, index) =>
    (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2.type)
  assertTrue (decide (independent.inputs.bindings.map (fun row => (row.name,row.id,row.type)) = expected.reverse ∧
    expectedNames.length = arguments.length)) "one original parameter no longer has one exact row/argument"
  let some compiled := compileRuntimeFunction? table owner source | throw (IO.userError "structural return did not compile")
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = independent.inputs.names ∧ compiled.inputs.context = independent.inputs.context)) "migrated return changed fixed Core/type"
  match preparedAt : prepareRuntimeFunction? table owner source arguments with
  | none => throw (IO.userError "original actual arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧
        prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context = compiled.inputs.context ∧
        prepared.inputs.bindings.length = source.value.signature.parameters.elements.length ∧
        prepared.inputs.environment.values = arguments.reverse.map (·.value))) "original argument layout changed"
      match bodyAt : source.value.body with
      | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
          for store in [[], [w.value, .cellRef .word 99]] do
            let original ← raw prepared.inputs.names prepared.inputs.environment store operand
            assertTrue (decide (original.value = value ∧ original.cost = cost)) "independent source value/cost changed"
            have bodyCost : TypedLetReturnTreeEvaluatesWithCost owner prepared.inputs.names prepared.inputs.environment
                store source.value.body original.value store original.cost := by
              rw [bodyAt]; exact .single (.expression original.costed)
            let costed := RuntimeFunctionEvaluatesWithCost.intro preparation bodyCost
            have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp costed).2
            have _ := (path store []).runStateful_done_iff (fuel := cost)
            assertTrue (decide (evaluateRuntimeFunctionWithCost? table owner source arguments = some (type, value, cost)))
              "whole direct return differs from independent fixture"
            for fuel in List.range (cost + 3) do
              have _ := costed.run_done_iff (fuel := fuel)
              assertTrue (match runRuntimeFunction? table owner source arguments fuel store with
                | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
                | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
                | _ => false) "migrated return changed threshold or own store"
            for spent in List.range cost do
              match exhausted : runRuntimeFunction? table owner source arguments spent store with
              | some (t, .outOfFuel checkpoint) =>
                  have _ := runRuntimeFunction?_resume exhausted (cost - spent)
                  assertTrue (decide (t = type ∧ Core.runStateful (cost - spent) checkpoint = .done value store))
                    "migrated return lost its genuine remaining path"
              | _ => throw (IO.userError "migrated return checkpoint missing")
      | _ => throw (IO.userError "original migrated body shape changed")
end ParsedStructuralTypes
open ParsedStructuralTypes

def frontendParsedStructuralTypeTests : IO Unit := do
  for (left, right) in [(Core.Ty.word, Core.Ty.bool), (.namedData ⟨83⟩, .cell .word),
      (.function .word .bool, .product .unit .bool)] do
    let caller : TypeNameTable := [(["Word"], left), (["Word"], .unit), (["Bool"], right)]
    for text in ["Word", "(Word)", "(Word,)", "((Word,),)"] do let _ ← checked text caller left
    for text in ["()", "(())", "((),)"] do let _ ← checked text caller .unit
    for text in ["(Word,Bool)", "(Word,Bool,)", "((Word,),(Bool,),)"] do
      let _ ← checked text caller (.product left right)
    let _ ← checked "(Bool,Word)" caller (.product right left)
    let _ ← checked "((Word,Bool),())" caller (.product (.product left right) .unit)
    let _ ← checked "(Word,(Bool,()))" caller (.product left (.product right .unit))
    for depth in [0, 1, 3, 6] do
      let text := (List.range depth).foldl (fun inner _ => "((),(" ++ inner ++ "),)") "Word"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit inner) left
      let _ ← checked text caller expected
    for text in ["Unknown", "(Word,Unknown)", "(Unknown,())", "((Unknown),)", "((),(Word,Unknown))"] do
      let source ← parsed text
      assertTrue (interpretStructuralType? caller source).isNone "missing written leaf received a fallback or was skipped"
  let _ ← checked "(Pkg /* first */ . Flag, Word)" table (.product .bool .word)
  let _ ← checked "(PairAlias,())" table (.product (.product .word .bool) .unit)
  let _ ← checked "((),())" [] (.product .unit .unit)
  let singleton ← parsed "(Word,)"
  assertTrue (match singleton.value with
    | .tuple [⟨span, .named name none⟩] => decide (span.startByte = 1 ∧ span.endByte = 5 ∧ qualifiedTypeNameKey name = ["Word"])
    | _ => false) "type singleton was rewritten into expression grouping"
  let nested ← parsed "((Word,Bool),())"
  assertTrue (match nested.value with
    | .tuple [⟨leftSpan, .tuple [left, right]⟩, ⟨unitSpan, .tuple []⟩] =>
        nested.span.contains leftSpan && leftSpan.contains left.span && leftSpan.contains right.span &&
        nested.span.contains unitSpan && decide (left.span.endByte < right.span.startByte ∧ leftSpan.endByte < unitSpan.startByte)
    | _ => false) "original nested associations or child ranges changed"
  for text in ["(Word,Bool,Word)", "((),(),(),())", "Word<Bool>", "(Word<Bool>)",
      "mapping(Word => Bool)", "@Word", "function(Word) returns(Bool)", "comptime<Word>",
      "((),@Word)", "(function() returns(),Word)"] do
    let source ← parsed text
    assertTrue (interpretStructuralType? table source).isNone "unsupported written constructor gained meaning"
  let missing ← parsed "(Word,New)"
  assertTrue (interpretStructuralType? table missing).isNone "unknown structural child already accepted"
  let _ ← checked "(Word,New)" (table ++ [(["New"], .bool)]) (.product .word .bool)
  let known ← parsed "(Word,Bool)"
  assertTrue (decide (interpretStructuralType? ((["Word"], .unit) :: table) known = some (.product .unit .bool)))
    "first-match meaning-changing shadowing was ignored"
  have sameLookup (key : List String) : table.lookup? key = (table ++ table).lookup? key := by
    simp (config := { contextual := true }) [table, TypeNameTable.lookup?]
  for text in ["(Word,Bool)", "(Word,Unknown)", "()", "(Word,Bool,Word)"] do
    let source ← parsed text
    have _ := interpretStructuralType?_congr_lookup table (table ++ table) sameLookup source
    assertTrue (decide (interpretStructuralType? table source = interpretStructuralType? (table ++ table) source))
      "duplicate-suffix lookup-equivalent tables changed the full optional result"
  checkedReturn "function unitParam(x: ()){return ();}" [u] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl) false
  checkedReturn "function pairParam(x: (Word,Bool)){return ();}" [p] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl) false
  checkedReturn "function singleParam(x: (Word)) returns(Word){return x;}" [w] (.var 0) .word w.value 1
    (by intro store k; exact .cons (.var rfl) .refl) false
  checkedReturn "function unitReturn() returns(()){return ();}" [] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl)
  checkedReturn "function pairReturn(x: Word,c: Bool) returns((Word,Bool)){return (x,c);}" [w,b]
    (.pair (.var 1) (.var 0)) (.product .word .bool) (.pair w.value b.value) 5
    (by intro store k; exact .cons .enterPair (.cons (.var rfl)
      (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
  checkedReturn "function singleReturn(x: Word) returns((Word)){return x;}" [w] (.var 0) .word w.value 1
    (by intro store k; exact .cons (.var rfl) .refl)
  oldGateRejected "function unitLet(){let x: ()=();return x;}" [] .unit
  oldGateRejected "function pairLet(x: Word,c: Bool) returns(PairAlias){let p: (Word,Bool)=(x,c);return p;}" [w,b] (.product .word .bool)
  for text in ["", "(", "Word Bool", "(Word,,Bool)", "(Word,Bool))", "(,)", "Word<>"] do
    assertTrue (← parsed? text).isNone s!"incomplete or malformed type accepted: {text}"
end Tests
