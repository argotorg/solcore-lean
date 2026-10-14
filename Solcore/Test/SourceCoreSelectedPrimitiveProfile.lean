import Solcore.Test.SourceCoreSelectedPrimitiveSource

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedPrimitiveProfile
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreSelectedPrimitiveFixture
open Tests.SourceCoreSelectedPrimitiveSource

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

theorem primitive_forms (left right : ExpressionId) (function : BuiltinFunctionId) (callee : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm false false false (.unary .bitNot left) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.binary left .add right) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.call callee [left, right] (.builtinFunction function)) = true :=
  ⟨rfl, rfl, rfl⟩

theorem narrow_forms (left right : ExpressionId) (function : BuiltinFunctionId) (callee : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm true false false (.unary .bitNot left) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.binary left .add right) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.call callee [left, right] (.builtinFunction function)) = false :=
  ⟨rfl, rfl, rfl⟩

private def success {artifact : SourceCoreExecution.Artifact}
    (fixture : Fixture) (session : SourceCoreExecution.Session artifact) (name : String)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let key ← SourceCoreUnifiedCorpusSupport.key fixture.program name
  let started ← get "primitive call" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0 | throw (IO.userError "primitive zero fuel did not suspend")
  let .succeeded result ← suspended.resume 100000 1000 | throw (IO.userError s!"primitive {name} failed")
  require (result.value == expected) s!"primitive {name} result changed: {reprStr result.value}"
  pure result.session

private def rawGuards (fixture : Fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled) : IO Unit := do
  for name in ["complement", "add", "builtin"] do
    let key ← SourceCoreUnifiedCorpusSupport.key fixture.program name
    let some named := fixture.recipe.compiled.indexed.base.functions.find? (fun named => decide (named.specialized.key = key))
      | throw (IO.userError "primitive raw guard row missing")
    let source := named.specialized.function.typedBody
    let some node := source.nodes.findSome? (fun
      | .expression node => match node.form with
        | .unary _ _ | .binary _ _ _ | .call _ _ (.builtinFunction _) => some node
        | _ => none
      | _ => none) | throw (IO.userError "primitive raw guard node missing")
    let certify := fun source => AcceptedCompilerExpressionProfile.certify fixture.recipe.compiled.indexed named source profile.table.rows
    require (certify source).isSome "primitive genuine expression profile failed"
    let dirty := {source with nodes := source.nodes.map (fun
      | .expression original => if original.id == node.id then .expression {original with coercions :=
          [{requirement := ⟨0⟩, source := original.rawType, target := original.type}]} else .expression original
      | other => other)}
    require (certify dirty).isNone "primitive output coercion bypassed metadata"
    let first :: _ := AcceptedCompilerExpressionProfile.operands node.form
      | throw (IO.userError "primitive actual ordered operand missing")
    let missing := {source with nodes := source.nodes.filter (fun
      | .expression original => original.id != first
      | _ => true)}
    require (certify missing).isNone "primitive missing operand accepted"
    if name == "builtin" then
      let dirty := {source with nodes := source.nodes.map (fun
        | .expression original => if original.id == node.id then .expression {original with requirements := [⟨0⟩]} else .expression original
        | other => other)}
      require (certify dirty).isNone "builtin requirement bypassed metadata"
  IO.println "PRIMITIVE_RAW_GUARDS_PASS: original nodes accepted; missing operands3, output coercions3, builtin requirements1 rejected"

def run : IO Unit := do
  let names := wordOperators.map (·.1) ++ comparisons.map (·.1) ++
    ["conjunction", "disjunction", "negation", "complement", "literal", "hugeLiteral", "nested", "builtin", "lt", "lessCall"]
  let compiled ← fixture names
  have checked : checkProgram workspace options.checkingFuel = .ok compiled.recipe.compiled.sourceProgram := by
    rw [compiled.sameProgram]; exact compiled.checked
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile compiled.recipe.compiled checked
    | throw (IO.userError "primitive selected profile rejected")
  IO.println s!"PRIMITIVE_CACHE: cache{compiled.recipe.compiled.indexed.base.functions.length}/table{profile.table.rows.length}"
  require (compiled.recipe.compiled.indexed.base.functions.length == 20 && profile.table.rows.length == 20)
    "primitive original cache/table changed"
  rawGuards compiled profile
  let complement ← row compiled "complement"
  let shape ← observeComplement complement
  let value := Word.ofNatModulo 37
  let started ← start compiled complement.row.key [.word value]
  have _sourceFirst : ∀ invocation, ∃ issued : SelectedCompilationCertifiedPublicSession.Profiled compiled.recipe,
      Nonempty (Conclusion issued started invocation) := fun invocation => from_source shape profile started invocation
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "primitive initial zero fuel did not suspend")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "primitive source-first complement failed")
  require (first.value == .word value.bitNot) "primitive source-first complement result changed"
  let after ← success compiled first.session "add" [word 17, word 25] (word 42)
  let after ← success compiled after "sub" [word 17, word 25] (.word ((Word.ofNatModulo 17).sub (Word.ofNatModulo 25)))
  let after ← success compiled after "mul" [word 6, word 7] (word 42)
  let after ← success compiled after "divide" [word 43, word 7] (word 6)
  let after ← success compiled after "modulo" [word 43, word 7] (word 1)
  let after ← success compiled after "band" [word 13, word 6] (word 4)
  let after ← success compiled after "bxor" [word 13, word 6] (word 11)
  let after ← success compiled after "bor" [word 13, word 6] (word 15)
  let after ← success compiled after "gt" [word 8, word 3] (.bool true)
  let after ← success compiled after "eq" [word 8, word 3] (.bool false)
  let after ← success compiled after "conjunction" [.bool true, .bool false] (.bool false)
  let after ← success compiled after "disjunction" [.bool false, .bool true] (.bool true)
  let after ← success compiled after "negation" [.bool true] (.bool false)
  let after ← success compiled after "literal" [] (word 17)
  let after ← success compiled after "hugeLiteral" [] (word 5)
  let after ← success compiled after "nested" [.bool true, word 5] (.product (word 7) (.bool true))
  let after ← success compiled after "nested" [.bool false, word 5] (.product (word 15) (.bool true))
  let after ← success compiled after "builtin" [] (word 1)
  let after ← success compiled after "lessCall" [word 3, word 8] (.bool true)
  require ([started.session.heapSize, first.session.heapSize, after.heapSize] == [21, 24, 123]) "primitive exact public heaps changed"
  IO.println s!"PRIMITIVE_HEAPS: initial{started.session.heapSize}; complement{first.session.heapSize}; final{after.heapSize}"
  IO.println "PRIMITIVE_COMPILER_PROFILE_FORWARD_PASS: unchanged original primitive program; actual whole profile and automatic startup; independent ordinary complement trace to closed public forward; exact builtin and ordered binary operands; zero-fuel resume"

end Tests.SourceCoreSelectedPrimitiveProfile
