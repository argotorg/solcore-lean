import Solcore.Frontend.SourceInference

/-!
End-to-end coverage for the occurrence-addressed typed source produced by
source inference.  The fixture deliberately combines lexical shadowing,
generic overload selection, rejected overload candidates, a two-edge coercion
path, an operator obligation, and final numeric-literal defaulting.
-/

set_option autoImplicit false

namespace Tests.SourceTypedIRInference

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private structure Fixture where
  environment : ProgramEnvironment
  checked : List CheckedFunction

private def check (content : String) : IO Fixture := do
  match loadProgram (workspace content) with
  | .error errors =>
      throw (IO.userError s!"typed IR loading failed: {reprStr errors}")
  | .ok loaded =>
      match SourceInference.checkLoadedProgram loaded with
      | .error errors =>
          throw (IO.userError s!"typed IR checking failed: {reprStr errors}")
      | .ok checked => pure { environment := loaded.environment, checked }

private def checkedNamed (fixture : Fixture) (name : String) :
    IO CheckedFunction :=
  match fixture.checked.find? fun function =>
      match fixture.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def namedType (environment : ProgramEnvironment) (name : String) :
    IO TypeSystem.Ty :=
  match environment.typesNamed name with
  | [declaration] => pure (.nominal declaration.id)
  | declarations =>
      throw (IO.userError
        s!"expected one type `{name}`, found {declarations.length}")

private def namedTrait (environment : ProgramEnvironment) (name : String) :
    IO Resolved.DeclarationId :=
  match environment.traitsNamed name with
  | [declaration] => pure declaration.id
  | declarations =>
      throw (IO.userError
        s!"expected one trait `{name}`, found {declarations.length}")

private def namedFunctionWhere (environment : ProgramEnvironment) (name : String)
    (accept : ProgramDeclaration → Bool) : IO Resolved.DeclarationId :=
  match (environment.valuesNamed name).filter accept with
  | [declaration] => pure declaration.id
  | declarations =>
      throw (IO.userError
        s!"expected one selected declaration `{name}`, found {declarations.length}")

private def predicate (trait : Resolved.DeclarationId) (subject : TypeSystem.Ty)
    (arguments : List TypeSystem.Ty := []) : ProgramPredicate := {
  trait
  subject
  arguments
}

private def expressionNodes (source : TypedSource) : List ExpressionNode :=
  source.nodes.filterMap fun
    | .expression node => some node
    | .statement _ => none

private def statementNodes (source : TypedSource) : List StatementNode :=
  source.nodes.filterMap fun
    | .expression _ => none
    | .statement node => some node

private def rootResolves (source : TypedSource) : NodeId → Bool
  | .expression id =>
      match source.lookupExpression? id with
      | some node => node.id == id
      | none => false
  | .statement id =>
      match source.lookupStatement? id with
      | some node => node.id == id
      | none => false

private def findSolved (function : CheckedFunction)
    (goal : ProgramPredicate) : IO SolvedRequirement :=
  match function.solvedRequirements.filter fun solved => solved.predicate == goal with
  | [solved] => pure solved
  | solved =>
      throw (IO.userError
        s!"expected one solved requirement for {reprStr goal}, found {solved.length}")

private def findCall (source : TypedSource)
    (declaration : Resolved.DeclarationId) : IO ExpressionNode :=
  match (expressionNodes source).filter fun node =>
      match node.form with
      | .call _ _ (.declaration instantiation) =>
          instantiation.declaration == declaration
      | _ => false with
  | [node] => pure node
  | nodes =>
      throw (IO.userError
        s!"expected one call of declaration {reprStr declaration}, found {nodes.length}")

private def testIdentityAndLookup (function : CheckedFunction) : IO Unit := do
  let source := function.typedBody
  let occurrences := source.nodes.map Node.occurrenceId
  let rootOccurrences := source.roots.map NodeId.occurrenceId
  assertTrue (decide (source.owner = function.declaration))
    "typed body owner differs from its checked declaration"
  assertTrue (!source.roots.isEmpty && source.roots.all (rootResolves source))
    "a typed body root does not resolve through its category-safe lookup"
  assertTrue (occurrences.length == occurrences.eraseDups.length)
    "typed source reused an occurrence identity"
  assertTrue (rootOccurrences.length == rootOccurrences.eraseDups.length)
    "typed source repeated a root identity"
  assertTrue (source.nodes.all fun node =>
      decide (node.occurrenceId.owner = source.owner))
    "a typed source node belongs to a different declaration"
  assertTrue (source.roots.all fun root =>
      decide (root.occurrenceId.owner = source.owner))
    "a typed source root belongs to a different declaration"
  assertTrue (source.nodes.all fun node =>
      match node with
      | .expression expression =>
          decide (source.lookupExpression? expression.id = some expression)
      | .statement statement =>
          decide (source.lookupStatement? statement.id = some statement))
    "a typed source node could not be recovered by its stable ID"

private def shadowedBinder (source : TypedSource) (input : TypedBinder) :
    IO TypedBinder := do
  match (statementNodes source).filterMap fun node =>
      match node.form with
      | .letDecl binder (some initializer) =>
          if binder.name == "item" then some (binder, initializer) else none
      | _ => none with
  | [(binder, initializer)] =>
      assertTrue (binder.id != input.id)
        "shadowing reused the input binder identity"
      match source.lookupExpression? initializer with
      | some { form := .reference "item" (.local resolved), .. } =>
          assertTrue (resolved == input.id)
            "the shadowing initializer did not resolve to the outer input"
      | _ => throw (IO.userError
          "the shadowing initializer lost its typed local reference")
      pure binder
  | bindings => throw (IO.userError
      s!"expected one shadowing item binding, found {bindings.length}")

private def testTypedInferenceFacts (fixture : Fixture)
    (run : CheckedFunction) : IO Unit := do
  let source := run.typedBody
  let word := TypeSystem.Ty.word
  let mid ← namedType fixture.environment "Mid"
  let box ← namedType fixture.environment "Box"
  let ready ← namedTrait fixture.environment "Ready"
  let coerce ← namedTrait fixture.environment "Coerce"
  let addition ← namedTrait fixture.environment "Add"
  let numeric ← namedTrait fixture.environment "Numeric"
  let genericChoose ← namedFunctionWhere fixture.environment "choose" fun declaration =>
    !declaration.genericParameters.isEmpty
  let accept ← namedFunctionWhere fixture.environment "accept" fun _ => true
  let input ← match source.inputs.find? fun binder => binder.name == "item" with
    | some input => pure input
    | none => throw (IO.userError "run lost its item input binder")
  let boxInput ← match source.inputs.find? fun binder => binder.name == "box" with
    | some input => pure input
    | none => throw (IO.userError "run lost its box input binder")
  assertTrue (source.inputs.length == 2 &&
      decide (input.scheme = .mono word) &&
      decide (boxInput.scheme = .mono box))
    "run's input binder lost its name or type"
  let inner ← shadowedBinder source input

  match source.roots with
  | [.statement blockId, .statement useOuterId, .statement returnId] =>
      match source.lookupStatement? blockId,
          source.lookupStatement? useOuterId,
          source.lookupStatement? returnId with
      | some { form := .block nested, .. },
          some { form := .expression outerReference true, .. },
          some { form := .returnStmt (some _), .. } =>
          assertTrue (nested.length == 3 && nested.all fun id =>
              !(source.roots.contains (.statement id)))
            "nested block statements leaked into the top-level root list"
          match source.lookupExpression? outerReference with
          | some { form := .reference "item" (.local binder), .. } =>
              assertTrue (binder == input.id)
                "block scope restoration did not recover the outer item binder"
          | _ => throw (IO.userError
              "post-block item use lost its typed outer reference")
      | _, _, _ => throw (IO.userError
          "typed statement roots lost block/expression/return source order")
  | roots => throw (IO.userError
      s!"expected three ordered top-level statement roots, found {roots.length}")

  let readySolved ← findSolved run (predicate ready word)
  let firstCoercion ← findSolved run (predicate coerce word [mid])
  let secondCoercion ← findSolved run (predicate coerce mid [box])
  let addSolved ← findSolved run (predicate addition box)
  let numericSolved ← findSolved run (predicate numeric box)
  assertTrue (decide (run.predicates = [
      predicate ready word,
      predicate coerce word [mid],
      predicate coerce mid [box],
      predicate addition box,
      predicate numeric box
    ]))
    "speculative overload requirements leaked or committed requirements reordered"

  let chooseCall ← findCall source genericChoose
  match chooseCall.form with
  | .call callee [argument] (.declaration selected) =>
      assertTrue (decide (selected.declaration = genericChoose ∧
          selected.parameterSubstitution =
            [(⟨genericChoose, 0⟩, word)] ∧
          selected.type = .function word .bool ∧
          selected.predicates = [predicate ready word] ∧
          chooseCall.requirements = [readySolved.id] ∧
          chooseCall.coercions = []))
        "generic overload selection lost its closed instantiation or requirement"
      match source.lookupExpression? callee with
      | some { form := .reference "choose" (.declaration reference), .. } =>
          assertTrue (decide (reference = selected))
            "the semantic choose reference disagrees with its call resolution"
      | _ => throw (IO.userError
          "the chosen overload has no matching semantic callee reference")
      match source.lookupExpression? argument with
      | some { form := .reference "item" (.local binder), requirements, coercions, .. } =>
          assertTrue (binder == inner.id && requirements.isEmpty && coercions.isEmpty)
            "a rejected choose overload leaked coercions or requirements"
      | _ => throw (IO.userError
          "the chosen generic argument lost its shadowed local resolution")
  | _ => throw (IO.userError "the chosen generic call changed shape")

  let acceptCall ← findCall source accept
  match acceptCall.form with
  | .call _ [argument] (.declaration selected) =>
      assertTrue (selected.declaration == accept)
        "accept call retained the wrong declaration"
      match source.lookupExpression? argument with
      | some node =>
          match node.form with
          | .reference "item" (.local binder) =>
              assertTrue (decide (binder = inner.id ∧
                  node.rawType = word ∧ node.type = box ∧
                  node.hasValidCoercionPath ∧
                  node.requirements = [firstCoercion.id, secondCoercion.id] ∧
                  node.coercions = [
                    { requirement := firstCoercion.id, source := word, target := mid },
                    { requirement := secondCoercion.id, source := mid, target := box }
                  ]))
                "accept argument lost its exact Word -> Mid -> Box coercion path"
          | _ => throw (IO.userError
              "accept argument lost its shadowed local resolution")
      | none => throw (IO.userError "accept argument is absent from typed source")
  | _ => throw (IO.userError "accept call changed shape")

  match (expressionNodes source).filter fun node =>
      match node.form with
      | .binary _ .add _ => true
      | _ => false with
  | [node] =>
      assertTrue (decide (node.type = box ∧
          node.requirements = [addSolved.id]))
        "Box addition lost its Add<Box> requirement"
  | nodes => throw (IO.userError
      s!"expected one addition node, found {nodes.length}")

  match (expressionNodes source).filter fun node =>
      node.requirements.contains numericSolved.id with
  | [{ form := .literal _, type, requirements, .. }] =>
      assertTrue (decide (type = box ∧ requirements = [numericSolved.id]))
        "the Box literal lost its Numeric<Box> requirement"
  | nodes => throw (IO.userError
      s!"expected one Numeric<Box> literal owner, found {nodes.length}")

  let attached := (expressionNodes source).flatMap (·.requirements)
  let solvedIds := run.solvedRequirements.map (·.id)
  assertTrue (attached.length == attached.eraseDups.length)
    "one requirement identity is owned by multiple expression nodes"
  assertTrue (decide (attached.length = solvedIds.length) &&
      attached.all solvedIds.contains && solvedIds.all attached.contains)
    "typed expression requirement ownership and solved requirements diverged"

private def testIndirectArgumentBundleCoercion : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function apply(f: function(Box) returns (Word), value: Word) returns (Word) {",
    "  return f(value);",
    "}"
  ])
  let apply ← checkedNamed fixture "apply"
  let box ← namedType fixture.environment "Box"
  let coerce ← namedTrait fixture.environment "Coerce"
  let solved ← findSolved apply (predicate coerce .word [box])
  match (expressionNodes apply.typedBody).filter fun node =>
      match node.form with
      | .call _ _ (.indirect _) => true
      | _ => false with
  | [{ type, form := .call _ [_] (.indirect metadata), requirements,
        coercions, .. }] =>
      assertTrue (decide (type = .word ∧ requirements = [solved.id] ∧
          coercions = [] ∧
          metadata.argumentTypeBeforeCoercion = .word ∧
          metadata.argumentTypeAfterCoercion = box ∧
          metadata.argumentCoercions = [{
            requirement := solved.id
            source := .word
            target := box
          }] ∧ metadata.hasValidArgumentCoercionPath))
        "an indirect argument-bundle coercion leaked into the call output path"
  | calls => throw (IO.userError
      s!"expected one indirect call with bundle metadata, found {calls.length}")

/-- Check that the real source-inference traversal produces a complete,
occurrence-addressed semantic carrier without leaking speculative candidates. -/
def testSourceTypedIRInference : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Coerce<From, To> {}",
    "trait Add<T> {}",
    "trait Numeric<T> {}",
    "enum Mid { Only }",
    "enum Box { Only }",
    "enum Flag { Only }",
    "impl Ready<Word> {}",
    "impl Coerce<Word, Mid> {}",
    "impl Coerce<Mid, Box> {}",
    "impl Add<Box> {}",
    "impl Numeric<Box> {}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Flag) returns (Bool) { return true; }",
    "function choose<T>(value: T) returns (Bool) where T: Ready {",
    "  return true;",
    "}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function run(item: Word, box: Box) returns (Box) {",
    "  {",
    "    let item = item;",
    "    choose(item);",
    "    accept(item);",
    "  }",
    "  item;",
    "  return box + 1;",
    "}"
  ])
  let run ← checkedNamed fixture "run"
  testIdentityAndLookup run
  testTypedInferenceFacts fixture run
  testIndirectArgumentBundleCoercion

end Tests.SourceTypedIRInference
