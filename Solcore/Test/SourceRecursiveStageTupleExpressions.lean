import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceCoreRecursiveNamedTupleExpressions

/-! Independent ordered source tuples preserve the actual prefix heaps and
failure origin. The native audits below exercise existing compiler packing;
they do not supply a staged child or callable-body correspondence theorem. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceRecursiveStageTupleExpressions
open Solcore Frontend SourceInference SourceSemantics Dynamic Staging.Recursive

section Source
variable {program : Program} {registry : Registry} {scope origin : Scope}
  {context : SourceSemantics.Context} {environment : Environment} {before middle after : Heap}
  {id a b c d call : ExpressionId} {reason : Staging.CallGuard.Fault}

theorem empty (occurrence : Occurrence scope id (.tuple [])) :
    Expression program registry scope context environment before id (.value .unit) before :=
  .tupleValue occurrence .nil .nil

theorem singleton {value : Value} (occurrence : Occurrence scope id (.tuple [a]))
    (child : Expression program registry scope context environment before a (.value value) after) :
    Expression program registry scope context environment before id (.value value) after :=
  .tupleValue occurrence (.cons child .nil) (.singleton value)

theorem triple {next : Heap} {x y z : Value}
    (occurrence : Occurrence scope id (.tuple [a, b, c]))
    (first : Expression program registry scope context environment before a (.value x) middle)
    (second : Expression program registry scope context environment middle b (.value y) next)
    (third : Expression program registry scope context environment next c (.value z) after) :
    Expression program registry scope context environment before id (.value (.product x (.product y z))) after :=
  .tupleValue occurrence (.cons first (.cons second (.cons third .nil))) (.cons (.cons (.singleton z)))

theorem repeated_occurrences {x y : Value}
    (occurrence : Occurrence scope id (.tuple [a, a]))
    (first : Expression program registry scope context environment before a (.value x) middle)
    (second : Expression program registry scope context environment middle a (.value y) after) :
    Expression program registry scope context environment before id (.value (.product x y)) after :=
  .tupleValue occurrence (.cons first (.cons second .nil)) (.cons (.singleton y))

theorem stage_at_head {suffix : List ExpressionId}
    (occurrence : Occurrence scope id (.tuple (a :: suffix)))
    (failed : Expression program registry scope context environment before a (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.tupleFault occurrence (Expressions.headFault (ids := suffix) failed)
  exact ⟨trace, trace.stage_origin rfl⟩

theorem stage_after_prefix {value : Value} {suffix : List ExpressionId}
    (occurrence : Occurrence scope id (.tuple (a :: b :: suffix)))
    (first : Expression program registry scope context environment before a (.value value) middle)
    (failed : Expression program registry scope context environment middle b (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.tupleFault occurrence (.tailFault first (.headFault failed))
  exact ⟨trace, trace.stage_origin rfl⟩

theorem semantic_fault {elements : List ExpressionId} {fault : SemanticFault}
    (occurrence : Occurrence scope id (.tuple elements))
    (failed : Expressions program registry scope context environment before elements (.fault (.semantic fault)) after) :
    Expression program registry scope context environment before id (.fault (.semantic fault)) after ∧
      ExpressionFaults program context scope.evidence scope.source environment before id fault after := by
  have trace := Expression.tupleFault occurrence failed
  exact ⟨trace, trace.semanticFault_plain⟩

theorem values_and_erasure {elements : List ExpressionId} {values : List Value} {packed : Value}
    (occurrence : Occurrence scope id (.tuple elements))
    (children : Expressions program registry scope context environment before elements (.values values) after)
    (pack : ValuesPack values packed) :
    Expression program registry scope context environment before id (.value packed) after ∧
      ExpressionEvaluates program context scope.evidence scope.source environment before id packed after ∧
      elements.length = values.length := by
  have trace := Expression.tupleValue occurrence children pack
  exact ⟨trace, trace.value_plain, children.length⟩

/-- The existing pair constructor remains a valid independent entry. -/
theorem old_pair {x y : Value} (occurrence : Occurrence scope id (.tuple [a, b]))
    (first : Expression program registry scope context environment before a (.value x) middle)
    (second : Expression program registry scope context environment middle b (.value y) after) :
    Expression program registry scope context environment before id (.value (.product x y)) after :=
  .pair occurrence first second

theorem empty_sequence_cannot_fault {failure : Failure} :
    ¬ Expressions program registry scope context environment before [] (.fault failure) after := by
  intro impossible
  cases impossible

theorem nonempty_tuple_not_atomic {rest : List ExpressionId} : ¬ AtomicForm (.tuple (a :: rest)) := by
  intro impossible
  cases impossible

theorem required_parent_excluded {node : ExpressionNode} {elements : List ExpressionId}
    (unique : NodeOccurrencesUnique scope.source) (found : scope.source.lookupExpression? id = some node)
    (required : node.requirements ≠ []) : ¬ Occurrence scope id (.tuple elements) := by
  rintro ⟨other, contains, _, empty, _⟩
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact required empty

theorem coerced_parent_excluded {node : ExpressionNode} {elements : List ExpressionId}
    (unique : NodeOccurrencesUnique scope.source) (found : scope.source.lookupExpression? id = some node)
    (coerced : node.coercions ≠ []) : ¬ Occurrence scope id (.tuple elements) := by
  rintro ⟨other, contains, _, _, empty⟩
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact coerced empty
end Source

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content := String.intercalate "\n" [
  "function empty() { return (); }",
  "function one() returns (Word) { return (7); }",
  "function pair() returns ((Word, Bool)) { return (11, true); }",
  "function triple() returns ((Word, Bool, Word)) { return (13, false, 17); }",
  "function nested() returns (((Word, Bool, Word), Word, Bool)) { return ((19, true, 23), 29, false); }"
]

/-- The source fixture supplies exact uncoerced tuple occurrences and full
numeric ledgers. Its native audit is about the existing packer only. -/
private def actual_occurrences : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive source tuples" content
    ["empty", "one", "pair", "triple", "nested"]
  let mut counts : List Nat := []
  let mut singletons := 0
  let mut repeated := 0
  for named in compiled.indexed.base.functions do
    let selected ← get "tuple full actual specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "tuple retained full specialization changed"
    let source := selected.function.typedBody
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
    let compilation : SourceCoreFunctions.Context := {
      plan := compiled.indexed.base.plan, owner := named.signature.key,
      globals := compiled.indexed.base.globals, administrativePrefix := 0,
      solvedRequirements := selected.function.solvedRequirements, internalReason := Core.Word.zero }
    let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
      .error (.unsupportedExpression ⟨⟨source.owner, 0⟩⟩ (.tuple []))
    let reasonAt := fun (_ : ExpressionId) => Core.Word.zero
    let lower := fun (input : TypedSource) budget id =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy noBody budget compilation input [] id reasonAt
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .integerLiteral literal resolution =>
          let _ ← get "tuple actual selected numeric row"
            (SourceCoreElaboration.validateWordIntegerLiteral compilation.solvedRequirements node literal resolution)
          require (node.requirements == [resolution.requirement]) "tuple numeric child requirement changed"
        | .tuple ids =>
          require (node.requirements.isEmpty && node.coercions.isEmpty) "tuple parent is not an ordinary occurrence"
          let children ← ids.mapM (fun child => get "tuple ordered original child" (lower source 99 child))
          let actual ← get "tuple actual parent" (lower source 100 node.id)
          require (actual == SourceCoreCalls.packArguments children && children.length == ids.length)
            "tuple same ordered child vector changed"
          counts := counts ++ [ids.length]
        | .group child =>
          let childNode ← match source.lookupExpression? child with
            | some child => pure child | none => throw (IO.userError "tuple group child absent")
          for ids in [[child], [child, child, child]] do
            let retained := {source with nodes := source.nodes.map (fun item => match item with
              | .expression current => if current.id == node.id then
                  .expression {current with form := .tuple ids, type := TypeSystem.Ty.productMany (ids.map (fun _ => childNode.type)), requirements := [], coercions := []}
                else item
              | _ => item)}
            let actual ← get "retained tuple arity" (lower retained 100 node.id)
            let children ← ids.mapM (fun id => get "retained tuple ordered child" (lower retained 99 id))
            require (retained.owner == source.owner && retained.inputs == source.inputs &&
              retained.roots == source.roots) "retained tuple source fields changed"
            require (actual == SourceCoreCalls.packArguments children) "retained tuple singleton/duplicate code changed"
            if ids.length == 1 then singletons := singletons + 1 else repeated := repeated + 1
        | _ => pure ()
      | _ => pure ()
  require (counts == [3, 3, 3, 2, 0] && singletons == 1 && repeated == 1)
    s!"source tuple occurrence inventory changed {counts}/{singletons}/{repeated}"

def run : IO Unit := do
  actual_occurrences
  SourceCoreRecursiveNamedTupleExpressions.run
  IO.println "recursive source tuples: actual empty/pair/nary/nested occurrences + complete numeric ledger; retained singleton/duplicate IR; existing native ordered fault/store/resume audit GREEN"

end Tests.SourceRecursiveStageTupleExpressions
