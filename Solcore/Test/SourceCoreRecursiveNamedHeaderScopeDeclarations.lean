import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The actual Header supplies initial lexical declarations to accepted read
and expression certificates. Source typing and ordinary syntax stay explicit;
no native payload is used to invent a source scheme or successful lookup. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedHeaderScopeDeclarations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts
open RecursiveNamedHeaderScopeDeclarations

section ActualHeader
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program} (header : Header prepared values ambient.definitions program)

/-- The emitted read's actual root declaration is independently present in the
same source context, including its complete raw scheme. -/
theorem accepted_read {fuel : Nat} {id : ExpressionId} {reason : Word} {code : Expr}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values header.function.source
      (bodyScope header) id reason = .ok code) :
    ∃ certificate : CompatibleExpressionReads.Certificate fuel values header.function.source (bodyScope header) id reason code,
      Resolved.LocalScope.Lookup header.context.locals certificate.binder certificate.declared.scheme := by
  obtain ⟨certificate⟩ := CompatibleExpressionReads.of_accepted accepted
  exact ⟨certificate, header_scope header _ _ _ _ certificate.slot certificate.declaration⟩

/-- Initial scope declarations are internal to this actual compiler consumer;
ordinary syntax, policy identity and independent source typing remain inputs. -/
theorem accepted_scalar {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel fuel : Nat}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (policyFor : CompatibleExpressionConditionals.PolicyFor policy compilation readFuel values
      header.function.source (bodyScope header) header.reasonAt)
    (coercions : ∀ child original, CompatibleExpressionConditionals.Syntax header.function.source child →
      header.function.source.lookupExpression? child = some original → original.coercions = [])
    (syntaxTree : CompatibleExpressionConditionals.Syntax header.function.source id)
    (found : header.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType header.function.source header.context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation header.function.source
      (bodyScope header) id header.reasonAt = .ok lowered) :
    CompatibleExpressionConditionals.Tree readFuel values header.function.source header.context
      compilation.solvedRequirements header.reasonAt (bodyScope header) id lowered :=
  CompatibleExpressionConditionals.tree_of_functions header.unique (header_scope header)
    policyFor coercions syntaxTree found typed accepted

/-- Deriving declarations does not replace the real residual context. -/
theorem actual_context : header.context.residualTypeVariables = true ∧
    CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context :=
  ⟨RecursiveNamedSourceContextFacts.header_residual header, header_scope header⟩
end ActualHeader

section Boundaries
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"header_scope", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder :=
  {id := ⟨owner, index⟩, name := "same", scheme := .mono type}
private def first := binder 0 (.comptime .word)
private def second := binder 1 .bool
private def source : TypedSource := {owner, inputs := [first, second], roots := [], nodes := []}

/-- Real lookup retains staging and all metadata, not its erased native type. -/
theorem raw_input_identity (declared : TypedBinder)
    (accepted : SourceCoreDataPlaces.rootBinder source first.id = .ok declared) : declared = first :=
  input_identifies (by simp [source]) accepted

theorem same_name_ordered_slots :
    SourceCoreDataPlaces.rootBinder source first.id = .ok first ∧
    SourceCoreDataPlaces.rootBinder source second.id = .ok second ∧
    SourceCoreLocalCell.lookup? [(second.id, Core.Ty.word), (first.id, Core.Ty.bool)] first.id = some (1, .bool) ∧
    SourceCoreLocalCell.lookup? [(second.id, Core.Ty.word), (first.id, Core.Ty.bool)] second.id = some (0, .word) := by
  cbv

/-- Input membership alone does not promise the compiler's singleton lookup. -/
theorem duplicate_input_rejected :
    ∀ declared, SourceCoreDataPlaces.rootBinder {source with inputs := [first, first]} first.id ≠ .ok declared := by
  intro declared accepted
  cases accepted

/-- Even a scoped slot cannot authenticate a missing source declaration. -/
theorem missing_input_rejected :
    SourceCoreLocalCell.lookup? [(first.id, Core.Ty.word)] first.id = some (0, .word) ∧
    ∀ declared, SourceCoreDataPlaces.rootBinder {source with inputs := []} first.id ≠ .ok declared := by
  constructor
  · rfl
  · intro declared accepted; cases accepted
end Boundaries

private def content : String := String.intercalate "\n" [
  "function pick(first: Word, gate: Bool, last: Word) returns (Word) { if (gate) { return first; } else { return last; } }",
  "function second<A, B>(first: A, last: B) returns (B) { return last; }",
  "function shadow(value: Word) returns (Word) { { let value = 13; } return value; }",
  "function fail(first: Word, gate: Bool) returns (Word) { let missing: Word; return missing; }",
  "function empty() {}",
  "function rootPick() returns (Word) { return pick(7, false, 11); }",
  "function rootGeneric() returns (Bool) { return second(9, true); }",
  "function rootReverse() returns (Word) { return second(false, 17); }",
  "function rootShadow() returns (Word) { return shadow(19); }",
  "function rootFault() returns (Word) { return fail(23, true); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word n)

/-- Audit actual full compiler inputs and scopes without asserting a source
Header or source typing certificate from these runtime comparisons. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut sizes : List Nat := []
  let mut generics : List (List TypeSystem.Ty) := []
  let mut shadowed := false
  for named in compiled.indexed.base.functions do
    let selected ← get "header scope selected specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "header scope full selected record changed"
    let source := selected.function.typedBody
    require (reprStr source.inputs == reprStr (named.inputs.map Prod.fst))
      "header scope source inputs differ from actual prepared binders"
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    for (binding, index) in named.inputs.reverse.zipIdx do
      let declared ← get "header scope actual rootBinder" (SourceCoreDataPlaces.rootBinder source binding.1.id)
      require (reprStr declared == reprStr binding.1) "header scope raw full binder changed"
      require (SourceCoreLocalCell.lookup? scope binding.1.id == some (index, binding.2))
        "header scope reversed input order or native payload changed"
      require (binding.1.id.owner == source.owner) "header scope input owner changed"
      let projected ← get "header scope independent native projection" (compiled.compatible.checked.catalog.project declared.scheme.body)
      require (projected == binding.2) "header scope actual input projection changed"
    for input in source.inputs do
      for declared in SourceCoreDataPlaces.declaredBinders source do
        if declared.name == input.name && declared.id != input.id then
          shadowed := true
          let actual ← get "header scope shadowed binder" (SourceCoreDataPlaces.rootBinder source declared.id)
          require (reprStr actual == reprStr declared) "header scope same-name shadow changed source ID"
    sizes := sizes ++ [named.inputs.length]
    if !selected.parameterSubstitution.isEmpty then
      generics := generics ++ [named.inputs.map (fun binding => binding.1.scheme.body)]
  require (sizes.contains 0 && sizes.contains 1 && sizes.contains 2 && sizes.contains 3)
    "header scope actual arity coverage changed"
  require (generics.contains [.word, .bool] && generics.contains [.bool, .word])
    "header scope generic raw order changed"
  require shadowed "header scope same-name distinct binders not exercised"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"header scope full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "header scope declarations" content
    ["empty", "rootPick", "rootGeneric", "rootReverse", "rootShadow", "rootFault"]
  inspect compiled
  let faultBinder ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "header scope fault binder not unique")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("empty", .unit, []),
    ("rootPick", word 11, [(.word, some (word 7)), (.bool, some (.bool false)), (.word, some (word 11))]),
    ("rootGeneric", .bool true, [(.word, some (word 9)), (.bool, some (.bool true))]),
    ("rootReverse", word 17, [(.bool, some (.bool false)), (.word, some (word 17))]),
    ("rootShadow", word 19, [(.word, some (word 19)), (.word, some (word 13))])]
  for budget in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] budget
      let finished ← get "header scope native resume" (started.resume 300000)
      match finished.observation with
      | .done actual state =>
        require (reprStr actual == reprStr expected) "header scope completed value changed"
        cells state heap
      | other => throw (IO.userError s!"header scope expected completion: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "rootFault" [] budget
    let finished ← get "header scope fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == faultBinder) "header scope wrong first source fault"
      cells state [(.word, some (word 23)), (.bool, some (.bool true)), (.word, none)]
    | other => throw (IO.userError s!"header scope expected source fault: {reprStr other}")
  IO.println "header scope declarations: actual ordered raw inputs, shadowed IDs, 6 roots/4 budgets/full heaps/resume GREEN"

end Tests.SourceCoreRecursiveNamedHeaderScopeDeclarations
