import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The production compiler success supplies the existing Calls.Tree. Formal
consumers retain the actual inventory, ordered instantiation, independent source
judgments and admission filter; no runtime meaning occurs in these receipts.
Whole source Syntax, scopes and unrestricted compiler admission remain separate
obligations. Runtime audits actual contextual child code and ordered full global
rows, then checks source heap effects and resumed success/failure. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedStaticExtraction
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup RecursiveNamedCatalog
open RecursiveNamedCallSelectionCertificates RecursiveNamedExpressionCompilerCertificates
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
#check_failure SourceTypedRuntime.run
#check_failure RecursiveNamedExpressionCompilerCertificates.BodyMeaning
section Formal
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

theorem actual_contextual_tree
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual admission coverage sourceTypes order ordinary callerSelected callerClosed
    unique closed residual declarations sourceSignatures allowed found typed readPolicy lowerPolicy leafPolicy accepted

/-- Full ordered source metadata follows from actual selected records, not
from agreement of native signatures or specialization keys alone. -/
theorem actual_selected_header {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation} {index : Nat}
    {signature : SourceCoreCalls.Signature}
    (coverage : Coverage headers compilation) (ordered : Ordered compilation.plan instantiation)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature)) :
    ∃ header, header ∈ headers ∧ header.slot = index ∧ header.named.signature = signature ∧
      instantiation = header.instantiation ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok header.named.specialized :=
  selected coverage ordered accepted
end Formal

theorem ordered_children_keep_duplicates (callee first second : ExpressionId) (instantiation : DeclarationInstantiation) :
    evaluationChildren (.call callee [first, second, first] (.declaration instantiation)) = [first, second, first] := rfl

theorem unsupported_product_arity (first second third : ExpressionId) :
    ¬ compositionForm (.tuple [first, second, third]) := by simp [compositionForm]

theorem indirect_calls_are_outside_admission (callee : ExpressionId) (arguments : List ExpressionId)
    (metadata : IndirectCallResolution) : ¬ compositionForm (.call callee arguments (.indirect metadata)) := by
  simp [compositionForm]

private def content : String := String.intercalate "\n" [
  "enum Box { Box(Bool) }",
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { return flag; }",
  "function pair<A, B>(a: A, b: B) returns (A) { return a; }",
  "function take(a: Word, b: Word) returns (Word) { return a - b; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function ordered() returns (Word) { return pair(side(7), truth(true)); }",
  "function duplicate() returns (Word) { return take(side(7), side(7)); }",
  "function grouped() returns (integer) { return ((integerSub(wordToInteger(side(7)), wordToInteger(side(9))))); }",
  "function choose() returns (integer) { return truth(true) ? integerAdd(wordToInteger(side(7)), wordToInteger(side(9))) : wordToInteger(fail()); }",
  "function boxed() returns (Box) { return Box(truth(integerEq(7, 7))); }",
  "function paired() returns ((Bool, Bool)) { return (truth(integerEq(7, 7)), truth(integerLt(7, 7))); }",
  "function indexed(m: mapping(Bool => Word)) returns (Word) { return m[truth(true)]; }",
  "function unary() returns (Bool) { return !truth(false); }",
  "function skip() returns (Bool) { return false && truth(integerEq(7, 7)); }",
  "function firstFault() returns (Word) { return take(fail(), side(99)); }",
  "function laterFault() returns (Word) { return take(side(7), fail()); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Re-enter the actual compiler callback using the real named source, global
inventory and parameter scope. These checks do not synthesize static source
judgments or treat runtime observation as evidence for a formal Tree. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "static extraction diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "static extraction parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut callCount := 0
  let mut genericCount := 0
  let mut formCount := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "static extraction source signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "static extraction own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      for item in source.nodes do
        match item with
        | .expression node =>
          match node.form with
          | .reference _ (.declaration _) => pure ()
          | _ =>
            let code ← get "actual contextual expression" (lower prepared.fuel source scope node.id reasonAt)
            let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
              prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
            require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
              "actual contextual expression lost native type"
            formCount := formCount + 1
            match node.form with
            | .call _ arguments (.declaration instantiation) =>
              let key ← get "actual static instantiation target" (SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation)
              let specialized ← get "actual full static record" (SourceCompilationPlan.exactSpecialization compilation.plan key)
              require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation specialized))
                "static extraction changed complete retained instantiation"
              require (decide (instantiation.parameterSubstitution.map Prod.fst = (specialized.parameterSubstitution.map Prod.fst).reverse))
                "static extraction changed retained domain order"
              let rows := compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key))
              let (signature, index) ← match rows with
                | [row] => pure row | _ => throw (IO.userError "static extraction actual full global row missing")
              require (compiled.indexed.base.functions[index]?.map (·.signature) == some signature)
                "static extraction header slot does not contain complete signature"
              let codes ← arguments.mapM (fun id => get "ordered actual child code" (lower (prepared.fuel - 1) source scope id reasonAt))
              require (codes.length == arguments.length && arguments.length == specialized.function.typedBody.inputs.length)
                "static extraction actual argument arity/order lost"
              require (code.expression == SourceCoreCalls.call signature
                (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason)
                "static extraction ordered argument emission changed"
              callCount := callCount + 1
              if specialized.parameterSubstitution.length == 2 then genericCount := genericCount + 1
            | _ => pure ()
        | _ => pure ()
  require (callCount >= 20 && genericCount == 1 && formCount >= 60)
    s!"static extraction fixture coverage changed: calls={callCount}, generic={genericCount}, nodes={formCount}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "static extraction public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"static extraction old heap changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"static extraction ordered source cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["ordered", "duplicate", "grouped", "choose", "boxed", "paired", "indexed", "unary", "skip", "firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named static extraction" content names
  inspect compiled names
  let box ← match compiled.sourceProgram.signatures.dataTypes with
    | [signature] => match signature.constructors with
      | [constructor] => pure (⟨constructor.id, [], constructor.payloadTypes, .nominal signature.id []⟩ : DataConstructorInstantiation)
      | _ => throw (IO.userError "static extraction constructor missing")
    | _ => throw (IO.userError "static extraction nominal signature missing")
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31)]
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", [], w 7, [(.word, some (w 7)), (.word, some (w 7)), (.bool, some (.bool true)), (.word, some (w 7)), (.bool, some (.bool true))]),
    ("duplicate", [], w 0, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7))]),
    ("grouped", [], .integer (-2), [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("choose", [], .integer 16, [(.bool, some (.bool true)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("boxed", [], .constructed box [.bool true], [(.bool, some (.bool true))]),
    ("paired", [], .product (.bool true) (.bool false), [(.bool, some (.bool true)), (.bool, some (.bool false))]),
    ("indexed", [mapping], w 31, [(.mapping .bool .word, some mapping), (.bool, some (.bool true))]),
    ("unary", [], .bool true, [(.bool, some (.bool false))]),
    ("skip", [], .bool false, [])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩]}
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← ["firstFault", "laterFault"].mapM (fun name => finish compiled name [] 300000 initial)
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"static extraction complete resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"static extraction result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"static extraction expected completion {name}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failed do
      let observed ← finish compiled name [] fuel initial
      require (reprStr observed == reprStr baseline) s!"static extraction fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        let earlier := if name == "laterFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)]) name
      | _ => throw (IO.userError "static extraction lost ordered source fault")
  IO.println "recursive named static extraction: actual contextual success, existing call Tree, full ordered instantiation/header slots, child emission, complete heap/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedStaticExtraction
