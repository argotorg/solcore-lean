import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The actual named source context retains residual variables. The new
entry consumes true-mode child certificates and derives both root scope facts
from SourceFrame and parameter installation. Cached support and assignment
native typing are internal; source admission and diagnostics stay explicit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedResidualContexts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open NativeExpressionContextSupport RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

include member definitions sameCache complete globals recipeAccepted entry in
/-- This consumer feeds the real prepared root's native proof into the single
compiler traversal, without requesting body/loop HasType at actual Γ. -/
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  RecursiveNamedCachedSupport.extract_source cached recipeAccepted
    (RecursiveNamedCachedRows.rows cached) (RecursiveNamedCachedRows.exact_cache cached) (RecursiveNamedCachedRows.ordered cached)
    member definitions sameCache complete globals entry
    diagnosticPolicy registered prefixEq factory readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy
    syntaxTree sourceSignatures declarations projection accepted

/-- The selected receipt still owns the diagnostic obligations. -/
theorem actual_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩

/-- This is a source structural fact, independent of native code or execution. -/
theorem actual_header_context :
    header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header

theorem old_false_excluded : header.context.residualTypeVariables ≠ false :=
  RecursiveNamedSourceContextFacts.header_not_false header

section Boundary
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {policy : SourceCoreLoops.Policy} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {sourceOwner : Resolved.DeclarationId}

/-- A real empty emitted flow is extracted in the unchanged declaration
context. Its false expression admission is vacuous because it has no children. -/
theorem empty_declaration_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope
      (declarationContext values.checked.signatures sourceOwner [] [] [])) :
    GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun _ _ _ _ => False) (declarationContext values.checked.signatures sourceOwner [] [] []) scope
      true [] .unit .unit (LocalLoop.fallthrough .unit) := by
  exact GenericLexicalStatements.tree_of_flow_with_residual true readPolicy binderPolicy allocationPolicy
    (expressionSyntax := fun _ => False)
    (by intro context closed residual signatures scope fuel id node lowered declarations impossible; cases impossible)
    (.nil (.inr rfl)) rfl rfl rfl declarations (fuel := 0) (reasonAt := fun _ => Word.ofNatModulo 0)
    (selfReason := Word.ofNatModulo 0) rfl rfl
end Boundary

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def flexible : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables

/-- A true residual scope permits used metavariables; it does not prove closed
well-formedness. Expression Valid/Closed receipts remain separate work. -/
theorem residual_admissibility_boundary :
    TypeAdmissible flexible (.variable ⟨0⟩) ∧ ¬ TypeWellFormed flexible (.variable ⟨0⟩) := by
  refine ⟨⟨⟨by simp [flexible, Context.withResidualTypeVariables, Context.ofSignatures, signatures],
    by simp [flexible, Context.withResidualTypeVariables, Context.ofSignatures, signatures]⟩,
    .variable (by simp [admissibleTypeVariables, flexible, Context.withResidualTypeVariables, Context.ofSignatures, TypeSystem.Ty.freeVariables])⟩, ?_⟩
  intro typed
  have impossible := TypeWellScoped.variable_iff.mp typed.typeWellScoped
  cases impossible

private def content : String := String.intercalate "\n" [
  "function step(n: Word) returns (Word) { return n + 1; }",
  "function self(n: Word) returns (Word) { if (n == 0) { return 0; } return self(n - 1); }",
  "function loop(n: Word) returns (Word) { let total = 0; for (let i = 0; i < n; i += 1) { total += step(i); } return total; }",
  "function down(n: Word) returns (Word) { while (n != 0) { n -= 1; } return n; }",
  "function assign(m: mapping(Bool => Word)) returns (Word) { m[true] = step(6); return m[true]; }",
  "function fail() returns (Word) { let saved = 17; let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  require (compiled.indexed.base.functions.length > 1) "residual actual named inventory missing"
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let context := declarationContext compiled.sourceProgram.signatures named.specialized.key.declaration []
      named.specialized.assumptions named.specialized.function.solvedRequirements
    require context.residualTypeVariables "actual declaration scope lost residual variables"
    require context.typeVariables.isEmpty "actual declaration acquired lexical inference variables"
    require (named.specialized.function.typedBody.inputs.map (·.id) == named.inputs.map (·.1.id))
      "actual prepared input order changed"
    let stored ← match compiled.indexed.secondPass.closures[slot]? with
      | some stored => pure stored
      | none => throw (IO.userError "residual full cached row missing")
    match stored with
    | .lambda parameter result _ =>
      require (parameter == named.signature.parameterType && result == LanguageResult.resultType named.signature.resultType)
        "residual cached signature changed"
    | _ => throw (IO.userError "residual cache is not the emitted lambda")

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "residual source context public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"residual old cells changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"residual full ordered cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual residual source context" content
    ["self", "loop", "down", "assign", "fail", "zero"]
  inspect compiled
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91), (.bool false, w 4)]
  let updated : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 7), (.bool true, w 91), (.bool false, w 4)]
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("self", [w 2], w 0, [(.word, some (w 2)), (.word, some (w 1)), (.word, some (w 0))]),
    ("loop", [w 2], w 3, [(.word, some (w 2)), (.word, some (w 3)), (.word, some (w 2)), (.word, some (w 0)), (.word, some (w 1))]),
    ("down", [w 2], w 0, [(.word, some (w 0))]),
    ("assign", [mapping], w 7, [(.mapping .bool .word, some updated), (.word, some (w 6))]),
    ("zero", [], .unit, [])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩, ⟨.bool, some (.bool false)⟩]}
  let baselines ← tests.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← finish compiled "fail" [] 300000 initial
  for fuel in [0, 7, 43, 300000] do
    for (test, baseline) in tests.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"residual full public resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"residual result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"residual expected success {name}")
    let observed ← finish compiled "fail" [] fuel initial
    require (reprStr observed == reprStr failed) "residual first fault/resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final => cells initial final [(.word, some (w 17)), (.word, none)] "fail"
    | _ => throw (IO.userError "residual first fault lost")
  IO.println "residual contexts: actual named scopes, ordered inputs/cache signatures, loops/assignments, cells/fault/resume GREEN"


end Tests.SourceCoreRecursiveNamedResidualContexts
