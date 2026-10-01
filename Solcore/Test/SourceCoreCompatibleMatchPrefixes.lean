import Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix
import Solcore.Test.SourceCompilerFeatureSupport

/-! Whole actual compatible match receipt extraction and ordered source
selection, plus runtime regressions for hidden/arm allocations, no-branch
fallthrough, scrutinee fault and loop control through the common Core entry. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Tests.SourceCoreCompatibleMatchPrefixes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_match_prefixes", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "compatible_match_prefixes.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutineeId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def bound : TypedBinder := ⟨⟨owner, 1⟩, "value", .mono .unit, [], false, none⟩
private def pattern : TypedMatchPattern := {source := .binder span "value", type := .unit, resolution := .binder bound}
private def resolution : MatchResolution := ⟨scrutineeId, hidden, [⟨span, pattern, []⟩], some [], []⟩
private def source : TypedSource := {owner, inputs := [], roots := [.statement site], nodes := [
  .statement ⟨site, span, .unit, .matchWith resolution⟩,
  .expression {id := scrutineeId, span, type := .unit, form := .tuple []}]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem checkedExists : (SourceCoreCompatibleCatalog.prepare signatures 50 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 50 [.unit]).toOption.get checkedExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def expression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, .inRight .word .unit⟩
private def body : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ => .ok (LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def compiled : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
    10 source [] site resolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem accepted : SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
    10 source [] site resolution .unit reasonAt Word.zero = .ok compiled := by rfl
private theorem matchCertificate : CompatibleMatchCertificates.Certificate compilation source [] site resolution .unit Word.zero
    (fun _ _ value => value = ⟨.unit, .inRight .word .unit⟩)
    (fun _ _ code => code = LocalLoop.fallthrough .unit) compiled := by
  apply CompatibleMatchCertificates.certificate_of_lowerWithReasons (accepted := accepted)
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem contextValid : CompatiblePatternLeaves.ContextValid compilation context := {
  signatures := rfl, ledger := rfl, valid := ⟨by simp [RequirementIdsUnique, context, Context.ofSignatures],
    by intro requirement member; cases member⟩}
private theorem signatureValid : SignatureCatalogWellFormed signatures := by
  constructor <;> simp [signatures, signatureDeclarationIds]

/-- Actual compatible lowering records the complete fold, including the real
ambient checker and source binder identity; no child runtime premise is used. -/
example : CompatibleMatchSelectionPrefix.Ordinary matchCertificate :=
  CompatibleMatchSelectionPrefix.ordinary_of_source_ids matchCertificate rfl (by intro arm member binder found; rfl)

example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} (extended : SourceCoreRawMetadata.Extends values.registry registry) :
    ∃ selection, Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody selection :=
  CompatibleMatchDecision.Certificate.source_selects matchCertificate contextValid signatureValid extended
    (show source.lookupExpression? resolution.scrutinee = some {id := scrutineeId, span, type := .unit, form := .tuple []} from rfl)
    (CompatiblePayload.ValueRep.unit (functions := functions) (mapping := mapping) (world := world))

example : SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body 10 source [(hidden, .unit)]
    site resolution .unit reasonAt Word.zero = .error (.duplicateBinding hidden) := by cbv

private def noBranchResolution : MatchResolution := ⟨scrutineeId, hidden, [], none, []⟩
private def noBranchSource : TypedSource := {source with nodes := [
  .statement ⟨site, span, .unit, .matchWith noBranchResolution⟩,
  .expression {id := scrutineeId, span, type := .unit, form := .tuple []}]}
private def noBranchCode : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
    10 noBranchSource [] site noBranchResolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem noBranchCertificate : CompatibleMatchCertificates.Certificate compilation noBranchSource [] site noBranchResolution .unit Word.zero
    (fun _ _ value => value = ⟨.unit, .inRight .word .unit⟩)
    (fun _ _ code => code = LocalLoop.fallthrough .unit) noBranchCode := by
  apply CompatibleMatchCertificates.certificate_of_lowerWithReasons (accepted := show
    SourceCoreCompatibleDataMatches.lowerWithReasons compilation expression body
      10 noBranchSource [] site noBranchResolution .unit reasonAt Word.zero = .ok noBranchCode from rfl)
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm
  · intro _ _ _ _ accepted; exact Except.ok.inj accepted.symm

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function fallthrough(p: Word) returns (Word) { match (p) { case 0 { return 11; } default {} } return 17; }",
    "function fault(p: Word) returns (Word) { let hole: Word; match (hole) { case v { return v; } default { return 99; } } return p; }",
    "function nested(p: Word) returns (Word) { match ((p, (7, 11))) { case (0, (x, y)) { match ((x, y)) { case (a, b) { return a + b; } } } default { return 99; } } }",
    "function flow(stop: Word) returns (Word) { let tally: Word = 0; for (let i: Word = 0; i < stop; i = i + 1) { match (i) { case 0 { continue; } case 2 { break; } default { tally = tally + i; } } } return tally; }"]}] }

def run : IO Unit := do
  -- The checker requires exhaustive matches. Exercise the compiler's retained
  -- no-branch case using its actual accepted typed IR, then checked roots below.
  match Core.runStateful 1000 (.initial noBranchCode [] []) with
  | .done result store =>
    SourceCompilerFeatureSupport.require (result == .inRight .word (.inLeft LocalLoop.transferType (.inLeft .unit .unit)))
      "empty match changed the no-branch control value"
    SourceCompilerFeatureSupport.require (store == [.inRight .unit .unit]) "empty match changed the actual hidden allocation"
  | _ => throw (IO.userError "empty accepted typed match did not complete")
  let program ← SourceCompilerFeatureSupport.get "compatible whole match prefixes" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let fallthrough ← SourceCompilerFeatureSupport.compileNamed program "fallthrough"
  for (p, result) in [(0, 11), (1, 17)] do
    SourceCompilerFeatureSupport.require ((← fallthrough.run [w p]) == w result) "default match changed fallthrough or first arm"
    fallthrough.checkCells [w p] [(.word, some (w p)), (.word, some (w p))]
    for budget in [0, 7, 43] do fallthrough.checkResume [w p] (w result) budget
  let fault ← SourceCompilerFeatureSupport.compileNamed program "fault"
  let failed ← fault.invoke [w 3]
  match failed.outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "scrutinee fault reached the match allocation or branch")
  fault.checkCells [w 3] [(.word, some (w 3)), (.word, none)]
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  SourceCompilerFeatureSupport.require ((← nested.run [w 0]) == w 18) "nested marked matches changed lexical binder order"
  for budget in [0, 7, 43] do nested.checkResume [w 0] (w 18) budget
  let flow ← SourceCompilerFeatureSupport.compileNamed program "flow"
  SourceCompilerFeatureSupport.require ((← flow.run [w 4]) == w 1) "match failed to restore for scope or transfer break/continue"
  flow.checkCells [w 4] [(.word, some (w 4)), (.word, some (w 1)), (.word, some (w 2)),
    (.word, some (w 0)), (.word, some (w 1)), (.word, some (w 2))]
  for budget in [0, 7, 43] do flow.checkResume [w 4] (w 1) budget
  IO.println "compatible whole match prefixes: actual fold receipts, ordered selection, raw hidden heap types, no-branch/fault/control and resume GREEN"
end Tests.SourceCoreCompatibleMatchPrefixes
