import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeMatchProfiles

/-! Static consumers preserve actual accepted code, runtime literal receipts,
full ledger fields and the initial context. Whole runtime body meaning and a
weaker Header are separate units. Existing runtime runners cover this change. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup RecursiveNamedCatalog
open GenericImperativeMatch.Tree
section Actual
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree)

include valid accepted projection generated tree errors in
/-- The constructor consumes the same full body/flow acceptance and supported
expression Tree; it does not add expression or body execution hypotheses. -/
theorem actual_profile : Nonempty (RuntimeMatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :=
  ⟨RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors⟩

include accepted projection generated tree errors in
theorem actual_frame_profile (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    Nonempty (RuntimeMatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :=
  ⟨RuntimeMatchProfileFor.of_frame programTyped sameLedger accepted projection generated tree errors⟩

include valid accepted projection generated tree errors in
theorem same_flow : (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).flow = flow := rfl

include valid accepted projection generated tree errors in
theorem same_native_code : header.body = CompatibleStatements.finish header.output
    (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).flow header.fellThrough header.escaped :=
  (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).emitted

include valid accepted projection generated tree errors in
theorem same_diagnostics : CatalogSites diagnosticPolicy registry faults
    (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).tree := errors

/-- The old profile keeps its initial ordinary proof in the common record.
That proof, rather than a runtime-to-ordinary cast, reconstructs ReadyFor. -/
theorem legacy_ready
    (profile : MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    GenericImperativeMatch.Tree.ReadyFor diagnosticPolicy registry faults profile.tree :=
  profile.errors.ready profile.initialValid
end Actual

section Sites
variable {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}

theorem runtime_context (fields : MatchContextFields compilation context)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence) :
    CompatiblePatternRuntime.ContextValid compilation context := fields.runtime valid

/-- Even unused rows remain members of the actual compilation ledger. -/
theorem unused_row (fields : MatchContextFields compilation context)
    {row : SolvedRequirement} (member : row ∈ context.solvedRequirements) :
    row ∈ compilation.solvedRequirements := fields.ledger ▸ member

/-- The existing arm certificate already contains the actual literal validator
receipt, so no independent numeric-support assumption is introduced. -/
theorem repeated_arms {source : TypedSource} {site : StatementId} {scope : SourceCoreCompatibleDataMatches.Scope}
    {expected : TypeSystem.Ty} {arm : TypedMatchCase} {pattern : SourceCoreCompatibleDataMatches.Pattern}
    {body : Expr} {bodyCertificate : CompatibleMatchCertificates.BodyCertificate}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern pattern)
    (typed : HasType [] pattern.matcher pattern.functionType compilation.definitions)
    (bodyCertified : bodyCertificate (CompatibleMatchCertificates.armScope scope pattern) arm.body body) :
    CompatibleMatchCertificates.Arms compilation source site scope expected bodyCertificate
      [arm, arm] [(pattern, body), (pattern, body)] ∧
    CompatiblePatternRuntime.Certificate compilation source scope site arm.span expected arm.pattern pattern :=
  ⟨.cons certificate typed bodyCertified (.cons certificate typed bodyCertified .nil),
    CompatiblePatternRuntime.of_certificate certificate⟩
end Sites

/-- Static signature/ledger equality and runtime validity cannot recreate the
old ordinary all-row condition. The unused assumption row remains in full. -/
theorem fields_not_ordinary (compilation : SourceCoreCompatibleDataMatches.Context)
    (id : RequirementId) (predicate : ProgramPredicate) :
    let row : SolvedRequirement := ⟨id, predicate, .assumption predicate⟩
    let changed := { compilation with solvedRequirements := [row] }
    let context := (SourceSemantics.Context.ofSignatures compilation.signatures).withSolvedRequirements [row]
    MatchContextFields changed context ∧ RuntimeRequirementLedgerValid context ∧
      ¬ RequirementLedgerWellFormed context := by
  dsimp only
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · constructor
    · simp [RequirementIdsUnique, Context.withSolvedRequirements]
    · intro row evidence member actual
      have same : row = ⟨id, predicate, .assumption predicate⟩ := by
        simpa [Context.withSolvedRequirements] using member
      subst row
      cases actual
  · intro valid
    have rowValid := valid.entriesValid ⟨id, predicate, .assumption predicate⟩ (by simp [Context.withSolvedRequirements])
    cases rowValid with
    | intro retained =>
      cases retained with
      | intro represents evidence =>
        cases represents with
        | assumption =>
          cases evidence with
          | assumption member => simp only [Context.withSolvedRequirements, Context.ofSignatures, List.not_mem_nil] at member

end Tests.SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles
