import Solcore.SourceSemantics.SourceCompiledPrivateBlockDescent

/-! Conditions are evaluated by the actual checker before entering a branch
or loop body. Their scope-preserving results carry every active privacy invariant. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : Selected compiled row fuel}

theorem enter_while_body (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {body : Syntax.Block} (form : source.value = .whileLoop condition body) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 } := by
  obtain ⟨occurrence⟩ := block.position checked position
  have occurrenceBelow := occurrence.entryNodesBelow
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, bodyResult, testAccepted, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_whileLoop_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken
        testProperties.1.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 })
        testProperties.2.1 (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) expectedAtTest bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      have closed : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow 0 := by
        intro type member
        cases Option.some.inj member
        simp [Ty.VariablesBelow,Ty.freeVariables,Ty.bool]
      have binders : occurrence.result.state.localBinders ⊆ bodyResult.state.localBinders := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed
        rw [same]
        exact inferStatementsFuel_binders_subset (initial := testState) bodyAccepted
      have requirements : occurrence.result.state.requirements = bodyResult.state.requirements :=
        congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
      refine ⟨{
        checkingFuel := childFuel,
        inferenceContext := { block.inferenceContext with loopDepth := block.inferenceContext.loopDepth + 1 },
        sources := body.value, expected := block.expected, entry := testState, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := testProperties.2.1,
        nodesBelow := ?_, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained),
        entryWellFormed := (Detail.inferExprFuel_direct_progress testAccepted).wellFormed occurrence.entryWellFormed,
        entryTemplates := (show LiveTemplatesBacked occurrence.entry.allocateStatementId.2 from occurrence.entryTemplates.congr rfl rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        entryOrigins := (occurrence.entryOrigins.congr_localBinders (final := occurrence.entry.allocateStatementId.2) rfl).inferExprFuel testAccepted,
        entryPrivate := (show ActiveQuantifiersPrivate occurrence.entry.allocateStatementId.2 from occurrence.entryPrivate.congr rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          occurrence.entryWellFormed occurrence.entryBound (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked)
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) closed testAccepted,
        entryBound := activeQuantifiersBelowNext_inferExprFuel (initial := occurrence.entry.allocateStatementId.2) occurrence.entryBound occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        expectedClosed := block.expectedClosed,
        retainedSource := ⟨block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
          (congrArg (fun result : Detail.StatementResult => result.state.owner) completed)),
          nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩,
        privacy := block.after_unchanged_occurrence occurrence unchanged binders requirements
      }, rfl, rfl⟩
      exact (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)


theorem enter_if_without_else (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {condition : Syntax.Expr} {body : Syntax.Block} (form : source.value = .ifThen condition body none) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have occurrenceBelow := occurrence.entryNodesBelow
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨test, testState, bodyResult, testAccepted, bodyAccepted, completed, _⟩ :=
        SourceInferenceSoundness.inferStatementFuel_success_ifWithoutElse_facts form rfl accepted
      have testProperties := Detail.inferExprFuel_inferenceProperties occurrence.ready.allocateStatementId
        (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
        (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) testAccepted
      have expectedAtTest := (block.expectedBelow.weaken occurrence.before.next_le).weaken
        testProperties.1.next_le
      have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
        (context := block.inferenceContext)
        testProperties.2.1 (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) expectedAtTest bodyAccepted
      have unchanged : occurrence.result.state.inference = bodyResult.state.inference :=
        congrArg (fun result : Detail.StatementResult => result.state.inference) completed
      have nodes : bodyResult.state.nodes <+: occurrence.result.state.nodes := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.nodes) completed
        rw [same]
        exact List.prefix_append _ _
      have closed : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow 0 := by
        intro type member
        cases Option.some.inj member
        simp [Ty.VariablesBelow,Ty.freeVariables,Ty.bool]
      have binders : occurrence.result.state.localBinders ⊆ bodyResult.state.localBinders := by
        have same := congrArg (fun result : Detail.StatementResult => result.state.localBinders) completed
        rw [same]
        exact inferStatementsFuel_binders_subset (initial := testState) bodyAccepted
      have requirements : occurrence.result.state.requirements = bodyResult.state.requirements :=
        congrArg (fun result : Detail.StatementResult => result.state.requirements) completed
      refine ⟨{
        checkingFuel := childFuel,
        inferenceContext := block.inferenceContext,
        sources := body.value, expected := block.expected, entry := testState, result := bodyResult,
        signatures := block.signatures, accepted := bodyAccepted, ready := testProperties.2.1,
        nodesBelow := ?_, expectedBelow := expectedAtTest,
        continuation := (State.InferenceProgress.of_inference_eq bodyProperties.2.1.solved unchanged).trans
          (occurrence.continuation.trans block.continuation),
        retained := nodes.trans (occurrence.retained.trans block.retained),
        entryWellFormed := (Detail.inferExprFuel_direct_progress testAccepted).wellFormed occurrence.entryWellFormed,
        entryTemplates := (show LiveTemplatesBacked occurrence.entry.allocateStatementId.2 from occurrence.entryTemplates.congr rfl rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        entryOrigins := (occurrence.entryOrigins.congr_localBinders (final := occurrence.entry.allocateStatementId.2) rfl).inferExprFuel testAccepted,
        entryPrivate := (show ActiveQuantifiersPrivate occurrence.entry.allocateStatementId.2 from occurrence.entryPrivate.congr rfl rfl).inferExprFuel occurrence.ready.allocateStatementId
          occurrence.entryWellFormed occurrence.entryBound (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked)
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked) closed testAccepted,
        entryBound := activeQuantifiersBelowNext_inferExprFuel (initial := occurrence.entry.allocateStatementId.2) occurrence.entryBound occurrence.ready.allocateStatementId
          (block.toBlockContinuation.formation checked) (block.toBlockContinuation.canonical checked)
          (fun type member => (closed type member).weaken (Nat.zero_le _)) testAccepted,
        expectedClosed := block.expectedClosed,
        retainedSource := ⟨block.retainedSource.owner_eq.trans (occurrence.resultOwner.trans
          (congrArg (fun result : Detail.StatementResult => result.state.owner) completed)),
          nodes.trans (occurrence.retained.trans block.retainedSource.nodes_prefix)⟩,
        privacy := block.after_unchanged_occurrence occurrence unchanged binders requirements
      }, rfl, rfl⟩
      exact (Detail.inferExprFuel_occurrenceBoundExtends testAccepted).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrenceBelow)


end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
