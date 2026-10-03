import Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

/-! Receipts from the actual numeric validator retain the exact selected row
and its premise-free builtin implementation. Only that implementation row is
consumed from the complete runtime ledger. Assumption and template rows remain
present; this module does not infer ordinary validity of the complete ledger. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
open Frontend SourceInference SourceCoreElaboration

/-- Actual singleton selection, full predicate and full retained evidence.
The complete input ledger is retained, including unrelated and unused rows. -/
def Selected (solved : List SolvedRequirement) (resolution : IntegerLiteralResolution)
    (implementation : ProgramImplId) : Prop :=
  ∃ row, solved.filter (fun row => decide (row.id = resolution.requirement)) = [row] ∧
    row.predicate = resolution.predicate ∧
    row.evidence = .implementation (.byImpl resolution.predicate implementation [])

/-- Successful Word validation authenticates the implementation and its empty
premise spine in addition to the existing literal metadata certificate. -/
theorem word {solved : List SolvedRequirement} {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node source resolution = .ok validated) :
    Selected solved resolution (.builtin .intWord) := by
  have metadata := validateWordIntegerLiteral_sound accepted
  simp only [validateWordIntegerLiteral, metadata.coercions, List.isEmpty_nil, ↓reduceIte] at accepted
  unfold validateWordIntegerLiteralWith at accepted
  simp only [pure, Except.pure, bind, Except.bind] at accepted
  split at accepted
  · cases accepted
  · rename_i value checked
    change (if resolution.targetType != node.type then _ else _) = Except.ok value at checked
    split at checked
    · cases checked
    · split at checked
      · cases checked
      · cases decoded : numericLiteralValue? source with
        | none => simp only [decoded, bind, Except.bind] at checked; cases checked
        | some number =>
          simp only [decoded, pure, Except.pure, bind, Except.bind] at checked
          split at checked
          · cases checked
          · simp only [metadata.targetType] at checked
            change (do let row ← (_ : Except SourceCoreElaboration.Error SolvedRequirement); _) = Except.ok value at checked
            simp only [bind, Except.bind] at checked
            split at checked
            · cases checked
            · rename_i row selected
              change (match solved.filter (fun row => decide (row.id = resolution.requirement)) with
                | [] => _ | [row] => pure row | rest => _) = Except.ok row at selected
              split at selected
              · cases selected
              · rename_i candidate singleton
                cases selected
                split at checked
                · cases checked
                · rename_i predicate
                  split at checked
                  · cases checked
                  · rename_i goal
                    split at checked
                    · cases checked
                    · rename_i actualGoal implementation premises evidence
                      split at checked
                      · cases checked
                      · rename_i implementationEq
                        split at checked
                        · cases checked
                        · rename_i empty
                          have implementationSame : implementation = .builtin .intWord := by
                            simpa [bne_iff_ne] using implementationEq
                          have premisesEmpty : premises = [] := by
                            simpa using empty
                          have predicateSame : row.predicate = resolution.predicate := by
                            simpa [bne_iff_ne] using predicate
                          have goalSame : actualGoal = resolution.predicate := by
                            simpa [evidence, PredicateEvidence.goal,
                              bne_iff_ne] using goal
                          refine ⟨row, singleton, predicateSame, ?_⟩
                          simpa only [implementationSame, premisesEmpty, goalSame] using evidence
              · cases selected

/-- Native Integer validation retains the same exact-row boundary, with the
Integer implementation and no premises. -/
theorem integer {solved : List SolvedRequirement} {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : NativeIntegerLiteral}
    (accepted : validateNativeIntegerLiteral solved node source resolution = .ok validated) :
    Selected solved resolution (.builtin .intInteger) := by
  have metadata := validateNativeIntegerLiteral_sound accepted
  simp only [validateNativeIntegerLiteral, metadata.coercions, List.isEmpty_nil, ↓reduceIte] at accepted
  simp only [pure, Except.pure, bind, Except.bind] at accepted
  split at accepted
  · cases accepted
  · rename_i value checked
    change (if resolution.targetType != node.type then _ else _) = Except.ok value at checked
    split at checked
    · cases checked
    · split at checked
      · cases checked
      · cases decoded : numericLiteralValue? source with
        | none => simp only [decoded, bind, Except.bind] at checked; cases checked
        | some number =>
          simp only [decoded, pure, Except.pure, bind, Except.bind] at checked
          split at checked
          · cases checked
          · simp only [metadata.targetType] at checked
            change (do let row ← (_ : Except SourceCoreElaboration.Error SolvedRequirement); _) = Except.ok value at checked
            simp only [bind, Except.bind] at checked
            split at checked
            · cases checked
            · rename_i row selected
              change (match solved.filter (fun row => decide (row.id = resolution.requirement)) with
                | [] => _ | [row] => pure row | rest => _) = Except.ok row at selected
              split at selected
              · cases selected
              · rename_i candidate singleton
                cases selected
                split at checked
                · cases checked
                · rename_i predicate
                  split at checked
                  · cases checked
                  · rename_i goal
                    split at checked
                    · cases checked
                    · rename_i actualGoal implementation premises evidence
                      split at checked
                      · cases checked
                      · rename_i implementationEq
                        split at checked
                        · cases checked
                        · rename_i empty
                          have implementationSame : implementation = .builtin .intInteger := by
                            simpa [bne_iff_ne] using implementationEq
                          have premisesEmpty : premises = [] := by
                            simpa using empty
                          have predicateSame : row.predicate = resolution.predicate := by
                            simpa [bne_iff_ne] using predicate
                          have goalSame : actualGoal = resolution.predicate := by
                            simpa [evidence, PredicateEvidence.goal,
                              bne_iff_ne] using goal
                          refine ⟨row, singleton, predicateSame, ?_⟩
                          simpa only [implementationSame, premisesEmpty, goalSame] using evidence
              · cases selected


namespace Selected
variable {solved : List SolvedRequirement} {resolution : IntegerLiteralResolution}
  {implementation : ProgramImplId} {context : Context}

/-- Runtime validity is consumed only at the implementation row authenticated
by the validator. Other rows and the complete ledger stay unchanged. -/
theorem proves (selected : Selected solved resolution implementation)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) :
    RequirementProves context resolution.requirement resolution.predicate := by
  obtain ⟨row, singleton, predicate, evidence⟩ := selected
  have member : row ∈ solved.filter (fun row => decide (row.id = resolution.requirement)) := by
    rw [singleton]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have contains : ContainsRequirement context resolution.requirement row :=
    ⟨sameLedger ▸ member, of_decide_eq_true identity⟩
  exact ⟨row, contains, predicate, runtime.implementationEntries row _ contains.1 evidence⟩

/-- A premise-free selected implementation closes in every dictionary. No
coverage or validity of unrelated dictionary entries is assumed. -/
theorem produces (selected : Selected solved resolution implementation)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (environment : Dynamic.EvidenceEnvironment) :
    Dynamic.RequirementProducesEvidence context environment resolution.requirement resolution.predicate
      (.implementation resolution.predicate implementation []) := by
  obtain ⟨row, singleton, predicate, evidence⟩ := selected
  have member : row ∈ solved.filter (fun row => decide (row.id = resolution.requirement)) := by
    rw [singleton]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have contains : ContainsRequirement context resolution.requirement row :=
    ⟨sameLedger ▸ member, of_decide_eq_true identity⟩
  have valid := runtime.implementationEntries row _ contains.1 evidence
  have represents : PredicateEvidenceRepresents row.evidence
      (.implementation resolution.predicate implementation []) := by
    rw [evidence]; exact .implementation (.byImpl .nil)
  have closed : EvidenceValid [] context.signatures.resolutionRules resolution.predicate
      (.implementation resolution.predicate implementation []) := by
    cases valid with
    | intro retained =>
      cases retained with
      | intro represented proof =>
        have same := represented.functional represents
        subst same
        rw [predicate] at proof
        cases proof with
        | implementation ruleMember idEq head premises =>
          cases premises
          exact .implementation ruleMember idEq head .nil
  exact .intro contains predicate represents valid (.implementation .nil) closed

/-- The actual selected numeric requirement cannot take a source requirement
fault branch, even if unrelated assumptions are not covered. -/
theorem safe (selected : Selected solved resolution implementation)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (environment : Dynamic.EvidenceEnvironment) :
    ¬ Dynamic.RequirementUnavailable context environment resolution.requirement :=
  (produces selected sameLedger runtime environment).excludes_unavailable runtime.idsUnique
end Selected

/-- The accepted Word literal has its independent source construction using
only the complete runtime ledger and its actual selected implementation. -/
theorem word_constructs {solved : List SolvedRequirement} {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : WordIntegerLiteral} {context : Context}
    (accepted : validateWordIntegerLiteral solved node source resolution = .ok validated)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) :
    Dynamic.ResolvedIntegerLiteralConstructs context source resolution (.word validated.value) := by
  have metadata := validateWordIntegerLiteral_sound accepted
  have evidence := (word accepted).proves sameLedger runtime
  rw [metadata.value]
  cases resolution with
  | mk raw target requirement =>
    have targetEq := metadata.targetType
    dsimp only at targetEq
    subst target
    exact .word metadata.meaning evidence

/-- Integer construction keeps its unbounded signed native value and exact
requirement identity. It does not require ordinary validity of unused rows. -/
theorem integer_constructs {solved : List SolvedRequirement} {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : NativeIntegerLiteral} {context : Context}
    (accepted : validateNativeIntegerLiteral solved node source resolution = .ok validated)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) :
    Dynamic.ResolvedIntegerLiteralConstructs context source resolution (.integer validated.value) := by
  have metadata := validateNativeIntegerLiteral_sound accepted
  have evidence := (integer accepted).proves sameLedger runtime
  rw [metadata.value]
  cases resolution with
  | mk raw target requirement =>
    have targetEq := metadata.targetType
    dsimp only at targetEq
    subst target
    exact .integer metadata.meaning evidence

/-- The raw independent source form follows from actual Word acceptance.
Its requirement and output-path lists are the original node's lists. -/
theorem word_raw {solved : List SolvedRequirement} {node : ExpressionNode}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : WordIntegerLiteral} {context : Context}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    (form : node.form = .integerLiteral literal resolution)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.word validated.value) heap := by
  have metadata := validateWordIntegerLiteral_sound accepted
  rw [form, metadata.requirements, metadata.coercions]
  exact .integerLiteral rfl (word_constructs accepted sameLedger runtime)

/-- Integer raw semantics retains the same full ledger and arbitrary evidence
rather than using an ordinary-context or coverage callback. -/
theorem integer_raw {solved : List SolvedRequirement} {node : ExpressionNode}
    {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : NativeIntegerLiteral} {context : Context}
    (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated)
    (form : node.form = .integerLiteral literal resolution)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.integer validated.value) heap := by
  have metadata := validateNativeIntegerLiteral_sound accepted
  rw [form, metadata.requirements, metadata.coercions]
  exact .integerLiteral rfl (integer_constructs accepted sameLedger runtime)

end Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
