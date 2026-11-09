import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins

/-!
# Compatible expressions: runtime

Numeric literal evidence and the runtime of literal, general and builtin expressions.

These results rest on `CallableSpecializationEquality`. The other expression files stay below it, so that `Callable/CallEvidence` keeps coming first in the import order of `Callable/MethodOrigins`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
/-! Atomic literal receipts retain actual numeric implementation evidence.
The old literal and ordinary-context APIs are unchanged. Runtime ledger validity
is consumed only at the selected numeric row; all unused rows stay present.
No source or native execution law is stored in this static certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionLiterals

/-- The primitive implementation is fixed by the actual compiler's numeric
target branch. Other atomic forms have no selected numeric evidence. -/
def NumericSelected (solved : List SolvedRequirement) (node : ExpressionNode) : Prop :=
  ∀ literal resolution, node.form = .integerLiteral literal resolution →
    NumericLiteralEvidenceReceipts.Selected solved resolution
      (.builtin (if node.type = .integer then .intInteger else .intWord))

/-- The ordinary literal metadata and the full actual numeric row receipt.
Neither the complete runtime ledger nor a semantic execution law is a field. -/
def Certificate (solved : List SolvedRequirement) (source : TypedSource)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧
    Literal solved node lowered.type lowered.expression ∧ NumericSelected solved node

theorem Certificate.forget {solved source id lowered}
    (receipt : Certificate solved source id lowered) :
    CompatibleExpressionLiterals.Certificate solved source id lowered := by
  obtain ⟨node, found, literal, _⟩ := receipt
  exact ⟨node, found, literal⟩

private theorem selected_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    NumericSelected context.solvedRequirements node := by
  intro literal resolution form
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
        bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals try rw [bypass] at accepted
      all_goals
        simp only [form] at accepted
        by_cases target : node.type = .integer
        · simp only [target, ↓reduceIte] at accepted ⊢
          cases validated : SourceCoreElaboration.validateNativeIntegerLiteral context.solvedRequirements node literal resolution with
          | error error => simp [validated, Except.mapError] at accepted
          | ok output => exact NumericLiteralEvidenceReceipts.integer validated
        · simp only [target, ↓reduceIte] at accepted ⊢
          cases validated : SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements node literal resolution with
          | error error => simp [validated, Except.mapError] at accepted
          | ok output => exact NumericLiteralEvidenceReceipts.word validated
    · simp [owner, bind, Except.bind] at accepted

/-- Successful actual function lowering supplies both old metadata and the
stronger selected-row receipt. The original override bypass is explicit. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : Atomic node.form) (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Certificate context.solvedRequirements source id lowered := by
  obtain ⟨other, otherFound, literal⟩ := CompatibleExpressionLiterals.of_functions found atomic unitType special readPolicy leafPolicy accepted
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  exact ⟨node, found, literal, selected_of_functions found special accepted⟩

/-- Only the authenticated row is checked against the complete runtime ledger.
No covering dictionary or ordinary validity of unused rows is required. -/
theorem NumericSelected.evidence {solved : List SolvedRequirement} {node : ExpressionNode}
    (selected : NumericSelected solved node) {context : SourceSemantics.Context}
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) (evidence : Dynamic.EvidenceEnvironment) :
    NumericEvidence context evidence node := by
  intro literal resolution form
  exact ⟨(selected literal resolution form).proves sameLedger runtime,
    (selected literal resolution form).safe sameLedger runtime evidence⟩

/-- The complete atomic family uses the shared literal preservation proof.
Its extra static evidence comes from actual numeric acceptance only. -/
theorem preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) {source : TypedSource}
    (unique : NodeOccurrencesUnique source) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  refine CompatibleExpressionLiterals.preserves_with_evidence (registry := registry) (solved := solved)
    functions program context evidence (certificate := fun _ id lowered => Certificate solved source id lowered) ?_ unique faults
  intro scope id lowered receipt
  obtain ⟨node, found, literal, selected⟩ := receipt
  exact ⟨node, found, literal, selected.evidence sameLedger runtime evidence⟩

/-- Reflection uses the same static receipt and original native completion;
no preservation law or prior independent source execution is an input. -/
theorem reflects {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) (source : TypedSource) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  refine CompatibleExpressionLiterals.reflects_with_evidence (registry := registry) (solved := solved)
    functions program context evidence source (certificate := fun _ id lowered => Certificate solved source id lowered) ?_ faults
  intro scope id lowered receipt
  obtain ⟨node, found, literal, selected⟩ := receipt
  exact ⟨node, found, literal, selected.evidence sameLedger runtime evidence⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntime
/-! General expression meaning consumes numeric receipts only at the exact
literal leaves of the existing tree. Every unused ledger row remains present.
The support is static: actual whole-root compiler extraction is a separate step.
Constructor validity, mapping comparison, source metadata and runtime entry
conditions remain independent. No dictionary coverage is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntime
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

abbrev Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionGeneral.Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
    (context := context) (solved := solved) (reasonAt := reasonAt)
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)

/-- The support preserves the exact pre-existing grammar and emitted code. -/
theorem Certificate.forget {fuel values source context solved reasonAt scope id code}
    (receipt : Certificate fuel values source context solved reasonAt scope id code) :
    CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id code :=
  receipt.choose

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful functionLeaves functionTypes sameLedger runtime unique uninitialized missing in
/-- Every independent source outcome is preserved using the complete runtime
ledger and actual selected rows at this tree's numeric leaves. -/
theorem preserves [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate fuel values source context solved reasonAt) faults :=
  CompatibleExpressionGeneral.preserves_with_literals functions extension faithful functionLeaves functionTypes
    program evidence unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults)

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing in
/-- Original native completion reconstructs an independent source outcome.
No source execution or preservation law is an input. -/
theorem reflects [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate fuel values source context solved reasonAt) faults :=
  CompatibleExpressionGeneral.reflects_with_literals functions extension faithful functionLeaves functionTypes
    program evidence uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntime
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntimeExtraction
/-! Actual Functions compilation supplies the existing General Tree and its
same-tree literal support. Only visited compiler leaves require numeric row
receipts; the original complete ledger and unused templates remain untouched.
Source typing, ordinary policy, constructor formation and runtime environment
conditions remain independent. Contextual dispatch, calls, lambdas and output
coercions are separate interfaces. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntimeExtraction
open Core Frontend SourceInference
open CompatibleExpressionGeneral

/-- The single compiler extraction retains actual numeric validator results
at every literal child. No external child certificate or execution law remains. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    CompatibleExpressionGeneralRuntime.Certificate readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  apply CompatibleExpressionGeneral.tree_of_functions_with_literals
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id code)
    ?_ unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted
  intro child childNode childFuel childCode childFound atomic unitType special readPolicy leafPolicy generated
  have receipt := CompatibleExpressionLiteralRuntime.of_functions childFound atomic unitType special readPolicy leafPolicy generated
  exact ⟨receipt.forget, receipt⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntimeExtraction
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
/-! Builtin expression meaning consumes numeric receipts only at the exact
literal leaves of the existing tree. Every unused ledger row remains present.
The support is static and follows actual accepted compiler children.
Constructor validity, mapping comparison, source metadata and runtime entry
conditions remain independent. No dictionary coverage is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

abbrev Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
    (context := context) (solved := solved) (reasonAt := reasonAt)
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)

/-- The support preserves the exact pre-existing grammar and emitted code. -/
theorem Certificate.forget {fuel values source context solved reasonAt scope id code}
    (receipt : Certificate fuel values source context solved reasonAt scope id code) :
    CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id code :=
  receipt.choose

/-- Actual atomic acceptance supplies the exact validator-selected literal row. -/
theorem literalFactory {policy body context values source scope reasonAt} :
    CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id code) := by
  intro id node fuel code found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted
  exact ⟨receipt.forget, receipt⟩

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful functionLeaves functionTypes sameLedger runtime unique uninitialized missing in
/-- Every independent source outcome is preserved using the complete runtime
ledger and actual selected rows at this tree's numeric leaves. -/
theorem preserves [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate fuel values source context solved reasonAt) faults :=
  CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful functionLeaves functionTypes
    program evidence unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults)

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing in
/-- Original native completion reconstructs an independent source outcome.
No source execution or preservation law is an input. -/
theorem reflects [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate fuel values source context solved reasonAt) faults :=
  CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful functionLeaves functionTypes
    program evidence uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults)

/-- One supported compiler traversal closes all builtin and general-expression literal leaves. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (CompatibleExpressionBuiltins.Syntax source))
    (policyFor : CompatibleExpressionBuiltins.PolicyFor policy context readFuel values source scope reasonAt)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (coercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Certificate readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact CompatibleExpressionBuiltins.tree_of_functions_with_literals _ literalFactory unique declarations signatures
    constructorValid policyFor native active profile coercions syntaxTree found typed accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
end
