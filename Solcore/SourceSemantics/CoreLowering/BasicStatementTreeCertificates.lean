import Solcore.SourceSemantics.CoreLowering.GeneralStatements

/-! Extract a complete basic statement certificate from successful lowering.

The compiler checks binder ownership, monomorphism, scalar/product types and
freshness in its scope. The additional source-context invariant below supplies
well-formed ambient rigid binders and the identity correspondence needed to
transport freshness into both declarative lexical tables. It does not assume
source typing, a desired statement Tree, or any child evaluation.

This is a runtime correspondence theorem. It does not establish the complete
static SourceHasType judgment or the agreement of ambient local schemes with
the compiler scope. Supported expression coercions are empty, so their raw
types already equal their retained types. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell

/-- The source context and compiler scope have the same lexical identity
order, including the qualified-scheme table. Scheme payloads need not be
reconstructed to transport freshness. Runtime values and cell types are
related separately by `GeneralHeap.EnvRepresents` and `HeapRepresents`. -/
structure ScopeContextAligned (scope : SourceCoreLocalCell.Scope) (context : Context) : Prop where
  binders : TypeParameterBindersWellFormed context
  locals : context.locals.map Prod.fst = scope.map Prod.fst
  requirements : context.localSchemeRequirements.map Prod.fst = scope.map Prod.fst

namespace ScopeContextAligned

theorem empty (signatures : ProgramSignatures) :
    ScopeContextAligned [] (Context.ofSignatures signatures) := by
  constructor
  · simp [TypeParameterBindersWellFormed, Context.ofSignatures]
  · rfl
  · rfl

theorem bind {scope : SourceCoreLocalCell.Scope} {context : Context}
    (aligned : ScopeContextAligned scope context) (binder : TypedBinder) (type : Core.Ty) :
    ScopeContextAligned ((binder.id, type) :: scope)
      (context.withLocal binder.id binder.scheme binder.schemeRequirements) := by
  constructor
  · exact aligned.binders
  · simpa [Context.withLocal] using congrArg (List.cons binder.id) aligned.locals
  · simpa [Context.withLocal] using congrArg (List.cons binder.id) aligned.requirements

theorem fresh {scope : SourceCoreLocalCell.Scope} {context : Context} {id : Resolved.LocalId}
    (aligned : ScopeContextAligned scope context)
    (absent : scope.any (fun entry => decide (entry.1 = id)) = false) : LocalFresh context id := by
  have missing : id ∉ scope.map Prod.fst := by
    intro member
    obtain ⟨entry, member, equal⟩ := List.mem_map.mp member
    have present : scope.any (fun entry => decide (entry.1 = id)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨entry, member, by simpa using equal⟩
    rw [absent] at present
    contradiction
  exact ⟨by simpa [aligned.locals] using missing,
    by simpa [aligned.requirements] using missing⟩

end ScopeContextAligned

theorem BinderCertificate.extends
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {binder : TypedBinder} {type : Core.Ty}
    (certificate : BinderCertificate source scope binder type)
    (aligned : ScopeContextAligned scope context) :
    BinderExtends source.owner context binder
      (context.withLocal binder.id binder.scheme binder.schemeRequirements) := by
  have sourceScoped : ∀ {sourceType : Ty} {coreType : Core.Ty},
      TypeRepresents sourceType coreType → ∀ variables, TypeWellScoped context variables sourceType := by
    intro sourceType coreType types variables
    induction types with
    | unit => exact .builtin .unit
    | bool => exact .builtin .bool
    | word => exact .builtin .word
    | product _ _ left right => exact .product left right
  exact .intro {
    owned := certificate.owned
    scheme := {
      binders := aligned.binders
      quantified_nodup := by simp [certificate.monomorphic]
      body := sourceScoped certificate.types _
    }
    quantified_fresh := by simp [SchemeQuantifiersFresh, certificate.monomorphic]
    monomorphic_requirements_empty := fun _ => certificate.requirements
  } (aligned.fresh certificate.fresh)

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Every actually accepted basic statement list has a structural certificate.
Explicit returns need no facts about the unreachable remainder. Extraction is
bounded by the same traversal fuel and has no evaluation premises. -/
theorem tree_of_lowerStatements
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {resultType : Core.Ty}
    {reason : Core.Word} {expression : Core.Expr}
    (aligned : ScopeContextAligned scope context)
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason = .ok expression) :
    ∃ depth, depth ≤ fuel ∧ Tree source reason scope context statements resultType expression depth := by
  induction fuel generalizing scope context statements expression with
  | zero =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨0, Nat.le_refl _, .nil⟩
          · cases accepted
      | cons => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨0, Nat.zero_le _, .nil⟩
          · cases accepted
      | cons id rest =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          have metadata := (readStatement_certificate read).2
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have unitType := ensureType_ok checked
              rw [← unitType] at metadata
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have certificate := lowerBinder_certificate binding
              have extension := certificate.extends aligned
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨depth, bound, tail⟩ := ih (aligned.bind binder payload) compiledBody
                  exact ⟨depth + 1, by omega, .letUninitialized metadata form certificate extension tail⟩
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyDepth, bodyBound, tail⟩ := ih (aligned.bind binder payload) compiledBody
                  obtain ⟨valueDepth, valueBound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                  rw [← same] at valueTree
                  exact ⟨max valueDepth bodyDepth + 1, by omega,
                    .letInitialized metadata form certificate extension valueTree tail⟩
          | assignValue assignment operator value =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have unitType := ensureType_ok checked
              rw [← unitType] at metadata
              obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have same := ensureType_ok checked
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨bodyDepth, bodyBound, tail⟩ := ih aligned compiledBody
              have targetCertificate := lowerAssignment_certificate target
              have equal := targetCertificate.equal
              subst operator
              obtain ⟨valueDepth, valueBound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
              rw [← same] at valueTree
              exact ⟨max valueDepth bodyDepth + 1, by omega,
                .assign metadata form targetCertificate valueTree tail⟩
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultSame := ensureType_ok resultChecked
                  have unitSame := ensureType_ok unitChecked
                  have resultUnit : resultType = .unit := resultSame.trans unitSame.symm
                  rw [← unitSame] at metadata
                  cases accepted
                  rw [resultUnit]
                  exact ⟨1, by omega, .returnUnit rest metadata form⟩
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultSame := ensureType_ok resultChecked
                  rw [← resultSame] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  cases accepted
                  obtain ⟨depth, bound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                  rw [← same] at valueTree
                  exact ⟨depth + 1, by omega, .returnValue rest metadata form valueTree⟩
          | expression value semicolon =>
              cases semicolon with
              | true =>
                  simp only [form, ↓reduceIte] at accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have unitType := ensureType_ok checked
                  rw [← unitType] at metadata
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyDepth, bodyBound, tail⟩ := ih aligned compiledBody
                  obtain ⟨valueDepth, valueBound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                  exact ⟨max valueDepth bodyDepth + 1, by omega, .discard metadata form valueTree tail⟩
              | false =>
                  cases rest with
                  | cons => simp [form] at accepted
                  | nil =>
                      simp only [form, List.isEmpty_nil, Bool.false_eq_true, ↓reduceIte] at accepted
                      obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                      cases checkedUnit
                      have resultSame := ensureType_ok resultChecked
                      rw [← resultSame] at metadata
                      obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                      obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                      cases checkedUnit
                      have same := ensureType_ok checked
                      cases accepted
                      obtain ⟨depth, bound, valueTree⟩ := BasicExpressions.tree_of_lowerExpression compiledValue
                      rw [← same] at valueTree
                      exact ⟨depth + 1, by omega, .tailExpression metadata form valueTree⟩
          | assignBitNot | ifThen | block | matchWith | forLoop | whileLoop | breakStmt | continueStmt =>
              simp [form] at accepted

/-- Actual successful basic lowering executes according to the independent
source semantics, even with administrative closures in the Core store. The
remaining premises describe the ambient context and initial representation;
no structural Tree or source execution is supplied by the caller. -/
theorem lowerStatements_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty}
    {reason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements type reason = .ok code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code =
      some (Core.LanguageResult.resultType type) ∧
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap
        statements finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason type outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) =
        .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) := by
  obtain ⟨depth, bound, tree⟩ := tree_of_lowerStatements aligned accepted
  exact (GeneralStatements.lower_run_preserves tree unique fuel bound program evidence environments heaps).2

end Solcore.SourceSemantics.CoreLowering.BasicStatements
