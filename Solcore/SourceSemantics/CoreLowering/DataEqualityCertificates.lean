import Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration
import Solcore.SourceSemantics.CoreLowering.DataEqualityValues

/-! Comparison certificates obtained from accepted code and finite equality
observations. Recursive helper execution follows the finite nominal payload,
not compilation fuel or a source runtime evaluator. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates
open Core Frontend SourceCoreDataEquality DataEquality DataEqualityValues DataEqualityGeneration

def ReferencesAt (catalog : Catalog) (base depth : Nat) (mapping : Renaming) (environment : Environment) : Prop :=
  ∀ index, index < catalog.entries.length →
    environment[mapping (referenceIndex catalog depth ⟨index⟩)]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index))

theorem ReferencesAt.lift {catalog : Catalog} {base depth : Nat} {mapping : Renaming} {environment : Environment}
    (references : ReferencesAt catalog base depth mapping environment) (value : Value) :
    ReferencesAt catalog base (depth + 1) mapping.lift (value :: environment) := by
  intro index bound
  have next : referenceIndex catalog (depth + 1) ⟨index⟩ = referenceIndex catalog depth ⟨index⟩ + 1 := by
    simp [referenceIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [next, Renaming.lift] using references index bound

theorem installedReferences (catalog : Catalog) (base : Nat) (ambient : Environment) (count : Nat) (pair : Value) :
    ReferencesAt catalog base 1 (DataEqualityInstalled.offset count).lift
      (pair :: DataEqualityInstalled.captured count (DataEqualityInstalled.allocatedEnvironment catalog base ambient)) := by
  intro index bound
  have next : referenceIndex catalog 1 ⟨index⟩ = referenceIndex catalog 0 ⟨index⟩ + 1 := by
    simp [referenceIndex, Nat.add_comm]
  simpa only [next, Renaming.lift, DataEqualityInstalled.offset, ← Nat.add_assoc,
    List.getElem?_cons_succ]
    using DataEqualityInstalled.captured_reference catalog base ambient count index bound

theorem tree_of_compareType {catalog : Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {helperFuel : Nat} {bodies : List Expr}
    (generatedHelpers : helperBodies helperFuel catalog = .ok bodies)
    {base : Nat} {ambient : Environment} {store : Store}
    (installed : DataEqualityInstalled.Installed catalog bodies base ambient store)
    {type : Ty} {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation catalog signatures identities type sourceLeft leftValue)
    (rightObserved : Observation catalog signatures identities type sourceRight rightValue)
    {fuel depth : Nat} {leftExpression rightExpression compiled : Expr}
    (accepted : compareType fuel catalog depth type leftExpression rightExpression = .ok compiled)
    (environment : Environment) (mapping : Renaming)
    (references : ReferencesAt catalog base depth mapping environment)
    (leftSelected : Selects environment (leftExpression.rename mapping) leftValue)
    (rightSelected : Selects environment (rightExpression.rename mapping) rightValue) :
    ∃ result, Tree identities store environment (compiled.rename mapping) sourceLeft sourceRight result := by
  induction leftObserved generalizing sourceRight rightValue fuel depth leftExpression rightExpression compiled environment mapping with
  | unit | bool | word | integer =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved
      first | exact ⟨true, .unit⟩ | exact ⟨_, .bool leftSelected rightSelected⟩ |
        exact ⟨_, .word leftSelected rightSelected⟩ | exact ⟨_, .integer leftSelected rightSelected⟩
  | @product leftType rightType a b x y first second firstIH secondIH =>
    cases rightObserved with
    | identified => exact False.elim (Carrier.not_sum first.carrier)
    | anonymous => exact False.elim (Carrier.not_sum first.carrier)
    | product otherFirst otherSecond =>
      cases fuel with
      | zero => simp [compareType] at accepted
      | succ fuel =>
        have generated : (show Except Error Expr from do
            let left ← compareType fuel catalog depth leftType (.first leftExpression) (.first rightExpression)
            let right ← compareType fuel catalog depth rightType (.second leftExpression) (.second rightExpression)
            pure (.ifE left right (.bool false))) = .ok compiled := by
          have carrier := first.carrier
          cases leftType <;> try cases carrier
          all_goals exact accepted
        obtain ⟨leftCode, leftCompiled, generated⟩ := bind_ok generated
        obtain ⟨rightCode, rightCompiled, generated⟩ := bind_ok generated
        simp only [pure, Except.pure, Except.ok.injEq] at generated
        subst compiled
        obtain ⟨leftResult, leftTree⟩ := firstIH otherFirst leftCompiled environment mapping references (.first leftSelected) (.first rightSelected)
        obtain ⟨rightResult, rightTree⟩ := secondIH otherSecond rightCompiled environment mapping references (.second leftSelected) (.second rightSelected)
        exact ⟨_, .product leftTree rightTree⟩
  | @identified source identity parameter result code meaning =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_sum first.carrier)
      | identified _ _ _ other => exact ⟨_, .identified meaning other leftSelected rightSelected⟩
      | anonymous source => exact ⟨false, .anonymousRight _ source leftSelected rightSelected⟩
  | @anonymous source parameter result code =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_sum first.carrier)
      | identified | anonymous => exact ⟨false, .anonymousLeft source _ leftSelected rightSelected⟩
  | @proxy id entry inner selected sourceType =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, selected, sourceType, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved with
      | proxy otherInner otherSelected otherType =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        have same := TypeSystem.Ty.proxy.inj (sourceType.symm.trans otherType)
        subst_vars
        exact ⟨true, .proxy _⟩
      | mapping otherSelected otherType =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [sourceType] at otherType
        cases otherType
      | constructed otherSelected otherType nominal =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [← otherType, sourceType] at nominal
        simp [SourceCoreDataCatalog.nominalParts] at nominal
  | @mapping id entry registeredKey registeredValue selected sourceType key value entries carrier =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, selected, sourceType, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved with
      | mapping => exact ⟨false, .mapping _ _ _ _ _ _⟩
      | proxy otherInner otherSelected otherType =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [sourceType] at otherType
        cases otherType
      | constructed otherSelected otherType nominal =>
        have entries := Option.some.inj (selected.symm.trans otherSelected)
        subst_vars
        rw [← otherType, sourceType] at nominal
        simp [SourceCoreDataCatalog.nominalParts] at nominal
  | @constructed id index entry metadata declaration arguments sources packed payloadType payload
      selected sourceType nominal authenticated registered arity packing representation ih =>
    have nominalEntry : SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments) := by
      rw [sourceType]; exact nominal
    rw [nominal_compareType selected nominalEntry accepted, invoke_rename]
    cases rightObserved with
    | proxy inner otherSelected otherType =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst_vars
      rw [otherType] at nominalEntry
      simp [SourceCoreDataCatalog.nominalParts] at nominalEntry
    | mapping otherSelected otherType =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst_vars
      rw [otherType] at nominalEntry
      simp [SourceCoreDataCatalog.nominalParts] at nominalEntry
    | @constructed _ otherIndex otherEntry otherMetadata otherDeclaration otherArguments otherSources otherPacked otherPayloadType otherPayload
        otherSelected otherType otherNominal otherAuthenticated otherRegistered otherArity otherPacking otherRepresentation =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst otherEntry
      have bound : id.index < catalog.entries.length := List.getElem?_eq_some_iff.mp selected |>.1
      obtain ⟨body, bodySelected, generatedBody⟩ := helperBodies_lookup generatedHelpers bound
      obtain ⟨definition, definitionSelected, generatedNominal⟩ := nominal_helperBody selected nominalEntry generatedBody
      have leftPayload := registered_payload selected definitionSelected registered
      have rightPayload := registered_payload selected definitionSelected otherRegistered
      obtain ⟨branches, rightBranches, branch, bodyEq, leftBranch, rightBranch, branchGenerated⟩ :=
        nominalBody_branches generatedNominal leftPayload rightPayload
      let captured := DataEqualityInstalled.captured id.index (DataEqualityInstalled.allocatedEnvironment catalog base ambient)
      let pair := Value.pair (.constructed ⟨id, index⟩ payload) (.constructed ⟨id, otherIndex⟩ otherPayload)
      let shift := (DataEqualityInstalled.offset id.index).lift
      have helperReferences : ReferencesAt catalog base 3 shift.lift.lift (otherPayload :: payload :: pair :: captured) :=
        (installedReferences catalog base ambient id.index pair).lift payload |>.lift otherPayload
      have installedBody := installed id.index body bodySelected
      have renamedLeft := renameList_lookup leftBranch shift.lift
      have renamedRight := renameList_lookup rightBranch shift.lift.lift
      by_cases same : index = otherIndex
      · subst otherIndex
        have payloadTypes := Option.some.inj (leftPayload.symm.trans rightPayload)
        subst otherPayloadType
        have metadataSame := metadata_eq authenticated otherAuthenticated (sourceType.symm.trans otherType)
        subst otherMetadata
        simp only [↓reduceIte] at branchGenerated
        obtain ⟨result, payloadTree⟩ := ih otherRepresentation branchGenerated _ shift.lift.lift helperReferences
          (.var rfl) (.var rfl)
        refine ⟨result, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ result
        rw [bodyEq]
        apply Tree.nominalSame metadata (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft) renamedRight
          packing otherPacking (arity.trans otherArity.symm) payloadTree
      · have branchEq : branch = .bool false := by simpa [same] using branchGenerated.symm
        have distinct : metadata ≠ otherMetadata := by
          intro sameMetadata
          rw [sameMetadata] at authenticated
          have tags := Except.ok.inj (authenticated.symm.trans otherAuthenticated)
          exact same (ConstructorId.mk.inj tags).2
        refine ⟨false, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ false
        rw [bodyEq]
        apply Tree.nominalDifferent metadata otherMetadata sources otherSources distinct
          (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft)
          (by simpa [branchEq, Expr.rename] using renamedRight)

theorem installed_append {catalog : Catalog} {bodies : List Expr} {base : Nat}
    {environment : Environment} {store : Store}
    (installed : DataEqualityInstalled.Installed catalog bodies base environment store) (suffix : Store) :
    DataEqualityInstalled.Installed catalog bodies base environment (store ++ suffix) := by
  intro index body selected
  have found := installed index body selected
  have bound : base + index < store.length := List.getElem?_eq_some_iff.mp found |>.1
  simpa [Store.read?, List.getElem?_append_left bound] using found

/-- Accepted preparation supplies both generated helper bodies and the main
comparison equation. A later mapping-helper allocation preserves `Installed`. -/
theorem prepared_tree {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (initialStore store : Store)
    (installed : DataEqualityInstalled.Installed checked.catalog prepared.bodies initialStore.length environment store) :
    ∃ result, Tree identities store
      (.pair leftValue rightValue :: DataEqualityInstalled.captured prepared.bodies.length
        (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment))
      (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift) sourceLeft sourceRight result := by
  apply tree_of_compareType prepared.bodiesGenerated installed leftObserved rightObserved prepared.bodyGenerated
  · exact installedReferences _ _ _ _ _
  · exact .first (.var rfl)
  · exact .second (.var rfl)

/-- The exact closure returned by real initialization is a finite, pure
OrderedMapping comparator in any store retaining the installed helper cells. -/
theorem prepared_compares {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (layout : OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (initialStore store : Store)
    (installed : DataEqualityInstalled.Installed checked.catalog prepared.bodies initialStore.length environment store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      OrderedMapping.Compares layout
        (.closure (.product prepared.type prepared.type) .bool
          (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
          (DataEqualityInstalled.captured prepared.bodies.length
            (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment)))
        leftValue rightValue result store := by
  obtain ⟨result, tree⟩ := prepared_tree prepared leftObserved rightObserved environment initialStore store installed
  exact ⟨result, tree.meaning faithful, by simpa only [keyType] using tree.compares layout⟩

/-- Initializer execution, recursive comparison, and independent source
equality are derived together. No child or helper evaluation is a premise. -/
theorem prepared_compare_preserves {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store
        (.letE prepared.expression (.apply (.var 0)
          (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0)))) (.bool result)
        (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  obtain ⟨result, tree⟩ := prepared_tree prepared leftObserved rightObserved environment store _
    (DataEqualityInstalled.prepared_installed prepared environment store)
  refine ⟨result, tree.meaning faithful, .letE (DataEqualityInstalled.prepared_evaluates_exact prepared environment store) ?_⟩
  exact .apply (.var rfl) (.pair ((leftSelected.weaken _).evaluates _) ((rightSelected.weaken _).evaluates _)) tree.evaluates

/-- Existing authenticated nominal values need no manually constructed
comparison tree, payload certificates, or extra Core typing premises. -/
theorem typed_compare_preserves {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresented : DataPatternTypedValues.TypedValueRep checked.catalog signatures prepared.sourceType sourceLeft leftValue)
    (rightRepresented : DataPatternTypedValues.TypedValueRep checked.catalog signatures prepared.sourceType sourceRight rightValue)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store
        (.letE prepared.expression (.apply (.var 0)
          (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0)))) (.bool result)
        (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  obtain ⟨leftType, leftProjection, leftObserved⟩ := TypedValueRep.observation (identities := identities) leftRepresented
  obtain ⟨rightType, rightProjection, rightObserved⟩ := TypedValueRep.observation (identities := identities) rightRepresented
  have leftEq := Except.ok.inj (leftProjection.symm.trans prepared.projection)
  have rightEq := Except.ok.inj (rightProjection.symm.trans prepared.projection)
  subst leftType; subst rightType
  exact prepared_compare_preserves prepared faithful leftObserved rightObserved environment store _ _ leftSelected rightSelected

theorem prepared_compare_run {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog signatures identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog signatures identities prepared.type sourceRight rightValue)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      let expression := Expr.letE prepared.expression (.apply (.var 0)
        (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0)))
      let finalStore := store ++ DataEqualityInstalled.cells
        (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial expression environment store) = .done (.bool result) finalStore) ∧
      (∀ fuel actual actualStore, runStateful fuel (.initial expression environment store) = .done actual actualStore →
        actual = .bool result ∧ actualStore = finalStore) := by
  obtain ⟨result, meaning, evaluated⟩ := prepared_compare_preserves prepared faithful leftObserved rightObserved
    environment store leftExpression rightExpression leftSelected rightSelected
  refine ⟨result, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated, ?_⟩
  intro fuel actual actualStore ran
  exact evaluation_deterministic (runStateful_evaluation_sound ran) evaluated

end Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates
