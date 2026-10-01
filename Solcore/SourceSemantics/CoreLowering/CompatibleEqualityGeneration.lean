import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityTree
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityValues
import Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates

/-! Static extraction from actual compatible comparator generation, following
finite equality observations. Recursive calls follow the represented payload,
so generated recursive helper references introduce no termination assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceCoreCompatibleDataEquality DataEquality DataEqualityGeneration

abbrev ReferencesAt (catalog : Catalog) := DataEqualityCertificates.ReferencesAt (storageCatalog catalog)

theorem data_compareType {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    (notMapping : ∀ key value, entry.sourceType ≠ .mapping key value)
    {fuel depth : Nat} {left right compiled : Expr}
    (accepted : compareType fuel catalog depth (.namedData id) left right = .ok compiled) :
    compiled = SourceCoreDataEquality.invoke (.var (referenceIndex catalog depth id)) left right := by
  cases fuel with
  | zero => simp [compareType] at accepted
  | succ fuel =>
    cases kind : entry.sourceType <;>
      simp only [compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, selected, kind,
        bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    all_goals first | exact accepted.symm | exact False.elim (notMapping _ _ kind)

theorem data_helperBody {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    (notMapping : ∀ key value, entry.sourceType ≠ .mapping key value)
    {fuel : Nat} {body : Expr} (accepted : helperBody fuel catalog id = .ok body) :
    ∃ definition, entry.definition = some definition ∧
      nominalBody fuel catalog id definition.constructorPayloadTypes = .ok body := by
  have next : (match entry.definition with
      | some definition => nominalBody fuel catalog id definition.constructorPayloadTypes
      | none => .error (.missingDefinition id)) = .ok body := by
    cases kind : entry.sourceType <;>
      simp only [helperBody, selected, kind, bind, Except.bind, pure, Except.pure] at accepted
    all_goals first | exact accepted | exact False.elim (notMapping _ _ kind)
  cases found : entry.definition with
  | none => simp [found] at next
  | some definition => exact ⟨definition, rfl, by simpa [found] using next⟩

theorem registered_payload {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry) {definition : DataDefinition}
    (definitionSelected : entry.definition = some definition) {index : Nat} {payloadType : Ty}
    (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType) :
    definition.constructorPayloadTypes[index]? = some payloadType := by
  simpa [SourceCoreCompatibleCatalog.Catalog.definitions, DataEnvironment.lookupConstructorPayloadType?,
    DataEnvironment.lookupDataType?, selected, definitionSelected] using registered

theorem tree_of_compareType {catalog : Catalog} {registry : Registry}
    {identities : Dynamic.Value → Word → Prop} {helperFuel : Nat} {bodies : List Expr}
    (generatedHelpers : helperBodies helperFuel catalog = .ok bodies)
    {base : Nat} {ambient : Environment} {store : Store}
    (installed : Installed catalog bodies base ambient store)
    {type : Ty} {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation catalog registry identities type sourceLeft leftValue)
    (rightObserved : Observation catalog registry identities type sourceRight rightValue)
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
      simp only [compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved
      first | exact ⟨true, .base .unit⟩ | exact ⟨_, .base (.bool leftSelected rightSelected)⟩ |
        exact ⟨_, .base (.word leftSelected rightSelected)⟩ | exact ⟨_, .base (.integer leftSelected rightSelected)⟩
  | @product leftType rightType a b x y first second firstIH secondIH =>
    cases rightObserved with
    | mapping => exact False.elim second.carrier.not_mapping_tail
    | identified => exact False.elim first.carrier.not_sum
    | anonymous => exact False.elim first.carrier.not_sum
    | contractedIdentified _ _ _ _ _ profile =>
        exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
    | contractedAnonymous _ _ _ _ _ profile =>
        exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
    | product otherFirst otherSecond =>
      cases fuel with
      | zero => simp [compareType] at accepted
      | succ fuel =>
        have generated : (show Except Error Expr from do
            let left ← compareType fuel catalog depth leftType (.first leftExpression) (.first rightExpression)
            let right ← compareType fuel catalog depth rightType (.second leftExpression) (.second rightExpression)
            pure (.ifE left right (.bool false))) = .ok compiled := by
          have carrier := first.carrier
          have noMap := second.carrier.product_not_mapping (left := leftType)
          have shape := Carrier.product_contract_shape (right := rightType) carrier
          cases leftType <;> try cases carrier
          all_goals simpa only [compareType, noMap, shape, Bool.false_eq_true, ↓reduceIte] using accepted
        obtain ⟨leftCode, leftCompiled, generated⟩ := bind_ok generated
        obtain ⟨rightCode, rightCompiled, generated⟩ := bind_ok generated
        cases generated
        obtain ⟨leftResult, leftTree⟩ := firstIH otherFirst leftCompiled environment mapping references (.first leftSelected) (.first rightSelected)
        obtain ⟨rightResult, rightTree⟩ := secondIH otherSecond rightCompiled environment mapping references (.second leftSelected) (.second rightSelected)
        exact ⟨_, .product leftTree rightTree⟩
  | @mapping id valueType recognized key value entries carrier =>
    cases rightObserved with
    | product _ otherSecond => exact False.elim otherSecond.carrier.not_mapping_tail
    | mapping =>
      cases fuel with
      | zero => simp [compareType] at accepted
      | succ fuel =>
        simp only [compareType, recognized, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
        subst compiled
        exact ⟨false, .base (.mapping _ _ _ _ _ _)⟩
  | @identified source identity parameter result code meaning profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim first.carrier.not_sum
      | identified _ _ _ other _ => exact ⟨_, .base (.identified meaning other leftSelected rightSelected)⟩
      | anonymous source => exact ⟨false, .base (.anonymousRight _ source leftSelected rightSelected)⟩
  | @anonymous source parameter result code profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim first.carrier.not_sum
      | identified | anonymous => exact ⟨false, .base (.anonymousLeft source _ leftSelected rightSelected)⟩
  | @contractedIdentified source identity parameter result code contract meaning profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [CallableContract.functionType, TaggedFunction.functionType, TaggedFunction.identityType,
        LanguageResult.resultType, compareType, isMappingCarrier, SourceCoreDataEquality.isCallableContractType, profile,
        Bool.false_eq_true, Bool.true_and, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
      | contractedIdentified _ _ _ _ other _ => exact ⟨_, .base (.identified meaning other (.first leftSelected) (.first rightSelected))⟩
      | contractedAnonymous source => exact ⟨false, .base (.anonymousRight _ source (.first leftSelected) (.first rightSelected))⟩
  | @contractedAnonymous source parameter result code contract profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [CallableContract.functionType, TaggedFunction.functionType, TaggedFunction.identityType,
        LanguageResult.resultType, compareType, isMappingCarrier, SourceCoreDataEquality.isCallableContractType, profile,
        Bool.false_eq_true, Bool.true_and, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
      | contractedIdentified | contractedAnonymous => exact ⟨false, .base (.anonymousLeft source _ (.first leftSelected) (.first rightSelected))⟩
  | @data id index entry source packed payloadType payload selected notMapping registered meaning representation ih =>
    rw [data_compareType selected notMapping accepted, invoke_rename]
    cases rightObserved with
    | @data _ otherIndex otherEntry otherSource otherPacked otherPayloadType otherPayload
        otherSelected otherNotMapping otherRegistered otherMeaning otherRepresentation =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst otherEntry
      have bound : id.index < catalog.entries.length := List.getElem?_eq_some_iff.mp selected |>.1
      obtain ⟨body, bodySelected, generatedBody⟩ := CompatibleEquality.helperBodies_lookup generatedHelpers bound
      obtain ⟨definition, definitionSelected, generatedNominal⟩ := data_helperBody selected notMapping generatedBody
      have leftPayload := CompatibleEquality.registered_payload selected definitionSelected registered
      have rightPayload := CompatibleEquality.registered_payload selected definitionSelected otherRegistered
      obtain ⟨branches, rightBranches, branch, bodyEq, leftBranch, rightBranch, branchGenerated⟩ :=
        CompatibleEquality.nominalBody_branches generatedNominal leftPayload rightPayload
      let captured := DataEqualityInstalled.captured id.index (DataEqualityInstalled.allocatedEnvironment (storageCatalog catalog) base ambient)
      let pair := Value.pair (.constructed ⟨id, index⟩ payload) (.constructed ⟨id, otherIndex⟩ otherPayload)
      let shift := (DataEqualityInstalled.offset id.index).lift
      have helperReferences : ReferencesAt catalog base 3 shift.lift.lift (otherPayload :: payload :: pair :: captured) :=
        (DataEqualityCertificates.installedReferences (storageCatalog catalog) base ambient id.index pair).lift payload |>.lift otherPayload
      have installedBody := installed id.index body bodySelected
      have renamedLeft := renameList_lookup leftBranch shift.lift
      have renamedRight := renameList_lookup rightBranch shift.lift.lift
      by_cases same : index = otherIndex
      · subst otherIndex
        have payloadTypes := Option.some.inj (leftPayload.symm.trans rightPayload)
        subst otherPayloadType
        simp only [↓reduceIte] at branchGenerated
        obtain ⟨result, payloadTree⟩ := ih otherRepresentation branchGenerated _ shift.lift.lift helperReferences
          (.var rfl) (.var rfl)
        refine ⟨result, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ result
        rw [bodyEq]
        apply Tree.dataSame (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft) renamedRight
          (meaning.equivalent otherMeaning) payloadTree
      · have branchEq : branch = .bool false := by simpa [same] using branchGenerated.symm
        have distinct : source ≠ sourceRight := by
          intro sourceSame
          subst sourceRight
          exact same (ConstructorId.mk.inj (meaning.tags_equal otherMeaning)).2
        refine ⟨false, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ false
        rw [bodyEq]
        apply Tree.dataDifferent distinct (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft)
          (by simpa [branchEq, Expr.rename] using renamedRight)

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
