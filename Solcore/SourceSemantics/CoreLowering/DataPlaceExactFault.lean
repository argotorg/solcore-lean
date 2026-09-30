import Solcore.SourceSemantics.CoreLowering.DataPlaceReadTotality

/-! Exact missing-default diagnostics from actual path preparation. Selection
and reconstruction return the token assigned to the independent source fault's
retained value type. Recursive helper execution is derived from full payloads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceExactFault
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates DataPlaceMappingIndex DataEquality

def token (missing : TypeSystem.Ty → Word) : Dynamic.SemanticFault → Word
  | .missingMappingDefault type => missing type
  | _ => Word.zero

/-- A fault's exact token follows every mixed member/index prefix. No enclosing
mapping insertion or source-cell write executes on this path. -/
theorem preserves {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType sourceTypes)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    {targetSteps : List PreparedStep} {targetKeys : List (ExpressionId × Ty)}
    {sources : List Dynamic.Value} {values allKeys : List Value}
    {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing position steps targetSteps targetKeys)
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (atPosition : ∀ i value, values[i]? = some value → allKeys[position + i]? = some value)
    (keyLength : prepared.keyTypes.length = allKeys.length)
    {sourceRoot : Dynamic.Value} {coreRoot : Value} {reason : Dynamic.SemanticFault}
    (rootRelated : ValueRep checked.catalog signatures functions mapping world root sourceRoot coreRoot rootType)
    (fault : Dynamic.ProjectionsFaults (some sourceRoot) evaluated reason)
    (environment : Environment) (before : Store) (current keys replacement : Expr)
    (rootSelected : Selects environment current coreRoot)
    (keysSelected : Selects environment keys (packValues allKeys)) :
    ∃ after administrative,
      Evaluates environment before (select prepared targetSteps current keys)
        (.inLeft prepared.optionalLeaf (.word (token missing reason))) after ∧
      Evaluates environment before (update prepared targetSteps rootType current keys replacement)
        (.inLeft rootType (.word (token missing reason))) after ∧
      after = before ++ administrative := by
  induction path generalizing position targetSteps targetKeys sources values evaluated coreTypes sourceRoot coreRoot
      environment before current keys replacement with
  | nil projected => cases shaped; cases fault
  | @member root field leaf dataType index name branches fieldType leafType steps rest types layout rootProjected fieldProjected tail ih =>
    cases preparation with
    | member preparation =>
      cases shaped with
      | member shaped =>
        obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
        obtain ⟨metadata, tag, sourceFields, fields, fieldTypes, sourceEq, coreEq, typeEq,
          result, authenticated, registered, payloads⟩ := rootRelated.nominal_parts nominal
        subst sourceRoot; subst coreRoot
        obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
        obtain ⟨sourceChild, coreChild, coreChildType, sourceAt, coreAt, typeAt, childRelated⟩ := payloads.at fieldAt
        have same := Except.ok.inj (childRelated.projection.symm.trans fieldProjected)
        subst coreChildType
        cases fault with
        | member faultAt fault =>
          have same := sourceAt.functional faultAt
          subst sourceChild
          obtain ⟨after, administrative, readEval, writeEval, appended⟩ :=
            ih preparation shaped keysRelated atPosition childRelated fault (packValues fields :: environment) before
              _ (shift 1 keys) (shift 1 replacement)
              (projectPacked_selects (Selects.var (index := 0) rfl) (arity.trans payloads.length.2.1) index coreAt)
              (by simpa [shift] using keysSelected.weaken (packValues fields))
          refine ⟨after, administrative, ?_, ?_, appended⟩
          · exact .matchData (rootSelected.evaluates before) owner
              (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) readEval
          · exact .matchData (rootSelected.evaluates before) owner
              (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl)
              (LanguageResult.bind_failure _ writeEval)
  | @index key value leaf layout id node steps rest leafType types identity erased keyProjected valueProjected found typed tail ih =>
    cases preparation with
    | @index _ _ _ _ entry sourceKey registeredValue comparison default _ target targetKeys selected mappingType comparisonGenerated defaultGenerated preparation =>
      obtain ⟨actualEntry, actualSelected, actualType⟩ := DataEqualityValues.identity_entry identity
      have sameEntry := Option.some.inj (selected.symm.trans actualSelected)
      subst actualEntry
      rw [erased, mappingType] at actualType
      obtain ⟨keySame, valueSame⟩ := TypeSystem.Ty.mapping.inj actualType
      subst sourceKey; subst registeredValue
      cases shaped with
      | @index _ _ sourceKeyValue remainingValues evaluatedRest shaped =>
        cases keysRelated with
        | @cons _ coreKeyType _ coreKey _ _ _ _ keyRelated keysRelated =>
          have keyRep : ValueRep checked.catalog signatures functions mapping world key _ _ _ := keyRelated
          have sameType := Except.ok.inj (keyRep.projection.symm.trans keyProjected)
          cases sameType
          let certificate : Index checked value
              ⟨layout, id, position, comparison.expression, default.expression, missing value⟩ :=
            Index.of_generated comparisonGenerated defaultGenerated keyProjected valueProjected
          obtain ⟨entries, coreEntries, sourceEq, coreEq, identity, registered, contents⟩ :=
            rootRelated.mapping_parts layout keyProjected valueProjected
          subst sourceRoot; subst coreRoot
          have keyObserved : KeyRep certificate signatures identities sourceKeyValue coreKey := by
            unfold KeyRep DataMappingComparison.KeyRep
            rw [← certificate.keyType]
            exact keyRep.observation observations
          have entriesObserved : OrderedMapping.EntriesRel (KeyRep certificate signatures identities)
              (fun source core => ValueRep checked.catalog signatures functions mapping world value source core layout.valueType)
              entries coreEntries := by
            unfold KeyRep DataMappingComparison.KeyRep
            rw [← certificate.keyType]
            exact contents.observed observations
          have keyAt := atPosition 0 coreKey rfl
          simp only [Nat.add_zero] at keyAt
          have keySelected := projectPacked_selects keysSelected keyLength position keyAt
          have finish {sourceChild : Dynamic.Value} (selected : Reads sourceKeyValue entries value sourceChild)
              (fault : Dynamic.ProjectionsFaults (some sourceChild) evaluatedRest reason) :
              ∃ after administrative,
                Evaluates environment before (select prepared
                  (.index ⟨layout, id, position, comparison.expression, default.expression, missing value⟩ :: target) current keys)
                  (.inLeft prepared.optionalLeaf (.word (token missing reason))) after ∧
                Evaluates environment before (update prepared
                  (.index ⟨layout, id, position, comparison.expression, default.expression, missing value⟩ :: target) layout.type current keys replacement)
                  (.inLeft layout.type (.word (token missing reason))) after ∧ after = before ++ administrative := by
            obtain ⟨child, childRep, childEval⟩ := selectedIndex_preserves certificate prepared faithful keyObserved entriesObserved selected
              environment before current keys rootSelected keySelected
            have childRelated : ValueRep checked.catalog signatures functions mapping world value sourceChild child layout.valueType := by
              rcases childRep with childRep | ⟨expression, defaulted⟩
              · exact childRep
              · exact default_represents_at layouts valueProjected defaulted
            obtain ⟨after, administrative, readEval, writeEval, appended⟩ :=
              ih preparation shaped keysRelated (by
                intro i v found
                simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1] using atPosition (i + 1) v found)
                childRelated fault (child :: environment) _ (.var 0) (shift 1 keys) (shift 1 replacement)
                (.var rfl) (by simpa [shift] using keysSelected.weaken child)
            obtain ⟨initialAdministrative, initialAppend, _⟩ := selectedStore_extension certificate environment before coreEntries coreKey
            exact ⟨after, initialAdministrative ++ administrative,
              LanguageResult.bind_success _ childEval readEval,
              LanguageResult.bind_success _ childEval (LanguageResult.bind_failure _ writeEval),
              by rw [appended, initialAppend, List.append_assoc]⟩
          cases fault with
          | indexDefaultUnavailable keyType absent unavailable =>
            have failed := selectedIndex_missing certificate prepared faithful keyObserved entriesObserved absent unavailable
              environment before current keys rootSelected keySelected
            obtain ⟨administrative, appended, _⟩ := selectedStore_extension certificate environment before coreEntries coreKey
            exact ⟨_, administrative, LanguageResult.bind_failure _ failed,
              LanguageResult.bind_failure _ failed, appended⟩
          | indexFound keyType lookup fault => exact finish (.found lookup) fault
          | indexDefault keyType absent defaulted fault => exact finish (.default absent defaulted) fault

end Solcore.SourceSemantics.CoreLowering.DataPlaceExactFault
