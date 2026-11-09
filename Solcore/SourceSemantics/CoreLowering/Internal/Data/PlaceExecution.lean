import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Payloads
import Solcore.Frontend.SourceCore.DataPlaces

/-!
# Data: place execution

Execution of places: update trees, write-back, snapshots, resolved targets, route certificates and exact faults.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTree
/-! Reconstruction of mixed finite paths from the latest supplied root.
Certificates contain structural representation closure laws, not evaluations
of generated children. Mapping defaults are derived from actual preparations;
all nested helper allocation is appended after the existing store prefix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTree
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

inductive Tree (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) (prepared : Prepared) (keys : List Value)
    (replacementSource : Dynamic.Value) (replacement : Value) :
    OrderedMapping.Relation → Dynamic.Value → Value → List PreparedStep →
      List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {relation : OrderedMapping.Relation} {source : Dynamic.Value} {value : Value}
      (represented : relation replacementSource replacement) :
      Tree checked signatures identities prepared keys replacementSource replacement relation source value [] [] replacementSource 0
  | member {relation childRelation : OrderedMapping.Relation}
      {metadata : DataConstructorInstantiation} {tag : ConstructorId}
      {sources : List Dynamic.Value} {values : List Value} {branch : MemberBranch}
      {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch} {fieldType : Ty} {name : String}
      {sourceChild updatedChild : Dynamic.Value} {valueChild : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (authenticated : checked.catalog.resolveConstructor signatures metadata = .ok tag)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag)
      (sourceArity : metadata.payloadTypes.length = sources.length)
      (coreArity : branch.payloadTypes.length = values.length)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : Tree checked signatures identities prepared keys replacementSource replacement childRelation
        sourceChild valueChild steps projections updatedChild count)
      (represented : ∀ child, childRelation updatedChild child →
        relation (.constructed metadata (sources.set index updatedChild))
          (.constructed tag (packValues (values.set index child)))) :
      Tree checked signatures identities prepared keys replacementSource replacement relation
        (.constructed metadata sources) (.constructed tag (packValues values))
        (.member dataType index branches fieldType :: steps) (.member name index :: projections)
        (.constructed metadata (sources.set index updatedChild)) count
  | mapping {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {relation valueRelation : OrderedMapping.Relation} {sourceKey sourceChild updatedChild : Dynamic.Value}
      {key : Value} {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (selected : Reads sourceKey sources sourceValueType sourceChild)
      (tail : ∀ value, (valueRelation sourceChild value ∨
          ∃ expression, DataDefaults.Tree checked.catalog sourceValueType sourceChild value expression) →
        Tree checked signatures identities prepared keys replacementSource replacement valueRelation
          sourceChild value steps projections updatedChild count)
      (inserted : Dynamic.MappingInsert sourceKey updatedChild sources updated)
      (represented : ∀ value, OrderedMapping.ValueRel index.layout
          (KeyRep certificate signatures identities) valueRelation updated value →
        relation (.mapping sourceKeyType sourceValueType updated) value) :
      Tree checked signatures identities prepared keys replacementSource replacement relation
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries)
        (.index index :: steps) (.index sourceKey :: projections) (.mapping sourceKeyType sourceValueType updated)
        (2 * (checked.catalog.entries.length + 1) + count)

private theorem replaceAt {values : List Dynamic.Value} {index : Nat} {previous : Dynamic.Value}
    (selected : Dynamic.ValueAt values index previous) (replacement : Dynamic.Value) :
    Dynamic.ValuesReplaceAt values index replacement (values.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

private theorem projectPacked_weaken (types : List Ty) (index : Nat) (expression : Expr) :
    SourceCoreDataExpressions.projectPacked index types (expression.weakenAt 0) =
      (SourceCoreDataExpressions.projectPacked index types expression).weakenAt 0 := by
  induction types generalizing index expression with
  | nil => simp [SourceCoreDataExpressions.projectPacked, Expr.weakenAt]
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest =>
      by_cases zero : index = 0
      · simp [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt]
      · simpa [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt] using ih (index - 1) (.second expression)

theorem Tree.preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {replacementSource : Dynamic.Value} {replacement : Value} {relation : OrderedMapping.Relation}
    {source : Dynamic.Value} {value : Value} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {updatedSource : Dynamic.Value} {count : Nat}
    (tree : Tree checked signatures identities prepared keys replacementSource replacement relation source value steps projections updatedSource count)
    (faithful : IdentityFaithful identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (type : Ty) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ updatedValue finalStore administrative,
      Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some source) projections updatedSource ∧
      relation updatedSource updatedValue ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression)
        (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store type current keyExpression replacementExpression with
  | leaf represented =>
    exact ⟨_, store, [], .leaf rfl, represented, .inRight (replacementSelected.evaluates store), by simp, rfl⟩
  | @member relation childRelation metadata tag sources values branch dataType index branches fieldType name sourceChild updatedChild valueChild steps projections count authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail represented ih =>
    obtain ⟨child, finalStore, administrative, changed, childRep, evaluated, extended, counted⟩ :=
      ih (packValues values :: environment) store fieldType _ (shift 1 keyExpression) (shift 1 replacementExpression)
        (projectPacked_selects (Selects.var (index := 0) rfl) coreArity index coreAt)
        (by simpa [shift] using keysSelected.weaken (packValues values))
        (by simpa [shift] using replacementSelected.weaken (packValues values))
    refine ⟨_, finalStore, administrative, .member sourceAt changed (replaceAt sourceAt updatedChild), represented child childRep,
      Evaluates.matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl) ?_, extended, counted⟩
    apply LanguageResult.bind_success _ evaluated
    rw [constructor]
    exact .inRight (.construct (DataPlaceMembers.replacePacked_evaluates coreArity (.var rfl) (.var rfl)))
  | @mapping sourceKeyType sourceValueType index certificate relation valueRelation sourceKey sourceChild updatedChild key sources updated entries steps projections count keyRep keyAt entriesRep read tail inserted represented ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep entriesRep read
      environment store current keyExpression selected keySelected
    obtain ⟨updatedChild, childStore, childCells, changed, updatedRep, tailEvaluated, childExtended, childCounted⟩ :=
      ih child childRep (child :: environment) _ index.layout.valueType (.var 0)
        (shift 1 keyExpression) (shift 1 replacementExpression) (.var rfl)
        (by simpa [shift] using keysSelected.weaken child)
        (by simpa [shift] using replacementSelected.weaken child)
    obtain ⟨updatedValue, valueRep, insertEvaluated⟩ := DataMappingComparison.insert_preserves certificate.comparison index.layout
      certificate.keyType faithful keyRep updatedRep entriesRep inserted (updatedChild :: child :: environment) childStore
      (shift 2 current) (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keyExpression)) (.var 0)
      (by simpa [shift, List.range_succ] using (selected.weaken child).weaken updatedChild)
      (by simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken child).weaken updatedChild) (.var rfl)
    obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
    obtain ⟨after, afterExtended, afterCounted⟩ := DataMappingComparison.helper_store_extension certificate.comparison
      (updatedChild :: child :: environment) childStore _ _ _ _
    refine ⟨updatedValue, DataMappingComparison.insertStore certificate.comparison index.layout
      (updatedChild :: child :: environment) childStore entries key updatedChild, before ++ childCells ++ after, ?_, represented updatedValue valueRep,
      LanguageResult.bind_success _ childEvaluated (LanguageResult.bind_success _ tailEvaluated ?_), ?_, ?_⟩
    · cases read with
      | found lookup => exact .indexFound lookup changed inserted
      | default absent defaulted => exact .indexDefault absent defaulted changed inserted
    · simpa only [certificate.comparisonExpression] using insertEvaluated
    · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
      rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from afterExtended,
        childExtended, beforeExtended]
      simp only [List.append_assoc]
    · simp only [List.length_append, beforeCounted, childCounted, afterCounted]
      omega

end Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers
/-! Closed helper invocation for mixed path certificates. Optional source roots
are normalized once before traversal. Empty mappings remain virtual until the
enclosing assignment writes the setter's completed result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues

inductive Root (prepared : Prepared) : Dynamic.Cell → Value → Dynamic.Value → Value → Prop where
  | initialized (type : TypeSystem.Ty) (source : Dynamic.Value) (value : Value) :
      Root prepared ⟨type, some source, none⟩ (.inRight .unit value) source value
  | emptyMapping {layout : Core.OrderedMapping.Layout} (key value : TypeSystem.Ty)
      (registered : prepared.route.rootMapping = some layout) :
      Root prepared ⟨.mapping key value, none, none⟩ (.inLeft layout.type .unit)
        (.mapping key value []) (Core.OrderedMapping.encode layout [])

theorem Root.initial {prepared : Prepared} {cell : Dynamic.Cell} {optional value : Value} {source : Dynamic.Value}
    (root : Root prepared cell optional source value) : Dynamic.RootInitialValue cell (some source) := by
  cases root with
  | initialized => exact .initialized
  | emptyMapping key value => exact .emptyMapping key value

theorem Root.normalizes {prepared : Prepared} {cell : Dynamic.Cell} {optional value : Value} {source : Dynamic.Value}
    (root : Root prepared cell optional source value) {environment : Environment} {expression : Expr}
    (selected : Selects environment expression optional) (store : Store) :
    Evaluates environment store (normalizeRoot prepared expression) (.inRight .unit value) store := by
  cases root with
  | initialized =>
    unfold normalizeRoot
    cases prepared.route.rootMapping with
    | none => exact selected.evaluates store
    | some => exact .caseRight (selected.evaluates store) (.inRight (.var rfl))
  | emptyMapping key value registered =>
    simp only [normalizeRoot, registered]
    exact .caseLeft (selected.evaluates store) (.inRight (.construct .unit))

theorem getter_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {relation : OrderedMapping.Relation} {cell : Dynamic.Cell} {optional value : Value}
    {source sourceLeaf : Dynamic.Value} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (root : Root prepared cell optional source value)
    (tree : DataPlaceReadTree.Tree checked signatures identities prepared keys relation source value steps projections sourceLeaf count)
    (sameSteps : prepared.steps = steps) (faithful : IdentityFaithful identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr)
    (argumentSelected : Selects environment argument (.pair optional (packValues keys))) :
    ∃ leaf finalStore administrative,
      Dynamic.RootInitialValue cell (some source) ∧
      Dynamic.ProjectionsRead (some source) projections (some sourceLeaf) ∧ relation sourceLeaf leaf ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (.inRight .word (.inRight .unit leaf)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  cases tree with
  | leaf represented =>
    refine ⟨value, store, [], root.initial, .nil, represented, ?_, by simp, rfl⟩
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps]
    exact .inRight (root.normalizes (.first (.var rfl)) store)
  | member authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail =>
    obtain ⟨leaf, finalStore, administrative, read, represented, evaluated, extended, counted⟩ :=
      (DataPlaceReadTree.Tree.member authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail).preserves
        faithful keyLength (_ :: .pair optional (packValues keys) :: environment) store (.var 0) (.second (.var 1))
        (.var rfl) (.second (.var rfl))
    refine ⟨leaf, finalStore, administrative, root.initial, read, represented, ?_, extended, counted⟩
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps]
    exact .caseRight (root.normalizes (.first (.var rfl)) store) evaluated
  | mapping certificate keyRep keyAt entriesRep selected tail =>
    obtain ⟨leaf, finalStore, administrative, read, represented, evaluated, extended, counted⟩ :=
      (DataPlaceReadTree.Tree.mapping certificate keyRep keyAt entriesRep selected tail).preserves
        faithful keyLength (_ :: .pair optional (packValues keys) :: environment) store (.var 0) (.second (.var 1))
        (.var rfl) (.second (.var rfl))
    refine ⟨leaf, finalStore, administrative, root.initial, read, represented, ?_, extended, counted⟩
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps]
    exact .caseRight (root.normalizes (.first (.var rfl)) store) evaluated

theorem setter_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {replacementSource : Dynamic.Value} {replacement : Value} {relation : OrderedMapping.Relation}
    {cell : Dynamic.Cell} {optional value : Value} {source updatedSource : Dynamic.Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (root : Root prepared cell optional source value)
    (tree : DataPlaceUpdateTree.Tree checked signatures identities prepared keys replacementSource replacement relation source value steps projections updatedSource count)
    (sameSteps : prepared.steps = steps) (faithful : IdentityFaithful identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr)
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement))) :
    ∃ updatedValue finalStore administrative,
      Dynamic.RootInitialValue cell (some source) ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some source) projections updatedSource ∧
      relation updatedSource updatedValue ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  cases tree with
  | leaf represented =>
    refine ⟨replacement, store, [], root.initial, .leaf rfl, represented, ?_, by simp, rfl⟩
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps]
    exact .inRight (.second (.second (.var rfl)))
  | member authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail promote =>
    obtain ⟨updatedValue, finalStore, administrative, changed, represented, evaluated, extended, counted⟩ :=
      (DataPlaceUpdateTree.Tree.member authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail promote).preserves
        faithful keyLength (_ :: .pair optional (.pair (packValues keys) replacement) :: environment) store prepared.route.rootType
        (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1))) (.var rfl) (.first (.second (.var rfl))) (.second (.second (.var rfl)))
    refine ⟨updatedValue, finalStore, administrative, root.initial, changed, represented, ?_, extended, counted⟩
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps]
    exact .caseRight (root.normalizes (.first (.var rfl)) store) evaluated
  | mapping certificate keyRep keyAt entriesRep selected tail inserted promote =>
    obtain ⟨updatedValue, finalStore, administrative, changed, represented, evaluated, extended, counted⟩ :=
      (DataPlaceUpdateTree.Tree.mapping certificate keyRep keyAt entriesRep selected tail inserted promote).preserves
        faithful keyLength (_ :: .pair optional (.pair (packValues keys) replacement) :: environment) store prepared.route.rootType
        (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1))) (.var rfl) (.first (.second (.var rfl))) (.second (.second (.var rfl)))
    refine ⟨updatedValue, finalStore, administrative, root.initial, changed, represented, ?_, extended, counted⟩
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps]
    exact .caseRight (root.normalizes (.first (.var rfl)) store) evaluated

end Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceExecution
/-! Exact administrative contexts for the emitted assignment sequence.
These are composition laws, not a whole source-compilation theorem. Child
compiler certificates must establish their own execution in the displayed
expanded environments; unrestricted exact-value weakening is not assumed.
Getter/setter certificates above supply their semantic executions separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceExecution
open Core Frontend SourceCoreDataPlaces

def referenceEnvironment (type : Ty) (location : Location) (environment : Environment) : Environment :=
  .cellRef (OptionalCell.cellType type) location :: environment

def keysEnvironment (type : Ty) (location : Location) (keys : Value) (environment : Environment) : Environment :=
  keys :: referenceEnvironment type location environment

def snapshotEnvironment (type : Ty) (location : Location) (keys snapshot : Value) (environment : Environment) : Environment :=
  snapshot :: keysEnvironment type location keys environment

def rhsEnvironment (type : Ty) (location : Location) (keys snapshot rhs : Value) (environment : Environment) : Environment :=
  rhs :: snapshotEnvironment type location keys snapshot environment

def modifiedEnvironment (type : Ty) (location : Location) (keys snapshot rhs changed : Value) (environment : Environment) : Environment :=
  changed :: rhsEnvironment type location keys snapshot rhs environment

def writtenEnvironment (type : Ty) (location : Location) (keys snapshot rhs changed updated : Value) (environment : Environment) : Environment :=
  .unit :: updated :: modifiedEnvironment type location keys snapshot rhs changed environment

/-- Exact success sequencing. The getter's store is the RHS input; the
setter sees the RHS store, and the write follows all setter administrative
allocations. No source-expression phase is repeated. -/
theorem execute_success {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore setterStore written finalStore : Store}
    {location : Location} {keyValue snapshot right changed updated old result : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word updated) setterStore)
    (passes : Passes operator right)
    (read : setterStore.read? location = some old)
    (write : setterStore.write? location (.inRight .unit updated) = some written)
    (nextEvaluated : Evaluates (writtenEnvironment prepared.route.rootType location keyValue snapshot right changed updated environment)
      written (shift 7 next) result finalStore) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand) result finalStore := by
  exact .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated
        (LanguageResult.bind_success _ rhsEvaluated
          (LanguageResult.bind_success _ modifiedEvaluated
            (LanguageResult.bind_success _ setterEvaluated
              (guard_passes passes (.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) write) nextEvaluated)))))))

/-- A panicking modifier with a zero right-hand side fails after the
structural update, with the setter's store and no write. -/
theorem execute_panic {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operation : BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore setterStore : Store}
    {location : Location} {keyValue snapshot changed updated : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word (.word Word.zero)) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot (.word Word.zero) environment) rhsStore
      (modified prepared.route.leafType (some ⟨operation, true⟩) bitNot (.var 1) (.var 0) invalidOperand)
      (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot (.word Word.zero) changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word updated) setterStore) :
    Evaluates environment before
      (execute prepared reference keys rhs next outputType (some ⟨operation, true⟩) bitNot invalidOperand)
      (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero))) setterStore := by
  exact .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated
        (LanguageResult.bind_success _ rhsEvaluated
          (LanguageResult.bind_success _ modifiedEvaluated
            (LanguageResult.bind_success _ setterEvaluated guard_panic)))))

/-- Failure in an index suppresses the getter, RHS, modifier, setter and
continuation. Each premise is for the actual shifted key code. -/
theorem execute_keys_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before after : Store} {location : Location}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inLeft keys.type (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before) (LanguageResult.bind_failure _ keysEvaluated)

theorem execute_snapshot_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore after : Store} {location : Location} {keyValue : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated (LanguageResult.bind_failure _ snapshotEvaluated))

theorem execute_rhs_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType rightType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore snapshotStore after : Store}
    {location : Location} {keyValue snapshot : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inLeft rightType (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated (LanguageResult.bind_failure _ rhsEvaluated)))

theorem execute_modified_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore after : Store}
    {location : Location} {keyValue snapshot right : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand)
      (.inLeft prepared.route.leafType (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated
        (LanguageResult.bind_success _ rhsEvaluated (LanguageResult.bind_failure _ modifiedEvaluated))))

theorem execute_setter_failure {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand reason : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore after : Store}
    {location : Location} {keyValue snapshot right changed : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inLeft prepared.route.rootType (.word reason)) after) :
    Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE (referenceSelected.evaluates before)
    (LanguageResult.bind_success _ keysEvaluated
      (LanguageResult.bind_success _ snapshotEvaluated
        (LanguageResult.bind_success _ rhsEvaluated
          (LanguageResult.bind_success _ modifiedEvaluated (LanguageResult.bind_failure _ setterEvaluated)))))

end Solcore.SourceSemantics.CoreLowering.DataPlaceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions
/-! Universal child meanings under execute's real temporary binders. These
lemmas instantiate the semantic induction hypothesis; static certificates do
not contain executions of keys, RHS expressions or continuation bodies.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open SourceCoreDataPlaces

def prefixRenaming : Nat → Renaming → Renaming
  | 0, ξ => ξ
  | count + 1, ξ => Renaming.comp (Renaming.insertion 0) (prefixRenaming count ξ)

theorem shift_succ (count : Nat) (expression : Expr) :
    shift (count + 1) expression = (shift count expression).weakenAt 0 := by
  simp [shift, List.range_succ, List.foldl_append]

theorem rename_prefix (expression : Expr) (count : Nat) (ξ : Renaming) :
    expression.rename (prefixRenaming count ξ) = shift count (expression.rename ξ) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [prefixRenaming, GenericExpressionMeaning.rename_prefix, ih, shift_succ]

theorem prefix_agrees {canonical actual : Environment} {ξ : Renaming}
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual) (slots : Environment) :
    ReadOnly.EnvironmentsAgree (prefixRenaming slots.length ξ) canonical (slots ++ actual) := by
  induction slots with
  | nil => exact layout
  | cons value rest ih => exact agree_prefix ih value

/-- This applies equally to the one key reference binder, the three RHS
binders and the seven post-write binders. Existing closure captures are kept;
no exact-value evaluation weakening principle is used. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Preserves model program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual) (slots : Environment)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (slots ++ actual) store (shift slots.length (lowered.expression.rename ξ)) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    meaning generated found environments heaps locals (prefix_agrees layout slots) trace
  exact ⟨value, finalStore, finalMap, finalWorld, by simpa only [rename_prefix] using evaluated, rest⟩

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Reflects model program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual) (slots : Environment)
    (evaluated : Evaluates (slots ++ actual) store
      (shift slots.length (lowered.expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply meaning generated found environments heaps locals (prefix_agrees layout slots)
  simpa only [rename_prefix] using evaluated

/-- A fault from the actual index vector completes the whole emitted
assignment with that fault. Getter, RHS, modifier, setter and continuation
are absent from the assumptions and are skipped by the proved evaluation. -/
theorem keys_fault {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {model : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep}
    (meaning : Preserves model program context evidence source certificate faults)
    {assignment : AssignmentResolution} {site : SourceCoreElaboration.ErrorSite} {fuel : Nat}
    {route : Route} {prepared : Prepared} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    {expression : ExpressionLowerer} {reasonAt : ExpressionId → Word} {codes : List SourceCoreBasic.LoweredExpr}
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalidProjection missing = .ok prepared)
    (generated : ListRel (DataPlaceCertificates.KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before assignment.target.projections reason after)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, tree, _⟩ := DataPlaceKeyOrder.tree_of_generated_keys described preparedBy generated extract
  obtain ⟨target, coreLookup, _⟩ := environments.lookup_visible lookup slot
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v found; exact found
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    DataPlaceKeyOrder.preserves_fault tree meaning environments heaps locals
      (prefix_agrees layout [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) trace
  have keysEvaluated : Evaluates
      (DataPlaceExecution.referenceEnvironment prepared.route.rootType target coreEnvironment) store
      (shift 1 (SourceCoreCalls.packArguments codes).expression)
      (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore := by
    simpa only [rename_prefix, Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append, DataPlaceExecution.referenceEnvironment] using evaluated
  exact ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace),
    DataPlaceExecution.execute_keys_failure (.var coreLookup) keysEvaluated, rest⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadUpdatePaths
/-! Complete payload preservation for the actual recursive place updater.
The induction follows static path receipts and independent source updates.
Comparison/default/recursive Core evaluations are all derived internally;
strong key authentication is retained when reconstructing mappings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMembers DataEquality

private theorem replacement_set {sources : List Dynamic.Value} {index : Nat} {replacement : Dynamic.Value}
    {updated : List Dynamic.Value} (changed : Dynamic.ValuesReplaceAt sources index replacement updated) :
    updated = sources.set index replacement := by
  induction changed with
  | head => rfl
  | tail _ ih => simp [List.set, ih]

private theorem projectPacked_weaken (types : List Ty) (index : Nat) (expression : Expr) :
    SourceCoreDataExpressions.projectPacked index types (expression.weakenAt 0) =
      (SourceCoreDataExpressions.projectPacked index types expression).weakenAt 0 := by
  induction types generalizing index expression with
  | nil => simp [SourceCoreDataExpressions.projectPacked, Expr.weakenAt]
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest =>
      by_cases zero : index = 0
      · simp [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt]
      · simpa [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt] using ih (index - 1) (.second expression)

private theorem comptime_parts {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world (.comptime inner) source value type) :
    ValueRep catalog signatures functions mapping world inner source value type := by
  cases represented with
  | comptime inner => exact inner
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal

theorem Path.update_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    {source updatedSource replacementSource : Dynamic.Value} {value replacement : Value}
    (represented : ValueRep checked.catalog signatures functions mapping world root source value type)
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some source) projections updatedSource)
    (environment : Environment) (store : Store) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ updatedValue finalStore administrative,
      ValueRep checked.catalog signatures functions mapping world root updatedSource updatedValue type ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression)
        (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * count := by
  induction path generalizing source value updatedSource environment store current keyExpression replacementExpression with
  | nil projected =>
    cases changed with
    | leaf modified => subst updatedSource; exact ⟨_, store, [], replacementRep, .inRight (replacementSelected.evaluates store), by simp, rfl⟩
  | @member root field leaf dataType index branches fieldType leafType name steps projections count layout fieldProjected tail ih =>
    obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
    obtain ⟨metadata, tag, sources, values, types, sourceEq, valueEq, typeEq, result, authenticated, registered, payloads⟩ :=
      represented.nominal_parts nominal
    subst source; subst value
    obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
    obtain ⟨sourceChild, valueChild, childType, sourceAt, coreAt, coreTypeAt, childRep⟩ := payloads.at fieldAt
    have childTypeEq := Except.ok.inj (childRep.projection.symm.trans fieldProjected)
    subst childType
    cases changed with
    | member selectedAt changed replaced =>
      have same := sourceAt.functional selectedAt
      subst sourceChild
      obtain ⟨child, finalStore, administrative, updatedRep, evaluated, extended, counted⟩ :=
        ih childRep replacementRep changed (packValues values :: environment) store _ (shift 1 keyExpression) (shift 1 replacementExpression)
          (projectPacked_selects (Selects.var (index := 0) rfl) (arity.trans payloads.length.2.1) index coreAt)
          (by simpa [shift] using keysSelected.weaken (packValues values))
          (by simpa [shift] using replacementSelected.weaken (packValues values))
      rw [replacement_set replaced]
      have reconstructed := DataPayload.ValueRep.constructed nominal result authenticated
        (by simpa only [owner] using represented.projection) registered
        (payloads.replace fieldAt coreTypeAt updatedRep)
      refine ⟨.constructed tag (packValues (values.set index child)), finalStore, administrative, ?_, ?_, extended, counted⟩
      · simpa only [owner] using reconstructed
      · apply Evaluates.matchData (selected.evaluates store) owner
          (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl)
        apply LanguageResult.bind_success _ evaluated
        rw [constructor]
        exact .inRight (.construct (replacePacked_evaluates (arity.trans payloads.length.2.1) (.var rfl) (.var rfl)))
  | @index keyType valueType leaf index leafType sourceKey key steps projections count certificate keyProjected valueProjected keyRelated keyAt tail ih =>
    obtain ⟨sources, entries, sourceEq, valueEq, identity, registered, contents⟩ :=
      represented.mapping_parts index.layout keyProjected valueProjected
    subst source; subst value
    have keyObserved : KeyRep certificate signatures identities sourceKey key := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact keyRelated.observation observations
    have entriesObserved : OrderedMapping.EntriesRel (KeyRep certificate signatures identities)
        (fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core index.layout.valueType)
        sources entries := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact contents.observed observations
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    have finish {sourceChild updatedChild : Dynamic.Value} {updatedEntries : List (Dynamic.Value × Dynamic.Value)}
        (read : Reads sourceKey sources valueType sourceChild)
        (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some sourceChild) projections updatedChild)
        (inserted : Dynamic.MappingInsert sourceKey updatedChild sources updatedEntries) :
        ∃ updatedValue finalStore administrative,
          ValueRep checked.catalog signatures functions mapping world (.mapping keyType valueType)
            (.mapping keyType valueType updatedEntries) updatedValue index.layout.type ∧
          Evaluates environment store (update prepared (.index index :: steps) index.layout.type current keyExpression replacementExpression)
            (.inRight .word updatedValue) finalStore ∧
          finalStore = store ++ administrative ∧ administrative.length = 2 * (checked.catalog.entries.length + 1 + count) := by
      obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyObserved entriesObserved read
        environment store current keyExpression selected keySelected
      have completeChild : ValueRep checked.catalog signatures functions mapping world valueType sourceChild child index.layout.valueType := by
        rcases childRep with childRep | ⟨expression, defaulted⟩
        · exact childRep
        · exact default_represents_at layouts valueProjected defaulted
      obtain ⟨updatedChild, childStore, childCells, updatedRep, tailEvaluated, childExtended, childCounted⟩ :=
        ih completeChild replacementRep changed (child :: environment) _ (.var 0)
          (shift 1 keyExpression) (shift 1 replacementExpression) (.var rfl)
          (by simpa [shift] using keysSelected.weaken child)
          (by simpa [shift] using replacementSelected.weaken child)
      obtain ⟨updatedValue, valueRep, insertEvaluated⟩ := DataPayload.insert_preserves observations faithful certificate.comparison
        index.layout certificate.keyType identity keyProjected valueProjected registered keyRelated updatedRep contents inserted
        (updatedChild :: child :: environment) childStore (shift 2 current)
        (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keyExpression)) (.var 0)
        (by simpa [shift, List.range_succ] using (selected.weaken child).weaken updatedChild)
        (by simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken child).weaken updatedChild) (.var rfl)
      obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
      obtain ⟨after, afterExtended, afterCounted⟩ := DataMappingComparison.helper_store_extension certificate.comparison
        (updatedChild :: child :: environment) childStore _ _ _ _
      refine ⟨updatedValue, DataMappingComparison.insertStore certificate.comparison index.layout
        (updatedChild :: child :: environment) childStore entries key updatedChild, before ++ childCells ++ after, valueRep,
        LanguageResult.bind_success _ childEvaluated (LanguageResult.bind_success _ tailEvaluated ?_), ?_, ?_⟩
      · simpa only [certificate.comparisonExpression] using insertEvaluated
      · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
        rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from afterExtended, childExtended, beforeExtended]
        simp only [List.append_assoc]
      · simp only [List.length_append, beforeCounted, afterCounted, childCounted]
        omega
    cases changed with
    | indexFound found changed inserted => exact finish (.found found) changed inserted
    | indexDefault absent defaulted changed inserted => exact finish (.default absent defaulted) changed inserted
  | comptime tail ih =>
    obtain ⟨output, finalStore, admin, represented, evaluated, extended, counted⟩ :=
      ih (comptime_parts represented) replacementRep changed environment store current keyExpression replacementExpression selected keysSelected replacementSelected
    exact ⟨output, finalStore, admin, .comptime represented, evaluated, extended, counted⟩

end Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack
/-! Commit an authenticated latest-root reconstruction through the common
GenericHeap relation. Helper initialization extends only the Core world; the
single subsequent source-cell write preserves aliases and old admin cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues GeneralHeap GenericHeap

def commit (prepared : Prepared) (keyType : Ty) (reference argument : Expr) : Expr :=
  LanguageResult.bind .unit (.apply (setter prepared keyType) argument)
    (LanguageResult.success (.storeCell (reference.weakenAt 0) (.inRight .unit (.var 0))))

private theorem source_write {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    Dynamic.Heap.Writes heap location (some value) ⟨heap.cells.set location.index {cell with value := some value}⟩ := by
  have replace : ∀ {cells : List Dynamic.Cell} {index : Nat} {old : Dynamic.Cell},
      Dynamic.Heap.CellAt cells index old →
      Dynamic.Heap.CellsWrite cells index {old with value := some value} (cells.set index {old with value := some value}) := by
    intro cells index old selected
    induction selected with
    | head => exact .head
    | tail selected ih => exact .tail ih
  cases read with
  | intro selected => exact .intro (.intro selected) (replace selected)

/-- The returned root is independently represented at the source declaration's
exact type. Core typing alone is not used to authenticate the new source value.
The path tree derives the setter execution, including every comparator and
default, before the mapped cell is written once. -/
theorem commit_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {model : PayloadModel checked.catalog}
    {prepared : Prepared} {keys : List Value} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {cell : Dynamic.Cell} {sourceLocation : Dynamic.Location} {target : Location}
    {source updatedSource replacementSource : Dynamic.Value} {optional value replacement : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (heapRelated : HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (sourceRead : Dynamic.Heap.Reads heap sourceLocation cell)
    (coreRead : store.read? target = some optional)
    (root : DataPlacePathHelpers.Root prepared cell optional source value)
    (tree : DataPlaceUpdateTree.Tree checked signatures identities prepared keys replacementSource replacement
      (fun source value => model.Represents mapping world cell.type source value prepared.route.rootType)
      source value steps projections updatedSource count)
    (sameSteps : prepared.steps = steps) (faithful : IdentityFaithful identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression argument : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) argument)
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement)))
    (leafSourceType : TypeSystem.Ty) (snapshot : Option Dynamic.Value) :
    ∃ updatedValue finalHeap finalStore futureWorld,
      Dynamic.ResolvedPlaceWrites (fun _ value => value = replacementSource) heap
        ⟨sourceLocation, cell.type, leafSourceType, projections, snapshot⟩ updatedSource finalHeap ∧
      Evaluates environment store (commit prepared keyType referenceExpression argument) (.inRight .word .unit) finalStore ∧
      WorldExtends world futureWorld ∧ HeapRepresents model mapping futureWorld finalHeap finalStore ∧
      model.Represents mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType ∧
      finalStore.read? target = some (.inRight .unit updatedValue) ∧
      AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨updatedValue, helperStore, administrative, initial, changed, represented, evaluated, extended, counted⟩ :=
    DataPlacePathHelpers.setter_preserves root tree sameSteps faithful keyLength environment store keyType argument argumentSelected
  obtain ⟨futureWorld, extension, helperHeap, _, administrativeFrame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heapRelated environmentTyped helperTyped evaluated extended
  have represented : model.Represents mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType :=
    model.extend represented (.refl _) extension
  have sourceWritten := source_write sourceRead updatedSource
  obtain ⟨finalStore, written, finalHeap, writeFrame⟩ :=
    helperHeap.write_initialized (reference.extend (.refl _) extension) sourceRead represented sourceWritten
  have helperRead : helperStore.read? target = some optional := by
    rw [extended]
    simpa [Store.read?, List.getElem?_append_left (heapRelated.target_lt reference.mapped)] using coreRead
  refine ⟨updatedValue, _, finalStore, futureWorld,
    .intro sourceRead rfl initial changed sourceWritten, ?_, extension, finalHeap, represented,
    Store.write?_reads_written written, administrativeFrame.trans writeFrame⟩
  · exact LanguageResult.bind_success _ evaluated
      (.inRight (.storeCell ((referenceSelected.weaken updatedValue).evaluates helperStore)
        helperRead (.inRight (.var rfl)) written))

end Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadWriteBack
/-! Strong payload reconstruction and writeback through the common mapped
heap. Setter arguments may read the live root through actual Core evaluation;
they are not restricted to the pure `Selects` fragment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadWriteBack
open Core Frontend Frontend.SourceInference GeneralHeap GenericHeap DataPatternValues DataEquality
open SourceCoreDataPlaces DataPayload DataPayloadReadPaths

/-- Invoke the actual closed setter after evaluating its argument. The caller
supplies the root observed by that argument and the static/source path facts;
all recursive helper evaluations are derived from the complete payload. -/
theorem setter_evaluates {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {rootType leaf : TypeSystem.Ty} {leafType : Ty} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys rootType prepared.route.rootType prepared.steps projections leaf leafType count)
    {cell : Dynamic.Cell} {optional value replacement : Value} {source updatedSource replacementSource : Dynamic.Value}
    (root : DataPlacePathHelpers.Root prepared cell optional source value)
    (represented : DataPayload.ValueRep checked.catalog signatures functions mapping world rootType source value prepared.route.rootType)
    (replacementRep : DataPayload.ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some source) projections updatedSource)
    {environment : Environment} {before store : Store} (keyType : Ty) {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (.pair (packValues keys) replacement)) store) :
    ∃ updatedValue finalStore administrative,
      DataPayload.ValueRep checked.catalog signatures functions mapping world rootType updatedSource updatedValue prepared.route.rootType ∧
      Evaluates environment before (.apply (setter prepared keyType) argument) (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * count := by
  obtain ⟨output, finalStore, admin, resultRep, evaluated, extended, counted⟩ :=
    path.update_preserves observations faithful layouts prepared keyLength represented replacementRep changed
      (value :: .pair optional (.pair (packValues keys) replacement) :: environment) store
      (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
      (.var rfl) (.first (.second (.var rfl))) (.second (.second (.var rfl)))
  cases stepsEq : prepared.steps with
  | nil =>
    have emptyEval : Evaluates (value :: .pair optional (.pair (packValues keys) replacement) :: environment) store
        (update prepared prepared.steps prepared.route.rootType (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1))))
        (.inRight .word replacement) store := by
      rw [stepsEq]
      exact .inRight (.second (.second (.var rfl)))
    have same := evaluation_deterministic evaluated emptyEval
    have valueSame := (Value.inRight.inj same.1).2
    subst output
    have storeSame := same.2
    rw [storeSame] at extended
    exact ⟨replacement, store, admin, resultRep,
      .apply .lambda argumentEvaluated (by simp only [stepsEq]; exact .inRight (.second (.second (.var rfl)))),
      extended, counted⟩
  | cons step steps =>
    refine ⟨output, finalStore, admin, resultRep, .apply .lambda argumentEvaluated ?_, extended, counted⟩
    simp only [stepsEq]
    exact .caseRight (root.normalizes (.first (.var rfl)) store) (by simpa only [stepsEq] using evaluated)

private theorem source_write {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    Dynamic.Heap.Writes heap location (some value) ⟨heap.cells.set location.index {cell with value := some value}⟩ := by
  have replace : ∀ {cells : List Dynamic.Cell} {index : Nat} {old : Dynamic.Cell},
      Dynamic.Heap.CellAt cells index old →
      Dynamic.Heap.CellsWrite cells index {old with value := some value} (cells.set index {old with value := some value}) := by
    intro cells index old selected
    induction selected with
    | head => exact .head
    | tail selected ih => exact .tail ih
  cases read with
  | intro selected => exact .intro (.intro selected) (replace selected)

/-- The completed reconstruction is written once into the mapped latest root.
The complete key/value payload survives; source aliases and all preexisting
administrative cells are preserved by the common GenericHeap laws. -/
theorem commit_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {leaf : TypeSystem.Ty} {leafType : Ty} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    {heap : Dynamic.Heap} {store : Store} {cell : Dynamic.Cell} {sourceLocation : Dynamic.Location} {target : Location}
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType prepared.steps projections leaf leafType count)
    (heapRelated : HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (sourceRead : Dynamic.Heap.Reads heap sourceLocation cell) {optional value replacement : Value}
    {source updatedSource replacementSource : Dynamic.Value} (coreRead : store.read? target = some optional)
    (root : DataPlacePathHelpers.Root prepared cell optional source value)
    (represented : DataPayload.ValueRep checked.catalog signatures functions mapping world cell.type source value prepared.route.rootType)
    (replacementRep : DataPayload.ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some source) projections updatedSource)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression argument : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) argument)
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (argumentEvaluated : Evaluates environment store argument (.pair optional (.pair (packValues keys) replacement)) store)
    (snapshot : Option Dynamic.Value) :
    ∃ updatedValue finalHeap finalStore futureWorld,
      Dynamic.ResolvedPlaceWrites (fun _ value => value = replacementSource) heap
        ⟨sourceLocation, cell.type, leaf, projections, snapshot⟩ updatedSource finalHeap ∧
      Evaluates environment store (DataPlaceWriteBack.commit prepared keyType referenceExpression argument) (.inRight .word .unit) finalStore ∧
      WorldExtends world futureWorld ∧
      HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld finalHeap finalStore ∧
      DataPayload.ValueRep checked.catalog signatures functions mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType ∧
      finalStore.read? target = some (.inRight .unit updatedValue) ∧
      AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨updatedValue, helperStore, admin, represented, evaluated, extended, counted⟩ :=
    setter_evaluates observations faithful layouts prepared keyLength path root represented replacementRep changed keyType argumentEvaluated
  obtain ⟨futureWorld, extension, helperHeap, _, administrativeFrame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heapRelated environmentTyped helperTyped evaluated extended
  have represented := represented.extend (.refl _) extension
  have sourceWritten := source_write sourceRead updatedSource
  obtain ⟨finalStore, written, finalHeap, writeFrame⟩ :=
    helperHeap.write_initialized (reference.extend (.refl _) extension) sourceRead represented sourceWritten
  have helperRead : helperStore.read? target = some optional := by
    rw [extended]
    simpa [Store.read?, List.getElem?_append_left (heapRelated.target_lt reference.mapped)] using coreRead
  refine ⟨updatedValue, _, finalStore, futureWorld,
    .intro sourceRead rfl root.initial changed sourceWritten, ?_, extension, finalHeap, represented,
    Store.write?_reads_written written, administrativeFrame.trans writeFrame⟩
  exact LanguageResult.bind_success _ evaluated
    (.inRight (.storeCell ((referenceSelected.weaken updatedValue).evaluates helperStore)
      helperRead (.inRight (.var rfl)) written))

end Solcore.SourceSemantics.CoreLowering.DataPayloadWriteBack
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot
/-! Snapshot extraction uses the actual optional cell and source root rule.
Mapping defaults remain virtual: only comparator administrative cells are
allocated by the getter. The static root-layout receipt authenticates the
empty mapping; runtime typing alone does not authenticate its source metadata.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPayloadReadPaths

inductive RootLayout (catalog : SourceCoreDataCatalog.Catalog) (prepared : Prepared) : TypeSystem.Ty → Prop where
  | ordinary {sourceType : TypeSystem.Ty}
      (notMapping : ¬ ∃ key value, sourceType = .mapping key value)
      (layout : prepared.route.rootMapping = none) : RootLayout catalog prepared sourceType
  | mapping {key value : TypeSystem.Ty} {layout : Core.OrderedMapping.Layout}
      (selected : prepared.route.rootMapping = some layout)
      (identity : catalog.identity? (.mapping key value) = some layout.dataType)
      (keyProjected : catalog.project key = .ok layout.keyType)
      (valueProjected : catalog.project value = .ok layout.valueType)
      (registered : layout.Registered catalog.definitions) : RootLayout catalog prepared (.mapping key value)

/-- The optional source snapshot is distinct from a language-result wrapper. -/
inductive OptionalRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (type : Ty) : Option Dynamic.Value → Value → Prop where
  | absent : OptionalRep catalog signatures functions mapping world sourceType type none (.inLeft type .unit)
  | present {source : Dynamic.Value} {value : Value}
      (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
      OptionalRep catalog signatures functions mapping world sourceType type (some source) (.inRight .unit value)

theorem OptionalRep.extend {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (represented : OptionalRep catalog signatures functions mapping world sourceType type source value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    OptionalRep catalog signatures functions futureMapping futureWorld sourceType type source value := by
  cases represented with
  | absent => exact .absent
  | present represented => exact .present (represented.extend maps worlds)

theorem OptionalRep.runtime_hasType {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (represented : OptionalRep catalog signatures functions mapping world sourceType type source value) :
    RuntimeValueHasType world value (OptionalCell.cellType type) catalog.definitions := by
  cases represented with
  | absent => exact .inLeft .unit
  | present represented => exact .inRight represented.runtime_hasType

theorem root_present {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {prepared : Prepared} {cell : Dynamic.Cell} {optional : Value} {source : Dynamic.Value}
    (layout : RootLayout catalog prepared cell.type)
    (represented : GenericHeap.CellRepresents (payloadModel catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (initial : Dynamic.RootInitialValue cell (some source)) :
    ∃ value, DataPlacePathHelpers.Root prepared cell optional source value ∧
      ValueRep catalog signatures functions mapping world cell.type source value prepared.route.rootType := by
  cases initial with
  | initialized =>
    cases represented with
    | initialized represented => exact ⟨_, .initialized _ _ _, represented⟩
  | emptyMapping key value =>
    cases layout with
    | ordinary notMapping => exact (notMapping ⟨key, value, rfl⟩).elim
    | @mapping _ _ coreLayout selected identity keyProjected valueProjected registered =>
      cases represented with
      | uninitialized projected =>
        have empty : ValueRep catalog signatures functions mapping world (.mapping key value)
            (.mapping key value []) (Core.OrderedMapping.encode coreLayout []) coreLayout.type :=
          .mapping identity keyProjected valueProjected registered (.empty _ _ _ _)
        have same := Except.ok.inj (empty.projection.symm.trans projected)
        exact ⟨_, by simpa only [← same] using DataPlacePathHelpers.Root.emptyMapping (prepared := prepared) key value selected,
          same ▸ empty⟩

theorem root_absent {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {prepared : Prepared} {cell : Dynamic.Cell} {optional : Value}
    (layout : RootLayout catalog prepared cell.type)
    (represented : GenericHeap.CellRepresents (payloadModel catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (initial : Dynamic.RootInitialValue cell none) :
    prepared.route.rootMapping = none ∧ optional = .inLeft prepared.route.rootType .unit := by
  cases initial with
  | uninitialized notMapping =>
    cases layout with
    | ordinary _ empty => cases represented; exact ⟨empty, rfl⟩
    | mapping => exact (notMapping ⟨_, _, rfl⟩).elim

private theorem read_present {source : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some source) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some source = initial at read
  induction read generalizing source with
  | nil => exact ⟨source, initialEq.symm⟩
  | indexFound _ _ ih => exact ih rfl
  | indexDefault _ _ _ ih => exact ih rfl
  | member _ _ ih => exact ih rfl

theorem path_empty {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {keys : List Value} {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps [] leaf leafType count) :
    steps = [] ∧ type = leafType ∧ count = 0 := by
  generalize projectionsEq : ([] : List Dynamic.EvaluatedProjection) = projections at path
  induction path with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | member => cases projectionsEq
  | index => cases projectionsEq
  | comptime _ ih => exact ih projectionsEq

/-- The argument is actually evaluated, so it may contain the live loadCell
emitted by execute. All recursive getter evaluations follow from the full
payload and independent projection trace, with no child execution premise. -/
theorem getter_evaluates {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {cell : Dynamic.Cell} {optional : Value} {initial selected : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection} {leaf : TypeSystem.Ty} {count : Nat}
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    (cellRep : GenericHeap.CellRepresents (payloadModel checked.catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (root : Dynamic.RootInitialValue cell initial)
    (read : Dynamic.ProjectionsRead initial projections selected)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    {environment : Environment} {before store : Store} {keyType : Ty} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (packValues keys)) store) :
    ∃ snapshot finalStore administrative,
      OptionalRep checked.catalog signatures functions mapping world leaf prepared.route.leafType selected snapshot ∧
      Evaluates environment before (.apply (getter prepared keyType) argument) (.inRight .word snapshot) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  cases initial with
  | none =>
    cases read
    obtain ⟨empty, same, rfl⟩ := path_empty path
    obtain ⟨noMapping, rfl⟩ := root_absent rootLayout cellRep root
    refine ⟨.inLeft prepared.route.leafType .unit, store, [], .absent, ?_, by simp, rfl⟩
    apply Evaluates.apply .lambda argumentEvaluated
    simp only [empty, normalizeRoot, noMapping, LanguageResult.success]
    rw [← same]
    exact .inRight (.first (.var rfl))
  | some source =>
    obtain ⟨sourceLeaf, rfl⟩ := read_present read
    obtain ⟨value, normalized, represented⟩ := root_present rootLayout cellRep root
    have tree := path.read_tree observations layouts prepared represented read
    obtain ⟨leafValue, finalStore, administrative, _, leafRep, evaluated, extended, counted⟩ :=
      tree.preserves faithful keyLength (value :: .pair optional (packValues keys) :: environment) store
        (.var 0) (.second (.var 1)) (.var rfl) (.second (.var rfl))
    cases stepsEq : prepared.steps with
    | nil =>
      have empty : Evaluates (value :: .pair optional (packValues keys) :: environment) store
          (select prepared prepared.steps (.var 0) (.second (.var 1))) (.inRight .word (.inRight .unit value)) store := by
        rw [stepsEq]; exact .inRight (.inRight (.var rfl))
      obtain ⟨same, stores⟩ := evaluation_deterministic evaluated empty
      have values := (Value.inRight.inj (Value.inRight.inj same).2).2
      subst leafValue
      rw [stores] at extended
      exact ⟨_, store, administrative, .present leafRep,
        .apply .lambda argumentEvaluated (by simp only [stepsEq]; exact .inRight (normalized.normalizes (.first (.var rfl)) store)),
        extended, counted⟩
    | cons step steps =>
      exact ⟨_, finalStore, administrative, .present leafRep,
        .apply .lambda argumentEvaluated (by
          simp only [stepsEq]
          exact .caseRight (normalized.normalizes (.first (.var rfl)) store) (by simpa only [stepsEq] using evaluated)),
        extended, counted⟩

/-- Read at the already resolved source reference. The runtime world fixes
the optional cell payload type even when other administrative cells coexist. -/
theorem read_at {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {target : Location} {type : Ty} {cell : Dynamic.Cell}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target type)
    (read : Dynamic.Heap.Reads heap sourceLocation cell) :
    ∃ optional, store.read? target = some optional ∧
      GenericHeap.CellRepresents model mapping world cell optional type := by
  obtain ⟨found, optional, actualType, actualReference, coreRead, represented⟩ := heaps.read read
  have locationEq := Option.some.inj (actualReference.mapped.symm.trans reference.mapped)
  subst found
  have typeEq := Option.some.inj (actualReference.typed.symm.trans reference.typed)
  have same := Ty.sum.inj typeEq
  cases same.2
  exact ⟨optional, coreRead, represented⟩

/-- Complete live-root snapshot phase. The emitted argument performs its own
load; the source heap is unchanged while the Core world includes exactly the
getter's appended administrative cells. -/
theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {heap : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {target : Location}
    {cell : Dynamic.Cell} {initial selected : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection} {leaf : TypeSystem.Ty} {count : Nat}
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap sourceLocation cell)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    (root : Dynamic.RootInitialValue cell initial)
    (selection : Dynamic.ProjectionsRead initial projections selected)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context
      (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression
      (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ snapshot finalStore futureWorld administrative,
      OptionalRep checked.catalog signatures functions mapping futureWorld leaf prepared.route.leafType selected snapshot ∧
      Evaluates environment store
        (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inRight .word snapshot) finalStore ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld heap finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨optional, coreRead, cellRep⟩ := read_at heaps reference read
  have argument : Evaluates environment store (.pair (.loadCell referenceExpression) keyExpression)
      (.pair optional (packValues keys)) store :=
    .pair (.loadCell (referenceSelected.evaluates store) coreRead) (keysSelected.evaluates store)
  obtain ⟨snapshot, finalStore, administrative, represented, evaluated, extended, counted⟩ :=
    getter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root selection path argument
  obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated extended
  exact ⟨snapshot, finalStore, futureWorld, administrative, represented.extend (.refl _) extension,
    evaluated, extension, finalHeaps, frame, extended, counted⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget
/-! The actual key vector and live-root getter implement source target
resolution. Layout is a static typing/data-layout obligation. Execution is
an output witness constructed from the universal expression theorem and the
independent source trace; it is never an input to the compiler certificate.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

private theorem packed_type (codes : List SourceCoreBasic.LoweredExpr) :
    SourceCoreDataMatches.bundleType (codes.map (·.type)) = (SourceCoreCalls.packArguments codes).type := by
  induction codes with
  | nil => rfl
  | cons code codes ih => cases codes with
    | nil => rfl
    | cons => exact congrArg (Ty.product code.type) ih

theorem values_typed {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {sourceTypes : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world sourceTypes (codes.map (·.type)) sources values) :
    RuntimeValueHasType world (packValues values) (SourceCoreCalls.packArguments codes).type catalog.definitions := by
  rw [← packed_type]
  generalize typesEq : codes.map (·.type) = types at represented ⊢
  clear typesEq codes
  induction represented with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => exact model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

/-- All fields are static metadata, compiler receipts or Core typing. Paths
instantiates those layouts with already related keys; it assumes no runtime
evaluation of a child expression, comparison, default or helper. -/
structure Layout (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (source : TypedSource)
    (certificate : Certificate) (scope : Scope) (place : PlaceResolution) (prepared : Prepared)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty) (context : Core.Context) : Prop where
  keys : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes
  keyTypes : prepared.keyTypes = codes.map (·.type)
  root : DataPlaceSnapshot.RootLayout checked.catalog prepared prepared.route.rootSourceType
  paths : ∀ {mapping world sources values projections},
    DataPlaceKeyOrder.Values place.projections sources projections →
    DataExpressionSequence.Values (payloadModel checked.catalog signatures functions) mapping world
      sourceTypes (codes.map (·.type)) sources values →
    ∃ count, DataPayloadReadPaths.Path checked signatures functions mapping world values
      prepared.route.rootSourceType prepared.route.rootType prepared.steps projections place.type prepared.route.leafType count
  getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType :: context)
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions

/-- This is a semantic output witness, including the exact code inserted by
execute. The source heap is the post-index heap throughout getter execution. -/
structure Execution (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (prepared : Prepared)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty) (place : PlaceResolution)
    (sourceTarget : Dynamic.ResolvedPlace) (environment : Environment) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (before after : Dynamic.Heap) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  snapshot : Value
  keyStore : Store
  store : Store
  mapping : LocationMap
  world : StoreTyping
  reference : ReferenceRepresents mapping world sourceTarget.location target prepared.route.rootType
  shaped : DataPlaceKeyOrder.Values place.projections sources sourceTarget.projections
  keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType target environment) initialStore
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType target (packValues values) environment) keyStore
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (.inRight .word snapshot) store
  keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions) mapping world
    sourceTypes (codes.map (·.type)) sources values
  snapshotRelated : DataPlaceSnapshot.OptionalRep checked.catalog signatures functions mapping world
    place.type prepared.route.leafType sourceTarget.selected snapshot
  heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world after store
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before after

theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (meaning : Preserves (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootType : sourceTarget.rootType = prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget after) :
    ∃ execution : Execution checked signatures functions prepared codes sourceTypes place sourceTarget coreEnvironment
      store mapping world before after,
      coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  cases trace with
  | @intro _ _ _ _ _ _ _ sourceLocation initialCell currentCell projections initial selected
      lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro i v found; exact found
    obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
      DataPlaceKeyOrder.preserves layout.keys meaning environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees sameEnvironment
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) evaluate
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment] using keyEvaluated
    have currentReference := reference.extend keyMaps keyWorlds
    obtain ⟨count, path⟩ := layout.paths shaped keysRelated
    have keyLength : prepared.keyTypes.length = values.length := layout.keyTypes ▸ keysRelated.length.2
    have rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared currentCell.type := by
      simpa only [← rootType] using layout.root
    have currentPath : DataPayloadReadPaths.Path checked signatures functions keyMap keyWorld values
        currentCell.type prepared.route.rootType prepared.steps projections place.type prepared.route.leafType count := by
      simpa only [← rootType] using path
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) checked.catalog.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) ((environments.extend keyMaps keyWorlds).runtime_hasTypes))
    obtain ⟨snapshot, finalStore, finalWorld, administrative, snapshotRelated, snapshotEvaluated,
      extension, finalHeaps, frame, _, _⟩ :=
      DataPlaceSnapshot.preserves observations faithful layouts prepared keyLength keyHeaps currentReference
        currentRead rootLayout initialValue selection currentPath typedEnvironment layout.getterTyped (.var rfl) (.var rfl)
    refine ⟨{ target := target
              sources := sources
              values := values
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := snapshotEvaluated
              keysRelated := keysRelated.extend (.refl _) extension
              snapshotRelated := snapshotRelated
              heaps := finalHeaps
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, coreLookup⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceRouteCertificates
/-! Static mixed member/index routes extracted from the real compiler.
Exact retained source types are explicit: equality of erased projections does
not by itself authenticate source nominal or mapping metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceRouteCertificates
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues
open DataPlaceMemberCertificates DataPlaceMembers

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

/-- A successful checked projection exposes both the raw projection and its
well-formedness under the actual catalog definitions. -/
theorem project_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {sourceType : TypeSystem.Ty} {type : Ty}
    (accepted : project checked site sourceType = .ok type) :
    checked.catalog.project sourceType = .ok type ∧ type.WellFormed checked.catalog.definitions := by
  unfold project SourceCoreGeneralTypes.projectType at accepted
  cases projected : checked.project sourceType with
  | error error => simp [projected, Except.map, Except.mapError] at accepted
  | ok projection =>
    simp only [projected, Except.map, Except.mapError, Except.ok.injEq] at accepted
    subst type
    refine ⟨?_, projection.typed⟩
    unfold SourceCoreDataCatalog.Checked.project at projected
    cases raw : checked.catalog.project sourceType with
    | error error => simp [raw, bind, Except.bind] at projected
    | ok actual =>
      simp only [raw, bind, Except.bind] at projected
      split at projected
      · cases projected; rfl
      · cases projected

private theorem nominal_project {catalog : SourceCoreDataCatalog.Catalog}
    {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {identity : DataTypeId}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : catalog.identity? type = some identity) : catalog.project type = .ok (.namedData identity) := by
  cases type with
  | constructor constructor =>
    cases constructor with
    | declaration => simp [SourceCoreDataCatalog.Catalog.project, selected]
    | builtin builtin => cases builtin <;> simp [SourceCoreDataCatalog.nominalParts] at nominal
  | application => simp [SourceCoreDataCatalog.Catalog.project, selected]
  | _ => simp [SourceCoreDataCatalog.nominalParts] at nominal

/-- A source metadata profile, containing no Core evaluation premises. Member
payloads retain exact source field types; each index occurrence has exactly the
mapping's retained key type, including observable type metadata. -/
inductive Profile (signatures : ProgramSignatures) (source : TypedSource) :
    TypeSystem.Ty → List PlaceProjection → TypeSystem.Ty → Prop where
  | nil {type : TypeSystem.Ty} (erased : SourceCoreDataCatalog.erase type = type) :
      Profile signatures source type [] type
  | member {root field leaf : TypeSystem.Ty} {name : String} {index : Nat}
      {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {rest : List PlaceProjection}
      (nominal : SourceCoreDataCatalog.nominalParts root = some (signature.id, arguments))
      (selected : signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (uniform : Uniform signature arguments index field)
      (tail : Profile signatures source field rest leaf) :
      Profile signatures source root (.member name index :: rest) leaf
  | index {key value leaf : TypeSystem.Ty} {id : ExpressionId} {node : ExpressionNode}
      {rest : List PlaceProjection}
      (erased : SourceCoreDataCatalog.erase (.mapping key value) = .mapping key value)
      (found : source.lookupExpression? id = some node) (typed : node.type = key)
      (tail : Profile signatures source value rest leaf) :
      Profile signatures source (.mapping key value) (.index id :: rest) leaf

theorem Profile.erased {signatures : ProgramSignatures} {source : TypedSource}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (profile : Profile signatures source root projections leaf) : SourceCoreDataCatalog.erase root = root := by
  cases profile with
  | nil erased | index erased => exact erased
  | member nominal => exact DataEqualityValues.erase_nominal nominal

/-- The emitted route with authentic source fields, actual projected types and
retained key occurrence metadata. Mapping helper preparation is a later step. -/
inductive RawPath (checked : Checked) (signatures : ProgramSignatures) (source : TypedSource) :
    TypeSystem.Ty → Ty → List Step → List PlaceProjection → TypeSystem.Ty → Ty →
      List TypeSystem.Ty → Prop where
  | nil {type : TypeSystem.Ty} {coreType : Ty}
      (projected : checked.catalog.project type = .ok coreType) :
      RawPath checked signatures source type coreType [] [] type coreType []
  | member {root field leaf : TypeSystem.Ty} {dataType : DataTypeId} {index : Nat} {name : String}
      {branches : List MemberBranch} {fieldType leafType : Ty} {steps : List Step}
      {rest : List PlaceProjection} {keys : List TypeSystem.Ty}
      (layout : MemberLayout checked signatures root field dataType index branches)
      (rootProjected : checked.catalog.project root = .ok (.namedData dataType))
      (fieldProjected : checked.catalog.project field = .ok fieldType)
      (tail : RawPath checked signatures source field fieldType steps rest leaf leafType keys) :
      RawPath checked signatures source root (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: rest) leaf leafType keys
  | index {key value leaf : TypeSystem.Ty} {layout : OrderedMapping.Layout} {id : ExpressionId}
      {node : ExpressionNode} {steps : List Step} {rest : List PlaceProjection} {leafType : Ty}
      {keys : List TypeSystem.Ty}
      (identity : checked.catalog.identity? (.mapping key value) = some layout.dataType)
      (erased : SourceCoreDataCatalog.erase (.mapping key value) = .mapping key value)
      (keyProjected : checked.catalog.project key = .ok layout.keyType)
      (valueProjected : checked.catalog.project value = .ok layout.valueType)
      (found : source.lookupExpression? id = some node) (typed : node.type = key)
      (tail : RawPath checked signatures source value layout.valueType steps rest leaf leafType keys) :
      RawPath checked signatures source (.mapping key value) layout.type
        (.index layout id value :: steps) (.index id :: rest) leaf leafType (key :: keys)

/-- Successful actual traversal produces the static mixed route. This theorem
never runs or assumes the meaning of a generated getter, comparator or default. -/
theorem raw_of_routeSteps {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {root leaf selected : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    {rootType leafType : Ty}
    (profile : Profile signatures source root projections leaf)
    (rootProjected : checked.catalog.project root = .ok rootType)
    (leafProjected : checked.catalog.project leaf = .ok leafType)
    (accepted : routeSteps checked signatures source site binder root projections = .ok (steps, selected)) :
    selected = leaf ∧ ∃ keys, RawPath checked signatures source root rootType steps projections leaf leafType keys := by
  induction profile generalizing steps selected rootType with
  | nil erased =>
    simp only [routeSteps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    have same := Except.ok.inj (rootProjected.symm.trans leafProjected)
    subst rootType
    exact ⟨rfl, [], .nil leafProjected⟩
  | @member root field leaf name index signature arguments rest nominal selectedSignature uniform tail ih =>
    simp only [routeSteps] at accepted
    obtain ⟨⟨head, chosen⟩, headAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨identity, branches, coreField, rfl, rfl, certificate⟩ :=
      certificate_of_memberStep (DataEqualityValues.erase_nominal nominal) nominal selectedSignature uniform headAccepted
    obtain ⟨⟨remaining, result⟩, tailAccepted, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    have projected := nominal_project nominal certificate.identityLookup
    have same := Except.ok.inj (rootProjected.symm.trans projected)
    subst rootType
    obtain ⟨rfl, keys, path⟩ := ih (project_facts certificate.projectedField).1 leafProjected tailAccepted
    exact ⟨rfl, keys, .member (certificate.layout nominal selectedSignature) projected
      (project_facts certificate.projectedField).1 path⟩
  | @index key value leaf id node rest erased found typed tail ih =>
    rw [routeSteps.eq_def] at accepted
    simp only [erased] at accepted
    by_cases owned : id.occurrence.owner = source.owner
    · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨coreKey, _, accepted⟩ := bind_ok accepted
      obtain ⟨projectedKey, keyProjected, accepted⟩ := bind_ok accepted
      obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
      cases checkedUnit
      obtain ⟨projectedValue, valueProjected, accepted⟩ := bind_ok accepted
      cases identity : checked.catalog.identity? (.mapping key value) with
      | none => simp [identity, throw] at accepted
      | some identityId =>
        simp only [identity] at accepted
        split at accepted
        next registered =>
          obtain ⟨⟨remaining, result⟩, tailAccepted, accepted⟩ := bind_ok accepted
          simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          have projected : checked.catalog.project (.mapping key value) = .ok (.namedData identityId) := by
            simp [SourceCoreDataCatalog.Catalog.project, identity]
          have same := Except.ok.inj (rootProjected.symm.trans projected)
          subst rootType
          obtain ⟨rfl, keys, path⟩ := ih (project_facts valueProjected).1 leafProjected tailAccepted
          exact ⟨rfl, key :: keys, .index (layout := ⟨projectedKey, projectedValue, identityId⟩) identity erased (project_facts keyProjected).1
            (project_facts valueProjected).1 found typed path⟩
        next rejected => cases accepted
    · simp [owned, throw, pure, Except.pure, bind, Except.bind] at accepted

/-- Exact key types in source projection order, including repeated occurrences. -/
inductive KeyTypes (source : TypedSource) : List PlaceProjection → List TypeSystem.Ty → Prop where
  | nil : KeyTypes source [] []
  | member {name index rest types} (tail : KeyTypes source rest types) :
      KeyTypes source (.member name index :: rest) types
  | index {id node type rest types} (found : source.lookupExpression? id = some node)
      (typed : node.type = type) (tail : KeyTypes source rest types) :
      KeyTypes source (.index id :: rest) (type :: types)

theorem RawPath.keyTypes {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {keys : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType keys) :
    KeyTypes source projections keys := by
  induction path with
  | nil => exact .nil
  | member _ _ _ _ ih => exact .member ih
  | index _ _ _ _ found typed _ ih => exact .index found typed ih

private theorem tree_cons {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope}
    {id : ExpressionId} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (id :: ids) types codes) :
    ∃ node typeTypes code restCodes, source.lookupExpression? id = some node ∧
      types = node.type :: typeTypes ∧ codes = code :: restCodes ∧
      DataExpressionSequence.Tree source certificate scope ids typeTypes restCodes := by
  cases tree with
  | single found generated => exact ⟨_, [], _, [], found, rfl, rfl, .nil⟩
  | cons found generated tail => exact ⟨_, _, _, _, found, rfl, rfl, tail⟩

theorem KeyTypes.tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope}
    {projections : List PlaceProjection} {keys types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (keyTypes : KeyTypes source projections keys)
    (tree : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes) :
    types = keys := by
  induction keyTypes generalizing types codes with
  | nil => cases tree; rfl
  | member tail ih => exact ih tree
  | @index id node type rest keys found typed tail ih =>
    obtain ⟨actual, remaining, code, restCodes, foundActual, rfl, rfl, restTree⟩ := tree_cons tree
    have same := Option.some.inj (found.symm.trans foundActual)
    subst actual
    rw [typed, ih restTree]

/-- Actual mapping preparation and the related key vector instantiate the
semantic path automatically. Key positions use the real preparation counter;
member projections leave that counter unchanged. -/
theorem RawPath.prepared_path {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType sourceTypes)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {preparedSteps : List PreparedStep}
    {preparedKeys : List (ExpressionId × Ty)} {sources : List Dynamic.Value} {values allKeys : List Value}
    {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (prepared : DataPlaceMappingPreparation.Steps checked fuel missing position steps preparedSteps preparedKeys)
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (represented : DataExpressionSequence.Values (DataPayload.payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (atPosition : ∀ i value, values[i]? = some value → allKeys[position + i]? = some value) :
    ∃ count, DataPayloadReadPaths.Path checked signatures functions mapping world allKeys
      root rootType preparedSteps evaluated leaf leafType count := by
  induction path generalizing position preparedSteps preparedKeys sources values evaluated coreTypes with
  | nil projected =>
    cases prepared
    cases shaped
    exact ⟨0, .nil projected⟩
  | member layout rootProjected fieldProjected tail ih =>
    cases prepared with
    | member prepared =>
      cases shaped with
      | member shaped =>
        obtain ⟨count, rest⟩ := ih prepared shaped represented atPosition
        exact ⟨count, .member layout fieldProjected rest⟩
  | @index key value leaf layout id node steps rest leafType types identity erased keyProjected valueProjected found typed tail ih =>
    cases prepared with
    | @index _ _ _ _ entry sourceKey registeredValue comparison default _ _ _ selected mappingType comparisonGenerated defaultGenerated prepared =>
      obtain ⟨actualEntry, actualSelected, actualType⟩ := DataEqualityValues.identity_entry identity
      have sameEntry := Option.some.inj (selected.symm.trans actualSelected)
      subst actualEntry
      rw [erased, mappingType] at actualType
      obtain ⟨keySame, valueSame⟩ := TypeSystem.Ty.mapping.inj actualType
      subst sourceKey
      subst registeredValue
      cases shaped with
      | index shaped =>
        cases represented with
        | cons head represented =>
          have headRep : DataPayload.ValueRep checked.catalog signatures functions mapping world key _ _ _ := head
          have sameType := Except.ok.inj (headRep.projection.symm.trans keyProjected)
          cases sameType
          obtain ⟨count, restPath⟩ := ih prepared shaped represented (by
            intro i v found
            simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1] using atPosition (i + 1) v found)
          refine ⟨checked.catalog.entries.length + 1 + count, .index
            (DataPlaceMappingIndex.Index.of_generated comparisonGenerated defaultGenerated keyProjected valueProjected)
            keyProjected valueProjected headRep ?_ restPath⟩
          simpa only [Nat.add_zero] using atPosition 0 _ rfl

/-- Root normalization authenticated by the actual describe branch. -/
inductive RootShape (catalog : SourceCoreDataCatalog.Catalog) :
    TypeSystem.Ty → Option OrderedMapping.Layout → Prop where
  | ordinary {sourceType : TypeSystem.Ty}
      (notMapping : ¬ ∃ key value, sourceType = .mapping key value) : RootShape catalog sourceType none
  | mapping {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
      (identity : catalog.identity? (.mapping key value) = some layout.dataType)
      (keyProjected : catalog.project key = .ok layout.keyType)
      (valueProjected : catalog.project value = .ok layout.valueType)
      (registered : layout.Registered catalog.definitions) : RootShape catalog (.mapping key value) (some layout)

theorem RootShape.layout {catalog : SourceCoreDataCatalog.Catalog} {prepared : Prepared}
    (shape : RootShape catalog prepared.route.rootSourceType prepared.route.rootMapping) :
    DataPlaceSnapshot.RootLayout catalog prepared prepared.route.rootSourceType := by
  cases prepared with
  | mk route steps keys invalid => cases route with
    | mk root rootType leafType routeSteps rootMapping =>
      cases shape with
      | ordinary notMapping => exact .ordinary notMapping rfl
      | mapping identity keyProjected valueProjected registered =>
        exact .mapping rfl identity keyProjected valueProjected registered

/-- A described route exposes its authentic root normalization and full mixed
path. The source profile is checked against the real declaration selected by
`rootBinder`, rather than an arbitrary externally supplied root type. -/
theorem described {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    (profile : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      Profile signatures source binder.scheme.body assignment.target.projections assignment.target.type)
    (accepted : describe checked signatures source site assignment = .ok route) :
    RootShape checked.catalog route.rootSourceType route.rootMapping ∧
      ∃ keys, RawPath checked signatures source route.rootSourceType route.rootType route.steps
        assignment.target.projections assignment.target.type route.leafType keys := by
  unfold describe at accepted
  dsimp only at accepted
  split at accepted
  next allowed =>
    obtain ⟨binder, binding, accepted⟩ := bind_ok accepted
    obtain ⟨rootType, rootProjected, accepted⟩ := bind_ok accepted
    obtain ⟨⟨steps, selected⟩, routed, accepted⟩ := bind_ok accepted
    split at accepted
    next compatible =>
      have sourceProfile := profile binder binding
      have erased := sourceProfile.erased
      simp only [erased] at accepted
      have finish {rootMapping : Option OrderedMapping.Layout}
          (shape : RootShape checked.catalog binder.scheme.body rootMapping)
          (finished : (do
            let leaf ← project checked site assignment.target.type
            pure (⟨binder.scheme.body, rootType, leaf, steps, rootMapping⟩ : Route)) = .ok route) :
          RootShape checked.catalog route.rootSourceType route.rootMapping ∧
            ∃ keys, RawPath checked signatures source route.rootSourceType route.rootType route.steps
              assignment.target.projections assignment.target.type route.leafType keys := by
        obtain ⟨leafType, leafProjected, finished⟩ := bind_ok finished
        simp only [pure, Except.pure, Except.ok.injEq] at finished
        subst route
        obtain ⟨_, keys, path⟩ := raw_of_routeSteps sourceProfile (project_facts rootProjected).1
          (project_facts leafProjected).1 routed
        exact ⟨shape, keys, path⟩
      cases typeEq : binder.scheme.body <;> simp only [typeEq] at accepted
      all_goals try
        exact finish (.ordinary (by
          rw [typeEq]
          rintro ⟨_, _, impossible⟩
          cases impossible)) (by simpa only [typeEq, pure, Except.pure, bind, Except.bind] using accepted)
      rename_i key value
      cases identity : checked.catalog.identity? (.mapping key value) with
      | none => simp [identity, throw, pure, Except.pure, bind, Except.bind] at accepted
      | some id =>
        simp only [identity, pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨coreKey, keyProjected, accepted⟩ := bind_ok accepted
        obtain ⟨coreValue, valueProjected, accepted⟩ := bind_ok accepted
        split at accepted
        next registered =>
          have keyFacts := project_facts keyProjected
          have valueFacts := project_facts valueProjected
          apply finish (rootMapping := some ⟨coreKey, coreValue, id⟩) ?_ ?_
          · rw [typeEq]
            exact .mapping identity keyFacts.1 valueFacts.1 ⟨keyFacts.2, valueFacts.2, registered⟩
          · simpa only [typeEq, pure, Except.pure, bind, Except.bind] using accepted
        next rejected => cases accepted
    next incompatible => cases accepted
  next rejected => cases accepted

end Solcore.SourceSemantics.CoreLowering.DataPlaceRouteCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceReadTotality
/-! Independent source read-or-fault totality for authenticated compiled paths.
It follows source ordered mappings and actual default-generation receipts,
without assuming either a source projection trace or a Core helper execution.
This is the semantic existence step needed for finite-execution reflection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceReadTotality
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates

/-- First source match or source absence, with the selected full payload.
Equivalence deliberately need not be reflexive for function/mapping keys. -/
theorem entries_lookup_or_absent {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {keyType valueType : TypeSystem.Ty} {keyCore valueCore : Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : Core.OrderedMapping.Entries}
    (related : EntriesRep catalog signatures functions mapping world keyType valueType keyCore valueCore sources entries)
    (key : Dynamic.Value) :
    (∃ selected value, Dynamic.MappingLookup key sources selected ∧
      ValueRep catalog signatures functions mapping world valueType selected value valueCore) ∨
      Dynamic.MappingAbsent key sources := by
  classical
  induction sources generalizing entries with
  | nil => cases related; exact .inr .nil
  | cons sourceEntry sources ih =>
    obtain ⟨sourceKey, sourceValue⟩ := sourceEntry
    cases related with
    | prepend keyRelated valueRelated rest =>
      by_cases equivalent : Dynamic.ValueEquivalent key sourceKey
      · exact .inl ⟨sourceValue, _, .head equivalent, valueRelated⟩
      · rcases ih rest with ⟨selected, core, found, represented⟩ | absent
        · exact .inl ⟨selected, core, .tail equivalent found, represented⟩
        · exact .inr (.cons equivalent absent)

/-- Every authenticated mixed route either selects a fully represented source
value or produces the independent missing-default fault. The initial root is
present here; absent ordinary roots and virtual mappings are handled by the
separate root normalization rules. -/
theorem read_or_fault {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType sourceTypes)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {preparedSteps : List PreparedStep}
    {preparedKeys : List (ExpressionId × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (prepared : DataPlaceMappingPreparation.Steps checked fuel missing position steps preparedSteps preparedKeys)
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    {sourceRoot : Dynamic.Value} {coreRoot : Value}
    (rootRelated : ValueRep checked.catalog signatures functions mapping world root sourceRoot coreRoot rootType) :
    (∃ selected value, Dynamic.ProjectionsRead (some sourceRoot) evaluated (some selected) ∧
      ValueRep checked.catalog signatures functions mapping world leaf selected value leafType) ∨
      ∃ reason, Dynamic.ProjectionsFaults (some sourceRoot) evaluated reason := by
  induction path generalizing position preparedSteps preparedKeys sources values evaluated coreTypes sourceRoot coreRoot with
  | nil projected => cases prepared; cases shaped; exact .inl ⟨_, _, .nil, rootRelated⟩
  | @member root field leaf dataType index name branches fieldType leafType steps rest types layout rootProjected fieldProjected tail ih =>
    cases prepared with
    | member prepared =>
      cases shaped with
      | member shaped =>
        obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
        obtain ⟨metadata, tag, sourceFields, fields, fieldTypes, sourceEq, coreEq, typeEq,
          result, authenticated, registered, payloads⟩ := rootRelated.nominal_parts nominal
        subst sourceRoot
        obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
        obtain ⟨sourceChild, coreChild, coreChildType, sourceAt, coreAt, typeAt, childRelated⟩ := payloads.at fieldAt
        have same := Except.ok.inj (childRelated.projection.symm.trans fieldProjected)
        subst coreChildType
        rcases ih prepared shaped keysRelated childRelated with ⟨selected, value, read, represented⟩ | ⟨reason, fault⟩
        · exact .inl ⟨selected, value, .member sourceAt read, represented⟩
        · exact .inr ⟨reason, .member sourceAt fault⟩
  | @index key value leaf layout id node steps rest leafType types identity erased keyProjected valueProjected found typed tail ih =>
    cases prepared with
    | @index _ _ _ _ entry sourceKey registeredValue comparison default _ _ _ selected mappingType comparisonGenerated defaultGenerated prepared =>
      cases shaped with
      | @index _ _ sourceKeyValue remainingValues evaluatedRest shaped =>
        cases keysRelated with
        | cons keyRelated keysRelated =>
          have keyRep : ValueRep checked.catalog signatures functions mapping world key _ _ _ := keyRelated
          have keyCanonical := (TypeSystem.Ty.mapping.inj erased).1
          have keyRuntime := (keyRep.source_runtimeType functionTypes keyCanonical).matches
          obtain ⟨entries, coreEntries, sourceEq, coreEq, identity, registered, contents⟩ :=
            rootRelated.mapping_parts layout keyProjected valueProjected
          subst sourceRoot
          have finish {sourceChild : Dynamic.Value} {coreChild : Value}
              (related : ValueRep checked.catalog signatures functions mapping world value sourceChild coreChild layout.valueType)
              (selected : DataPlaceMappingIndex.Reads sourceKeyValue entries value sourceChild) :
              (∃ selected coreResult, Dynamic.ProjectionsRead (some (.mapping key value entries))
                  (.index sourceKeyValue :: evaluatedRest) (some selected) ∧
                ValueRep checked.catalog signatures functions mapping world leaf selected coreResult leafType) ∨
                ∃ reason, Dynamic.ProjectionsFaults (some (.mapping key value entries))
                  (.index sourceKeyValue :: evaluatedRest) reason := by
            rcases ih prepared shaped keysRelated related with ⟨selectedValue, result, read, represented⟩ | ⟨reason, fault⟩
            · cases selected with
              | found lookup => exact .inl ⟨selectedValue, result, .indexFound lookup read, represented⟩
              | default absent defaulted => exact .inl ⟨selectedValue, result, .indexDefault absent defaulted read, represented⟩
            · cases selected with
              | found lookup => exact .inr ⟨reason, .indexFound keyRuntime lookup fault⟩
              | default absent defaulted => exact .inr ⟨reason, .indexDefault keyRuntime absent defaulted fault⟩
          rcases entries_lookup_or_absent contents _ with ⟨selected, core, lookup, represented⟩ | absent
          · exact finish represented (.found lookup)
          · obtain ⟨result, defaultMeaning, _⟩ := DataDefaults.prepared_preserves default [] []
            rw [DataPlaceMappingPreparation.default_sourceType defaultGenerated] at defaultMeaning
            cases defaultMeaning with
            | absent unavailable => exact .inr ⟨_, .indexDefaultUnavailable keyRuntime absent (by intro available; obtain ⟨v, defaulted⟩ := available.exists_default; exact unavailable v defaulted)⟩
            | present defaulted =>
              exact finish (default_represents_at layouts valueProjected defaulted) (.default absent defaulted.meaning)

end Solcore.SourceSemantics.CoreLowering.DataPlaceReadTotality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceExactFault
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog
/-! Finite catalog-entry receipts suffice for the mapping/proxy layout laws.
Outer staging erasure is handled structurally; nominal arguments and proxy
inner identities are preserved by the actual catalog's erase operation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference

theorem erase_idempotent (type : TypeSystem.Ty) :
    SourceCoreDataCatalog.erase (SourceCoreDataCatalog.erase type) = SourceCoreDataCatalog.erase type := by
  induction type <;> simp_all [SourceCoreDataCatalog.erase]

theorem identity_erase (catalog : SourceCoreDataCatalog.Catalog) (type : TypeSystem.Ty) :
    catalog.identity? (SourceCoreDataCatalog.erase type) = catalog.identity? type := by
  simp [SourceCoreDataCatalog.Catalog.identity?, erase_idempotent]

theorem project_erase_ok (catalog : SourceCoreDataCatalog.Catalog) (type : TypeSystem.Ty) (core : Ty) :
    catalog.project (SourceCoreDataCatalog.erase type) = .ok core ↔ catalog.project type = .ok core := by
  induction type generalizing core with
  | product left right first second | function left right first second =>
    cases a : catalog.project left <;> cases ae : catalog.project (SourceCoreDataCatalog.erase left) <;>
      cases b : catalog.project right <;> cases be : catalog.project (SourceCoreDataCatalog.erase right) <;>
      simp_all [SourceCoreDataCatalog.erase, SourceCoreDataCatalog.Catalog.project, bind, Except.bind, pure, Except.pure]
    all_goals
      have aSame := (first _).mp rfl
      have bSame := (second _).mp rfl
      subst_vars; rfl
  | comptime inner ih => exact ih core
  | mapping key value =>
    have identity := identity_erase catalog (.mapping key value)
    simp only [SourceCoreDataCatalog.erase] at identity ⊢
    simp only [SourceCoreDataCatalog.Catalog.project, identity]
    cases selected : catalog.identity? (.mapping key value) <;> simp [pure, Except.pure]
  | constructor | «variable» | parameter | error | application | proxy => rfl

/-- Only entries that declare a mapping or proxy need a special layout. The
same receipt can be checked once for each finite actual catalog entry. -/
def EntryLayout (catalog : SourceCoreDataCatalog.Catalog) (id : DataTypeId)
    (entry : SourceCoreDataCatalog.Entry) : Prop :=
  match entry.sourceType with
  | .proxy _ => catalog.definitions.lookupConstructorPayloadType? ⟨id, 0⟩ = some .unit
  | .mapping key value => ∃ keyType valueType,
      catalog.project key = .ok keyType ∧ catalog.project value = .ok valueType ∧
      (Core.OrderedMapping.Layout.mk keyType valueType id).Registered catalog.definitions
  | _ => True

theorem CatalogLayouts.of_entries {catalog : SourceCoreDataCatalog.Catalog}
    (entries : ∀ id entry, catalog.entries[id.index]? = some entry → EntryLayout catalog id entry) :
    CatalogLayouts catalog := by
  constructor
  · intro inner id identity
    obtain ⟨entry, selected, sourceType⟩ := DataEqualityValues.identity_entry identity
    have layout := entries id entry selected
    simp only [SourceCoreDataCatalog.erase] at sourceType
    simpa only [EntryLayout, sourceType] using layout
  · intro key value id identity
    obtain ⟨entry, selected, sourceType⟩ := DataEqualityValues.identity_entry identity
    have layout := entries id entry selected
    simp only [SourceCoreDataCatalog.erase] at sourceType
    simp only [EntryLayout, sourceType] at layout
    obtain ⟨keyType, valueType, keyProjected, valueProjected, registered⟩ := layout
    exact ⟨keyType, valueType, (project_erase_ok catalog key keyType).mp keyProjected,
      (project_erase_ok catalog value valueType).mp valueProjected, registered⟩

end Solcore.SourceSemantics.CoreLowering.DataPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceFaultTree
/-! Missing-default faults through mixed paths. Selection and update stop at
the first fault; no enclosing insertion or source-cell write runs afterwards.
All children and helper initializers are derived from structural certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceFaultTree
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

inductive Tree (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) (prepared : Prepared) (keys : List Value) :
    Dynamic.Value → Value → Ty → List PreparedStep → List Dynamic.EvaluatedProjection →
      Dynamic.SemanticFault → Word → Nat → Prop where
  | missing {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {valueRelation : OrderedMapping.Relation} {sourceKey : Dynamic.Value} {key : Value}
      {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyType : Dynamic.ValueRuntimeTypeMatches sourceKey sourceKeyType) (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (absent : Dynamic.MappingAbsent sourceKey sources) (unavailable : ¬ Dynamic.Defaultable sourceValueType) :
      Tree checked signatures identities prepared keys
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries) index.layout.type
        (.index index :: steps) (.index sourceKey :: projections) (.missingMappingDefault sourceValueType) index.missing
        (checked.catalog.entries.length + 1)
  | member {metadata : DataConstructorInstantiation} {tag : ConstructorId}
      {sources : List Dynamic.Value} {values : List Value} {branch : MemberBranch}
      {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch} {fieldType : Ty} {name : String}
      {sourceChild : Dynamic.Value} {valueChild : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
      (authenticated : checked.catalog.resolveConstructor signatures metadata = .ok tag)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (sourceArity : metadata.payloadTypes.length = sources.length)
      (coreArity : branch.payloadTypes.length = values.length)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : Tree checked signatures identities prepared keys sourceChild valueChild fieldType steps projections reason token count) :
      Tree checked signatures identities prepared keys
        (.constructed metadata sources) (.constructed tag (packValues values)) (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) reason token count
  | mapping {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {valueRelation : OrderedMapping.Relation} {sourceKey sourceChild : Dynamic.Value}
      {key : Value} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
      {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyType : Dynamic.ValueRuntimeTypeMatches sourceKey sourceKeyType) (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (selected : Reads sourceKey sources sourceValueType sourceChild)
      (tail : ∀ value, (valueRelation sourceChild value ∨
          ∃ expression, DataDefaults.Tree checked.catalog sourceValueType sourceChild value expression) →
        Tree checked signatures identities prepared keys sourceChild value index.layout.valueType steps projections reason token count) :
      Tree checked signatures identities prepared keys
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries) index.layout.type
        (.index index :: steps) (.index sourceKey :: projections) reason token
        (checked.catalog.entries.length + 1 + count)

/-- Reading and reconstruction observe the same first unavailable default.
The arbitrary replacement is never inspected along this failing path. -/
theorem Tree.preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {source : Dynamic.Value} {value : Value} {type : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : Tree checked signatures identities prepared keys source value type steps projections reason token count)
    (faithful : IdentityFaithful identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression replacement : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ finalStore administrative,
      Dynamic.ProjectionsFaults (some source) projections reason ∧
      Evaluates environment store (select prepared steps current keyExpression)
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates environment store (update prepared steps type current keyExpression replacement)
        (.inLeft type (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression replacement with
  | @missing sourceKeyType sourceValueType index certificate valueRelation sourceKey key sources entries steps projections keyRep keyType keyAt entriesRep absent unavailable =>
    have evaluated := selectedIndex_missing certificate prepared faithful keyRep entriesRep absent unavailable
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    obtain ⟨administrative, extended, counted⟩ := selectedStore_extension certificate environment store entries key
    exact ⟨_, administrative, .indexDefaultUnavailable keyType absent unavailable,
      LanguageResult.bind_failure _ evaluated, LanguageResult.bind_failure _ evaluated, extended, counted⟩
  | @member metadata tag sources values branch dataType index branches fieldType name sourceChild valueChild steps projections reason token count authenticated owner branchAt sourceArity coreArity sourceAt coreAt tail ih =>
    obtain ⟨finalStore, administrative, fault, readEvaluation, updateEvaluation, extended, counted⟩ :=
      ih (packValues values :: environment) store _ (shift 1 keyExpression) (shift 1 replacement)
        (projectPacked_selects (Selects.var (index := 0) rfl) coreArity index coreAt)
        (by simpa [shift] using keysSelected.weaken (packValues values))
    refine ⟨finalStore, administrative, .member sourceAt fault, ?_, ?_, extended, counted⟩
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) readEvaluation
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl)
        (LanguageResult.bind_failure _ updateEvaluation)
  | @mapping sourceKeyType sourceValueType index certificate valueRelation sourceKey sourceChild key sources entries steps projections reason token count keyRep keyType keyAt entriesRep read tail ih =>
    obtain ⟨child, represented, evaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep entriesRep read
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    obtain ⟨finalStore, after, fault, readEvaluation, updateEvaluation, extended, counted⟩ :=
      ih child represented (child :: environment) _ (.var 0) (shift 1 keyExpression) (shift 1 replacement) (.var rfl)
        (by simpa [shift] using keysSelected.weaken child)
    obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
    refine ⟨finalStore, before ++ after, ?_, LanguageResult.bind_success _ evaluated readEvaluation,
      LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ updateEvaluation), ?_, ?_⟩
    · cases read with
      | found lookup => exact .indexFound keyType lookup fault
      | default absent defaulted => exact .indexDefault keyType absent defaulted fault
    · rw [extended, beforeExtended, List.append_assoc]
    · simp only [List.length_append, beforeCounted, counted]

end Solcore.SourceSemantics.CoreLowering.DataPlaceFaultTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping
/-! Getter typing comes from the real enclosing Core checker. Finite-well-
formed catalog definitions alone do not authenticate nominal row completeness.
No runtime evaluation premise is used in this extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping
open Core Frontend SourceCoreDataPlaces

theorem of_execute {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    (typed : HasType context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      resultType definitions) :
    HasType (keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions := by
  unfold execute LanguageResult.bind at typed
  cases typed with
  | letE reference body =>
    cases body with
    | caseE keys failure success =>
      cases success with
      | caseE snapshot failure success =>
        cases snapshot with
        | apply function argument =>
          cases function with
          | lambda parameterTyped resultTyped body =>
            cases argument with
            | pair referenceArgument keyArgument =>
              cases referenceArgument with
              | loadCell referenceTyped =>
                cases referenceTyped with
                | var referenceAt =>
                  cases keyArgument with
                  | var keyAt =>
                    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at referenceAt keyAt
                    subst_vars
                    exact .apply (.lambda parameterTyped resultTyped body) (.pair (.loadCell (.var rfl)) (.var rfl))

/-- Direct consumer of an actual successful whole-expression inference. -/
theorem of_infer {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    (accepted : infer? context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      definitions = some resultType) :
    HasType (keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions :=
  of_execute (infer_sound accepted)

end Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceLayoutCertificates
/-! Actual place compilation and its enclosing Core checker produce the full
static layout consumed by target-resolution and assignment meaning. Children
supply static compiler certificates here, never runtime evaluations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceLayoutCertificates
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues
open DataPlaceCertificates DataPlaceRouteCertificates

/-- Every semantic-path and getter-typing field is extracted. The only source
profile assumption concerns exact retained metadata, not generated semantics. -/
theorem of_describe_prepare {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route} {prepared : Prepared}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    {context : Core.Context} {reference rhs next : Expr} {outputType resultType : Ty}
    {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand : Word}
    (profile : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      Profile signatures source binder.scheme.body assignment.target.projections assignment.target.type)
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalid missing = .ok prepared)
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (typed : HasType context (execute prepared reference (SourceCoreCalls.packArguments codes) rhs next
      outputType operator bitNot invalidOperand) resultType checked.catalog.definitions) :
    ∃ sourceTypes, DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope
      assignment.target prepared codes sourceTypes context := by
  obtain ⟨sourceTypes, tree, keyTypes⟩ := DataPlaceKeyOrder.tree_of_generated_keys described preparedBy generated extract
  obtain ⟨root, rawTypes, raw⟩ := DataPlaceRouteCertificates.described profile described
  have typesSame := raw.keyTypes.tree_types tree
  subst sourceTypes
  obtain ⟨sameRoute, _, preparation⟩ := DataPlaceMappingPreparation.steps_of_prepare preparedBy
  refine ⟨rawTypes, tree, keyTypes, ?_, ?_, DataPlaceGetterTyping.of_execute typed⟩
  · apply RootShape.layout
    simpa only [sameRoute] using root
  · intro mapping world sources values projections shaped represented
    have path := raw.prepared_path preparation shaped represented (allKeys := values) (by
      intro index value selected
      simpa only [Nat.zero_add] using selected)
    simpa only [sameRoute] using path

/-- A successful production lowering plus actual Core typing provides the
layout and the exact execute equation. The compiler is not duplicated here. -/
theorem of_lower {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope}
    {reasonAt : ExpressionId → Word} {sourceOperator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {next lowered : Expr} {outputType resultType : Ty} {invalid invalidOperand : Word}
    {missing : TypeSystem.Ty → Word} {certificate : GenericExpressionMeaning.Certificate} {context : Core.Context}
    (profile : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      Profile signatures source binder.scheme.body assignment.target.projections assignment.target.type)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (accepted : lower checked signatures expression fuel source scope site assignment sourceOperator rhs outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType context lowered resultType checked.catalog.definitions) :
    ∃ prepared codes sourceTypes index value,
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope assignment.target
        prepared codes sourceTypes context ∧
      RhsGenerated expression fuel source scope reasonAt prepared.route.leafType rhs value ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments codes) value next outputType
        (binaryOperator (prepared.route.leafType = .integer) sourceOperator) rhs.isNone invalidOperand := by
  have generated := generated_of_lower accepted
  cases generated with
  | intro route prepared index keys value described lookup preparedBy keysGenerated operatorValid rhsGenerated =>
    have sameRoute := (DataPlaceMappingPreparation.steps_of_prepare preparedBy).1
    obtain ⟨types, layout⟩ := of_describe_prepare profile described preparedBy keysGenerated extract typed
    exact ⟨prepared, keys, types, index, value, by simpa only [sameRoute] using lookup, layout,
      by simpa only [sameRoute] using rhsGenerated, by simp only [sameRoute]⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceLayoutCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceReadReflection
/-! Reflection of any completed generated selector from an authenticated
present root. The independent source read/fault is constructed, not assumed.
Fault tokens remain actual generated results; their site-table interpretation
is a separate diagnostic obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceReadReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates DataEquality

/-- Success retains the exact full leaf relation; failure retains an
independent source fault and the exact returned Core word. No source trace or
child/helper evaluation is an assumption of this reflection theorem. -/
theorem reflects {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities)
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection}
    {coreTypes : List Ty}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    {sourceRoot : Dynamic.Value} {coreRoot : Value}
    (rootRelated : ValueRep checked.catalog signatures functions mapping world root sourceRoot coreRoot rootType)
    {environment : Environment} {before after : Store} {current keys : Expr} {result : Value}
    (rootSelected : Selects environment current coreRoot)
    (keysSelected : Selects environment keys (packValues values))
    (completed : Evaluates environment before (select prepared prepared.steps current keys) result after) :
    ∃ administrative count,
      after = before ++ administrative ∧ administrative.length ≤ count ∧
      DataPayloadReadPaths.Path checked signatures functions mapping world values root rootType
        prepared.steps evaluated leaf leafType count ∧
      ((∃ selected value, Dynamic.ProjectionsRead (some sourceRoot) evaluated (some selected) ∧
          ValueRep checked.catalog signatures functions mapping world leaf selected value leafType ∧
          result = .inRight .word (.inRight .unit value)) ∨
        ∃ reason token, Dynamic.ProjectionsFaults (some sourceRoot) evaluated reason ∧
          result = .inLeft prepared.optionalLeaf (.word token)) := by
  obtain ⟨count, semanticPath⟩ := path.prepared_path preparation shaped keysRelated (allKeys := values)
    (by intro index value selected; simpa only [Nat.zero_add] using selected)
  rcases DataPlaceReadTotality.read_or_fault functionTypes layouts path preparation shaped keysRelated rootRelated with
      ⟨selected, value, read, related⟩ | ⟨reason, fault⟩
  · have tree := semanticPath.read_tree observations layouts prepared rootRelated read
    obtain ⟨actual, finalStore, administrative, _, actualRelated, ran, appended, length⟩ :=
      tree.preserves faithful keyLength environment before current keys rootSelected keysSelected
    have same := evaluation_deterministic completed ran
    rcases same with ⟨rfl, rfl⟩
    exact ⟨administrative, count, appended, by omega, semanticPath,
      .inl ⟨selected, actual, read, actualRelated, rfl⟩⟩
  · obtain ⟨token, finalStore, administrative, ran, _, appended, length⟩ :=
      semanticPath.fault_preserves observations faithful layouts prepared keyLength rootRelated fault
        environment before current keys .unit rootSelected keysSelected
    have same := evaluation_deterministic completed ran
    rcases same with ⟨rfl, rfl⟩
    exact ⟨administrative, count, appended, length, semanticPath, .inr ⟨reason, token, fault, rfl⟩⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceReadReflection
end
