import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPath
import Solcore.SourceSemantics.CoreLowering.DataPatternValues

/-! Closed ordinary getter/setter execution for a single mapping projection.
An absent mapping root is a virtual empty value; the helper does not write it
back. A setter reconstructs the supplied latest root and returns the new value.
The enclosing assignment performs the eventual source-cell write separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

/-- A helper's optional-root argument. This is a structural input certificate,
not a new heap relation; heap/world preservation uses GenericHeap. -/
inductive RootInput (layout : Core.OrderedMapping.Layout) (sourceKey sourceValue : TypeSystem.Ty)
    (keyRel valueRel : OrderedMapping.Relation) :
    Dynamic.Cell → Value → List (Dynamic.Value × Dynamic.Value) → Core.OrderedMapping.Entries → Prop where
  | initialized {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      (represented : OrderedMapping.EntriesRel keyRel valueRel sources entries) :
      RootInput layout sourceKey sourceValue keyRel valueRel
        ⟨.mapping sourceKey sourceValue, some (.mapping sourceKey sourceValue sources), none⟩
        (.inRight .unit (Core.OrderedMapping.encode layout entries)) sources entries
  | absent : RootInput layout sourceKey sourceValue keyRel valueRel
      ⟨.mapping sourceKey sourceValue, none, none⟩ (.inLeft layout.type .unit) [] []

theorem RootInput.initial {layout : Core.OrderedMapping.Layout} {sourceKey sourceValue : TypeSystem.Ty}
    {keyRel valueRel : OrderedMapping.Relation} {cell : Dynamic.Cell} {optional : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput layout sourceKey sourceValue keyRel valueRel cell optional sources entries) :
    Dynamic.RootInitialValue cell (some (.mapping sourceKey sourceValue sources)) := by
  cases input with
  | initialized => exact .initialized
  | absent => exact .emptyMapping _ _

theorem RootInput.entries {layout : Core.OrderedMapping.Layout} {sourceKey sourceValue : TypeSystem.Ty}
    {keyRel valueRel : OrderedMapping.Relation} {cell : Dynamic.Cell} {optional : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput layout sourceKey sourceValue keyRel valueRel cell optional sources entries) :
    OrderedMapping.EntriesRel keyRel valueRel sources entries := by
  cases input with
  | initialized represented => exact represented
  | absent => exact .nil

theorem RootInput.normalize {layout : Core.OrderedMapping.Layout} {sourceKey sourceValue : TypeSystem.Ty}
    {keyRel valueRel : OrderedMapping.Relation} {cell : Dynamic.Cell} {optional : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput layout sourceKey sourceValue keyRel valueRel cell optional sources entries)
    (prepared : Prepared) (rootMapping : prepared.route.rootMapping = some layout)
    {environment : Environment} {expression : Expr} (selected : Selects environment expression optional) (store : Store) :
    Evaluates environment store (normalizeRoot prepared expression)
      (.inRight .unit (Core.OrderedMapping.encode layout entries)) store := by
  simp only [normalizeRoot, rootMapping]
  cases input with
  | initialized => exact .caseRight (selected.evaluates store) (.inRight (.var rfl))
  | absent => exact .caseLeft (selected.evaluates store) (.inRight (.construct .unit))

theorem getter_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey sourceSelected : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (packValues keys))) :
    ∃ value finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsRead (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey] (some sourceSelected) ∧
      (valueRel sourceSelected value ∨ ∃ expression, DataDefaults.Tree checked.catalog sourceValue sourceSelected value expression) ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (.inRight .word (.inRight .unit value)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (packValues keys) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  obtain ⟨value, represented, evaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep input.entries read
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) keySelected
  obtain ⟨administrative, extension, count⟩ := selectedStore_extension certificate bodyEnvironment store entries key
  refine ⟨value, _, administrative, input.initial, read.projections sourceKeyType, represented, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))

theorem setter_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey sourceSelected sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement))) :
    ∃ output finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = sourceReplacement)
        (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey] (.mapping sourceKeyType sourceValue updated) ∧
      OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) (.inRight .word output) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (.pair (packValues keys) replacement) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  obtain ⟨output, finalStore, administrative, represented, evaluated, extension, count⟩ :=
    DataPlaceMappingPath.update_preserves certificate prepared faithful keyRep replacementRep input.entries read inserted
      bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
      (.var rfl) keySelected (.second (.second (.var rfl)))
  refine ⟨output, finalStore, administrative, input.initial, read.update inserted sourceKeyType, represented, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact evaluated

/-- A missing default stops the getter after its lookup. It neither creates a
virtual source mapping cell nor evaluates a leaf continuation. -/
theorem getter_missing {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (keyTyped : Dynamic.ValueRuntimeTypeMatches sourceKey sourceKeyType)
    (absent : Dynamic.MappingAbsent sourceKey sources) (missing : ¬ Dynamic.Defaultable sourceValue)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (packValues keys))) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsFaults (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey]
        (.missingMappingDefault sourceValue) ∧
      Evaluates environment store (.apply (getter prepared keyType) argument)
        (.inLeft prepared.optionalLeaf (.word index.missing)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (packValues keys) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  have evaluated := selectedIndex_missing certificate prepared faithful keyRep input.entries absent missing
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) keySelected
  obtain ⟨administrative, extension, count⟩ := selectedStore_extension certificate bodyEnvironment store entries key
  refine ⟨_, administrative, input.initial, .indexDefaultUnavailable keyTyped absent missing, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact LanguageResult.bind_failure _ evaluated

/-- The updater checks the path before replacing its leaf. Missing defaults
therefore stop before insertion, including a constant replacement. -/
theorem setter_missing {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey : Dynamic.Value} {key replacement : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (keyTyped : Dynamic.ValueRuntimeTypeMatches sourceKey sourceKeyType)
    (absent : Dynamic.MappingAbsent sourceKey sources) (missing : ¬ Dynamic.Defaultable sourceValue)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement))) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsFaults (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey]
        (.missingMappingDefault sourceValue) ∧
      Evaluates environment store (.apply (setter prepared keyType) argument)
        (.inLeft index.layout.type (.word index.missing)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (.pair (packValues keys) replacement) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  have evaluated := selectedIndex_missing certificate prepared faithful keyRep input.entries absent missing
    bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.var rfl) keySelected
  obtain ⟨administrative, extension, count⟩ := selectedStore_extension certificate bodyEnvironment store entries key
  refine ⟨_, administrative, input.initial, .indexDefaultUnavailable keyTyped absent missing, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact LanguageResult.bind_failure _ evaluated

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
