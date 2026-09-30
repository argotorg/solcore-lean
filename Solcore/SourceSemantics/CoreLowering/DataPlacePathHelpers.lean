import Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTree

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
