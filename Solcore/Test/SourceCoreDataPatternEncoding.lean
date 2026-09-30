import Solcore.SourceSemantics.CoreLowering.DataPatternEncoding
import Solcore.SourceSemantics.CoreLowering.DataPatternParametricLeaves

/-! Concrete consumers of accepted pattern compilation and independent source
matching. Synthetic retained metadata makes the compiler certificate reducible;
source matching is proved separately from the Core machine execution. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPatternEncoding
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataMatches DataPatternValues DataPatternLeaves DataPatternExecution DataPatternSuccess
open DataPatternTypedValues DataPatternDecision

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"data_pattern_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "data_pattern_proofs.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def treeType : TypeSystem.Ty := .nominal dataId []
private def constructorSource (name : String) : Syntax.EnumConstructor :=
  ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Tree", parameters := []
  constructors := [
    ⟨⟨dataId, 0⟩, "Empty", [], constructorSource "Empty"⟩,
    ⟨⟨dataId, 1⟩, "Leaf", [.integer], constructorSource "Leaf"⟩,
    ⟨⟨dataId, 2⟩, "Pair", [treeType, treeType], constructorSource "Pair"⟩]
  source := ⟨span, ⟨none, ⟨span, "Tree"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [{
  sourceType := treeType
  definition := some ⟨[.unit, .integer, .product (.namedData ⟨0⟩) (.namedData ⟨0⟩)]⟩
  constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩, ⟨dataId, 2⟩]
}] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, signatures, []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [] }
private def left : TypedBinder := ⟨⟨owner, 0⟩, "left", .mono .integer, [], false, none⟩
private def right : TypedBinder := ⟨⟨owner, 1⟩, "right", .mono .integer, [], false, none⟩
private def emptyMetadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [], treeType⟩
private def leafMetadata : DataConstructorInstantiation := ⟨⟨dataId, 1⟩, [], [.integer], treeType⟩
private def pairMetadata : DataConstructorInstantiation := ⟨⟨dataId, 2⟩, [], [treeType, treeType], treeType⟩
private def pattern : TypedMatchPattern := {
  source := .group span (.constructor span (some span) [] "Pair" 2)
  type := treeType
  resolution := .constructor pairMetadata
    [.constructor leafMetadata 1, .binder left, .constructor leafMetadata 1, .binder right]
}
private def fallback : CertifiedPattern catalog.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)
}
private def compiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span treeType pattern with
  | .ok result => result
  | .error _ => fallback

private theorem accepted : compilePattern compilation 20 source [] site span treeType pattern = .ok compiled := by cbv
private theorem bindings_order : compiled.pattern.bindings = [(left, .integer), (right, .integer)] := by cbv

private def sourceLeaf (value : Int) : Dynamic.Value := .constructed leafMetadata [.integer value]
private def coreLeaf (value : Int) : Core.Value := .constructed ⟨⟨0⟩, 1⟩ (.integer value)
private def sourceValue : Dynamic.Value := .constructed pairMetadata [sourceLeaf 7, sourceLeaf (-3)]
private def coreValue : Core.Value := .constructed ⟨⟨0⟩, 2⟩ (.pair (coreLeaf 7) (coreLeaf (-3)))
private def sourceBindings : List (TypedBinder × Dynamic.Value) := [(left, .integer 7), (right, .integer (-3))]


open DataPatternEncoding
private def publicLeaf (value : Int) : PublicValue := .constructed leafMetadata [.integer value]
private def publicTree : PublicValue := .constructed pairMetadata [publicLeaf 7, publicLeaf (-3)]
private theorem publicProfile : CarrierProfile publicTree :=
  .constructed (by intro type member; simp [pairMetadata] at member; subst type; exact .nominal (by rfl))
    (.cons (.constructed (by intro type member; simp [leafMetadata] at member; subst type; exact .integer) (.cons (.integer _) .nil))
      (.cons (.constructed (by intro type member; simp [leafMetadata] at member; subst type; exact .integer) (.cons (.integer _) .nil)) .nil))
private theorem publicMeaning : Means publicTree sourceValue :=
  .constructed (.cons (.constructed (.cons (.integer _) .nil)) (.cons (.constructed (.cons (.integer _) .nil)) .nil))
private theorem encoded : SourceCoreDataValues.encode 30 ⟨checked, signatures⟩ treeType publicTree = .ok coreValue := by cbv
private theorem decoded : SourceCoreDataValues.decode 30 ⟨checked, signatures⟩ treeType coreValue = .ok publicTree := by cbv
private theorem contextValid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}

/-- The exact independent value is extracted from the real public encoder. -/
example : TypedValueRep catalog signatures treeType sourceValue coreValue := by
  obtain ⟨dynamic, meaning, represented⟩ := encode_represents (.nominal (by rfl)) publicProfile encoded
  have same := Means.functional meaning publicMeaning
  exact same ▸ represented

example : TypedValueRep catalog signatures treeType sourceValue coreValue := by
  obtain ⟨dynamic, meaning, represented⟩ := decode_represents (.nominal (by rfl)) publicProfile decoded
  have same := Means.functional meaning publicMeaning
  exact same ▸ represented

/-- No manual constructor or matcher correspondence certificate is supplied. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ sourceValue outcome, Means publicTree sourceValue ∧
      OutcomeRep catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) :=
  encode_matcher_run_preserves compilation 20 30 source [] site span treeType pattern compiled accepted context contextValid
    (.nominal (by rfl)) publicProfile encoded environment store

private def functionType : TypeSystem.Ty := .function .integer .integer
private def functionBinder : TypedBinder := ⟨⟨owner, 2⟩, "callback", .mono functionType, [], false, none⟩
private def functionPattern : TypedMatchPattern := ⟨.binder span "callback", functionType, .binder functionBinder, []⟩
private def functionCompiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span functionType functionPattern with
  | .ok result => result
  | .error _ => fallback
private theorem functionAccepted : compilePattern compilation 20 source [] site span functionType functionPattern = .ok functionCompiled := by cbv

/-- Function binding transports any already established value/capture relation;
the matcher itself makes no assumptions about the closure representation. -/
example (relation : Dynamic.Value → Core.Value → Prop) {sourceValue : Dynamic.Value} {value : Core.Value}
    (represented : relation sourceValue value) :
    ∃ bindings values, Dynamic.PatternMatches context functionPattern sourceValue bindings ∧
      DataPatternParametricLeaves.BindingsRelated relation functionCompiled.pattern.bindings bindings values ∧
      MatcherRuns functionCompiled.pattern value values :=
  DataPatternParametricLeaves.compilePattern_preserves compilation 20 source [] site span functionType functionPattern
    functionCompiled functionAccepted context rfl (.binder functionBinder) relation represented

end Tests.SourceCoreDataPatternEncoding
