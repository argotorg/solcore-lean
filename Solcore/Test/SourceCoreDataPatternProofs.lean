import Solcore.SourceSemantics.CoreLowering.DataPatternDecision

/-! Concrete consumers of accepted pattern compilation and independent source
matching. Synthetic retained metadata makes the compiler certificate reducible;
source matching is proved separately from the Core machine execution. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPatternProofs
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

private theorem source_matches : Dynamic.PatternMatches context pattern sourceValue sourceBindings := by
  apply Dynamic.PatternMatches.intro
    (rootArity := 2) (.group (.constructor ⟨signature, by simp [context, SourceSemantics.Context.ofSignatures, signatures],
      ⟨⟨dataId, 2⟩, "Pair", [treeType, treeType], constructorSource "Pair"⟩, by simp [signature], rfl, rfl⟩))
  exact .constructor (.refl _) rfl (.cons (.constructor (.refl _) rfl (.cons .binder .nil))
    (.cons (.constructor (.refl _) rfl (.cons .binder .nil)) .nil))

private theorem represented : ValueRep catalog sourceValue coreValue :=
  .constructed (by rfl) (.cons (.constructed (by rfl) (.cons (.integer _) .nil))
    (.cons (.constructed (by rfl) (.cons (.integer _) .nil)) .nil))

/-- Compiler acceptance, independent source matching, and finite machine
execution are joined without assuming that the generated matcher evaluates. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ values, BindingsRep catalog compiled.pattern.bindings sourceBindings values ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) =
          .done (.inRight .unit (packValues values)) store) ∧
      (∀ fuel outcome finalStore,
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) =
          .done outcome finalStore → outcome = .inRight .unit (packValues values) ∧ finalStore = store) :=
  compilePattern_success_run compilation 20 source [] site span treeType pattern compiled accepted
    context rfl represented source_matches environment store

private def sentinel : Core.Store := [.integer 900, .cellRef .integer 0]
example : Core.runStateful 1000 (.initial (.apply compiled.pattern.matcher (.var 0)) [coreValue] sentinel) =
    .done (.inRight .unit (.pair (.integer 7) (.integer (-3)))) sentinel := by cbv

private def failedSource : Dynamic.Value := .constructed pairMetadata [sourceLeaf 7, .constructed emptyMetadata []]
private def failedCore : Core.Value := .constructed ⟨⟨0⟩, 2⟩ (.pair (coreLeaf 7) (.constructed ⟨⟨0⟩, 0⟩ .unit))

private theorem failed_representation : ValueRep catalog failedSource failedCore :=
  .constructed (by rfl) (.cons (.constructed (by rfl) (.cons (.integer _) .nil))
    (.cons (.constructed (by rfl) .nil) .nil))

/-- A successful first child does not leak bindings when the second constructor
mismatches. The independent source relation also rejects that exact value. -/
private theorem source_fails : Dynamic.PatternDoesNotMatch context pattern failedSource := by
  apply Dynamic.PatternDoesNotMatch.intro (rootArity := 2)
    (.group (.constructor ⟨signature, by simp [context, SourceSemantics.Context.ofSignatures, signatures],
      ⟨⟨dataId, 2⟩, "Pair", [treeType, treeType], constructorSource "Pair"⟩, by simp [signature], rfl, rfl⟩))
  refine ⟨.constructor (.succ (.constructor (.succ .binder .zero)) (.succ (.constructor (.succ .binder .zero)) .zero)), ?_⟩
  intro bindings matched
  cases matched with
  | constructor agree arity children =>
    cases children with
    | cons first rest =>
      cases first with
      | constructor firstAgree firstArity firstChildren =>
        cases firstChildren with
        | cons head tail =>
          cases head
          cases tail
          cases rest with
          | cons second last =>
            cases second with
            | constructor wrong => cases wrong.constructor_eq

example : Core.runStateful 1000 (.initial (.apply compiled.pattern.matcher (.var 0)) [failedCore] sentinel) =
    .done (.inLeft (.product .integer .integer) .unit) sentinel := by cbv


private theorem contextValid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}
private theorem leafTyped (value : Int) : TypedValueRep catalog signatures treeType (sourceLeaf value) (coreLeaf value) :=
  .constructed (metadata := leafMetadata) (values := [.integer value]) (by rfl) rfl (by cbv) (.cons (.integer _) .nil)
private theorem typedRepresentation : TypedValueRep catalog signatures treeType sourceValue coreValue :=
  .constructed (metadata := pairMetadata) (values := [coreLeaf 7, coreLeaf (-3)]) (by rfl) rfl (by cbv)
    (.cons (leafTyped 7) (.cons (leafTyped (-3)) .nil))
private theorem failedTypedRepresentation : TypedValueRep catalog signatures treeType failedSource failedCore :=
  .constructed (metadata := pairMetadata) (values := [coreLeaf 7, .constructed ⟨⟨0⟩, 0⟩ .unit]) (by rfl) rfl (by cbv)
    (.cons (leafTyped 7) (.cons (.constructed (metadata := emptyMetadata) (values := []) (by rfl) rfl (by cbv) .nil) .nil))

example (environment : Core.Environment) (store : Core.Store) :
    ∃ outcome, OutcomeRep catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply compiled.pattern.matcher (.var 0)) (coreValue :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) :=
  compilePattern_run_preserves compilation 20 source [] site span treeType pattern compiled accepted context contextValid
    typedRepresentation environment store

example (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates (failedCore :: environment) store (.apply compiled.pattern.matcher (.var 0))
      (.inLeft (.product .integer .integer) .unit) store := by
  have evaluated := compilePattern_failure_preserves compilation 20 source [] site span treeType pattern compiled accepted
    context contextValid failedTypedRepresentation source_fails environment store
  simpa only [Pattern.bindingTypes, bindings_order, List.map_cons, List.map_nil, bundleType] using evaluated

private def tupleType : TypeSystem.Ty := .product treeType (.product .bool .integer)
private def tuplePattern : TypedMatchPattern := {
  source := .tuple span 2
  type := tupleType
  resolution := .tuple [.constructor leafMetadata 1, .binder left, .tuple 2, .wildcard, .binder right]
}
private def tupleCompiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span tupleType tuplePattern with
  | .ok result => result
  | .error _ => fallback
private theorem tupleAccepted : compilePattern compilation 20 source [] site span tupleType tuplePattern = .ok tupleCompiled := by cbv
private def tupleSource : Dynamic.Value := .product (sourceLeaf 7) (.product (.bool true) (.integer (-3)))
private def tupleCore : Core.Value := .pair (coreLeaf 7) (.pair (.bool true) (.integer (-3)))
private theorem tupleSourceMatches : Dynamic.PatternMatches context tuplePattern tupleSource sourceBindings :=
  .intro .tuple (.tuple (.cons (.singleton _)) rfl
    (.cons (.constructor (.refl _) rfl (.cons .binder .nil))
      (.cons (.tuple (.cons (.singleton _)) rfl (.cons .wildcard (.cons .binder .nil))) .nil)))
private theorem tupleRepresents : ValueRep catalog tupleSource tupleCore :=
  .product (.constructed (by rfl) (.cons (.integer _) .nil)) (.product (.bool _) (.integer _))

example : ∃ values, BindingsRep catalog tupleCompiled.pattern.bindings sourceBindings values ∧
    MatcherRuns tupleCompiled.pattern tupleCore values :=
  compilePattern_success_preserves compilation 20 source [] site span tupleType tuplePattern tupleCompiled
    tupleAccepted context rfl tupleRepresents tupleSourceMatches

example : Core.runStateful 1000 (.initial (.apply tupleCompiled.pattern.matcher (.var 0)) [tupleCore] sentinel) =
    .done (.inRight .unit (.pair (.integer 7) (.integer (-3)))) sentinel := by cbv

/-- Repeated root groups preserve the arity of the nested tuple pattern. -/
private def groupedTuplePattern : TypedMatchPattern :=
  { tuplePattern with source := .group span (.group span tuplePattern.source) }
private def groupedTupleCompiled : CertifiedPattern catalog.definitions :=
  match compilePattern compilation 20 source [] site span tupleType groupedTuplePattern with
  | .ok result => result
  | .error _ => fallback
private theorem groupedTupleAccepted :
    compilePattern compilation 20 source [] site span tupleType groupedTuplePattern = .ok groupedTupleCompiled := by cbv

/-- The static certificate comes from the actual compiler, including the root
instruction arity and both nested child certificates. -/
example : DataPatternCertificates.Certificate compilation source [] site span tupleType groupedTuplePattern
    groupedTupleCompiled.pattern :=
  DataPatternCertificates.certificate_of_compilePattern compilation 20 source [] site span tupleType
    groupedTuplePattern groupedTupleCompiled groupedTupleAccepted

private theorem groupedTupleSourceMatches :
    Dynamic.PatternMatches context groupedTuplePattern tupleSource sourceBindings := by
  cases tupleSourceMatches with
  | intro spelling matched => exact .intro (.group (.group spelling)) matched

private theorem tupleTypedRepresents : TypedValueRep catalog signatures tupleType tupleSource tupleCore :=
  .product (leafTyped 7) (.product (.bool _) (.integer _))

/-- Independent source matching determines the finite Core result with the
same binder order and the original store, for arbitrary surrounding state. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ values, BindingsRep catalog groupedTupleCompiled.pattern.bindings sourceBindings values ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done (.inRight .unit (packValues values)) store) ∧
      (∀ fuel outcome finalStore,
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done outcome finalStore →
        outcome = .inRight .unit (packValues values) ∧ finalStore = store) :=
  compilePattern_success_run compilation 20 source [] site span tupleType groupedTuplePattern groupedTupleCompiled
    groupedTupleAccepted context rfl tupleRepresents groupedTupleSourceMatches environment store

example (environment : Core.Environment) (store : Core.Store) :
    ∃ outcome, OutcomeRep catalog context groupedTuplePattern groupedTupleCompiled.pattern tupleSource outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
          (tupleCore :: environment) store) = .done actual finalStore → actual = outcome ∧ finalStore = store) :=
  compilePattern_run_preserves compilation 20 source [] site span tupleType groupedTuplePattern groupedTupleCompiled
    groupedTupleAccepted context contextValid tupleTypedRepresents environment store

example : Core.runStateful 1000 (.initial (.apply groupedTupleCompiled.pattern.matcher (.var 0))
    [tupleCore] sentinel) = .done (.inRight .unit (.pair (.integer 7) (.integer (-3)))) sentinel := by cbv

end Tests.SourceCoreDataPatternProofs
