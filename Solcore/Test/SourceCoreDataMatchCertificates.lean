import Solcore.SourceSemantics.CoreLowering.DataMatchCertificates
import Solcore.SourceSemantics.CoreLowering.DataMatchSourceScopes

/-! Kernel-checked extraction and representation regressions. The match fixture
uses actual metadata checks and exact callback syntax. The heap fixture keeps
a Core-only closure before a nominal source cell and allocates a hidden local
without introducing a source lexical binding. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataMatchCertificates
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"data_match_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "data_match_certificates.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutineeId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def bound : TypedBinder := ⟨⟨owner, 1⟩, "value", .mono .unit, [], false, none⟩
private def pattern : TypedMatchPattern := {
  source := .binder span "value", type := .unit, resolution := .binder bound
}
private def resolution : MatchResolution := ⟨scrutineeId, hidden, [⟨span, pattern, []⟩], some [], []⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [
    .statement ⟨site, span, .unit, .matchWith resolution⟩,
    .expression { id := scrutineeId, span, type := .unit, form := .tuple [] }]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨{}, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, ⟨[], [], [], [], [], []⟩, []⟩
private def expression : SourceCoreDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, .inRight .word .unit⟩
private def body : SourceCoreDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ =>
  .ok (Core.LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Core.Word := fun _ => Core.Word.zero
private def compiled : Core.Expr :=
  match SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution .unit reasonAt Core.Word.zero with
  | .ok code => code
  | .error _ => .unit
private theorem accepted : SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site
    resolution .unit reasonAt Core.Word.zero = .ok compiled := by rfl

/-- Callback syntax, binder order and hidden/default scopes are extracted from
the executable compiler; no source or Core child evaluation is assumed. -/
private theorem matchCertificate : DataMatchCertificates.Certificate compilation source [] site resolution .unit Core.Word.zero
    (fun _ _ value => value = ⟨.unit, .inRight .word .unit⟩)
    (fun _ _ code => code = Core.LocalLoop.fallthrough .unit) compiled := by
  apply DataMatchCertificates.certificate_of_lowerWithReasons (accepted := accepted)
  · intro _ _ _ _ accepted
    exact Except.ok.inj accepted.symm
  · intro _ _ _ _ accepted
    exact Except.ok.inj accepted.symm

example : SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [(hidden, .unit)] site
    resolution .unit reasonAt Core.Word.zero = .error (.duplicateBinding hidden) := by cbv

private def context : SourceSemantics.Context := .ofSignatures compilation.signatures
private theorem contextValid : DataPatternLeaves.ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}

/-- Whole compiler acceptance supplies ordered source selection without an
input source matching derivation or a child evaluator premise. -/
example : ∃ selection, Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody selection :=
  DataMatchDecision.Certificate.source_selects matchCertificate contextValid
    (show source.lookupExpression? resolution.scrutinee = some
      { id := scrutineeId, span, type := .unit, form := .tuple [] } from rfl)
    (DataPatternTypedValues.TypedValueRep.unit)

private def nominal : TypeSystem.Ty := .nominal dataId []
private def constructorSource : Syntax.EnumConstructor := ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.integer], constructorSource⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [{
  sourceType := nominal, definition := some ⟨[.integer]⟩, constructors := [⟨dataId, 0⟩]
}] }
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [.integer], nominal⟩
private def sourceBox (n : Int) : Dynamic.Value := .constructed metadata [.integer n]
private def coreBox (n : Int) : Core.Value := .constructed ⟨⟨0⟩, 0⟩ (.integer n)
private theorem represented (n : Int) :
    DataPatternTypedValues.TypedValueRep catalog signatures nominal (sourceBox n) (coreBox n) :=
  .constructed (catalog := catalog) (signatures := signatures) (metadata := metadata)
    (tag := ⟨⟨0⟩, 0⟩) rfl rfl (by cbv) (.cons (.integer n) .nil)
example : ∃ type, catalog.project nominal = .ok type ∧
    ∀ world, Core.RuntimeValueHasType world (coreBox (-7)) type catalog.definitions :=
  DataValueTyping.TypedValueRep.project_typed (represented (-7))

private def admin : Core.Value := .closure .unit .unit .unit []
private def adminType : Core.Ty := .function .unit .unit
private def initialWorld : Core.StoreTyping := [adminType]
private def initialStore : Core.Store := [admin]
private theorem initialHeap : DataHeap.HeapRepresents catalog signatures [] initialWorld ⟨[]⟩ initialStore :=
  DataHeap.HeapRepresents.empty.allocate_administrative (.closure .nil .unit)
private theorem initialEnv : DataHeap.EnvRepresents catalog [] initialWorld [] [] [] [] := .nil .nil
private def finalWorld : Core.StoreTyping := [adminType, Core.OptionalCell.cellType (.namedData ⟨0⟩)]
private def finalStore : Core.Store := [admin, .inRight .unit (coreBox 7)]
private def finalHeap : Dynamic.Heap := ⟨[⟨nominal, some (sourceBox 7), none⟩]⟩

/-- Source location zero maps to Core location one. The hidden Core slot does
not add an entry to the source environment. -/
private theorem hiddenAllocation :
    DataHeap.EnvRepresents catalog [1] finalWorld [] [(hidden, .namedData ⟨0⟩)] []
      [.cellRef (Core.OptionalCell.cellType (.namedData ⟨0⟩)) 1] ∧
    DataHeap.HeapRepresents catalog signatures [1] finalWorld finalHeap finalStore :=
  initialEnv.bind_internal initialHeap rfl (.initialized rfl (represented 7)) .append
example : ¬ Dynamic.Environment.LooksUp ([] : Dynamic.Environment) hidden ⟨0⟩ := by intro impossible; cases impossible
example : Core.RuntimeStoreHasTypes finalWorld finalStore catalog.definitions := hiddenAllocation.2.runtime_hasTypes
example : GeneralHeap.AdministrativePreserved [] initialStore [1] finalStore :=
  GeneralHeap.AdministrativePreserved.allocate [] initialStore (.inRight .unit (coreBox 7))

private def updatedHeap : Dynamic.Heap := ⟨[⟨nominal, some (sourceBox 9), none⟩]⟩
example : ∃ updated, finalStore.write? 1 (.inRight .unit (coreBox 9)) = some updated ∧
    DataHeap.HeapRepresents catalog signatures [1] finalWorld updatedHeap updated ∧
    GeneralHeap.AdministrativePreserved [1] finalStore [1] updated :=
  hiddenAllocation.2.write_initialized ⟨rfl, rfl⟩ (.intro .head) (represented 9)
    (.intro (.intro .head) .head)
private def boxBinder : TypedBinder := ⟨⟨owner, 2⟩, "box", .mono nominal, [], false, none⟩
private def integerBinder : TypedBinder := ⟨⟨owner, 3⟩, "integer", .mono .integer, [], false, none⟩
private def twoBinders : List (TypedBinder × Core.Ty) := [(boxBinder, .namedData ⟨0⟩), (integerBinder, .integer)]
private def boundSources : List (TypedBinder × Dynamic.Value) := [(boxBinder, sourceBox 7), (integerBinder, .integer 9)]
private def boundValues : List Core.Value := [coreBox 7, .integer 9]
private theorem bindingsRepresented : DataPatternBindings.BindingsRep catalog signatures twoBinders boundSources boundValues :=
  .cons rfl (represented 7) (.cons rfl (.integer 9) .nil)

/-- Every successful binder is allocated once, in source order. -/
example : ∃ finalEnvironment finalSourceHeap finalCanonical finalCoreStore finalMap finalCoreWorld,
    Dynamic.BindersAllocate [] finalHeap (boundSources.map Prod.fst) (boundSources.map Prod.snd)
      finalEnvironment finalSourceHeap ∧
    DataHeap.EnvRepresents catalog finalMap finalCoreWorld []
      (twoBinders.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) [(hidden, .namedData ⟨0⟩)])
      finalEnvironment finalCanonical ∧
    DataHeap.HeapRepresents catalog signatures finalMap finalCoreWorld finalSourceHeap finalCoreStore ∧
    GeneralHeap.LocationMap.Extends [1] finalMap ∧ Core.WorldExtends finalWorld finalCoreWorld ∧
    GeneralHeap.AdministrativePreserved [1] finalStore finalMap finalCoreStore :=
  DataMatchAllocation.BindingsRep.allocate bindingsRepresented hiddenAllocation.1 hiddenAllocation.2

private def selectedBody : Core.Expr := Core.OptionalCell.read .integer (.var 0) Core.Word.zero
private def selectedCode : Core.Expr :=
  SourceCoreDataMatches.bindArm twoBinders .integer (selectedBody.weakenAt twoBinders.length)
private def selectedEnvironment : Core.Environment :=
  [DataPatternValues.packValues boundValues, coreBox 7, .cellRef (Core.OptionalCell.cellType (.namedData ⟨0⟩)) 1]

/-- Two temporary slots and two source bindings must not interchange the
bundle, loaded scrutinee or last-bound Integer cell. This is actual Core code. -/
example : Core.runStateful 200 (.initial selectedCode selectedEnvironment finalStore) =
    .done (.inRight .word (.integer 9))
      [admin, .inRight .unit (coreBox 7), .inRight .unit (coreBox 7), .inRight .unit (.integer 9)] := by cbv

end Tests.SourceCoreDataMatchCertificates
