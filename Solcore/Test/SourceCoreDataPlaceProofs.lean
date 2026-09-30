import Solcore.SourceSemantics.CoreLowering.DataPlaceMemberCertificates

/-! Actual generated member helpers and independent source place semantics.
The last example observes the snapshot before the RHS and reconstruction from
the latest root, including a changed constructor and an untouched sibling. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPlaceProofs
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMembers DataPlaceCertificates DataPatternTypedValues

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"data_place_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "data_place_proofs.solc"⟩, 0, 1⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def constructorSource (name : String) : Syntax.EnumConstructor :=
  ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [
    ⟨⟨dataId, 0⟩, "A", [.integer, .integer], constructorSource "A"⟩,
    ⟨⟨dataId, 1⟩, "B", [.integer, .integer], constructorSource "B"⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [{
  sourceType := boxType
  definition := some ⟨[.product .integer .integer, .product .integer .integer]⟩
  constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩]
}] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "box", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.member "first" 0], .integer⟩, []⟩
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.integer, .integer]⟩, ⟨⟨⟨0⟩, 1⟩, [.integer, .integer]⟩]
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .integer, [.member ⟨0⟩ 0 branches .integer], none⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 branches .integer], [], Core.Word.zero⟩
private def metadata (index : Nat) : DataConstructorInstantiation := ⟨⟨dataId, index⟩, [], [.integer, .integer], boxType⟩

private theorem memberAccepted : memberStep checked signatures site binder.id boxType 0 =
    .ok (.member ⟨0⟩ 0 branches .integer, .integer) := by cbv
private theorem described : describe checked signatures source site assignment = .ok route := by cbv
private theorem preparedBy : prepare checked 20 route (Core.Word.zero) (fun _ => Core.Word.zero) = .ok prepared := by cbv

private theorem uniform : DataPlaceMemberCertificates.Uniform signature [] 0 .integer := by
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- The layout proof is extracted from successful member compilation and exact
source uniformity; no hand-supplied branch certificate or child evaluation is
needed. -/
private theorem memberLayout : MemberLayout checked signatures boxType .integer ⟨0⟩ 0 branches := by
  obtain ⟨identity, emitted, fieldType, _, sameStep, certificate⟩ :=
    DataPlaceMemberCertificates.certificate_of_memberStep (by rfl) (by rfl) (by cbv) uniform memberAccepted
  cases sameStep
  exact DataPlaceMemberCertificates.Certificate.layout (by rfl) (by cbv) certificate

private theorem routed : routeSteps checked signatures source site binder.id boxType [.member "first" 0] =
    .ok (route.steps, .integer) := by cbv
private theorem profile : DataPlaceMemberCertificates.Profile signatures boxType [.member "first" 0] .integer :=
  .member (by rfl) (by rfl) (by cbv) uniform .nil

/-- Route and prepare receipts automatically produce the exact semantic path. -/
private theorem members : Members checked signatures boxType prepared.steps [.member "first" 0] .integer := by
  obtain ⟨_, _, _, _, resolved, names, members⟩ :=
    DataPlaceMemberCertificates.route_prepare_members profile routed preparedBy
  cases names with
  | member tail => cases tail; exact members
private def sourceValue (index : Nat) (first second : Int) : Dynamic.Value :=
  .constructed (metadata index) [.integer first, .integer second]
private def coreValue (index : Nat) (first second : Int) : Core.Value :=
  .constructed ⟨⟨0⟩, index⟩ (.pair (.integer first) (.integer second))
private theorem representsA (first second : Int) :
    TypedValueRep catalog signatures boxType (sourceValue 0 first second) (coreValue 0 first second) :=
  .constructed (metadata := metadata 0) (values := [.integer first, .integer second]) (by rfl) rfl (by cbv)
    (.cons (.integer _) (.cons (.integer _) .nil))
private theorem representsB (first second : Int) :
    TypedValueRep catalog signatures boxType (sourceValue 1 first second) (coreValue 1 first second) :=
  .constructed (metadata := metadata 1) (values := [.integer first, .integer second]) (by rfl) rfl (by cbv)
    (.cons (.integer _) (.cons (.integer _) .nil))

example : Dynamic.ProjectionsRead (some (sourceValue 0 7 1)) [.member "first" 0] (some (.integer 7)) :=
  .member .head .nil
example : Dynamic.ProjectionsUpdate (fun _ updated => updated = .integer 12)
    (some (sourceValue 1 8 900)) [.member "first" 0] (sourceValue 1 12 900) :=
  .member .head (.leaf rfl) .head

/-- The helper theorem derives all generated child evaluations. Its input
representation authenticates the nominal metadata against the actual catalog. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ updatedSource updatedCore, TypedValueRep catalog signatures boxType updatedSource updatedCore ∧
      Dynamic.ProjectionsUpdate (fun _ updated => updated = .integer 12)
        (some (sourceValue 1 8 900)) [.member "first" 0] updatedSource ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply (SourceCoreDataPlaces.setter prepared .unit) (.var 0))
          (.pair (.inRight .unit (coreValue 1 8 900)) (.pair .unit (.integer 12)) :: environment) store) =
          .done (.inRight .word updatedCore) store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply (SourceCoreDataPlaces.setter prepared .unit) (.var 0))
          (.pair (.inRight .unit (coreValue 1 8 900)) (.pair .unit (.integer 12)) :: environment) store) = .done actual finalStore →
        actual = .inRight .word updatedCore ∧ finalStore = store) :=
  Members.setter_run members prepared rfl rfl (representsB 8 900) (.integer 12) environment store .unit .unit

example : Core.infer? [] (getter prepared .unit) catalog.definitions =
    some (.function (.product (.sum .unit (.namedData ⟨0⟩)) .unit) (.sum .word (.sum .unit .integer))) := by cbv
example : Core.infer? [] (SourceCoreDataPlaces.setter prepared .unit) catalog.definitions =
    some (.function (.product (.sum .unit (.namedData ⟨0⟩)) (.product .unit .integer)) (.sum .word (.namedData ⟨0⟩))) := by cbv
private def sentinel : Core.Store := [.integer 1000, .cellRef .integer 0]
example : Core.runStateful 1000 (.initial (.apply (getter prepared .unit) (.var 0))
    [.pair (.inRight .unit (coreValue 0 7 1)) .unit] sentinel) =
    .done (.inRight .word (.inRight .unit (.integer 7))) sentinel := by cbv
example : Core.runStateful 1000 (.initial (.apply (SourceCoreDataPlaces.setter prepared .unit) (.var 0))
    [.pair (.inRight .unit (coreValue 1 8 900)) (.pair .unit (.integer 12))] sentinel) =
    .done (.inRight .word (coreValue 1 12 900)) sentinel := by cbv
example : Core.runStateful 1000 (.initial (.apply (getter prepared .unit) (.var 0))
    [.pair (.inLeft (.namedData ⟨0⟩) .unit) .unit] sentinel) =
    .done (.inLeft (.sum .unit .integer) (.word (Core.Word.zero))) sentinel := by cbv

private def scope : Scope := [(binder.id, .namedData ⟨0⟩)]
private def rhsId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def rhsExpression : Core.Expr :=
  .letE (.storeCell (.var 0) (.inRight .unit (.construct ⟨⟨0⟩, 1⟩ (.pair (.integer 8) (.integer 900)))))
    (Core.LanguageResult.success (.integer 5))
private def expression : ExpressionLowerer := fun _ _ _ id _ =>
  if id = rhsId then .ok ⟨.integer, rhsExpression⟩ else .error (.missingExpression id)
private def next : Core.Expr := Core.OptionalCell.read (.namedData ⟨0⟩) (.var 0) (Core.Word.zero)
private def lowered : Core.Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhsExpression next
  (.namedData ⟨0⟩) (some .integerAdd) false (Core.Word.zero)
private theorem accepted : lower checked signatures expression 20 source scope site assignment .add (some rhsId)
    (.namedData ⟨0⟩) next (fun _ => Core.Word.zero) (Core.Word.zero) (Core.Word.zero)
    (fun _ => Core.Word.zero) = .ok lowered := by cbv
example : Generated checked signatures expression 20 source scope site assignment .add (some rhsId)
    (.namedData ⟨0⟩) next (fun _ => Core.Word.zero) (Core.Word.zero) (Core.Word.zero)
    (fun _ => Core.Word.zero) lowered := generated_of_lower accepted

/-- The RHS changes the root from A(7,1) to B(8,900). Compound addition uses
snapshot 7, then writes 12 into the latest B while preserving its second field. -/
example : Core.infer? [Core.OptionalCell.referenceType (.namedData ⟨0⟩)] lowered catalog.definitions =
    some (.sum .word (.namedData ⟨0⟩)) := by cbv
example : Core.runStateful 1000 (.initial lowered
    [.cellRef (.sum .unit (.namedData ⟨0⟩)) 0] [.inRight .unit (coreValue 0 7 1)]) =
    .done (.inRight .word (coreValue 1 12 900)) [.inRight .unit (coreValue 1 12 900)] := by cbv

end Tests.SourceCoreDataPlaceProofs
