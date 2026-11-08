import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Frontend.Fragments.Internal.RuntimeParameters
import Solcore.Frontend.Fragments.Internal.Computation
import Solcore.Frontend.Fragments.Internal.RecursiveComputation
import Solcore.Core.Fuel
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Test.Frontend.ComputationRuntime
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Frontend.Fragments.Internal.ReturnBodies
import Solcore.Frontend.Fragments.Internal.LocalComputations
import Solcore.Frontend.Fragments.Internal.SourceValues
import Solcore.Resolved.LocalScope

/-!
# Computation owner tests

Owner transport for computations: bodies, raw owners, function owners, scoped shadowing and source
computation bodies.
-/

section
-- leanmerge: from Solcore.Test.FrontendCompilationOwnerProperties
/-! Type-only owner changes preserve complete compilation observations even
when the declared nominal parameter has no runtime argument inhabitant. -/

set_option autoImplicit false

namespace Tests.FrontendCompilationOwner

open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StaticOwners", by decide⟩], by decide⟩⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "static-owners.sol"⟩, 31, 7⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def parameters := [parameter "c" "Bool", parameter "x" "Arg", parameter "y" "Arg"]
private def types (type : Core.Ty) : TypeNameTable := [(["Arg"], type), (["Result"], type), (["Bool"], .bool)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def body (conditional : Bool) : Syntax.Block :=
  if conditional then ⟨span, [⟨span, .ifThen (ref "c") (returned "x") (some (returned "y"))⟩]⟩ else returned "x"
private def declaration (conditional : Bool) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "choose"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Result"]⟩⟩, none⟩, body conditional⟩⟩
private def inputs (id : Resolved.DeclarationId) (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh id "c" .bool).bindFresh id "x" type).bindFresh id "y" type
private theorem freshOne (id : Resolved.DeclarationId) :
    Resolved.freshLocalId id [⟨id, 0⟩] = ⟨id, 1⟩ :=
  congrArg (Resolved.LocalId.mk id) (Resolved.freshLocalId_cons_fresh_binderIndex id [])
private theorem freshTwo (id : Resolved.DeclarationId) :
    Resolved.freshLocalId id [⟨id, 1⟩, ⟨id, 0⟩] = ⟨id, 2⟩ := by
  have indices := Resolved.freshLocalId_cons_fresh_binderIndex id [⟨id, 0⟩]
  rw [freshOne] at indices
  change (Resolved.freshLocalId id [⟨id, 1⟩, ⟨id, 0⟩]).binderIndex = 2 at indices
  exact congrArg (Resolved.LocalId.mk id) indices
private theorem inputs_ids (id : Resolved.DeclarationId) (type : Core.Ty) :
    (inputs id type).ids = [⟨id, 2⟩, ⟨id, 1⟩, ⟨id, 0⟩] := by
  simp only [inputs, LocalTypeInputs.bindFresh_ids, LocalTypeInputs.empty_ids,
    Resolved.freshLocalId_empty, freshOne, freshTwo]
private def core (conditional : Bool) : Core.Expr := if conditional then .ifE (.var 2) (.var 1) (.var 0) else .var 1
private def compiled (id : Resolved.DeclarationId) (type : Core.Ty) (conditional : Bool) : CompiledRuntimeFunction :=
  ⟨inputs id type, core conditional, type⟩
private theorem indices_ne (id : Resolved.DeclarationId) {a b : Nat} (different : a ≠ b) :
    (⟨id, a⟩ : Resolved.LocalId) ≠ ⟨id, b⟩ := fun same => different (congrArg Resolved.LocalId.binderIndex same)
private theorem declared (id : Resolved.DeclarationId) (type : Core.Ty) :
    RuntimeParametersDeclare (types type) id parameters (inputs id type) :=
  .cons (.named (.tail (by decide) (.tail (by decide) .head))) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named .head) (by change "x" ∉ ["c"]; decide)
      (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil))
private theorem elaborated (id : Resolved.DeclarationId) (type : Core.Ty) (conditional : Bool) :
    TerminalReturnTreeElaborates (inputs id type).names (inputs id type).context (body conditional) (core conditional) type := by
  have names : (inputs id type).names = [("y", ⟨id, 2⟩), ("x", ⟨id, 1⟩), ("c", ⟨id, 0⟩)] := by
    simp only [inputs, LocalTypeInputs.bindFresh_names, LocalTypeInputs.bindFresh_ids,
      LocalTypeInputs.empty_names, LocalTypeInputs.empty_ids, Resolved.freshLocalId_empty, freshOne, freshTwo]
  have context : (inputs id type).context = [(⟨id, 2⟩, type), (⟨id, 1⟩, type), (⟨id, 0⟩, .bool)] := by
    simp only [inputs, LocalTypeInputs.bindFresh_context, LocalTypeInputs.bindFresh_ids,
      LocalTypeInputs.empty_context, LocalTypeInputs.empty_ids, Resolved.freshLocalId_empty, freshOne, freshTwo]
  rw [names, context]
  have x : ReturnBodyElaborates (inputs id type).names (inputs id type).context (returned "x") (.var 1) type :=
    by rw [names, context]; exact .expression (.identifier (.tail (by decide) .head))
        (.var (.tail (indices_ne id (by decide)) .head)) (.var (.tail (indices_ne id (by decide)) .head))
  rw [names, context] at x
  cases conditional
  · exact .single x
  · exact .conditional (.identifier (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (indices_ne id (by decide)) (.tail (indices_ne id (by decide)) .head)))
      (.var (.tail (indices_ne id (by decide)) (.tail (indices_ne id (by decide)) .head))) (.single x)
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (id : Resolved.DeclarationId) (type : Core.Ty) (conditional : Bool) :
    RuntimeFunctionCompiles (types type) id (declaration conditional) (compiled id type conditional) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
    declared id type, TypedLetReturnBodyElaborates.returnTree <| .terminal (elaborated id type conditional)⟩
private def projection (output : CompiledRuntimeFunction) := (output.core, output.returnType, output.inputs.context.values)

theorem arbitrary_types_have_independent_static_provenance_and_open_core_typing
    (id : Resolved.DeclarationId) (type : Core.Ty) (conditional : Bool) (definitions : Core.DataEnvironment) :
    RuntimeParametersDeclare (types type) id parameters (inputs id type) ∧
    RuntimeFunctionCompiles (types type) id (declaration conditional) (compiled id type conditional) ∧
    compileRuntimeFunction? (types type) id (declaration conditional) = some (compiled id type conditional) ∧
    Core.HasType [type, type, .bool] (core conditional) type definitions ∧
    ¬ Core.HasType [] (core conditional) type definitions := by
  refine ⟨declared id type, compilation id type conditional, (compilation id type conditional).complete, ?_, ?_⟩
  · cases conditional
    · exact .var rfl
    · exact .ifE (.var rfl) (.var rfl) (.var rfl)
  · intro closed
    cases conditional
    · cases closed with | var found => cases found
    · cases closed with | ifE condition _ _ => cases condition with | var found => cases found

theorem static_rows_and_bundles_retain_identity_composition_and_exact_projections
    (row : LocalTypeBinding) (supplied : LocalTypeInputs) (first second : Resolved.LocalId → Resolved.LocalId)
    (fi : Function.Injective first) (si : Function.Injective second) :
    row.mapIds id = row ∧ (row.mapIds first).mapIds second = row.mapIds (second ∘ first) ∧
    supplied.mapIds id (fun _ _ same => same) = supplied ∧
    (supplied.mapIds first fi).mapIds second si = supplied.mapIds (second ∘ first) (si.comp fi) ∧
    (supplied.mapIds first fi).bindings = supplied.bindings.map (LocalTypeBinding.mapIds first) ∧
    (supplied.mapIds first fi).ids = supplied.ids.map first ∧
    (supplied.mapIds first fi).names = LocalNameTable.mapIds first supplied.names ∧
    (supplied.mapIds first fi).context = Resolved.LocalScope.mapIds first supplied.context :=
  ⟨row.mapIds_id, row.mapIds_comp first second, supplied.mapIds_id, supplied.mapIds_comp first second fi si,
    supplied.mapIds_bindings first fi, supplied.mapIds_ids first fi,
    supplied.mapIds_names first fi, supplied.mapIds_context first fi⟩

theorem empty_start_declarations_and_both_body_shapes_transport_without_arguments
    (id : Resolved.DeclarationId) (type : Core.Ty) (conditional : Bool)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    RuntimeParametersDeclare (types type) (mapping id) parameters
      ((inputs id type).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) ∧
    RuntimeFunctionCompiles (types type) (mapping id) (declaration conditional)
      { compiled id type conditional with inputs := ((inputs id type).mapIds
          (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) } :=
  ⟨(declared id type).map_owner mapping injective, (compilation id type conditional).mapOwner mapping injective⟩

private def moveOwner (id : Resolved.DeclarationId) : Resolved.DeclarationId := { id with declarationIndex := id.declarationIndex + 7 }
private theorem moveOwner_injective : Function.Injective moveOwner := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
theorem changed_owners_change_ids_but_keep_binder_indices_spellings_and_type_order (type : Core.Ty) :
    let mapped := (inputs (owner 0) type).mapIds (ownerLocalIdMap moveOwner)
      (ownerLocalIdMap_injective moveOwner moveOwner_injective)
    mapped.ids = [⟨owner 7, 2⟩, ⟨owner 7, 1⟩, ⟨owner 7, 0⟩] ∧
    mapped.ids.map (·.binderIndex) = [2, 1, 0] ∧ mapped.names.map Prod.fst = ["y", "x", "c"] ∧
    mapped.context.values = [type, type, .bool] ∧ mapped.ids ≠ (inputs (owner 0) type).ids := by
  intro mapped
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro same
  have first := congrArg (fun ids => ids.head?.map (·.owner.declarationIndex)) same
  change some 7 = some 0 at first
  cases first

theorem complete_optional_projection_agrees_but_identity_bearing_outputs_differ
    (leftOwner rightOwner : Resolved.DeclarationId) (different : leftOwner ≠ rightOwner)
    (type : Core.Ty) (conditional : Bool) :
    (compileRuntimeFunction? (types type) leftOwner (declaration conditional)).map projection =
      (compileRuntimeFunction? (types type) rightOwner (declaration conditional)).map projection ∧
    (compileRuntimeFunction? (types type) leftOwner (declaration conditional)).map projection =
      some (core conditional, type, [type, type, .bool]) ∧
    compiled leftOwner type conditional ≠ compiled rightOwner type conditional := by
  refine ⟨compileRuntimeFunction?_owner_projection_eq _ _ _ _, ?_, ?_⟩
  · rw [(compilation leftOwner type conditional).complete]; rfl
  · intro same
    have heads := congrArg (fun output => output.inputs.ids.head?.map (·.owner)) same
    change some leftOwner = some rightOwner at heads
    exact different (Option.some.inj heads)

private theorem nominal_argument_absent (dataType : Core.DataTypeId) :
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData dataType := by
  rintro ⟨⟨type, value, typed⟩, same⟩
  cases same
  cases typed with
  | constructed found _ =>
      simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
theorem nominal_both_body_compilations_need_no_runtime_inhabitant
    (leftOwner rightOwner : Resolved.DeclarationId) (dataType : Core.DataTypeId) (conditional : Bool) :
    compileRuntimeFunction? (types (.namedData dataType)) leftOwner (declaration conditional) =
      some (compiled leftOwner (.namedData dataType) conditional) ∧
    (compileRuntimeFunction? (types (.namedData dataType)) leftOwner (declaration conditional)).map projection =
      (compileRuntimeFunction? (types (.namedData dataType)) rightOwner (declaration conditional)).map projection ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData dataType :=
  ⟨(compilation leftOwner _ conditional).complete, compileRuntimeFunction?_owner_projection_eq _ _ _ _,
    nominal_argument_absent dataType⟩

theorem no_actual_input_bundle_can_be_reconstructed_from_the_nominal_static_context
    (id : Resolved.DeclarationId) (dataType : Core.DataTypeId) :
    ¬ ∃ supplied : LocalInputs, supplied.toTypeInputs = inputs id (.namedData dataType) := by
  rintro ⟨supplied, erased⟩
  have contexts := congrArg LocalTypeInputs.context erased
  rw [LocalInputs.toTypeInputs_context] at contexts
  cases supplied with
  | mk bindings distinct =>
    cases bindings with
    | nil => cases contexts
    | cons first rest =>
      have sameType := congrArg Prod.snd (List.cons.inj contexts).1
      exact nominal_argument_absent dataType ⟨⟨first.type, first.value, first.valueTyped⟩, sameType⟩

private def missing : Syntax.FunctionDecl := ⟨span,
  ⟨(declaration true).value.signature, ⟨span, [⟨span, .ifThen (ref "c") (returned "x") (some (returned "missing"))⟩]⟩⟩⟩
theorem invalid_unselected_arm_remains_none_for_every_owner_and_type
    (leftOwner rightOwner : Resolved.DeclarationId) (type : Core.Ty) :
    compileRuntimeFunction? (types type) leftOwner missing = none ∧
    compileRuntimeFunction? (types type) rightOwner missing = none := by
  have rejected : compileRuntimeFunction? (types type) leftOwner missing = none := by
    apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, accepted⟩
    have sameInputs := accepted.parameters.result_unique (declared leftOwner type)
    have checked := accepted.body.complete
    rw [sameInputs] at checked
    simp [elaborateTypedLetReturnTree?, elaborateReturnBody?,
      elaborateLocalExpression?, resolveLocalExpression?, missing, returned, ref, inputs, LocalTypeInputs.names,
      LocalTypeInputs.context, LocalTypeInputs.bindFresh, LocalTypeInputs.empty, LocalNameTable.lookup?] at checked
  refine ⟨rejected, ?_⟩
  have same := compileRuntimeFunction?_owner_projection_eq (types type) leftOwner rightOwner missing
  rw [rejected] at same
  cases right : compileRuntimeFunction? (types type) rightOwner missing with
  | none => rfl
  | some output => simp only [right, Option.map_none, Option.map_some, reduceCtorEq] at same

theorem erasure_commutes_only_for_already_supplied_inputs
    (supplied : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (supplied.mapIds mapping injective).toTypeInputs = supplied.toTypeInputs.mapIds mapping injective ∧
    (supplied.toTypeInputs.mapIds mapping injective).context.values = supplied.context.values := by
  refine ⟨supplied.toTypeInputs_mapIds mapping injective, ?_⟩
  rw [LocalTypeInputs.mapIds_context, Resolved.LocalScope.values_mapIds, supplied.toTypeInputs_context]

private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 10 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl
theorem injective_static_relabeling_does_not_commute_with_fresh_allocation
    (id : Resolved.DeclarationId) (type : Core.Ty) :
    (LocalTypeInputs.empty.bindFresh id "x" type).mapIds shift shift_injective ≠
      (LocalTypeInputs.empty.mapIds shift shift_injective).bindFresh id "x" type := by
  intro same
  have indices := congrArg (fun supplied => supplied.ids.map (·.binderIndex)) same
  change [10] = [0] at indices
  cases indices

theorem equal_core_and_types_do_not_license_a_shifted_handmade_compilation
    (id : Resolved.DeclarationId) (type : Core.Ty) (conditional : Bool) :
    let forged := { compiled id type conditional with inputs := (inputs id type).mapIds shift shift_injective }
    forged.core = (compiled id type conditional).core ∧ forged.inputs.context.values = [type, type, .bool] ∧
    ¬ RuntimeFunctionCompiles (types type) id (declaration conditional) forged := by
  intro forged
  refine ⟨rfl, ?_, ?_⟩
  · simp only [forged, LocalTypeInputs.mapIds_context, Resolved.LocalScope.values_mapIds]; rfl
  · intro claimed
    have sameInputs := claimed.parameters.result_unique (declared id type)
    have indices := congrArg (fun supplied => supplied.ids.map (·.binderIndex)) sameInputs
    simp only [forged, LocalTypeInputs.mapIds_ids, inputs_ids, List.map_cons, List.map_nil, shift,
      Nat.reduceAdd] at indices
    cases indices

end Tests.FrontendCompilationOwner
end

section
-- leanmerge: from Solcore.Test.FrontendComputationBodyOwnerBoundaryProperties
/-! Sparse same-owner indices and arbitrarily large foreign indices are not
interchangeable. Owner covariance preserves fresh allocation; arbitrary
injective changes to binder indices need not. Actual rows are never rebuilt. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyOwnerBoundary
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"BodyOwnerBoundary",by decide⟩],by decide⟩⟩,130⟩
private def foreign : Resolved.DeclarationId := { owner with declarationIndex := 131 }
private def ident (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"body-owner-boundary.sol"⟩,31,173⟩
private def inputs (a : Core.Ty) (high : Nat) : LocalTypeInputs :=
  ⟨[⟨"x",ident 7,a⟩,⟨"x",⟨foreign,high⟩,.bool⟩,⟨"old",ident 2,.word⟩],by simp [ident,owner,foreign]⟩
private def first (a : Core.Ty) (high : Nat) := (inputs a high).bindFresh owner "x" a
private def second (a : Core.Ty) (high : Nat) := (first a high).bindFresh owner "x" a
private def names (high : Nat) : LocalNameTable := [("x",ident 7),("x",⟨foreign,high⟩),("old",ident 2)]
private def ref : Syntax.Expr := ⟨span,.identifier ⟨span,"x"⟩⟩
private def named : Syntax.TypeExpr := ⟨span,.named ⟨span,⟨⟨⟨span,"A"⟩,[]⟩⟩⟩ none⟩
private def source : Syntax.Block := ⟨span,[
  ⟨span,.letDecl ⟨span,"x"⟩ (some named) (some ref)⟩,
  ⟨span,.letDecl ⟨span,"x"⟩ none (some ref)⟩,
  ⟨span,.returnStmt (some ref)⟩]⟩
private def core : Core.Expr := .letE (.var 0) (.letE (.var 0) (.var 0))
private def types (a : Core.Ty) : TypeNameTable := [(["A"],a)]
private theorem original (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) source core a :=
  .binding (.named .head) (.pure (.identifier .head) (.var .head) (.var .head))
    (.inferred (.pure (.identifier .head) (.var .head) (.var .head))
      (.expression (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem originalTyped (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) source a :=
  .binding (.named .head) (.pure (.identifier .head .head))
    (.inferred (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head))))
private def shifted (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex+200 }
private theorem shiftedInjective : Function.Injective shifted := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private def map := ownerLocalIdMap shifted
private theorem mapInjective : Function.Injective map := ownerLocalIdMap_injective shifted shiftedInjective

theorem fresh_owner_filter_ignores_arbitrary_foreign_indices_and_repeated_spellings
    (a : Core.Ty) (high : Nat) :
    Resolved.freshLocalId owner (inputs a high).ids=ident 8 ∧
    Resolved.freshLocalId owner (first a high).ids=ident 9 ∧
    (second a high).ids=[ident 9,ident 8,ident 7,⟨foreign,high⟩,ident 2] ∧
    (second a high).bindings.map (fun b => (b.name,b.type))=
      [("x",a),("x",a),("x",a),("x",.bool),("old",.word)] := by
  exact ⟨rfl,rfl,rfl,rfl⟩
theorem each_initializer_reads_the_old_head_before_its_own_fresh_binding
    (a : Core.Ty) (high : Nat) :
    (inputs a high).names.lookup? "x"=some (ident 7) ∧
    (first a high).names.lookup? "x"=some (ident 8) ∧
    (second a high).names.lookup? "x"=some (ident 9) ∧
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) source a ∧
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) source core a :=
  ⟨rfl,rfl,rfl,originalTyped a high,original a high⟩
theorem nonsurjective_owner_shift_keeps_indices_spelling_type_and_order
    (a : Core.Ty) (high : Nat) :
    Function.Injective shifted ∧ (¬ ∃ id,shifted id={ owner with declarationIndex := 0 }) ∧
    ((inputs a high).mapIds map mapInjective).ids=
      [⟨shifted owner,7⟩,⟨shifted foreign,high⟩,⟨shifted owner,2⟩] ∧
    ((inputs a high).mapIds map mapInjective).bindings.map (fun b => (b.name,b.type))=
      [("x",a),("x",.bool),("old",.word)] := by
  refine ⟨shiftedInjective,?_,rfl,rfl⟩
  rintro ⟨id,same⟩
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change id.declarationIndex+200=0 at impossible
  omega
theorem repeated_fresh_binding_and_body_transport_keep_the_literal_core
    (a : Core.Ty) (high : Nat) :
    (second a high).mapIds map mapInjective=
      (((inputs a high).mapIds map mapInjective).bindFresh (shifted owner) "x" a).bindFresh (shifted owner) "x" a ∧
    RecursiveComputationReturnTreeHasType (types a) (shifted owner) ((inputs a high).mapIds map mapInjective) source a ∧
    RecursiveComputationReturnTreeElaborates (types a) (shifted owner) ((inputs a high).mapIds map mapInjective) source core a ∧
    elaborateRecursiveComputationReturnTree? (types a) (shifted owner)
      ((inputs a high).mapIds map mapInjective) source=some (core,a) := by
  refine ⟨?_,(computationReturnTreeHasType_mapOwner_iff shifted shiftedInjective
      (recursiveLocalComputationHasType_mapIds_iff map mapInjective)).mpr (originalTyped a high),
    (computationReturnTreeElaborates_mapOwner_iff shifted shiftedInjective
      (recursiveLocalComputationElaborates_mapIds_iff map mapInjective)).mpr (original a high),?_⟩
  · exact (LocalTypeInputs.bindFresh_mapOwner (first a high) owner shifted shiftedInjective "x" a).trans
      (congrArg (fun i => i.bindFresh (shifted owner) "x" a)
        (LocalTypeInputs.bindFresh_mapOwner (inputs a high) owner shifted shiftedInjective "x" a))
  · exact (elaborateComputationReturnTree?_mapOwner shifted shiftedInjective elaborateRecursiveLocalComputation?
      (elaborateRecursiveLocalComputation?_mapIds map mapInjective) _ _ _ _).trans
        ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original a high))
private def environment (high : Nat) (v other old : Core.Value) : Resolved.Environment :=
  [(ident 7,v),(⟨foreign,high⟩,other),(ident 2,old)]
theorem original_actual_rows_and_seven_step_path_are_independent_of_static_types
    (high : Nat) (v other old : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (names high) (environment high v other old) store source v store 7 ∧
    (Resolved.LocalScope.mapIds map (environment high v other old)).values=[v,other,old] ∧
    Core.Steps 7 ⟨.eval core [v,other,old],k,store⟩ ⟨.ret v,k,store⟩ := by
  refine ⟨?_,rfl,CostStepComposition.letE (.cons (.var rfl) .refl)
      (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))⟩
  refine .binding (initializerCost := 1) (tailCost := 4) (boundValue := v) (middleStore := store) ?_ ?_
  · exact .pure (.identifier .head .head)
  · refine .inferred (initializerCost := 1) (tailCost := 1) (boundValue := v) (middleStore := store) ?_ ?_
    · exact .pure (.identifier .head .head)
    · exact .expression (.pure (.identifier .head .head))

private def zero := Core.Word.ofNatModulo 0
private def one := Core.Word.ofNatModulo 1
private def returned : Syntax.Block := ⟨span,[⟨span,.returnStmt (some ref)⟩]⟩
private def literalArm : Syntax.MatchCase := ⟨span,⟨⟨span,.literal ⟨span,.decimal "1"⟩⟩,returned⟩⟩
private def wildcardArm : Syntax.MatchCase := ⟨span,⟨⟨span,.group ⟨span,.wildcard span⟩⟩,returned⟩⟩
private def matchSource : Syntax.Block := ⟨span,[⟨span,.matchWith
  ⟨span,⟨⟨span,.literal ⟨span,.decimal "0"⟩⟩,[]⟩⟩
  ⟨span,⟨[literalArm,wildcardArm],some returned⟩⟩⟩]⟩
private def matchCore : Core.Expr :=
  .letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 1) (.var 1))
private theorem zeroDenotes : WordLiteralDenotes ⟨span,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private theorem literalClassifies : WordMatchPatternClassifies literalArm.value.pattern (some one) :=
  .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)⟩
private theorem matchOriginal (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) matchSource matchCore a := by
  refine .wordMatch (entries := [(literalArm,some one,.var 0),(wildcardArm,none,.var 0)])
    (defaultEntry := some (returned,.var 0)) (.pure (.wordLiteral zeroDenotes) .word .word)
    rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact literalClassifies
    · exact .group (.wildcard rfl)
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      exact .expression (.pure (.identifier .head) (.var .head) (.var .head))
  · intro entry member
    simp only [Option.toList_some,List.mem_singleton] at member
    subst entry
    exact .expression (.pure (.identifier .head) (.var .head) (.var .head))
  · simp [Core.Expr.weakenAt]
private theorem matchType (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) matchSource a := by
  refine .wordMatch (.pure (.wordLiteral zeroDenotes)) ?_ (.inl rfl) (.inl rfl) ?_ ?_
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨some one,literalClassifies⟩
    · exact ⟨none,.group (.wildcard rfl)⟩
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .expression (.pure (.identifier .head .head))
  · intro entry member
    simp only [Option.toList_some,List.mem_singleton] at member
    subst entry
    exact .expression (.pure (.identifier .head .head))
theorem tagged_rows_keep_order_and_all_original_branches_in_both_owner_directions
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (a : Core.Ty) (high : Nat) :
    RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) matchSource a ∧
    RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) matchSource matchCore a ∧
    (RecursiveComputationReturnTreeHasType (types a) (mapping owner)
      ((inputs a high).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) matchSource a ↔
      RecursiveComputationReturnTreeHasType (types a) owner (inputs a high) matchSource a) ∧
    (RecursiveComputationReturnTreeElaborates (types a) (mapping owner)
      ((inputs a high).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) matchSource matchCore a ↔
      RecursiveComputationReturnTreeElaborates (types a) owner (inputs a high) matchSource matchCore a) :=
  ⟨matchType a high,matchOriginal a high,
    computationReturnTreeHasType_mapOwner_iff mapping injective
      (recursiveLocalComputationHasType_mapIds_iff _ (ownerLocalIdMap_injective mapping injective)),
    computationReturnTreeElaborates_mapOwner_iff mapping injective
      (recursiveLocalComputationElaborates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))⟩
theorem the_original_miss_then_wildcard_costs_one_comparison_not_two
    (high : Nat) (v other old : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    WordMatchChooses (.word zero) [literalArm,wildcardArm] (some returned) returned 1 ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (names high) (environment high v other old) store matchSource v store 11 ∧
    Core.Steps 11 ⟨.eval matchCore [v,other,old],k,store⟩ ⟨.ret v,k,store⟩ := by
  have selection : WordMatchChooses (.word zero) [literalArm,wildcardArm] (some returned) returned 1 :=
    .miss literalClassifies (by decide) (.wildcard (.group (.wildcard rfl)))
  refine ⟨selection,?_,CostStepComposition.letE (.cons .word .refl)
    (CostStepComposition.ifFalse (CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) rfl)
      (.cons (.var rfl) .refl))⟩
  refine .wordMatch (scrutineeCost := 1) (branchCost := 1) (tests := 1)
    (.pure (.wordLiteral zeroDenotes)) selection ?_
  exact .expression (.pure (.identifier .head .head))

private def indexShift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex+10 }
private theorem indexInjective : Function.Injective indexShift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl
private def onlyForeign (a : Core.Ty) (high : Nat) : LocalTypeInputs :=
  ⟨[⟨"x",⟨foreign,high⟩,a⟩],by simp⟩
theorem arbitrary_injective_index_changes_do_not_commute_with_fresh_binding
    (a : Core.Ty) (high : Nat) :
    Function.Injective indexShift ∧
    (((onlyForeign a high).bindFresh owner "x" a).mapIds indexShift indexInjective).ids=
      [ident 10,⟨foreign,high+10⟩] ∧
    (((onlyForeign a high).mapIds indexShift indexInjective).bindFresh owner "x" a).ids=
      [ident 0,⟨foreign,high+10⟩] ∧
    ((onlyForeign a high).bindFresh owner "x" a).mapIds indexShift indexInjective ≠
      ((onlyForeign a high).mapIds indexShift indexInjective).bindFresh owner "x" a := by
  refine ⟨indexInjective,rfl,rfl,?_⟩
  intro same
  have ids := congrArg LocalTypeInputs.ids same
  have firstId := (List.cons.inj ids).1
  have impossible := congrArg Resolved.LocalId.binderIndex firstId
  exact (by decide : (10 : Nat)≠0) impossible
theorem the_fresh_counterexample_still_satisfies_concrete_child_covariance
    (a : Core.Ty) (high : Nat) :
    elaborateRecursiveLocalComputation? (onlyForeign a high).names (onlyForeign a high).context ref=some (.var 0,a) ∧
    elaborateRecursiveLocalComputation? ((onlyForeign a high).mapIds indexShift indexInjective).names
      ((onlyForeign a high).mapIds indexShift indexInjective).context ref=some (.var 0,a) := by
  have originalChild : RecursiveLocalComputationElaborates (onlyForeign a high).names (onlyForeign a high).context ref (.var 0) a :=
    .pure (.identifier .head) (.var .head) (.var .head)
  refine ⟨elaborateRecursiveLocalComputation?_iff.mpr originalChild,?_⟩
  exact (elaborateRecursiveLocalComputation?_mapIds indexShift indexInjective _ _ _).trans
    (elaborateRecursiveLocalComputation?_iff.mpr originalChild)
end Tests.FrontendComputationBodyOwnerBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendComputationBodyOwnerProperties
/-! Original repeated typed/inferred lets, discard, scope barrier, conditional
and grouped-wildcard/default rows have independent typing and elaboration.
Only this variable/literal fixture preserves stores. No raw owner law is used. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyOwner
open Solcore Solcore.Frontend
private def types (a : Core.Ty) : TypeNameTable := [(["A"],a)]
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,"A"⟩,[]⟩⟩⟩ none⟩
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def zero := Core.Word.ofNatModulo 0
private def literal (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal "0"⟩⟩
private theorem denotes (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private def condition (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.binary (literal s) ⟨s,.equal⟩ (literal s)⟩
private def guardCore : Core.Expr := .binary .wordEq (.word zero) (.word zero)
private def returned (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some (ref s))⟩]⟩
private def arm (s : Syntax.SourceSpan) : Syntax.MatchCase := ⟨s,⟨⟨s,.group ⟨s,.wildcard s⟩⟩,returned s⟩⟩
private def matched (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨literal s,[]⟩⟩ ⟨s,⟨[arm s],some (returned s)⟩⟩⟩]⟩
private def scopeBlock (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.block (matched s).value⟩]⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.expression (ref s) true⟩,⟨s,.ifThen (condition s) (scopeBlock s) (some (returned s))⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s)) (some (ref s))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s))⟩::statements s n
private def beforeDiscard : Core.Expr := .ifE guardCore (.letE (.word zero) (.var 1)) (.var 0)
private def core : Nat → Core.Expr
  | 0 => .letE (.var 0) (.ifE guardCore (.letE (.word zero) (.var 2)) (.var 1))
  | n+1 => .letE (.var 0) (.letE (.var 0) (core n))
private theorem discardShift : beforeDiscard.weakenAt 0=.ifE guardCore (.letE (.word zero) (.var 2)) (.var 1) := by
  simp [beforeDiscard,guardCore,Core.Expr.weakenAt]
private theorem protection (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    ComputationNamesProtected (i.names.map Prod.fst) (scopeBlock s) :=
  computationBlockPreservesNames_iff.mp (by simp only [scopeBlock,computationBlockPreservesNames])
private theorem guardElab (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    RecursiveLocalComputationElaborates i.names i.context (condition s) guardCore .bool :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))) (.binary .word .word) (.binary .word .word)
private theorem guardTyped (s : Syntax.SourceSpan) (i : LocalTypeInputs) :
    RecursiveLocalComputationHasType i.names i.context (condition s) .bool :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s)))
private theorem matchElab (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s) (.var 0) a) :
    RecursiveComputationReturnTreeElaborates (types a) o i (matched s) (.letE (.word zero) (.var 1)) a := by
  refine .wordMatch (entries := [(arm s,none,.var 0)]) (defaultEntry := some (returned s,.var 0))
    (.pure (.wordLiteral (denotes s)) .word .word) rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .group (.wildcard rfl)
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression leaf
  · intro entry member; simp only [Option.toList_some,List.mem_singleton] at member; subst entry; exact .expression leaf
  · simp [Core.Expr.weakenAt]
private theorem matchTyped (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (leaf : RecursiveLocalComputationHasType i.names i.context (ref s) a) :
    RecursiveComputationReturnTreeHasType (types a) o i (matched s) a := by
  refine .wordMatch (.pure (.wordLiteral (denotes s))) ?_ (.inl rfl) (.inl rfl) ?_ ?_
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨none,.group (.wildcard rfl)⟩
  · intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression leaf
  · intro entry member; simp only [Option.toList_some,List.mem_singleton] at member; subst entry; exact .expression leaf
private theorem elaborated (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId)
    (n : Nat) (i : LocalTypeInputs) (leaf : RecursiveLocalComputationElaborates i.names i.context (ref s) (.var 0) a) :
    RecursiveComputationReturnTreeElaborates (types a) o i ⟨s,statements s n⟩ (core n) a := by
  induction n generalizing i with
  | zero =>
      change RecursiveComputationReturnTreeElaborates _ _ _ _ (.letE (.var 0) _) _
      rw [← discardShift]
      exact .discard leaf (.conditional (guardElab s i) (protection s i) (.block (matchElab s a o i leaf)) (.expression leaf))
  | succ n ih =>
      exact .binding (.named .head) leaf (.inferred (.pure (.identifier .head) (.var .head) (.var .head))
        (ih ((i.bindFresh o "x" a).bindFresh o "x" a) (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem typed (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId)
    (n : Nat) (i : LocalTypeInputs) (leaf : RecursiveLocalComputationHasType i.names i.context (ref s) a) :
    RecursiveComputationReturnTreeHasType (types a) o i ⟨s,statements s n⟩ a := by
  induction n generalizing i with
  | zero => exact .discard leaf (.conditional (guardTyped s i) (protection s i) (.block (matchTyped s a o i leaf)) (.expression leaf))
  | succ n ih =>
      exact .binding (.named .head) leaf (.inferred (.pure (.identifier .head .head))
        (ih ((i.bindFresh o "x" a).bindFresh o "x" a) (.pure (.identifier .head .head))))
private theorem guardCost (s : Syntax.SourceSpan) (names : LocalNameTable) (e : Resolved.Environment) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names e store (condition s) (.bool true) store 5 :=
  .pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s)))
private def freshNames (o : Resolved.DeclarationId) (names : LocalNameTable) := ("x",Resolved.freshLocalId o (names.map Prod.snd))::names
private def freshEnv (o : Resolved.DeclarationId) (names : LocalNameTable) (e : Resolved.Environment) (v : Core.Value) :=
  (Resolved.freshLocalId o (names.map Prod.snd),v)::e
private theorem raw (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : Nat)
    (names : LocalNameTable) (e : Resolved.Environment) (v : Core.Value) (store : Core.Store)
    (leaf : RecursiveLocalComputationEvaluatesWithCost names e store (ref s) v store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o names e store ⟨s,statements s n⟩ v store (6*n+14) := by
  induction n generalizing names e with
  | zero =>
      refine .discard (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (expressionCost := 1) (tailCost := 11) leaf ?_
      exact .ifTrue (conditionCost := 5) (branchCost := 4) (guardCost s names e store)
        (.block (ComputationReturnTreeEvaluatesWithCost.wordMatch (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          (scrutineeCost := 1) (branchCost := 1) (tests := 0)
          (.pure (.wordLiteral (denotes s))) (.wildcard (.group (.wildcard rfl))) (.expression leaf)))
  | succ n ih =>
      have count : 6*(n+1)+14=1+(1+(6*n+14)+2)+2 := by omega
      rw [count]
      exact .binding leaf (.inferred (.pure (.identifier .head .head))
        (ih (freshNames o (freshNames o names)) (freshEnv o (freshNames o names) (freshEnv o names e v) v)
          (.pure (.identifier .head .head))))
private theorem manual (n : Nat) (v : Core.Value) (rest : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (6*n+14) ⟨.eval (core n) (v::rest),k,store⟩ ⟨.ret v,k,store⟩ := by
  induction n generalizing rest k with
  | zero =>
      exact CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.ifTrue (CostStepComposition.binary (.cons .word .refl) (.cons .word .refl) rfl)
          (CostStepComposition.letE (.cons .word .refl) (.cons (.var rfl) .refl)))
  | succ n ih =>
      have count : 6*(n+1)+14=1+(1+(6*n+14)+2)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::v::rest) k))
private def start (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) := i.bindFresh o "x" a
private theorem original (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    RecursiveComputationReturnTreeElaborates (types a) o (start o i a) ⟨s,statements s n⟩ (core n) a :=
  elaborated s a o n (start o i a) (.pure (.identifier .head) (.var .head) (.var .head))

theorem original_typing_and_elaboration_are_independently_constructed
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    RecursiveComputationReturnTreeHasType (types a) o (start o i a) ⟨s,statements s n⟩ a ∧
    RecursiveComputationReturnTreeElaborates (types a) o (start o i a) ⟨s,statements s n⟩ (core n) a :=
  ⟨typed s a o n (start o i a) (.pure (.identifier .head .head)),original s a o i n⟩
theorem owner_transport_keeps_both_independent_judgments_and_all_original_branches
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    let changed := (start o i a).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
    RecursiveComputationReturnTreeHasType (types a) (mapping o) changed ⟨s,statements s n⟩ a ∧
    RecursiveComputationReturnTreeElaborates (types a) (mapping o) changed ⟨s,statements s n⟩ (core n) a :=
  ⟨(computationReturnTreeHasType_mapOwner_iff mapping injective
      (recursiveLocalComputationHasType_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr
      (original_typing_and_elaboration_are_independently_constructed s a o i n).1,
    (computationReturnTreeElaborates_mapOwner_iff mapping injective
      (recursiveLocalComputationElaborates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr (original s a o i n)⟩
theorem complete_checker_keeps_the_literal_core_after_owner_transport
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n : Nat) :
    elaborateRecursiveComputationReturnTree? (types a) (mapping o)
      ((start o i a).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      ⟨s,statements s n⟩=some (core n,a) :=
  (elaborateComputationReturnTree?_mapOwner mapping injective elaborateRecursiveLocalComputation?
    (elaborateRecursiveLocalComputation?_mapIds _ (ownerLocalIdMap_injective mapping injective)) _ _ _ _).trans
      ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (original s a o i n))
theorem original_raw_cost_and_handwritten_path_do_not_use_an_owner_transport_law
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : Nat) (names : LocalNameTable) (e : Resolved.Environment)
    (v : Core.Value) (rest : Core.Environment) (store : Core.Store) (k : List Core.Frame)
    (leaf : RecursiveLocalComputationEvaluatesWithCost names e store (ref s) v store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost o names e store ⟨s,statements s n⟩ v store (6*n+14) ∧
    Core.Steps (6*n+14) ⟨.eval (core n) (v::rest),k,store⟩ ⟨.ret v,k,store⟩ :=
  ⟨raw s o n names e v store leaf,manual n v rest store k⟩
theorem complete_machine_records_use_literal_core_and_unchanged_actual_values
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (a : Core.Ty) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (n fuel : Nat)
    (e : Resolved.Environment) (store : Core.Store) :
    (elaborateRecursiveComputationReturnTree? (types a) (mapping o)
      ((start o i a).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) ⟨s,statements s n⟩).map
      (fun (ce,t) => (t,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) e).values store)))=
      some (a,Core.runStateful fuel (.initial (core n) e.values store)) := by
  rw [complete_checker_keeps_the_literal_core_after_owner_transport mapping injective s a o i n,Option.map_some,Resolved.LocalScope.values_mapIds]
theorem exact_fuel_and_all_genuine_resumptions_keep_actual_payloads
    (n fuel extra : Nat) (v : Core.Value) (rest : Core.Environment) (store : Core.Store) :
    (Core.runStateful fuel (.initial (core n) (v::rest) store)=.done v store ↔ 6*n+14≤fuel) ∧
    ∀ cp, Core.runStateful fuel (.initial (core n) (v::rest) store)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core n) (v::rest) store) :=
  ⟨(manual n v rest store []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem first_initializer_finishes_in_its_original_environment
    (n : Nat) (v : Core.Value) (rest : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    let e := v::rest
    let cp : Core.State := ⟨.ret v,.letBody (.letE (.var 0) (core n)) e::k,store⟩
    Core.runStateful 2 ⟨.eval (core (n+1)) e,k,store⟩=.outOfFuel cp ∧
    ∀ extra, Core.runStateful extra cp=Core.runStateful (2+extra) ⟨.eval (core (n+1)) e,k,store⟩ := by
  have path : Core.Steps 2 ⟨.eval (core (n+1)) (v::rest),k,store⟩
      ⟨.ret v,.letBody (.letE (.var 0) (core n)) (v::rest)::k,store⟩ := .cons .enterLet (.cons (.var rfl) .refl)
  have stopped := Core.runStateful_outOfFuel_complete path (show Core.advance _=.next _ from rfl)
  exact ⟨stopped,Core.runStateful_resume stopped⟩
end Tests.FrontendComputationBodyOwner
end

section
-- leanmerge: from Solcore.Test.FrontendComputationBodyRawOwnerBoundaryProperties
/-! These artificial child interfaces test the generic contract, not Core
semantics. A cost interface need not erase into an uncosted interface, nor must
an uncosted interface possess a cost. Raw absence is not a fault classification. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyRawOwnerBoundary
open Solcore Solcore.Frontend
private abbrev Eval := LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop
private abbrev Cost := LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop
private def allRaw : Eval := fun _ _ _ _ _ _ => True
private def noRaw : Eval := fun _ _ _ _ _ _ => False
private def allCost : Cost := fun _ _ _ _ _ _ _ => True
private def noCost : Cost := fun _ _ _ _ _ _ _ => False
private def returned (span : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Block := ⟨span,[⟨span,.returnStmt (some e)⟩]⟩

theorem generic_uncosted_transport_requires_no_cost_existence_bridge
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment)
    (span : Syntax.SourceSpan) (e : Syntax.Expr) (s t : Core.Store) (v : Core.Value) :
    ComputationReturnTreeEvaluates allRaw o names env s (returned span e) v t ∧
    ComputationReturnTreeEvaluates allRaw (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span e) v t ∧
    ¬ ∃ cost, ComputationReturnTreeEvaluatesWithCost noCost o names env s (returned span e) v t cost := by
  have original : ComputationReturnTreeEvaluates allRaw o names env s (returned span e) v t := .expression trivial
  refine ⟨original,(computationReturnTreeEvaluates_mapOwner_iff mapping injective (by intros; rfl)).mpr original,?_⟩
  rintro ⟨cost,h⟩
  cases h with | expression impossible => exact impossible
theorem generic_cost_transport_requires_no_uncosted_erasure_bridge
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment)
    (span : Syntax.SourceSpan) (e : Syntax.Expr) (s t : Core.Store) (v : Core.Value) (cost : Nat) :
    ComputationReturnTreeEvaluatesWithCost allCost o names env s (returned span e) v t cost ∧
    ComputationReturnTreeEvaluatesWithCost allCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span e) v t cost ∧
    ¬ ComputationReturnTreeEvaluates noRaw o names env s (returned span e) v t := by
  have original : ComputationReturnTreeEvaluatesWithCost allCost o names env s (returned span e) v t cost := .expression trivial
  refine ⟨original,(computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective (by intros; rfl)).mpr original,?_⟩
  intro h
  cases h with | expression impossible => exact impossible

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RawOwnerBoundary",by decide⟩],by decide⟩⟩,133⟩
private def ident : Resolved.LocalId := ⟨owner,0⟩
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId := {id with declarationIndex := id.declarationIndex+10}
private theorem injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private def names : LocalNameTable := [("x",ident)]
private def reference (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def fixedRaw : Eval := fun table _ _ _ _ _ => table.lookup? "x"=some ident
private def fixedCost : Cost := fun table _ _ _ _ _ cost => table.lookup? "x"=some ident ∧ cost=7
private theorem changedLookup :
    ¬ (LocalNameTable.mapIds (ownerLocalIdMap shift) names).lookup? "x"=some ident := by decide
theorem injective_nonsurjective_owner_maps_still_require_the_supplied_child_covariance
    (span : Syntax.SourceSpan) (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    Function.Injective shift ∧ (¬ Function.Surjective shift) ∧
    ComputationReturnTreeEvaluates fixedRaw owner names env s (returned span (reference span)) v t ∧
    ComputationReturnTreeEvaluatesWithCost fixedCost owner names env s (returned span (reference span)) v t 7 ∧
    ¬ ComputationReturnTreeEvaluates fixedRaw (shift owner) (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env) s (returned span (reference span)) v t ∧
    ¬ ∃ cost, ComputationReturnTreeEvaluatesWithCost fixedCost (shift owner)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names) (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env)
      s (returned span (reference span)) v t cost := by
  refine ⟨injective,?_,.expression rfl,.expression ⟨rfl,rfl⟩,?_,?_⟩
  · intro surjective
    obtain ⟨id,same⟩ := surjective { owner with declarationIndex := 0 }
    have impossible := congrArg Resolved.DeclarationId.declarationIndex same
    change id.declarationIndex+10=0 at impossible
    omega
  · intro h
    cases h with | expression child => exact changedLookup child
  · rintro ⟨cost,h⟩
    cases h with | expression child => exact changedLookup child.1
theorem the_failed_covariance_premises_are_genuinely_false
    (span : Syntax.SourceSpan) (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ (fixedRaw (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env) s (reference span) v t ↔
      fixedRaw names env s (reference span) v t) ∧
    ¬ (fixedCost (LocalNameTable.mapIds (ownerLocalIdMap shift) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) env) s (reference span) v t 7 ↔
      fixedCost names env s (reference span) v t 7) :=
  ⟨fun covariance => changedLookup (covariance.mpr rfl),fun covariance => changedLookup (covariance.mpr ⟨rfl,rfl⟩).1⟩

private def unsupported (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.string "no raw rule"⟩⟩
private theorem absent (span : Syntax.SourceSpan) (o : Resolved.DeclarationId) (table : LocalNameTable)
    (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) :
    ¬ RecursiveComputationReturnTreeEvaluates o table env s (returned span (unsupported span)) v t := by
  intro h
  cases h with | expression child => cases child with | pure pureChild => cases pureChild with | wordLiteral meaning => cases meaning
private theorem costAbsent (span : Syntax.SourceSpan) (o : Resolved.DeclarationId) (table : LocalNameTable)
    (env : Resolved.Environment) (s t : Core.Store) (v : Core.Value) (cost : Nat) :
    ¬ RecursiveComputationReturnTreeEvaluatesWithCost o table env s (returned span (unsupported span)) v t cost := by
  intro h
  cases h with | expression child => cases child with | pure pureChild => cases pureChild with | wordLiteral meaning => cases meaning
theorem a_real_unsupported_child_has_no_raw_success_or_cost_after_owner_transport
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (inj : Function.Injective mapping)
    (span : Syntax.SourceSpan) (o : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) :
    (¬ ∃ v t, RecursiveComputationReturnTreeEvaluates (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span (unsupported span)) v t) ∧
    (¬ ∃ v t cost, RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s (returned span (unsupported span)) v t cost) := by
  constructor
  · rintro ⟨v,t,h⟩
    exact absent span o table env s t v ((computationReturnTreeEvaluates_mapOwner_iff mapping inj
      (recursiveLocalComputationEvaluates_mapIds_iff _ (ownerLocalIdMap_injective mapping inj))).mp h)
  · rintro ⟨v,t,cost,h⟩
    exact costAbsent span o table env s t v cost ((computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping inj
      (recursiveLocalComputationEvaluatesWithCost_mapIds_iff _ (ownerLocalIdMap_injective mapping inj))).mp h)
end Tests.FrontendComputationBodyRawOwnerBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendComputationBodyRawOwnerProperties
/-! Symbolic original blocks, not parser outputs. Arbitrary raw rows stay raw:
only the separately elaborated two-row fixture below has a positional Core
claim. Discard retains the actual closure's whole cost and store transition. -/
set_option autoImplicit false
namespace Tests.FrontendComputationBodyRawOwner
open Solcore Solcore.Frontend
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def zero := Core.Word.ofNatModulo 0
private def one := Core.Word.ofNatModulo 1
private def literal (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.literal ⟨s,.decimal "0"⟩⟩
private theorem denotes (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "0"⟩ zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩
private def returned (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt (some (ref s "x"))⟩]⟩
private def condition (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.binary (literal s) ⟨s,.equal⟩ (literal s)⟩
private def literalArm (s : Syntax.SourceSpan) (bad : Syntax.Block) : Syntax.MatchCase := ⟨s,⟨⟨s,.literal ⟨s,.decimal "1"⟩⟩,bad⟩⟩
private def wildArm (s : Syntax.SourceSpan) : Syntax.MatchCase := ⟨s,⟨⟨s,.group ⟨s,.wildcard s⟩⟩,returned s⟩⟩
private def arms (s : Syntax.SourceSpan) (bad : Syntax.Block) : List Syntax.MatchCase := [literalArm s bad,wildArm s]
private def matched (s : Syntax.SourceSpan) (bad : Syntax.Block) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨literal s,[]⟩⟩ ⟨s,⟨arms s bad,some bad⟩⟩⟩]⟩
private def statements (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) : Nat → List Syntax.Statement
  | 0 => [⟨s,.expression (call s) true⟩,⟨s,.ifThen (condition s) (matched s bad) (some bad)⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some annotation) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s annotation bad n
private theorem choice (s : Syntax.SourceSpan) (bad : Syntax.Block) :
    WordMatchChooses (.word zero) (arms s bad) (some bad) (returned s) 1 :=
  .miss (literal := one) (.literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)⟩)
    (by decide) (.wildcard (.group (.wildcard rfl)))
private structure Rows (v f : Core.Value) where
  names : LocalNameTable
  env : Resolved.Environment
  xId : Resolved.LocalId
  fId : Resolved.LocalId
  namedX : LocalNameTable.Lookup names "x" xId
  namedF : LocalNameTable.Lookup names "f" fId
  valueX : Resolved.LocalScope.Lookup env xId v
  valueF : Resolved.LocalScope.Lookup env fId f
private def Rows.bind {v f : Core.Value} (r : Rows v f) (o : Resolved.DeclarationId) : Rows v f where
  names := ("x",Resolved.freshLocalId o (r.names.map Prod.snd))::r.names
  env := (Resolved.freshLocalId o (r.names.map Prod.snd),v)::r.env
  xId := Resolved.freshLocalId o (r.names.map Prod.snd)
  fId := r.fId
  namedX := .head
  namedF := .tail (by decide) r.namedF
  valueX := .head
  valueF := .tail (by
    intro same
    exact Resolved.freshLocalId_not_mem o (r.names.map Prod.snd)
      (same ▸ List.mem_map.mpr ⟨("f",r.fId),r.namedF.mem,rfl⟩)) r.valueF
private theorem originalRaw (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block)
    (o : Resolved.DeclarationId) (n : Nat) (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (v ignored : Core.Value) (initial final : Core.Store)
    (actual : Core.Evaluates (v::captured) initial body ignored final)
    (r : Rows v (.closure a b body captured)) :
    RecursiveComputationReturnTreeEvaluates o r.names r.env initial ⟨s,statements s annotation bad n⟩ v final := by
  induction n generalizing r with
  | zero =>
      refine .discard (.application (.pure (.identifier r.namedF r.valueF)) (.pure (.identifier r.namedX r.valueX)) actual) ?_
      exact .ifTrue (.pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))))
        (.wordMatch (.pure (.wordLiteral (denotes s))) (choice s bad) (.expression (.pure (.identifier r.namedX r.valueX))))
  | succ n ih =>
      exact .binding (.pure (.identifier r.namedX r.valueX))
        (.inferred (.pure (.identifier .head .head)) (ih ((r.bind o).bind o)))
private theorem originalCost (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block)
    (o : Resolved.DeclarationId) (n : Nat) (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (v ignored : Core.Value) (initial final : Core.Store) (bodyCost : Nat)
    (actual : Core.Steps bodyCost (.initial body (v::captured) initial) (.final ignored final))
    (r : Rows v (.closure a b body captured)) :
    RecursiveComputationReturnTreeEvaluatesWithCost o r.names r.env initial
      ⟨s,statements s annotation bad n⟩ v final (6*n+bodyCost+25) := by
  induction n generalizing r with
  | zero =>
      have count : 6*0+bodyCost+25=(1+1+bodyCost+3)+18+2 := by omega
      rw [count]
      refine .discard (expressionCost := 1+1+bodyCost+3) (tailCost := 18) (discardedValue := ignored) (middleStore := final) ?_ ?_
      · exact .application (.pure (.identifier r.namedF r.valueF)) (.pure (.identifier r.namedX r.valueX)) actual
      · exact .ifTrue (conditionCost := 5) (branchCost := 11)
          (.pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))))
          (.wordMatch (scrutineeCost := 1) (branchCost := 1) (tests := 1)
            (.pure (.wordLiteral (denotes s))) (choice s bad) (.expression (.pure (.identifier r.namedX r.valueX))))
  | succ n ih =>
      have count : 6*(n+1)+bodyCost+25=1+(1+(6*n+bodyCost+25)+2)+2 := by omega
      rw [count]
      exact .binding (.pure (.identifier r.namedX r.valueX))
        (.inferred (.pure (.identifier .head .head)) (ih ((r.bind o).bind o)))

theorem raw_and_cost_are_original_independent_derivations
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId) (n : Nat)
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (initial final : Core.Store) (bodyCost : Nat)
    (actualRaw : Core.Evaluates (v::captured) initial body ignored final)
    (actualCost : Core.Steps bodyCost (.initial body (v::captured) initial) (.final ignored final))
    (r : Rows v (.closure a b body captured)) :
    RecursiveComputationReturnTreeEvaluates o r.names r.env initial ⟨s,statements s annotation bad n⟩ v final ∧
    RecursiveComputationReturnTreeEvaluatesWithCost o r.names r.env initial ⟨s,statements s annotation bad n⟩ v final (6*n+bodyCost+25) :=
  ⟨originalRaw s annotation bad o n a b body captured v ignored initial final actualRaw r,
    originalCost s annotation bad o n a b body captured v ignored initial final bodyCost actualCost r⟩
theorem owner_change_preserves_both_raw_interfaces_and_the_discarded_effects
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId) (n : Nat)
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (initial final : Core.Store) (bodyCost : Nat)
    (actualRaw : Core.Evaluates (v::captured) initial body ignored final)
    (actualCost : Core.Steps bodyCost (.initial body (v::captured) initial) (.final ignored final))
    (r : Rows v (.closure a b body captured)) :
    let names := LocalNameTable.mapIds (ownerLocalIdMap mapping) r.names
    let env := Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) r.env
    RecursiveComputationReturnTreeEvaluates (mapping o) names env initial ⟨s,statements s annotation bad n⟩ v final ∧
    RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) names env initial ⟨s,statements s annotation bad n⟩ v final (6*n+bodyCost+25) :=
  ⟨(computationReturnTreeEvaluates_mapOwner_iff mapping injective
      (recursiveLocalComputationEvaluates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr
      (originalRaw s annotation bad o n a b body captured v ignored initial final actualRaw r),
    (computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective
      (recursiveLocalComputationEvaluatesWithCost_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))).mpr
      (originalCost s annotation bad o n a b body captured v ignored initial final bodyCost actualCost r)⟩
theorem whole_success_absence_is_reflected_without_classifying_faults
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (body : Syntax.Block) :
    (¬ ∃ v t, RecursiveComputationReturnTreeEvaluates (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s body v t) ↔
    (¬ ∃ v t, RecursiveComputationReturnTreeEvaluates o names env s body v t) := by
  simp only [computationReturnTreeEvaluates_mapOwner_iff mapping injective
    (recursiveLocalComputationEvaluates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))]
theorem every_exact_cost_is_reflected_separately
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (o : Resolved.DeclarationId) (names : LocalNameTable) (env : Resolved.Environment)
    (s t : Core.Store) (body : Syntax.Block) (v : Core.Value) (cost : Nat) :
    RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) env) s body v t cost ↔
    RecursiveComputationReturnTreeEvaluatesWithCost o names env s body v t cost :=
  computationReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective
    (recursiveLocalComputationEvaluatesWithCost_mapIds_iff _ (ownerLocalIdMap_injective mapping injective))
private def alignedInputs (o : Resolved.DeclarationId) (a b : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x",⟨o,0⟩,a⟩,⟨"f",⟨o,1⟩,.function a b⟩],by simp⟩
private def alignedRows (o : Resolved.DeclarationId) (v f : Core.Value) : Rows v f :=
  ⟨[("x",⟨o,0⟩),("f",⟨o,1⟩)],[(⟨o,0⟩,v),(⟨o,1⟩,f)],⟨o,0⟩,⟨o,1⟩,
    .head,.tail (by decide) .head,.head,.tail (by simp) .head⟩
private def guardCore : Core.Expr := .binary .wordEq (.word zero) (.word zero)
private def matchCore : Core.Expr := .letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 1) (.var 1))
private def beforeDiscard : Core.Expr := .ifE guardCore matchCore (.var 0)
private def literalCore : Core.Expr := .letE (.apply (.var 1) (.var 0))
  (.ifE guardCore (.letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 2) (.var 2))) (.var 1))
private theorem alignedElab (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr)
    (o : Resolved.DeclarationId) (a b : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] o (alignedInputs o a b)
      ⟨s,statements s annotation (returned s) 0⟩ literalCore a := by
  have leaf : RecursiveLocalComputationElaborates (alignedInputs o a b).names (alignedInputs o a b).context (ref s "x") (.var 0) a :=
    .pure (.identifier .head) (.var .head) (.var .head)
  have branch : RecursiveComputationReturnTreeElaborates [] o (alignedInputs o a b) (matched s (returned s)) matchCore a := by
    refine .wordMatch (entries := [(literalArm s (returned s),some one,.var 0),(wildArm s,none,.var 0)])
      (defaultEntry := some (returned s,.var 0)) (.pure (.wordLiteral (denotes s)) .word .word) rfl ?_ (.inl rfl) ?_ rfl ?_ ?_
    · intro entry member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)⟩
      · exact .group (.wildcard rfl)
    · intro entry member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> exact .expression leaf
    · intro entry member
      simp only [Option.toList_some,List.mem_singleton] at member
      subst entry; exact .expression leaf
    · simp [Core.Expr.weakenAt]
  have shifted : beforeDiscard.weakenAt 0= .ifE guardCore
      (.letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 2) (.var 2))) (.var 1) := by
    simp [beforeDiscard,matchCore,guardCore,Core.Expr.weakenAt]
  change RecursiveComputationReturnTreeElaborates _ _ _ _ (.letE _ _) _
  rw [← shifted]
  exact .discard (.application (.pure (.identifier (.tail (by change ("x" : String)≠"f"; decide) .head)) (.var (.tail (by simp) .head)) (.var (.tail (by simp) .head))) leaf)
    (.conditional (.pure (.equal (.wordLiteral (denotes s)) (.wordLiteral (denotes s))) (.binary .word .word) (.binary .word .word))
      (computationBlockPreservesNames_iff.mp (by simp only [matched,computationBlockPreservesNames])) branch (.expression leaf))
private theorem literalPath (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (v ignored : Core.Value) (s t : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (v::captured) s) (.final ignored t)) (k : List Core.Frame) :
    Core.Steps (cost+25) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ ⟨.ret v,k,t⟩ := by
  have count : cost+25=(1+1+cost+3)+(5+(1+(5+1+2)+2)+2)+2 := by omega
  rw [count]
  exact CostStepComposition.letE (valueCost := 1+1+cost+3) (bodyCost := 18)
    (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) actual)
    (CostStepComposition.ifTrue (conditionCost := 5) (branchCost := 11) (CostStepComposition.binary (.cons .word .refl) (.cons .word .refl) rfl)
      (CostStepComposition.letE (.cons .word .refl)
        (CostStepComposition.ifFalse (CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) rfl)
          (.cons (.var rfl) .refl))))
theorem only_the_explicit_aligned_fixture_has_this_independent_literal_path
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (o : Resolved.DeclarationId)
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (initial final : Core.Store) (cost : Nat)
    (actual : Core.Steps cost (.initial body (v::captured) initial) (.final ignored final)) (k : List Core.Frame) :
    RecursiveComputationReturnTreeElaborates [] o (alignedInputs o a b)
      ⟨s,statements s annotation (returned s) 0⟩ literalCore a ∧
    Core.Steps (cost+25) ⟨.eval literalCore [v,.closure a b body captured],k,initial⟩ ⟨.ret v,k,final⟩ :=
  ⟨alignedElab s annotation o a b,literalPath a b body captured v ignored initial final cost actual k⟩
theorem aligned_full_fuel_and_saved_states_retain_the_complete_discarded_effect
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (s t : Core.Store) (cost fuel extra : Nat)
    (actual : Core.Steps cost (.initial body (v::captured) s) (.final ignored t)) :
    (Core.runStateful fuel (.initial literalCore [v,.closure a b body captured] s)=.done v t ↔ cost+25≤fuel) ∧
    ∀ cp, Core.runStateful fuel (.initial literalCore [v,.closure a b body captured] s)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial literalCore [v,.closure a b body captured] s) :=
  ⟨(literalPath a b body captured v ignored s t cost actual []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem one_actual_allocation_survives_any_number_of_shadowing_lets
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId)
    (n : Nat) (a : Core.Ty) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    let r := alignedRows o v (.closure a (.cell a) (.newCell a (.var 0)) captured)
    RecursiveComputationReturnTreeEvaluatesWithCost (mapping o) (LocalNameTable.mapIds (ownerLocalIdMap mapping) r.names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) r.env) store ⟨s,statements s annotation bad n⟩ v (store++[v]) (6*n+28) := by
  have actual : Core.Steps 3 (.initial (.newCell a (.var 0)) (v::captured) store) (.final (.cellRef a store.length) (store++[v])) :=
    .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  simpa only [Nat.add_assoc] using (owner_change_preserves_both_raw_interfaces_and_the_discarded_effects mapping injective
    s annotation bad o n a (.cell a) (.newCell a (.var 0)) captured v (.cellRef a store.length) store (store++[v]) 3
    (Core.steps_from_initial_sound actual) actual (alignedRows o v (.closure a (.cell a) (.newCell a (.var 0)) captured))).2
theorem discarded_closure_completes_before_the_pending_body_resumes
    (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (v ignored : Core.Value)
    (s t : Core.Store) (cost : Nat) (k : List Core.Frame)
    (actual : Core.Steps cost (.initial body (v::captured) s) (.final ignored t)) :
    ∃ cp, cp.control=.ret ignored ∧ cp.store=t ∧
      Core.runStateful (cost+6) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩=.outOfFuel cp ∧
      ∀ extra, Core.runStateful extra cp=Core.runStateful (cost+6+extra) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ := by
  let cp : Core.State := ⟨.ret ignored,.letBody (.ifE guardCore
    (.letE (.word zero) (.ifE (.binary .wordEq (.var 0) (.word one)) (.var 2) (.var 2))) (.var 1))
    [v,.closure a b body captured]::k,t⟩
  have beforePath : Core.Steps ((1+1+cost+3)+1) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ cp :=
    .cons .enterLet (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) actual)
  have path : Core.Steps (cost+6) ⟨.eval literalCore [v,.closure a b body captured],k,s⟩ cp := by
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using beforePath
  have stopped := Core.runStateful_outOfFuel_complete path (show Core.advance _=.next _ from rfl)
  exact ⟨_,rfl,rfl,stopped,Core.runStateful_resume stopped⟩
private def delayed (a : Core.Ty) : Nat → Core.Expr
  | 0 => .newCell a (.var 0)
  | m+1 => .letE (.var 0) (delayed a m)
private theorem delayedPath (a : Core.Ty) (m : Nat) (v : Core.Value) (captured : Core.Environment)
    (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*m+3) ⟨.eval (delayed a m) (v::captured),k,s⟩ ⟨.ret (.cellRef a s.length),k,s++[v]⟩ := by
  induction m generalizing captured k with
  | zero => exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  | succ m ih =>
      have count : 3*(m+1)+3=1+(3*m+3)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::captured) k)
theorem a_fixed_original_body_has_unbounded_actual_cost_and_a_retained_allocation
    (s : Syntax.SourceSpan) (annotation : Syntax.TypeExpr) (bad : Syntax.Block) (o : Resolved.DeclarationId)
    (a : Core.Ty) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) (bound : Nat) :
    ∃ m, bound<3*m+28 ∧
      let r := alignedRows o v (.closure a (.cell a) (delayed a m) captured)
      RecursiveComputationReturnTreeEvaluatesWithCost o r.names r.env store
        ⟨s,statements s annotation bad 0⟩ v (store++[v]) (3*m+28) := by
  refine ⟨bound,by omega,?_⟩
  simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_assoc] using originalCost s annotation bad o 0 a (.cell a)
    (delayed a bound) captured v (.cellRef a store.length) store (store++[v]) (3*bound+3)
    (delayedPath a bound v captured store []) (alignedRows o v (.closure a (.cell a) (delayed a bound) captured))
end Tests.FrontendComputationBodyRawOwner
end

section
-- leanmerge: from Solcore.Test.FrontendComputationFunctionArgumentProperties
/-! Independent value-free compilation precedes every supplied actual argument.
Reconstruction is compared against independently bound rows, never a checker
graph. Literal closure captures and store effects are retained; no world safety
follows from these structural arguments. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionArgument
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def fnType (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.function s ⟨s,[named s "A"]⟩ (some ⟨s,[named s "B"]⟩)⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b),(["A"],.bool)]
private def parameters (s : Syntax.SourceSpan) : List Syntax.FunctionParameter :=
  [⟨s,.typed none ⟨s,"f"⟩ (fnType s)⟩,⟨s,.typed none ⟨s,"x"⟩ (named s "A")⟩]
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.returnStmt (some (call s))⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s "A")) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s n
private def entry (s : Syntax.SourceSpan) (n : Nat) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"independentArguments"⟩,none,⟨s,parameters s⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s "B"]⟩⟩,none⟩,⟨s,statements s n⟩⟩⟩
private def scope (o : Resolved.DeclarationId) (a b : Core.Ty) : Nat → LocalTypeInputs
  | 0 => (LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "x" a
  | m+1 => (scope o a b m).bindFresh o "x" a
private def code : Nat → Nat → Core.Expr
  | 0,m => .apply (.var (m+1)) (.var 0)
  | n+1,m => .letE (.var 0) (.letE (.var 0) (code n (m+2)))
private theorem functionMeaning (s : Syntax.SourceSpan) (a b : Core.Ty) : StructuralTypeDenotes (types a b) (fnType s) (.function a b) :=
  .functionReturns (.named .head) (.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head)))
private theorem header (s : Syntax.SourceSpan) (a b : Core.Ty) (n : Nat) : RuntimeFunctionHeader (types a b) (entry s n).value.signature b :=
  ⟨rfl,rfl,rfl,rfl,.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head))⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) :
    RuntimeParametersDeclare (types a b) o (parameters s) (scope o a b 0) :=
  .cons (functionMeaning s a b) (by simp) (.cons (.named .head) (by simp [LocalTypeInputs.names,LocalTypeInputs.bindFresh,LocalTypeInputs.empty]) .nil)
private theorem functionFacts (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    LocalNameTable.Lookup (scope o a b m).names "f" ⟨o,0⟩ ∧
    Resolved.LocalScope.IndexOf (scope o a b m).context.ids ⟨o,0⟩ (m+1) ∧
    Resolved.LocalScope.Lookup (scope o a b m).context ⟨o,0⟩ (.function a b) := by
  induction m with
  | zero =>
      have different := Resolved.freshLocalId_cons_fresh_ne o []
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) .head,.tail different .head,.tail different .head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId o (scope o a b m).ids ≠ ⟨o,0⟩ := by
        intro same
        have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o a b m).names.map Prod.snd := List.mem_map.mpr ⟨("f",⟨o,0⟩),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) ih.1,.tail different ih.2.1,.tail different ih.2.2⟩
private theorem argumentElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    RecursiveLocalComputationElaborates (scope o a b m).names (scope o a b m).context (ref s "x") (.var 0) a := by
  cases m <;> exact .pure (.identifier .head) (.var .head) (.var .head)
private theorem bodyElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n m : Nat) :
    RecursiveComputationReturnTreeElaborates (types a b) o (scope o a b m) ⟨s,statements s n⟩ (code n m) b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (functionFacts o a b m).1) (.var (functionFacts o a b m).2.1) (.var (functionFacts o a b m).2.2))
      (argumentElab s o a b m))
  | succ n ih =>
      exact .binding (.named .head) (argumentElab s o a b m)
        (.inferred (argumentElab s o a b (m+1)) (ih (m+2)))
private structure Actual where
  argument : TypedRuntimeArgument
  resultType : Core.Ty
  body : Core.Expr
  captured : Core.Environment
  typed : Core.ValueHasType (.closure argument.type resultType body captured) (.function argument.type resultType)
private def Actual.fn (r : Actual) : TypedRuntimeArgument := ⟨.function r.argument.type r.resultType,.closure r.argument.type r.resultType r.body r.captured,r.typed⟩
private def Actual.inputs (r : Actual) (o : Resolved.DeclarationId) :=
  (LocalInputs.empty.bindFresh o "f" r.fn.type r.fn.value r.fn.valueTyped).bindFresh o "x" r.argument.type r.argument.value r.argument.valueTyped
private def compiled (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) : CompiledRuntimeFunction := ⟨scope o a b 0,code n 0,b⟩
private def prepared (o : Resolved.DeclarationId) (r : Actual) (n : Nat) : PreparedRuntimeFunction := ⟨r.inputs o,code n 0,r.resultType⟩
private theorem compilation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) :
    RecursiveComputationFunctionCompiles (types a b) o (entry s n) (compiled o a b n) :=
  ⟨header s a b n,declared s o a b,bodyElab s o a b n 0⟩
private theorem binding (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) :
    RuntimeParametersBind (types r.argument.type r.resultType) o (parameters s) [r.fn,r.argument] (r.inputs o) :=
  .cons (functionMeaning s _ _) (by simp) (.cons (.named .head) (by simp [LocalInputs.names,LocalInputs.bindFresh,LocalInputs.empty]) .nil)
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) :=
  ⟨header s _ _ n,binding s o r,bodyElab s o _ _ n 0⟩
private def environment (o : Resolved.DeclarationId) (r : Actual) : Nat → Resolved.Environment
  | 0 => (r.inputs o).environment
  | m+1 => (Resolved.freshLocalId o (scope o r.argument.type r.resultType m).ids,r.argument.value)::environment o r m
private theorem rawFunction (o : Resolved.DeclarationId) (r : Actual) (m : Nat) :
    Resolved.LocalScope.Lookup (environment o r m) ⟨o,0⟩ r.fn.value := by
  induction m with
  | zero => exact .tail (Resolved.freshLocalId_cons_fresh_ne o []) .head
  | succ m ih =>
      refine .tail ?_ ih
      intro same
      have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o r.argument.type r.resultType m).names.map Prod.snd :=
        List.mem_map.mpr ⟨("f",⟨o,0⟩),(functionFacts o r.argument.type r.resultType m).1.mem,rfl⟩
      rw [LocalTypeInputs.names_ids] at member
      exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
private theorem rawArgument (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (m : Nat) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (scope o r.argument.type r.resultType m).names (environment o r m) store
      (ref s "x") r.argument.value store 1 := by
  cases m <;> exact .pure (.identifier .head .head)
private theorem rawCost (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n m : Nat)
    (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (scope o r.argument.type r.resultType m).names (environment o r m)
      initial ⟨s,statements s n⟩ v final (6*n+cost+5) := by
  induction n generalizing m with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact .expression (.application (.pure (.identifier (functionFacts o r.argument.type r.resultType m).1 (rawFunction o r m))) (rawArgument s o r m initial) actual)
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      refine .binding (rawArgument s o r m initial) ?_
      change RecursiveComputationReturnTreeEvaluatesWithCost o
        (("x",Resolved.freshLocalId o ((scope o r.argument.type r.resultType m).names.map Prod.snd))::(scope o r.argument.type r.resultType m).names) _ _ _ _ _ _
      rw [LocalTypeInputs.names_ids]
      refine .inferred (rawArgument s o r (m+1) initial) ?_
      simpa only [scope,LocalTypeInputs.bindFresh_names,LocalTypeInputs.bindFresh_ids,List.map_cons,
        LocalTypeInputs.names_ids,environment] using ih (m+2)
private theorem manual (r : Actual) (n m : Nat) (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) (k : List Core.Frame) :
    Core.Steps (6*n+cost+5) ⟨.eval (code n m) (List.replicate (m+1) r.argument.value++[r.fn.value]),k,initial⟩ ⟨.ret v,k,final⟩ := by
  induction n generalizing m k with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact CostStepComposition.apply (parameterType := r.argument.type) (resultType := r.resultType)
        (.cons (.var (by simp [Actual.fn])) .refl) (.cons (.var (by simp)) .refl) actual
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      simpa [code,List.replicate_succ] using CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (m+2) k))

theorem arbitrary_annotated_types_compile_without_any_runtime_inhabitants
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) :
    RecursiveComputationFunctionCompiles (types a b) o (entry s n) (compiled o a b n) := compilation s o a b n
theorem supplied_arguments_factor_exactly_through_ordered_types
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) (args : List TypedRuntimeArgument) :
    (∃ p,RecursiveComputationFunctionPrepares (types a b) o (entry s n) args p ∧ p.toCompiled=compiled o a b n) ↔
      args.map (·.type)=[.function a b,a] := by
  constructor
  · intro restored
    exact (computationFunctionPrepares_toCompiled_iff.mp restored).2
  · intro matching
    exact computationFunctionPrepares_toCompiled_iff.mpr ⟨compilation s o a b n,matching⟩
theorem reconstruction_equals_the_independently_bound_actual_record
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    ∃ p,RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] p ∧
      p.toCompiled=compiled o r.argument.type r.resultType n ∧ p=prepared o r n ∧
      p.inputs.environment.values=[r.argument.value,.closure r.argument.type r.resultType r.body r.captured] := by
  obtain ⟨p,evidence,erased⟩ := (compilation s o r.argument.type r.resultType n).prepare_arguments [r.fn,r.argument] rfl
  have same : p=prepared o r n := evidence.unique_of_toCompiled_eq (preparation s o r n) erased
  refine ⟨p,evidence,erased,same,?_⟩
  exact evidence.argument_values
theorem independent_preparation_erases_to_the_same_value_free_compilation
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionCompiles (types r.argument.type r.resultType) o (entry s n) (prepared o r n).toCompiled ∧
    (prepared o r n).toCompiled=compiled o r.argument.type r.resultType n :=
  ⟨(preparation s o r n).compiles,rfl⟩
theorem fixed_projection_uniqueness_retains_literal_arguments_and_captures
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) (p : PreparedRuntimeFunction)
    (evidence : RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] p)
    (erased : p.toCompiled=compiled o r.argument.type r.resultType n) :
    p=prepared o r n ∧ p.inputs.environment.values=[r.argument.value,r.fn.value] ∧
      p.inputs.bindings.map (·.name)=["x","f"] := by
  have same : p=prepared o r n := evidence.unique_of_toCompiled_eq (preparation s o r n) erased
  exact ⟨same,evidence.argument_values,by rw [same]; rfl⟩
theorem same_typed_but_different_actual_values_need_not_give_equal_preparations
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r t : Actual) (n : Nat)
    (sameArgumentType : r.argument.type=t.argument.type) (sameResultType : r.resultType=t.resultType)
    (different : r.argument.value≠t.argument.value ∨ r.fn.value≠t.fn.value) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) ∧
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [t.fn,t.argument] (prepared o t n) ∧
    (prepared o r n).toCompiled=(prepared o t n).toCompiled ∧ prepared o r n≠prepared o t n := by
  refine ⟨preparation s o r n,?_,?_,?_⟩
  · simpa only [sameArgumentType,sameResultType] using preparation s o t n
  · change compiled o r.argument.type r.resultType n=compiled o t.argument.type t.resultType n
    rw [sameArgumentType,sameResultType]
  · intro same
    have values : [r.argument.value,r.fn.value]=[t.argument.value,t.fn.value] :=
      congrArg (fun p : PreparedRuntimeFunction => p.inputs.environment.values) same
    rcases List.cons.inj values with ⟨sameArgument,sameFunction⟩
    cases different with
    | inl h => exact h sameArgument
    | inr h => exact h (List.cons.inj sameFunction).1
theorem restored_records_have_the_original_raw_cost_and_independent_literal_path
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) :
    ∃ p,RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] p ∧
      p.toCompiled=compiled o r.argument.type r.resultType n ∧
      RecursiveComputationReturnTreeEvaluatesWithCost o p.inputs.names p.inputs.environment initial (entry s n).value.body v final (6*n+cost+5) ∧
      ∀ k,Core.Steps (6*n+cost+5) ⟨.eval p.core p.inputs.environment.values,k,initial⟩ ⟨.ret v,k,final⟩ := by
  obtain ⟨p,evidence,erased,same,_⟩ := reconstruction_equals_the_independently_bound_actual_record s o r n
  refine ⟨p,evidence,erased,?_,?_⟩
  · rw [same]; exact rawCost s o r n 0 initial final v cost actual
  · intro k; rw [same]; exact manual r n 0 initial final v cost actual k
theorem every_reconstructed_run_keeps_exact_fuel_and_full_saved_states
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (initial final : Core.Store) (v : Core.Value) (cost fuel extra : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final))
    (p : PreparedRuntimeFunction)
    (evidence : RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] p)
    (erased : p.toCompiled=compiled o r.argument.type r.resultType n) :
    (Core.runStateful fuel (.initial p.core p.inputs.environment.values initial)=.done v final ↔ 6*n+cost+5≤fuel) ∧
    ((∃ cp,Core.runStateful fuel (.initial p.core p.inputs.environment.values initial)=.outOfFuel cp) ↔ fuel<6*n+cost+5) ∧
    ∀ cp,Core.runStateful fuel (.initial p.core p.inputs.environment.values initial)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial p.core p.inputs.environment.values initial) := by
  have same : p=prepared o r n := evidence.unique_of_toCompiled_eq (preparation s o r n) erased
  rw [same]
  exact ⟨(manual r n 0 initial final v cost actual []).runStateful_done_iff,
    (manual r n 0 initial final v cost actual []).runStateful_outOfFuel_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem full_checker_run_is_consumed_only_after_independent_reconstruction
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n fuel : Nat) (store : Core.Store) :
    runRecursiveComputationFunction? (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] fuel store=
      some (r.resultType,Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] store)) := by
  obtain ⟨p,evidence,_,same,_⟩ := reconstruction_equals_the_independently_bound_actual_record s o r n
  have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence
  dsimp only [runRecursiveComputationFunction?,runComputationFunction?]
  rw [accepted,same]; rfl
theorem reconstruction_does_not_replace_the_first_initializer_checkpoint
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) (store : Core.Store) (k : List Core.Frame)
    (p : PreparedRuntimeFunction)
    (evidence : RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s (n+1)) [r.fn,r.argument] p)
    (erased : p.toCompiled=compiled o r.argument.type r.resultType (n+1)) :
    Core.runStateful 2 ⟨.eval p.core p.inputs.environment.values,k,store⟩=
      .outOfFuel ⟨.ret r.argument.value,.letBody (.letE (.var 0) (code n 2)) [r.argument.value,r.fn.value]::k,store⟩ := by
  rw [evidence.unique_of_toCompiled_eq (preparation s o r (n+1)) erased]; rfl
private def delayed (a : Core.Ty) : Nat → Core.Expr
  | 0 => .newCell a (.var 0)
  | m+1 => .letE (.var 0) (delayed a m)
private theorem delayedTyped (a : Core.Ty) (_payload : Core.CellPayload a) (m : Nat) (context : Core.Context) :
    Core.HasType (a::context) (delayed a m) (.cell a) := by
  induction m generalizing context with
  | zero => exact .newCell (.var rfl)
  | succ m ih => exact .letE (.var rfl) (ih (a::context))
private theorem delayedPath (a : Core.Ty) (m : Nat) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*m+3) ⟨.eval (delayed a m) (v::captured),k,store⟩ ⟨.ret (.cellRef a store.length),k,store++[v]⟩ := by
  induction m generalizing captured k with
  | zero => exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  | succ m ih =>
      have count : 3*(m+1)+3=1+(3*m+3)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::captured) k)
private def allocator (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (m : Nat) : Actual :=
  ⟨arg,.cell arg.type,delayed arg.type m,captured,.closure typed (delayedTyped arg.type payload m context)⟩
theorem reconstructed_actual_captures_retain_the_allocation_and_its_exact_cost
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (n m : Nat) (store : Core.Store) :
    let r := allocator arg payload captured context typed m
    ∃ p,RecursiveComputationFunctionPrepares (types arg.type (.cell arg.type)) o (entry s n) [r.fn,arg] p ∧
      p.toCompiled=compiled o arg.type (.cell arg.type) n ∧
      Core.runStateful (6*n+3*m+8) (.initial p.core p.inputs.environment.values store)=
        .done (.cellRef arg.type store.length) (store++[arg.value]) := by
  let r := allocator arg payload captured context typed m
  obtain ⟨p,evidence,erased,same,_⟩ := reconstruction_equals_the_independently_bound_actual_record s o r n
  refine ⟨p,evidence,erased,?_⟩
  rw [same]
  exact (manual r n 0 store (store++[arg.value]) (.cellRef arg.type store.length) (3*m+3)
    (delayedPath arg.type m arg.value captured store []) []).runStateful_done_iff.mpr (by omega)
end Tests.FrontendComputationFunctionArgument
end

section
-- leanmerge: from Solcore.Test.FrontendComputationFunctionCheckpointProperties
/-! Independent original preparation with arbitrarily many typed/inferred shadows.
The actual closure, captures, store and caller frames share one runtime world.
Safety needs no callee termination or source-cost premise. Literal allocation
paths below are additional fixture evidence, not consequences of that safety. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionCheckpoint
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def fnType (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.function s ⟨s,[named s "A"]⟩ (some ⟨s,[named s "B"]⟩)⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b),(["A"],.bool)]
private def parameters (s : Syntax.SourceSpan) : List Syntax.FunctionParameter :=
  [⟨s,.typed none ⟨s,"f"⟩ (fnType s)⟩,⟨s,.typed none ⟨s,"x"⟩ (named s "A")⟩]
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.returnStmt (some (call s))⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s "A")) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s n
private def entry (s : Syntax.SourceSpan) (n : Nat) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"checkpointShadows"⟩,none,⟨s,parameters s⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s "B"]⟩⟩,none⟩,⟨s,statements s n⟩⟩⟩
private def scope (o : Resolved.DeclarationId) (a b : Core.Ty) : Nat → LocalTypeInputs
  | 0 => (LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "x" a
  | m+1 => (scope o a b m).bindFresh o "x" a
private def code : Nat → Nat → Core.Expr
  | 0,m => .apply (.var (m+1)) (.var 0)
  | n+1,m => .letE (.var 0) (.letE (.var 0) (code n (m+2)))
private theorem functionMeaning (s : Syntax.SourceSpan) (a b : Core.Ty) : StructuralTypeDenotes (types a b) (fnType s) (.function a b) :=
  .functionReturns (.named .head) (.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head)))
private theorem header (s : Syntax.SourceSpan) (a b : Core.Ty) (n : Nat) : RuntimeFunctionHeader (types a b) (entry s n).value.signature b :=
  ⟨rfl,rfl,rfl,rfl,.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head))⟩
private theorem functionFacts (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    LocalNameTable.Lookup (scope o a b m).names "f" ⟨o,0⟩ ∧
    Resolved.LocalScope.IndexOf (scope o a b m).context.ids ⟨o,0⟩ (m+1) ∧
    Resolved.LocalScope.Lookup (scope o a b m).context ⟨o,0⟩ (.function a b) := by
  induction m with
  | zero =>
      have different := Resolved.freshLocalId_cons_fresh_ne o []
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) .head,.tail different .head,.tail different .head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId o (scope o a b m).ids ≠ ⟨o,0⟩ := by
        intro same
        have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o a b m).names.map Prod.snd := List.mem_map.mpr ⟨("f",⟨o,0⟩),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) ih.1,.tail different ih.2.1,.tail different ih.2.2⟩
private theorem argumentElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    RecursiveLocalComputationElaborates (scope o a b m).names (scope o a b m).context (ref s "x") (.var 0) a := by
  cases m <;> exact .pure (.identifier .head) (.var .head) (.var .head)
private theorem bodyElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n m : Nat) :
    RecursiveComputationReturnTreeElaborates (types a b) o (scope o a b m) ⟨s,statements s n⟩ (code n m) b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (functionFacts o a b m).1) (.var (functionFacts o a b m).2.1) (.var (functionFacts o a b m).2.2))
      (argumentElab s o a b m))
  | succ n ih =>
      exact .binding (.named .head) (argumentElab s o a b m)
        (.inferred (argumentElab s o a b (m+1)) (ih (m+2)))
private structure Actual where
  argument : TypedRuntimeArgument
  resultType : Core.Ty
  body : Core.Expr
  captured : Core.Environment
  typed : Core.ValueHasType (.closure argument.type resultType body captured) (.function argument.type resultType)
private def Actual.fn (r : Actual) : TypedRuntimeArgument := ⟨.function r.argument.type r.resultType,.closure r.argument.type r.resultType r.body r.captured,r.typed⟩
private def Actual.inputs (r : Actual) (o : Resolved.DeclarationId) :=
  (LocalInputs.empty.bindFresh o "f" r.fn.type r.fn.value r.fn.valueTyped).bindFresh o "x" r.argument.type r.argument.value r.argument.valueTyped
private def prepared (o : Resolved.DeclarationId) (r : Actual) (n : Nat) : PreparedRuntimeFunction := ⟨r.inputs o,code n 0,r.resultType⟩
private theorem binding (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) :
    RuntimeParametersBind (types r.argument.type r.resultType) o (parameters s) [r.fn,r.argument] (r.inputs o) :=
  .cons (functionMeaning s _ _) (by simp) (.cons (.named .head) (by simp [LocalInputs.names,LocalInputs.bindFresh,LocalInputs.empty]) .nil)
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) :=
  ⟨header s _ _ n,binding s o r,bodyElab s o _ _ n 0⟩

private def start (o : Resolved.DeclarationId) (r : Actual) (n : Nat) (store : Core.Store) (k : List Core.Frame) : Core.State :=
  ⟨.eval (prepared o r n).core (prepared o r n).inputs.environment.values,k,store⟩
private theorem argumentsTyped {world : Core.StoreTyping} (r : Actual)
    (functionTyped : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (argumentTyped : Core.RuntimeValueHasType world r.argument.value r.argument.type) :
    ∀ arg ∈ [r.fn,r.argument], Core.RuntimeValueHasType world arg.value arg.type := by
  intro arg member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> assumption

theorem original_preparation_retains_both_actual_arguments_and_all_captures
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) ∧
      (prepared o r n).inputs.environment.values=[r.argument.value,.closure r.argument.type r.resultType r.body r.captured] :=
  ⟨preparation s o r n,rfl⟩
theorem arbitrary_shadow_depth_and_typed_callers_never_fault
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (k : List Core.Frame) (result : Core.Ty)
    (ft : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (xt : Core.RuntimeValueHasType world r.argument.value r.argument.type)
    (st : Core.StoreHasTypes world store) (kt : Core.ContinuationHasType world k r.resultType result) :
    Core.StateHasType (start o r n store k) result ∧
      ∀ fuel error faultState, Core.runStateful fuel (start o r n store k) ≠ .fault error faultState := by
  have safety := (preparation s o r n).runtime_checkpoint_safety
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st kt
  exact ⟨safety.1,safety.2.1⟩
theorem every_genuine_checkpoint_is_typed_safe_and_exactly_resumable
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (k : List Core.Frame) (result : Core.Ty)
    (ft : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (xt : Core.RuntimeValueHasType world r.argument.value r.argument.type)
    (st : Core.StoreHasTypes world store) (kt : Core.ContinuationHasType world k r.resultType result)
    (spent : Nat) (cp : Core.State) (stopped : Core.runStateful spent (start o r n store k)=.outOfFuel cp) :
    Core.StateHasType cp result ∧
      (∀ additional error faultState, Core.runStateful additional cp ≠ .fault error faultState) ∧
      ∀ additional, Core.runStateful additional cp=Core.runStateful (spent+additional) (start o r n store k) := by
  have safety := (preparation s o r n).runtime_checkpoint_safety
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st kt
  exact ⟨(safety.2.2 stopped).1,(safety.2.2 stopped).2,Core.runStateful_resume stopped⟩
theorem one_saved_world_extends_to_every_further_actual_path
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (k : List Core.Frame) (result : Core.Ty)
    (ft : Core.RuntimeValueHasType world r.fn.value r.fn.type)
    (xt : Core.RuntimeValueHasType world r.argument.value r.argument.type)
    (st : Core.StoreHasTypes world store) (kt : Core.ContinuationHasType world k r.resultType result)
    (spent : Nat) (cp : Core.State) (stopped : Core.runStateful spent (start o r n store k)=.outOfFuel cp) :
    ∃ saved, Core.WorldExtends world saved ∧ Core.RuntimeStoreHasTypes saved cp.store ∧
      ∀ {steps next}, Core.Steps steps cp next →
        ∃ future, Core.WorldExtends saved future ∧ Core.RuntimeStoreHasTypes future next.store ∧
          ∀ {location : Nat} {type : Core.Ty}, world[location]?=some type → future[location]?=some type := by
  obtain ⟨saved,extension,stored,later⟩ := (preparation s o r n).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st kt stopped
  refine ⟨saved,extension,stored,?_⟩
  intro steps next path
  obtain ⟨future,more,typed⟩ := later path
  exact ⟨future,more,typed,fun found => (extension.trans more).lookup found⟩
theorem the_first_initializer_finishes_before_any_actual_callee_effect
    (o : Resolved.DeclarationId) (r : Actual) (n : Nat) (store : Core.Store) (k : List Core.Frame) :
    Core.runStateful 2 (start o r (n+1) store k)=
      .outOfFuel ⟨.ret r.argument.value,.letBody (.letE (.var 0) (code n 2)) [r.argument.value,r.fn.value]::k,store⟩ := rfl

private theorem manual (r : Actual) (n m : Nat) (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) (k : List Core.Frame) :
    Core.Steps (6*n+cost+5) ⟨.eval (code n m) (List.replicate (m+1) r.argument.value++[r.fn.value]),k,initial⟩ ⟨.ret v,k,final⟩ := by
  induction n generalizing m k with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact CostStepComposition.apply (parameterType := r.argument.type) (resultType := r.resultType)
        (.cons (.var (by simp [Actual.fn])) .refl) (.cons (.var (by simp)) .refl) actual
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      simpa [code,List.replicate_succ] using CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (m+2) k))

private def delayed (a : Core.Ty) : Nat → Core.Expr
  | 0 => .newCell a (.var 0)
  | m+1 => .letE (.var 0) (delayed a m)
private theorem delayedTyped (a : Core.Ty) (_payload : Core.CellPayload a) (m : Nat) (context : Core.Context) :
    Core.HasType (a::context) (delayed a m) (.cell a) := by
  induction m generalizing context with
  | zero => exact .newCell (.var rfl)
  | succ m ih => exact .letE (.var rfl) (ih (a::context))
private theorem delayedPath (a : Core.Ty) (m : Nat) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*m+3) ⟨.eval (delayed a m) (v::captured),k,store⟩ ⟨.ret (.cellRef a store.length),k,store++[v]⟩ := by
  induction m generalizing captured k with
  | zero => exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  | succ m ih =>
      have count : 3*(m+1)+3=1+(3*m+3)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::captured) k)
private def allocator (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (m : Nat) : Actual :=
  ⟨arg,.cell arg.type,delayed arg.type m,captured,.closure typed (delayedTyped arg.type payload m context)⟩


private def pending (a : Core.Ty) (retained : Core.Value) : List Core.Frame :=
  [.loadCellApply,.newCellApply a,.pairApply retained]
private def saved (a : Core.Ty) (v retained : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.cellRef a store.length),pending a retained,store++[v]⟩
private def allocatedAgain (a : Core.Ty) (v retained : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.cellRef a (store.length+1)),[.pairApply retained],store++[v,v]⟩
private theorem pendingTyped {world : Core.StoreTyping} {retained : Core.Value} {a b : Core.Ty}
    (_payload : Core.CellPayload a) (typed : Core.RuntimeValueHasType world retained b) :
    Core.ContinuationHasType world (pending a retained) (.cell a) (.product b (.cell a)) :=
  .cons (.loadCellApply) (.cons (.newCellApply) (.cons (.pairApply typed) .nil))
private theorem savedPath (a : Core.Ty) (v retained : Core.Value) (store : Core.Store) :
    Core.Steps 2 (saved a v retained store) (allocatedAgain a v retained store) := by
  have path := Core.Steps.cons (.applyLoadCell (elementType := a) (Core.Store.allocate_fresh_lookup store v))
    (.cons (.applyNewCell (elementType := a) (continuation := [.pairApply retained])) .refl)
  simpa [saved,allocatedAgain,pending,Core.Store.allocate,List.append_assoc] using path
private theorem allocationPath (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context)
    (n m : Nat) (store : Core.Store) (retained : Core.Value) :
    Core.Steps (6*n+3*m+8) (start o (allocator arg payload captured context typed m) n store (pending arg.type retained))
      (saved arg.type arg.value retained store) := by
  simpa [start,prepared,Actual.inputs,LocalInputs.environment,LocalInputs.bindFresh,LocalInputs.empty,
    Resolved.LocalScope.values,saved,allocator,Nat.add_assoc] using manual (allocator arg payload captured context typed m) n 0 store (store++[arg.value])
    (.cellRef arg.type store.length) (3*m+3) (delayedPath arg.type m arg.value captured store []) (pending arg.type retained)

theorem independent_allocation_checkpoint_preserves_the_pending_caller_and_complete_resume
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context)
    (n m : Nat) (store : Core.Store) (retained : Core.Value) :
    let r := allocator arg payload captured context typed m
    RecursiveComputationFunctionPrepares (types arg.type (.cell arg.type)) o (entry s n) [r.fn,arg] (prepared o r n) ∧
      Core.runStateful (6*n+3*m+8) (start o r n store (pending arg.type retained))=.outOfFuel (saved arg.type arg.value retained store) ∧
      Core.runStateful 2 (saved arg.type arg.value retained store)=.outOfFuel (allocatedAgain arg.type arg.value retained store) ∧
      Core.runStateful 3 (saved arg.type arg.value retained store)=
        .done (.pair retained (.cellRef arg.type (store.length+1))) (store++[arg.value,arg.value]) := by
  refine ⟨preparation s o (allocator arg payload captured context typed m) n,?_,?_,?_⟩
  · exact Core.runStateful_outOfFuel_complete (allocationPath o arg payload captured context typed n m store retained)
      (Core.advance_next_iff.mpr (.applyLoadCell (Core.Store.allocate_fresh_lookup store arg.value)))
  · exact Core.runStateful_outOfFuel_complete (savedPath arg.type arg.value retained store)
      (Core.advance_next_iff.mpr .applyPair)
  · exact ((savedPath arg.type arg.value retained store).trans (.cons .applyPair .refl)).runStateful_done_iff.mpr (by decide)

theorem callee_and_caller_allocations_strictly_extend_the_same_saved_world
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (n m : Nat)
    (world : Core.StoreTyping) (store : Core.Store) (retained : Core.Value) (retainedType : Core.Ty)
    (xt : Core.RuntimeValueHasType world arg.value arg.type) (ct : Core.RuntimeEnvironmentHasTypes world captured context)
    (st : Core.StoreHasTypes world store) (rt : Core.RuntimeValueHasType world retained retainedType) :
    Core.StateHasType (saved arg.type arg.value retained store) (.product retainedType (.cell arg.type)) ∧
      (∀ fuel error faultState, Core.runStateful fuel (saved arg.type arg.value retained store) ≠ .fault error faultState) ∧
      ∃ savedWorld future, Core.WorldExtends world savedWorld ∧ Core.WorldExtends savedWorld future ∧
        Core.RuntimeStoreHasTypes savedWorld (store++[arg.value]) ∧ Core.RuntimeStoreHasTypes future (store++[arg.value,arg.value]) ∧
        world.length<savedWorld.length ∧ savedWorld.length<future.length ∧
        ∀ {location : Nat} {type : Core.Ty}, world[location]?=some type → future[location]?=some type := by
  let r := allocator arg payload captured context ct.erase m
  have ft : Core.RuntimeValueHasType world r.fn.value r.fn.type :=
    .closure ct (delayedTyped arg.type payload m context)
  have stopped := (independent_allocation_checkpoint_preserves_the_pending_caller_and_complete_resume
    s o arg payload captured context ct.erase n m store retained).2.1
  have safety := (preparation s o r n).runtime_checkpoint_safety
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st (pendingTyped payload rt)
  obtain ⟨savedWorld,extension,stored,further⟩ := (preparation s o r n).runtime_checkpoint_world_extension
    RecursiveLocalComputationElaborates.core_hasType (argumentsTyped r ft xt) st (pendingTyped payload rt) stopped
  obtain ⟨future,more,storedAgain⟩ := further (savedPath arg.type arg.value retained store)
  refine ⟨(safety.2.2 stopped).1,(safety.2.2 stopped).2,savedWorld,future,extension,more,stored,storedAgain,?_,?_,
    fun found => (extension.trans more).lookup found⟩
  all_goals
    have firstLength := stored.length_eq
    have secondLength := storedAgain.length_eq
    have initialLength := st.length_eq
    change savedWorld.length=(store++[arg.value]).length at firstLength
    change future.length=(store++[arg.value,arg.value]).length at secondLength
    simp only [List.length_append,List.length_cons,List.length_nil] at firstLength secondLength
    omega

end Tests.FrontendComputationFunctionCheckpoint
end

section
-- leanmerge: from Solcore.Test.FrontendComputationFunctionOwnerBoundaryProperties
/-! Covariance is an equation, not child-checker correctness. The graph below
is explicitly an artificial interface, never original-source elaboration.
An injective nonsurjective owner map alone does not supply that equation. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionOwnerBoundary
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,"A"⟩,[]⟩⟩⟩ none⟩
private def table (a : Core.Ty) : TypeNameTable := [(["A"],a)]
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def parameter (s : Syntax.SourceSpan) : Syntax.FunctionParameter := ⟨s,.typed none ⟨s,"x"⟩ (named s)⟩
private def entry (s : Syntax.SourceSpan) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"checkerBoundary"⟩,none,⟨s,[parameter s]⟩,⟨none,none⟩,some ⟨s,⟨s,[named s]⟩⟩,none⟩,
    ⟨s,[⟨s,.letDecl ⟨s,"x"⟩ (some (named s)) (some (ref s))⟩,⟨s,.returnStmt (some (ref s))⟩]⟩⟩⟩
private def staticInputs (o : Resolved.DeclarationId) (a : Core.Ty) := LocalTypeInputs.empty.bindFresh o "x" a
private def inputs (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :=
  LocalInputs.empty.bindFresh o "x" arg.type arg.value arg.valueTyped
private theorem header (s : Syntax.SourceSpan) (a : Core.Ty) : RuntimeFunctionHeader (table a) (entry s).value.signature a :=
  ⟨rfl,rfl,rfl,rfl,.single (.named .head)⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RuntimeParametersDeclare (table a) o [parameter s] (staticInputs o a) := .cons (.named .head) (by simp) .nil
private theorem bound (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RuntimeParametersBind (table arg.type) o [parameter s] [arg] (inputs o arg) := .cons (.named .head) (by simp) .nil
private def bogus (a : Core.Ty) (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) := some (.var 99,a)
private def graph (a : Core.Ty) (names : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) := bogus a names context source=some (core,type)
private def badCore : Core.Expr := .letE (.var 99) (.var 99)
private def badCompiled (o : Resolved.DeclarationId) (a : Core.Ty) : CompiledRuntimeFunction := ⟨staticInputs o a,badCore,a⟩
private def badPrepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) : PreparedRuntimeFunction := ⟨inputs o arg,badCore,arg.type⟩
private theorem bogusSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (bogus arg.type) (table arg.type) o (entry s) [arg]=some (badPrepared o arg) :=
  (prepareComputationFunction?_iff (ChildElab := graph arg.type) Iff.rfl).mpr
    ⟨header s arg.type,bound s o arg,.binding (.named .head) rfl (.expression rfl)⟩
private theorem bogusRun (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (table arg.type) (mapping o) (entry s) [arg] fuel store=
      some (arg.type,Core.runStateful fuel (.initial badCore [arg.value] store)) := by
  rw [runComputationFunction?_mapOwner mapping injective _ (by intros; rfl)]
  simp only [runComputationFunction?,bogusSome s o arg]; rfl
private def badState (arg : TypedRuntimeArgument) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 99) [arg.value],[.letBody (.var 99) [arg.value]],store⟩

theorem all_three_whole_option_laws_require_covariance_but_no_soundness
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (a : Core.Ty) (types : TypeNameTable) (o : Resolved.DeclarationId) (source : Syntax.FunctionDecl)
    (args : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    compileComputationFunction? (bogus a) types (mapping o) source=
      (compileComputationFunction? (bogus a) types o source).map (fun c => {c with inputs := (c.inputs.mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))}) ∧
    prepareComputationFunction? (bogus a) types (mapping o) source args=
      (prepareComputationFunction? (bogus a) types o source args).map (fun p => {p with inputs := (p.inputs.mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))}) ∧
    runComputationFunction? (bogus a) types (mapping o) source args fuel store=
      runComputationFunction? (bogus a) types o source args fuel store :=
  ⟨compileComputationFunction?_mapOwner mapping injective _ (by intros; rfl) types o source,
   prepareComputationFunction?_mapOwner mapping injective _ (by intros; rfl) types o source args,
   runComputationFunction?_mapOwner mapping injective _ (by intros; rfl) types o source args fuel store⟩
theorem original_source_is_well_typed_but_the_covariant_checker_is_not_correct
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RecursiveComputationFunctionCompiles (table arg.type) o (entry s) ⟨staticInputs o arg.type,.letE (.var 0) (.var 0),arg.type⟩ ∧
    prepareComputationFunction? (bogus arg.type) (table arg.type) o (entry s) [arg]=some (badPrepared o arg) ∧
    ¬ Core.HasType [arg.type] (.var 99) arg.type := by
  refine ⟨⟨header s _,declared s o _,.binding (.named .head)
    (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))⟩,bogusSome s o arg,?_⟩
  intro h
  cases h with | var impossible => simp at impossible
theorem the_bad_checker_preserves_genuine_exhaustion_and_full_resumption
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (table arg.type) (mapping o) (entry s) [arg] 0 store=
      some (arg.type,.outOfFuel (.initial badCore [arg.value] store)) ∧
    ∀ extra,Core.runStateful extra (.initial badCore [arg.value] store)=Core.runStateful (0+extra) (.initial badCore [arg.value] store) := by
  rw [bogusRun mapping injective s o arg]
  exact ⟨rfl,Core.runStateful_resume (show Core.runStateful 0 (.initial badCore [arg.value] store)=.outOfFuel _ from rfl)⟩
theorem every_positive_fuel_keeps_the_same_actual_fault_state
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (table arg.type) (mapping o) (entry s) [arg] (fuel+1) store=
      some (arg.type,.fault (.unboundVariable 99) (badState arg store)) := by
  rw [bogusRun mapping injective s o arg]
  simp [Core.runStateful,Core.advance,badCore,badState,Core.State.initial]

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"FunctionOwnerBoundary",by decide⟩],by decide⟩⟩,138⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private def sensitive (a : Core.Ty) (names : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if names.lookup? "x"=some ⟨owner,0⟩ then some (.var 0,a) else none
private def direct (s : Syntax.SourceSpan) : Syntax.FunctionDecl :=
  {(entry s) with value := {(entry s).value with body := ⟨s,[⟨s,.returnStmt (some (ref s))⟩]⟩}}
private def sensitiveGraph (a : Core.Ty) (names : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) := sensitive a names context source=some (core,type)
private theorem sensitiveSome (s : Syntax.SourceSpan) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (sensitive arg.type) (table arg.type) owner (direct s) [arg]=some ⟨inputs owner arg,.var 0,arg.type⟩ :=
  (prepareComputationFunction?_iff (ChildElab := sensitiveGraph arg.type) Iff.rfl).mpr
    ⟨header s _,bound s owner arg,.expression (by simp [sensitiveGraph,sensitive,inputs,LocalNameTable.lookup?,Resolved.freshLocalId_empty])⟩
private theorem sensitiveNone (s : Syntax.SourceSpan) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (sensitive arg.type) (table arg.type) (shift owner) (direct s) [arg]=none := by
  have checkedHeader : interpretRuntimeFunctionHeader? (table arg.type) (direct s).value.signature=some arg.type :=
    interpretRuntimeFunctionHeader?_iff.mpr (header s arg.type)
  have checkedParameters : bindRuntimeParameters? (table arg.type) (shift owner)
      (direct s).value.signature.parameters.elements [arg]=some (inputs (shift owner) arg) := (bound s (shift owner) arg).complete
  simp only [prepareComputationFunction?,checkedHeader,checkedParameters,bind,Option.bind_some]
  simp [elaborateComputationReturnTree?,direct,entry,sensitive,inputs,LocalInputs.toTypeInputs,
    LocalTypeInputs.names,LocalInputs.bindFresh,LocalInputs.empty,LocalInputs.ids,LocalNameTable.lookup?,owner,shift,Resolved.freshLocalId_empty]
theorem injective_nonsurjective_maps_do_not_replace_checker_covariance
    (s : Syntax.SourceSpan) (arg : TypedRuntimeArgument) :
    Function.Injective shift ∧ (¬ Function.Surjective shift) ∧
    prepareComputationFunction? (sensitive arg.type) (table arg.type) owner (direct s) [arg]=some ⟨inputs owner arg,.var 0,arg.type⟩ ∧
    prepareComputationFunction? (sensitive arg.type) (table arg.type) (shift owner) (direct s) [arg]=none := by
  refine ⟨injective,?_,sensitiveSome s arg,sensitiveNone s arg⟩
  intro surjective
  obtain ⟨id,same⟩ := surjective {owner with declarationIndex := 0}
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  change id.declarationIndex+10=0 at impossible
  omega
theorem failed_child_covariance_is_an_actual_unequal_option
    (s : Syntax.SourceSpan) (a : Core.Ty) :
    sensitive a (LocalNameTable.mapIds (ownerLocalIdMap shift) (staticInputs owner a).names)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap shift) (staticInputs owner a).context) (ref s) ≠
      sensitive a (staticInputs owner a).names (staticInputs owner a).context (ref s) := by
  simp [sensitive,staticInputs,LocalTypeInputs.bindFresh_names,LocalNameTable.mapIds,LocalNameTable.lookup?,
    ownerLocalIdMap,owner,shift,Resolved.freshLocalId_empty]
end Tests.FrontendComputationFunctionOwnerBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendComputationFunctionOwnerProperties
/-! Original f,x parameters bind in written order before arbitrary repeated
typed/inferred x binders. Header, parameters, body meaning and actual paths are
constructed independently. Structural actual typing does not validate stores. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionOwner
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr := ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private def fnType (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s,.function s ⟨s,[named s "A"]⟩ (some ⟨s,[named s "B"]⟩)⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b),(["A"],.bool)]
private def parameters (s : Syntax.SourceSpan) : List Syntax.FunctionParameter :=
  [⟨s,.typed none ⟨s,"f"⟩ (fnType s)⟩,⟨s,.typed none ⟨s,"x"⟩ (named s "A")⟩]
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.call (ref s "f") ⟨s,[ref s "x"]⟩⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s,.returnStmt (some (call s))⟩]
  | n+1 => ⟨s,.letDecl ⟨s,"x"⟩ (some (named s "A")) (some (ref s "x"))⟩::
      ⟨s,.letDecl ⟨s,"x"⟩ none (some (ref s "x"))⟩::statements s n
private def entry (s : Syntax.SourceSpan) (n : Nat) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"ownerCovariant"⟩,none,⟨s,parameters s⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s "B"]⟩⟩,none⟩,⟨s,statements s n⟩⟩⟩
private def scope (o : Resolved.DeclarationId) (a b : Core.Ty) : Nat → LocalTypeInputs
  | 0 => (LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "x" a
  | m+1 => (scope o a b m).bindFresh o "x" a
private def code : Nat → Nat → Core.Expr
  | 0,m => .apply (.var (m+1)) (.var 0)
  | n+1,m => .letE (.var 0) (.letE (.var 0) (code n (m+2)))
private theorem functionMeaning (s : Syntax.SourceSpan) (a b : Core.Ty) : StructuralTypeDenotes (types a b) (fnType s) (.function a b) :=
  .functionReturns (.named .head) (.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head)))
private theorem header (s : Syntax.SourceSpan) (a b : Core.Ty) (n : Nat) : RuntimeFunctionHeader (types a b) (entry s n).value.signature b :=
  ⟨rfl,rfl,rfl,rfl,.single (.named (.tail (by change (["A"] : List String) ≠ ["B"]; decide) .head))⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) :
    RuntimeParametersDeclare (types a b) o (parameters s) (scope o a b 0) :=
  .cons (functionMeaning s a b) (by simp) (.cons (.named .head) (by simp [LocalTypeInputs.names,LocalTypeInputs.bindFresh,LocalTypeInputs.empty]) .nil)
private theorem functionFacts (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    LocalNameTable.Lookup (scope o a b m).names "f" ⟨o,0⟩ ∧
    Resolved.LocalScope.IndexOf (scope o a b m).context.ids ⟨o,0⟩ (m+1) ∧
    Resolved.LocalScope.Lookup (scope o a b m).context ⟨o,0⟩ (.function a b) := by
  induction m with
  | zero =>
      have different := Resolved.freshLocalId_cons_fresh_ne o []
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) .head,.tail different .head,.tail different .head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId o (scope o a b m).ids ≠ ⟨o,0⟩ := by
        intro same
        have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o a b m).names.map Prod.snd := List.mem_map.mpr ⟨("f",⟨o,0⟩),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
      exact ⟨.tail (by change ("x" : String) ≠ "f"; decide) ih.1,.tail different ih.2.1,.tail different ih.2.2⟩
private theorem argumentElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (m : Nat) :
    RecursiveLocalComputationElaborates (scope o a b m).names (scope o a b m).context (ref s "x") (.var 0) a := by
  cases m <;> exact .pure (.identifier .head) (.var .head) (.var .head)
private theorem bodyElab (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n m : Nat) :
    RecursiveComputationReturnTreeElaborates (types a b) o (scope o a b m) ⟨s,statements s n⟩ (code n m) b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (functionFacts o a b m).1) (.var (functionFacts o a b m).2.1) (.var (functionFacts o a b m).2.2))
      (argumentElab s o a b m))
  | succ n ih =>
      exact .binding (.named .head) (argumentElab s o a b m)
        (.inferred (argumentElab s o a b (m+1)) (ih (m+2)))
private structure Actual where
  argument : TypedRuntimeArgument
  resultType : Core.Ty
  body : Core.Expr
  captured : Core.Environment
  typed : Core.ValueHasType (.closure argument.type resultType body captured) (.function argument.type resultType)
private def Actual.fn (r : Actual) : TypedRuntimeArgument := ⟨.function r.argument.type r.resultType,.closure r.argument.type r.resultType r.body r.captured,r.typed⟩
private def Actual.inputs (r : Actual) (o : Resolved.DeclarationId) :=
  (LocalInputs.empty.bindFresh o "f" r.fn.type r.fn.value r.fn.valueTyped).bindFresh o "x" r.argument.type r.argument.value r.argument.valueTyped
private def compiled (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) : CompiledRuntimeFunction := ⟨scope o a b 0,code n 0,b⟩
private def prepared (o : Resolved.DeclarationId) (r : Actual) (n : Nat) : PreparedRuntimeFunction := ⟨r.inputs o,code n 0,r.resultType⟩
private theorem compilation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a b : Core.Ty) (n : Nat) :
    RecursiveComputationFunctionCompiles (types a b) o (entry s n) (compiled o a b n) :=
  ⟨header s a b n,declared s o a b,bodyElab s o a b n 0⟩
private theorem binding (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) :
    RuntimeParametersBind (types r.argument.type r.resultType) o (parameters s) [r.fn,r.argument] (r.inputs o) :=
  .cons (functionMeaning s _ _) (by simp) (.cons (.named .head) (by simp [LocalInputs.names,LocalInputs.bindFresh,LocalInputs.empty]) .nil)
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) :=
  ⟨header s _ _ n,binding s o r,bodyElab s o _ _ n 0⟩
private def environment (o : Resolved.DeclarationId) (r : Actual) : Nat → Resolved.Environment
  | 0 => (r.inputs o).environment
  | m+1 => (Resolved.freshLocalId o (scope o r.argument.type r.resultType m).ids,r.argument.value)::environment o r m
private theorem rawFunction (o : Resolved.DeclarationId) (r : Actual) (m : Nat) :
    Resolved.LocalScope.Lookup (environment o r m) ⟨o,0⟩ r.fn.value := by
  induction m with
  | zero => exact .tail (Resolved.freshLocalId_cons_fresh_ne o []) .head
  | succ m ih =>
      refine .tail ?_ ih
      intro same
      have member : (⟨o,0⟩ : Resolved.LocalId) ∈ (scope o r.argument.type r.resultType m).names.map Prod.snd :=
        List.mem_map.mpr ⟨("f",⟨o,0⟩),(functionFacts o r.argument.type r.resultType m).1.mem,rfl⟩
      rw [LocalTypeInputs.names_ids] at member
      exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
private theorem rawArgument (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (m : Nat) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (scope o r.argument.type r.resultType m).names (environment o r m) store
      (ref s "x") r.argument.value store 1 := by
  cases m <;> exact .pure (.identifier .head .head)
private theorem rawCost (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n m : Nat)
    (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (scope o r.argument.type r.resultType m).names (environment o r m)
      initial ⟨s,statements s n⟩ v final (6*n+cost+5) := by
  induction n generalizing m with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact .expression (.application (.pure (.identifier (functionFacts o r.argument.type r.resultType m).1 (rawFunction o r m))) (rawArgument s o r m initial) actual)
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      refine .binding (rawArgument s o r m initial) ?_
      change RecursiveComputationReturnTreeEvaluatesWithCost o
        (("x",Resolved.freshLocalId o ((scope o r.argument.type r.resultType m).names.map Prod.snd))::(scope o r.argument.type r.resultType m).names) _ _ _ _ _ _
      rw [LocalTypeInputs.names_ids]
      refine .inferred (rawArgument s o r (m+1) initial) ?_
      simpa only [scope,LocalTypeInputs.bindFresh_names,LocalTypeInputs.bindFresh_ids,List.map_cons,
        LocalTypeInputs.names_ids,environment] using ih (m+2)
private theorem manual (r : Actual) (n m : Nat) (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) (k : List Core.Frame) :
    Core.Steps (6*n+cost+5) ⟨.eval (code n m) (List.replicate (m+1) r.argument.value++[r.fn.value]),k,initial⟩ ⟨.ret v,k,final⟩ := by
  induction n generalizing m k with
  | zero =>
      have count : 6*0+cost+5=1+1+cost+3 := by omega
      rw [count]
      exact CostStepComposition.apply (parameterType := r.argument.type) (resultType := r.resultType)
        (.cons (.var (by simp [Actual.fn])) .refl) (.cons (.var (by simp)) .refl) actual
  | succ n ih =>
      have count : 6*(n+1)+cost+5=1+(1+(6*n+cost+5)+2)+2 := by omega
      rw [count]
      simpa [code,List.replicate_succ] using CostStepComposition.letE (.cons (.var rfl) .refl)
        (CostStepComposition.letE (.cons (.var rfl) .refl) (ih (m+2) k))
private theorem childMap (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    {table context source core type} :
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
      RecursiveLocalComputationElaborates table context source core type :=
  recursiveLocalComputationElaborates_mapIds_iff _ (ownerLocalIdMap_injective mapping injective)
private theorem checkerMap (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (table context source) :
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source = elaborateRecursiveLocalComputation? table context source :=
  elaborateRecursiveLocalComputation?_mapIds _ (ownerLocalIdMap_injective mapping injective) table context source
private theorem preparedSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    prepareComputationFunction? elaborateRecursiveLocalComputation? (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument]=some (prepared o r n) :=
  (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (preparation s o r n)

theorem original_records_have_independent_header_parameters_and_body
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionCompiles (types r.argument.type r.resultType) o (entry s n)
      (compiled o r.argument.type r.resultType n) ∧
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) o (entry s n) [r.fn,r.argument] (prepared o r n) :=
  ⟨compilation s o _ _ n,preparation s o r n⟩
theorem original_argument_order_is_reversed_exactly_once_in_actual_rows
    (o : Resolved.DeclarationId) (r : Actual) :
    (r.inputs o).bindings.map (·.name)=["x","f"] ∧
    (r.inputs o).environment.values=[r.argument.value,r.fn.value] ∧
    (r.inputs o).ids=[Resolved.freshLocalId o [⟨o,0⟩],⟨o,0⟩] ∧
    (Resolved.freshLocalId o [⟨o,0⟩]).binderIndex=1 :=
  ⟨rfl,rfl,rfl,Resolved.freshLocalId_cons_fresh_binderIndex o []⟩
theorem both_independent_record_judgments_preserve_original_source_and_actuals
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    RecursiveComputationFunctionCompiles (types r.argument.type r.resultType) (mapping o) (entry s n)
      {(compiled o r.argument.type r.resultType n) with inputs := ((scope o r.argument.type r.resultType 0).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))} ∧
    RecursiveComputationFunctionPrepares (types r.argument.type r.resultType) (mapping o) (entry s n) [r.fn,r.argument]
      {(prepared o r n) with inputs := (r.inputs o).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} :=
  ⟨(computationFunctionCompiles_mapOwner_iff mapping injective (childMap mapping injective)).mpr (compilation s o _ _ n),
   (computationFunctionPrepares_mapOwner_iff mapping injective (childMap mapping injective)).mpr (preparation s o r n)⟩
theorem whole_optional_records_preserve_original_body_and_return_annotation
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat) :
    compileRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n)=
      some {(compiled o r.argument.type r.resultType n) with inputs := ((scope o r.argument.type r.resultType 0).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))} ∧
    prepareRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n) [r.fn,r.argument]=
      some {(prepared o r n) with inputs := (r.inputs o).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)} := by
  constructor
  · dsimp only [compileRecursiveComputationFunction?]
    rw [compileComputationFunction?_mapOwner mapping injective _ (checkerMap mapping injective),
      (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (compilation s o r.argument.type r.resultType n)]; rfl
  · dsimp only [prepareRecursiveComputationFunction?]
    rw [prepareComputationFunction?_mapOwner mapping injective _ (checkerMap mapping injective),preparedSome s o r n]; rfl
theorem original_raw_cost_and_separately_written_literal_core_path
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n : Nat)
    (initial final : Core.Store) (v : Core.Value) (cost : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) (k : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (r.inputs o).names (r.inputs o).environment
      initial (entry s n).value.body v final (6*n+cost+5) ∧
    Core.Steps (6*n+cost+5) ⟨.eval (code n 0) [r.argument.value,r.fn.value],k,initial⟩ ⟨.ret v,k,final⟩ :=
  ⟨rawCost s o r n 0 initial final v cost actual,manual r n 0 initial final v cost actual k⟩
theorem full_runner_preserves_exact_faults_checkpoints_and_final_records
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (r : Actual) (n fuel : Nat) (store : Core.Store) :
    runRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n) [r.fn,r.argument] fuel store =
      some (r.resultType,Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] store)) := by
  dsimp only [runRecursiveComputationFunction?]
  rw [runComputationFunction?_mapOwner mapping injective _ (checkerMap mapping injective)]
  unfold runComputationFunction?
  rw [preparedSome s o r n]; rfl
theorem all_fuel_thresholds_and_genuine_resumption_keep_actual_body_effects
    (r : Actual) (n : Nat) (initial final : Core.Store) (v : Core.Value) (cost fuel extra : Nat)
    (actual : Core.Steps cost (.initial r.body (r.argument.value::r.captured) initial) (.final v final)) :
    (Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] initial)=.done v final ↔ 6*n+cost+5≤fuel) ∧
    ((∃ cp,Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] initial)=.outOfFuel cp) ↔ fuel<6*n+cost+5) ∧
    ∀ cp,Core.runStateful fuel (.initial (code n 0) [r.argument.value,r.fn.value] initial)=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (code n 0) [r.argument.value,r.fn.value] initial) :=
  ⟨(manual r n 0 initial final v cost actual []).runStateful_done_iff,
   (manual r n 0 initial final v cost actual []).runStateful_outOfFuel_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem first_initializer_finishes_in_the_old_actual_environment
    (r : Actual) (n : Nat) (store : Core.Store) (k : List Core.Frame) :
    let cp : Core.State := ⟨.ret r.argument.value,.letBody (.letE (.var 0) (code n 2)) [r.argument.value,r.fn.value]::k,store⟩
    Core.runStateful 2 ⟨.eval (code (n+1) 0) [r.argument.value,r.fn.value],k,store⟩=.outOfFuel cp ∧
    ∀ extra,Core.runStateful extra cp=Core.runStateful (2+extra) ⟨.eval (code (n+1) 0) [r.argument.value,r.fn.value],k,store⟩ := by
  have stopped : Core.runStateful 2 ⟨.eval (code (n+1) 0) [r.argument.value,r.fn.value],k,store⟩=.outOfFuel _ := rfl
  exact ⟨stopped,Core.runStateful_resume stopped⟩
private def delayed (a : Core.Ty) : Nat → Core.Expr
  | 0 => .newCell a (.var 0)
  | m+1 => .letE (.var 0) (delayed a m)
private theorem delayedTyped (a : Core.Ty) (_payload : Core.CellPayload a) (m : Nat) (context : Core.Context) :
    Core.HasType (a::context) (delayed a m) (.cell a) := by
  induction m generalizing context with
  | zero => exact .newCell (.var rfl)
  | succ m ih => exact .letE (.var rfl) (ih (a::context))
private theorem delayedPath (a : Core.Ty) (m : Nat) (v : Core.Value) (captured : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*m+3) ⟨.eval (delayed a m) (v::captured),k,store⟩ ⟨.ret (.cellRef a store.length),k,store++[v]⟩ := by
  induction m generalizing captured k with
  | zero => exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))
  | succ m ih =>
      have count : 3*(m+1)+3=1+(3*m+3)+2 := by omega
      rw [count]; exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (v::captured) k)
private def allocator (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (m : Nat) : Actual :=
  ⟨arg,.cell arg.type,delayed arg.type m,captured,.closure typed (delayedTyped arg.type payload m context)⟩
theorem actual_allocation_and_every_retained_capture_survive_owner_change
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (n m : Nat) (store : Core.Store) :
    let r := allocator arg payload captured context typed m
    runRecursiveComputationFunction? (types arg.type (.cell arg.type)) (mapping o) (entry s n) [r.fn,arg] (6*n+3*m+8) store=
      some (.cell arg.type,.done (.cellRef arg.type store.length) (store++[arg.value])) := by
  let r := allocator arg payload captured context typed m
  change runRecursiveComputationFunction? (types r.argument.type r.resultType) (mapping o) (entry s n)
    [r.fn,r.argument] (6*n+3*m+8) store=some (r.resultType,.done (.cellRef arg.type store.length) (store++[arg.value]))
  rw [full_runner_preserves_exact_faults_checkpoints_and_final_records mapping injective s o r n]
  congr 1
  congr 1
  exact (manual r n 0 store (store++[arg.value]) (.cellRef arg.type store.length) (3*m+3)
    (delayedPath arg.type m arg.value captured store []) []).runStateful_done_iff.mpr (by omega)
theorem a_fixed_original_declaration_has_no_source_only_actual_cost_bound
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (payload : Core.CellPayload arg.type)
    (captured : Core.Environment) (context : Core.Context) (typed : Core.EnvironmentHasTypes captured context) (store : Core.Store) (bound : Nat) :
    ∃ m, bound<3*m+8 ∧
      let r := allocator arg payload captured context typed m
      RecursiveComputationReturnTreeEvaluatesWithCost o (r.inputs o).names (r.inputs o).environment
        store (entry s 0).value.body (.cellRef arg.type store.length) (store++[arg.value]) (3*m+8) := by
  refine ⟨bound,by omega,?_⟩
  simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_assoc,Nat.reduceAdd] using (original_raw_cost_and_separately_written_literal_core_path s o
    (allocator arg payload captured context typed bound) 0 store (store++[arg.value]) (.cellRef arg.type store.length) (3*bound+3)
    (delayedPath arg.type bound arg.value captured store []) []).1
end Tests.FrontendComputationFunctionOwner
end

section
-- leanmerge: from Solcore.Test.FrontendComputationFunctionTypeTableProperties
/-! Original symbolic headers, parameter binding and same-name lets have independent
meaning before checker transport. Arbitrary actual records retain every capture.
The deliberately incorrect checker below tests equations, not source soundness. -/
set_option autoImplicit false
namespace Tests.FrontendComputationFunctionTypeTable
open Solcore Solcore.Frontend
private def named (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,"Payload"⟩,[]⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Payload"],a),(["Payload"],.bool)]
private def ref (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s,.identifier ⟨s,"x"⟩⟩
private def body (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,
  [⟨s,.letDecl ⟨s,"x"⟩ (some (named s)) (some (ref s))⟩,⟨s,.returnStmt (some (ref s))⟩]⟩
private def parameter (s : Syntax.SourceSpan) : Syntax.FunctionParameter := ⟨s,.typed none ⟨s,"x"⟩ (named s)⟩
private def entry (s : Syntax.SourceSpan) : Syntax.FunctionDecl := ⟨s,
  ⟨⟨s,⟨s,"transported"⟩,none,⟨s,[parameter s]⟩,⟨none,none⟩,
    some ⟨s,⟨s,[named s]⟩⟩,none⟩,body s⟩⟩
private def initial (o : Resolved.DeclarationId) (a : Core.Ty) := LocalTypeInputs.empty.bindFresh o "x" a
private def core : Core.Expr := .letE (.var 0) (.var 0)
private def compiled (o : Resolved.DeclarationId) (a : Core.Ty) : CompiledRuntimeFunction := ⟨initial o a,core,a⟩
private def inputs (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :=
  LocalInputs.empty.bindFresh o "x" arg.type arg.value arg.valueTyped
private def prepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨inputs o arg,core,arg.type⟩
private theorem header (s : Syntax.SourceSpan) (a : Core.Ty) : RuntimeFunctionHeader (types a) (entry s).value.signature a :=
  ⟨rfl,rfl,rfl,rfl,.single (.named .head)⟩
private theorem declared (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RuntimeParametersDeclare (types a) o [parameter s] (initial o a) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty,LocalTypeInputs.names]) .nil
private theorem provenance (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) o (initial o a) (body s) core a :=
  .binding (.named .head) (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    RecursiveComputationFunctionCompiles (types a) o (entry s) (compiled o a) :=
  ⟨header s a,declared s o a,provenance s o a⟩
private theorem bound (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RuntimeParametersBind (types arg.type) o [parameter s] [arg] (inputs o arg) :=
  .cons (.named .head) (by simp [LocalInputs.empty,LocalInputs.names]) .nil
private theorem preparation (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    RecursiveComputationFunctionPrepares (types arg.type) o (entry s) [arg] (prepared o arg) :=
  ⟨header s arg.type,bound s o arg,provenance s o arg.type⟩
private theorem raw (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (inputs o arg).names (inputs o arg).environment
      store (body s) arg.value store 4 := by
  change ComputationReturnTreeEvaluatesWithCost RecursiveLocalComputationEvaluatesWithCost o
    [("x",_)] [(_,arg.value)] store (body s) arg.value store 4
  refine ComputationReturnTreeEvaluatesWithCost.binding (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (initializerCost := 1) (tailCost := 1) (boundValue := arg.value) (middleStore := store) ?_ ?_
  · exact .pure (.identifier .head .head)
  · exact .expression (.pure (.identifier .head .head))
private theorem manual (value : Core.Value) (retained : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 4 ⟨.eval core (value::retained),k,store⟩ ⟨.ret value,k,store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
private theorem compileSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (a : Core.Ty) :
    compileRecursiveComputationFunction? (types a) o (entry s)=some (compiled o a) :=
  (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (compilation s o a)
private theorem prepareSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    prepareRecursiveComputationFunction? (types arg.type) o (entry s) [arg]=some (prepared o arg) :=
  (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr (preparation s o arg)

theorem independent_original_records_survive_every_meaning_extension
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types arg.type) next) :
    RecursiveComputationFunctionCompiles next o (entry s) (compiled o arg.type) ∧
    RecursiveComputationFunctionPrepares next o (entry s) [arg] (prepared o arg) :=
  ⟨(compilation s o arg.type).extend_types extension,(preparation s o arg).extend_types extension⟩
theorem complete_compilation_and_value_bearing_preparation_survive_append
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (extras : TypeNameTable) :
    compileRecursiveComputationFunction? (types arg.type++extras) o (entry s)=some (compiled o arg.type) ∧
    prepareRecursiveComputationFunction? (types arg.type++extras) o (entry s) [arg]=some (prepared o arg) :=
  ⟨compileComputationFunction?_some_of_extends (TypeNameTable.Extends.append_right _ _) (compileSome s o arg.type),
    prepareComputationFunction?_some_of_extends (TypeNameTable.Extends.append_right _ _) (prepareSome s o arg)⟩
theorem independent_raw_cost_and_literal_pending_path
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (store : Core.Store) (k : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost o (inputs o arg).names (inputs o arg).environment
      store (body s) arg.value store 4 ∧
    Core.Steps 4 ⟨.eval core (inputs o arg).environment.values,k,store⟩ ⟨.ret arg.value,k,store⟩ :=
  ⟨raw s o arg store,manual arg.value [] store k⟩
theorem every_full_run_preserves_exact_actual_values_and_store
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types arg.type) next) (fuel : Nat) (store : Core.Store) :
    runRecursiveComputationFunction? next o (entry s) [arg] fuel store=
      some (arg.type,Core.runStateful fuel (.initial core [arg.value] store)) := by
  apply runComputationFunction?_some_of_extends extension
  simp only [runComputationFunction?,prepareSome s o arg]; rfl
theorem exact_completion_and_all_genuine_resumptions_survive_append
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (extras : TypeNameTable) (fuel extra : Nat) (store : Core.Store) :
    (runRecursiveComputationFunction? (types arg.type++extras) o (entry s) [arg] fuel store=
      some (arg.type,.done arg.value store) ↔ 4≤fuel) ∧
    ∀ cp, runRecursiveComputationFunction? (types arg.type++extras) o (entry s) [arg] fuel store=
      some (arg.type,.outOfFuel cp) →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial core [arg.value] store) := by
  rw [every_full_run_preserves_exact_actual_values_and_store s o arg _ (TypeNameTable.Extends.append_right _ _) fuel store]
  simp only [Option.some.injEq,Prod.mk.injEq,true_and]
  exact ⟨(manual arg.value [] store []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
private theorem hiddenMutual (a hidden : Core.Ty) :
    TypeNameTable.Extends (types a) [(["Payload"],a),(["Payload"],hidden)] ∧
    TypeNameTable.Extends [(["Payload"],a),(["Payload"],hidden)] (types a) := by
  constructor <;> intro key type found <;> cases found with
  | head => exact .head
  | tail different found => cases found with
    | head => exact False.elim (different rfl)
    | tail _ found => cases found
theorem hidden_rows_keep_all_optional_records_for_an_arbitrary_fixed_checker
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (a hidden : Core.Ty) (o : Resolved.DeclarationId) (source : Syntax.FunctionDecl)
    (args : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    compileComputationFunction? checkChild (types a) o source=
      compileComputationFunction? checkChild [(["Payload"],a),(["Payload"],hidden)] o source ∧
    prepareComputationFunction? checkChild (types a) o source args=
      prepareComputationFunction? checkChild [(["Payload"],a),(["Payload"],hidden)] o source args ∧
    runComputationFunction? checkChild (types a) o source args fuel store=
      runComputationFunction? checkChild [(["Payload"],a),(["Payload"],hidden)] o source args fuel store :=
  ⟨compileComputationFunction?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o source,
    prepareComputationFunction?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o source args,
    runComputationFunction?_eq_of_mutual_extends (hiddenMutual a hidden).1 (hiddenMutual a hidden).2 o source args fuel store⟩

private def bogus (a : Core.Ty) (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  some (.var 99,a)
private def graph (a : Core.Ty) (names : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) (expression : Core.Expr) (type : Core.Ty) := bogus a names context source=some (expression,type)
private def badCore : Core.Expr := .letE (.var 99) (.var 99)
private def badPrepared (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) : PreparedRuntimeFunction :=
  ⟨inputs o arg,badCore,arg.type⟩
private theorem bogusSome (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) :
    prepareComputationFunction? (bogus arg.type) (types arg.type) o (entry s) [arg]=some (badPrepared o arg) :=
  (prepareComputationFunction?_iff (ChildElab := graph arg.type) Iff.rfl).mpr
    ⟨header s arg.type,bound s o arg,.binding (.named .head) rfl (.expression rfl)⟩
private def badState (arg : TypedRuntimeArgument) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 99) [arg.value],[.letBody (.var 99) [arg.value]],store⟩
private theorem bogusRun (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types arg.type) next) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) next o (entry s) [arg] fuel store=
      some (arg.type,Core.runStateful fuel (.initial badCore [arg.value] store)) := by
  apply runComputationFunction?_some_of_extends extension
  simp only [runComputationFunction?,bogusSome s o arg]; rfl
theorem incorrect_checker_exhaustion_is_transported_without_becoming_safety
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument) (extras : TypeNameTable) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (types arg.type++extras) o (entry s) [arg] 0 store=
      some (arg.type,.outOfFuel (.initial badCore [arg.value] store)) := by
  rw [bogusRun s o arg _ (TypeNameTable.Extends.append_right _ _)]; rfl
theorem incorrect_checker_fault_keeps_the_exact_saved_state_for_all_positive_fuel
    (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (arg : TypedRuntimeArgument)
    (extras : TypeNameTable) (fuel : Nat) (store : Core.Store) :
    runComputationFunction? (bogus arg.type) (types arg.type++extras) o (entry s) [arg] (fuel+1) store=
      some (arg.type,.fault (.unboundVariable 99) (badState arg store)) := by
  rw [bogusRun s o arg _ (TypeNameTable.Extends.append_right _ _)]
  simp [Core.runStateful,Core.advance,badCore,badState,Core.State.initial]
end Tests.FrontendComputationFunctionTypeTable
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationFunctionOwnerBoundaries
/-! Original parsed preparation failures remain absent under owner transport.
Selected raw body success does not repair a header, parameter list or branch. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationFunctionOwnerBoundaries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"FunctionOwnerBoundary",by decide⟩],by decide⟩⟩,136⟩
private def mapping (o : Resolved.DeclarationId) : Resolved.DeclarationId :=
  {o with declarationIndex := o.declarationIndex+17}
private theorem injective : Function.Injective mapping := by
  rintro ⟨a,n⟩ ⟨b,m⟩ same; simpa [mapping] using same
private def relabel := ownerLocalIdMap mapping
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective mapping injective
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Word"],.bool)]
private def word : Core.Value := .word (Core.Word.ofNatModulo 14)
private def wordArg : TypedRuntimeArgument := ⟨.word,word,.word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool,.bool b,.bool⟩
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"function-owner-boundary.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"parser: {text}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) &&
    source.span.contains source.value.signature.span && source.span.contains source.value.body.span &&
    source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original complete function and header/body ranges"
  return source
private def compiledRows (c : CompiledRuntimeFunction) :=
  (c.inputs.bindings.map (fun r => (r.name,r.id,r.type)),c.core,c.returnType)
private def preparedRows (p : PreparedRuntimeFunction) :=
  (p.inputs.bindings.map (fun r => (r.name,r.id,r.type,r.value)),p.core,p.returnType)
private def rejected (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument)
    (compiles : Bool := false) : IO Unit := do
  let oldCompile := compileRecursiveComputationFunction? types owner source
  let nextCompile := compileRecursiveComputationFunction? types (mapping owner) source
  have compileLaw := compileComputationFunction?_mapOwner mapping injective elaborateRecursiveLocalComputation?
    (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner source
  have prepareLaw := prepareComputationFunction?_mapOwner mapping injective elaborateRecursiveLocalComputation?
    (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner source args
  check (oldCompile.isSome==compiles) "value-free compilation must be classified separately from bad actual arguments"
  check (decide (nextCompile.map compiledRows = (oldCompile.map (fun c =>
    {c with inputs := c.inputs.mapIds relabel relabel_injective})).map compiledRows)) "all compiled rows/Core/type retained"
  have _ := congrArg (Option.map compiledRows) compileLaw
  match absent : prepareRecursiveComputationFunction? types owner source args with
  | some _ => throw (IO.userError "original preparation unexpectedly accepted")
  | none =>
      have absentMapped : prepareRecursiveComputationFunction? types (mapping owner) source args=none := by
        change prepareComputationFunction? _ _ _ _ _ = _
        rw [prepareLaw]
        change (prepareRecursiveComputationFunction? types owner source args).map _ = none
        rw [absent]; rfl
      have noOriginal : ¬ ∃ p, RecursiveComputationFunctionPrepares types owner source args p := by
        rintro ⟨p,h⟩
        have impossible := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr h
        change prepareRecursiveComputationFunction? types owner source args=some p at impossible
        rw [absent] at impossible; cases impossible
      have noMapped : ¬ ∃ p, RecursiveComputationFunctionPrepares types (mapping owner) source args p := by
        rintro ⟨p,h⟩
        have impossible := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr h
        change prepareRecursiveComputationFunction? types (mapping owner) source args=some p at impossible
        rw [absentMapped] at impossible; cases impossible
      have _ := noOriginal; have _ := noMapped
      check (decide ((prepareRecursiveComputationFunction? types (mapping owner) source args).map preparedRows=none))
        "no mapped complete prepared record"
      for store in [[],[Core.Value.bool false,.cellRef .word 700,word]] do
        for fuel in [0,1,4,25] do
          have _ := runComputationFunction?_mapOwner mapping injective elaborateRecursiveLocalComputation?
            (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner source args fuel store
          have originalNone : runRecursiveComputationFunction? types owner source args fuel store=none := by
            simp only [runRecursiveComputationFunction?,runComputationFunction?,absent,bind,Option.bind_none]
          have _ := originalNone
          check (decide (runRecursiveComputationFunction? types owner source args fuel store=none ∧
            runRecursiveComputationFunction? types (mapping owner) source args fuel store=none))
            "preparation absence is None, never a runtime fault or exhausted state"
  match absent : compileRecursiveComputationFunction? types owner source with
  | none =>
      have _ : ¬ ∃ c, RecursiveComputationFunctionCompiles types owner source c := by
        rintro ⟨c,h⟩
        have impossible := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr h
        change compileRecursiveComputationFunction? types owner source=some c at impossible
        rw [absent] at impossible; cases impossible
      check nextCompile.isNone "compile absence retained"
  | some _ => pure ()
private structure Atom (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ st, RecursiveLocalComputationEvaluatesWithCost names env st s value st 1
private def atom (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Expr) : IO (Atom names env s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : names.lookup? name.value with
    | some localId => match found : env.lookup? localId with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .pure (.identifier
          (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _ => throw (IO.userError "original raw row")
    | _ => throw (IO.userError "original raw name")
  | _ => throw (IO.userError "raw identifier fixture")
private structure Raw (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ st, RecursiveComputationReturnTreeEvaluatesWithCost owner names env st s value st cost
private def raw (names : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Block) : IO (Raw names env s) := do
  check (s.value.all fun statement => s.span.contains statement.span) "original raw statement ranges"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ =>
      let a ← atom names env expression
      return ⟨a.value,1,fun st => by rw [shape]; exact .expression (a.evidence st)⟩
  | ⟨span,⟨_,.letDecl name annotation (some init)⟩::rest⟩ =>
      let a ← atom names env init
      let fresh := Resolved.freshLocalId owner (names.map Prod.snd)
      let b ← raw ((name.value,fresh)::names) ((fresh,a.value)::env) ⟨span,rest⟩
      return ⟨b.value,1+b.cost+2,fun st => by
        rw [shape]; cases annotation with
        | none => exact .inferred (a.evidence st) (b.evidence st)
        | some _ => exact .binding (a.evidence st) (b.evidence st)⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let a ← atom names env condition
      match selected : a.value with
      | .bool true =>
          let b ← raw names env yes
          return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifTrue (selected ▸ a.evidence st) (b.evidence st)⟩
      | .bool false =>
          let b ← raw names env no
          return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifFalse (selected ▸ a.evidence st) (b.evidence st)⟩
      | _ => throw (IO.userError "original raw condition")
  | _ => throw (IO.userError "raw body fixture")
termination_by sizeOf s
private def rawOnly (text : String) (yesCost noCost : Nat) (yesValue noValue : Core.Value) : IO Unit := do
  let source ← parsed text
  let names : LocalNameTable := [("c",⟨owner,1⟩),("x",⟨owner,0⟩)]
  for choice in [false,true] do
    let env : Resolved.Environment := [(⟨owner,1⟩,.bool choice),(⟨owner,0⟩,word)]
    let original ← raw names env source.value.body
    if same : original.cost=(if choice then yesCost else noCost) ∧ original.value=(if choice then yesValue else noValue) then
      have _ : ∀ st, RecursiveComputationReturnTreeEvaluatesWithCost owner names env st source.value.body
          (if choice then yesValue else noValue) st (if choice then yesCost else noCost) := by
        simpa only [same.1,same.2] using original.evidence
      rejected source [wordArg,boolArg choice]
    else throw (IO.userError "independent selected original raw value/cost")
end ParsedComputationFunctionOwnerBoundaries
open ParsedComputationFunctionOwnerBoundaries in
def frontendParsedComputationFunctionOwnerBoundaryTests : IO Unit := do
  let identity ← parsed "function identity(x:Word)returns(Word){return x;}"
  for args in [[],[wordArg,wordArg],[boolArg true]] do rejected identity args true
  let noArgs ← parsed "function empty(){return;}"
  rejected noArgs [wordArg] true
  for (text,args) in [
      ("function duplicate(x:Word,x:Word)returns(Word){return x;}",[wordArg,wordArg]),
      ("function compile(comptime x:Word)returns(Word){return x;}",[wordArg]),
      ("function unknown(x:Missing)returns(Word){return x;}",[wordArg]),
      ("function mismatch(x:Word)returns(Bool){return x;}",[wordArg]),
      ("function absent(x:Word){return x;}",[wordArg]),
      ("function unknownReturn(x:Word)returns(Missing){return x;}",[wordArg]),
      ("function emptyReturn(x:Word)returns(){return x;}",[wordArg]),
      ("function many(x:Word)returns(Word,Bool){return x;}",[wordArg]),
      ("function generic<T>(x:Word)returns(Word){return x;}",[wordArg]),
      ("function constrained(x:Word)returns(Word)where Word:Eq{return x;}",[wordArg]),
      ("function missing(x:Word)returns(Word){return missing;}",[wordArg])] do
    rejected (← parsed text) args
  for text in ["function publicOnly(x:Word)public returns(Word){return x;}",
      "function payableOnly(x:Word)payable returns(Word){return x;}"] do
    rejected (← parsed text .contract) [wordArg]
  rawOnly "function unknownBranch(x:Word,c:Bool)returns(Word){if(c){return x;}else{let x:Missing=x;return x;}}" 4 7 word word
  rawOnly "function exposed(x:Word,c:Bool)returns(Word){if(c){let x=x;return x;}else{return x;}}" 7 4 word word
  rawOnly "function branches(x:Word,c:Bool)returns(Word){if(c){return c;}else{return x;}}" 4 4 (.bool true) word
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationFunctionOwnerEffects
/-! Independent original header/parameters/body and actual raw/manual paths precede
owner transport. Actual closures, stores and full records retain their identity. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationFunctionOwnerEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationFunctionOwnerEffects",by decide⟩],by decide⟩⟩,134⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by rintro ⟨lm,li⟩ ⟨rm,ri⟩ same; simpa [shift] using same
private theorem non_surjective : ¬ Function.Surjective shift := by
  intro h; obtain ⟨o,same⟩ := h {owner with declarationIndex := 0}
  have h := congrArg Resolved.DeclarationId.declarationIndex same; simp [shift] at h
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def checkedReader (l : Nat) : Core.Value := .closure .word .word (.binary .wordAdd (.loadCell (.var 1)) (.var 0)) [.cellRef .word l]
private def callCore : Core.Expr := .apply (.var 3) (.var 0)
private def branchCore : Core.Expr := .letE callCore (.var 0)
private def afterCore : Core.Expr := .ifE (.var 1) branchCore callCore
private def core : Core.Expr := .letE (.apply (.var 3) (.var 1)) afterCore
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:function(Word) returns(Word),g:function(Word) returns(Word),x:Word,c:Bool) returns(Word){let x:Word=f(x);if(c){{let x=g(x);return x;}}else{return g(x);}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-function-owner-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple results⟩; return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _,_ => throw (IO.userError "original arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← body i ⟨span,statements⟩; return ⟨r.core,r.type,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.length=i.ids.length+1 ∧ next.ids.head?=some ⟨owner,i.bindings.length⟩ ∧ i.names.lookup? "x"=some ⟨owner,if i.bindings.length=4 then 2 else 4⟩)) "fresh4/5 retains old x2/4 and every captured row"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← child i c; let t ← body i yes; let e ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : a.type=.bool ∧ t.type=e.type then return ⟨.ifE a.core t.core e.core,t.type,by rw [shape]; exact .conditional (same.1 ▸ a.evidence) protection t.evidence (same.2.symm ▸ e.evidence)⟩ else throw (IO.userError "branch type")
      | _ => throw (IO.userError "original explicit then scope barrier")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private structure Preparation (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) where
  compiled : CompiledRuntimeFunction
  prepared : PreparedRuntimeFunction
  compilation : RecursiveComputationFunctionCompiles types owner source compiled
  preparation : RecursiveComputationFunctionPrepares types owner source args prepared
  coreFixed : prepared.core=core
  typeFixed : prepared.returnType=.word
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Preparation source args) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have preparation : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,core,.word⟩ := ⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("c",⟨owner,3⟩),("x",⟨owner,2⟩),("g",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original declared rows and actual reverse exactly once"
          return ⟨⟨ps.statics,core,.word⟩,⟨ps.actual,core,.word⟩,compilation,preparation,rfl,rfl⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core and original outer return annotation")
  | _ => throw (IO.userError "outer single return policy")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← rawBody table env s ⟨span,statements⟩; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← rawChild table env s c
      match cv : a.value with
      | .bool true => let r ← rawBody table env a.final yes; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifTrue (cv ▸ a.evidence) r.evidence⟩
      | .bool false => let r ← rawBody table env a.final no; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifFalse (cv ▸ a.evidence) r.evidence⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b


private def arguments (g : Core.Value) (c : Bool) : IO (List TypedRuntimeArgument) :=
  [allocator,g,w 14,.bool c].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "unchanged actual closures/captures"; return a
    | none => throw (IO.userError "original actual argument")
private def compiledView (p : CompiledRuntimeFunction) := (p.inputs.bindings.map (fun b => (b.name,b.id,b.type)),p.core,p.returnType)
private def preparedView (p : PreparedRuntimeFunction) := (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)
private def transport (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (p : Preparation source args) (s : Core.Store) (limit : Nat) : IO Unit := do
  have cc := (computationFunctionCompiles_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr p.compilation
  have pc := (computationFunctionPrepares_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr p.preparation
  have _ := (computationFunctionCompiles_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mp cc
  have _ := (computationFunctionPrepares_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mp pc
  have _ := compileComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source
  have _ := prepareComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source args
  check (decide ((compileRecursiveComputationFunction? types (shift owner) source).map compiledView=some (compiledView {p.compiled with inputs := p.compiled.inputs.mapIds relabel relabel_injective}))) "whole original compiled record, mapped IDs only"
  check (decide ((prepareRecursiveComputationFunction? types (shift owner) source args).map preparedView=some (preparedView {p.prepared with inputs := p.prepared.inputs.mapIds relabel relabel_injective}))) "whole actual preparation retains values/captures/core/tag"
  for fuel in List.range limit do
    have _ := runComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types (shift owner) source args fuel s=runRecursiveComputationFunction? types owner source args fuel s ∧ runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core p.prepared.inputs.environment.values s)))) "complete original/mapped runner record"
private def verify (write : Bool) (l : Nat) (c : Bool) (s final : Core.Store) (value : Core.Value) : IO Unit := do
  let g := if write then writer l else reader l; let source ← parsed; let args ← arguments g c
  let manual ← path 80 core [.bool c,w 14,g,allocator] s; let p ← prepare source args
  let i := p.prepared.inputs; let env := i.environment.values; let cost := (if write then 35 else 28)+(if c then 3 else 0)
  let raw ← rawBody i.names i.environment s source.value.body
  if fixed : env=[.bool c,w 14,g,allocator] ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ raw.cost=cost then
    have ⟨ev,mv,ms,mc,rv,rs,rc⟩ := fixed
    have literal (k) : Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩ := by rw [ev]; simpa only [mv,ms,mc] using manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.coreFixed,p.typeFixed] using p.preparation.body
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body value final cost := by simpa only [rv,rs,rc] using raw.evidence
    have sourcePath (k) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using counted) original (by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds) k
    have _ := (sourcePath []).final_unique (literal [])
    transport source args p s (cost+2)
    for fuel in List.range (cost+2) do
      have _ := (literal []).runStateful_done_iff (fuel := fuel)
      match genuine : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact actual result/store/fuel"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel genuine
          for more in [0,1,cost-fuel,cost+2] do
            have _ := Core.runStateful_resume genuine more
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core env s))) "all genuine full resumptions"
      | .fault _ _ => throw (IO.userError "successful example faulted")
    let bound := w 15::env; let allocated := s++[w 14]
    let gBody : Core.Expr := if write then .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2)) else .loadCell (.var 1)
    let gK : List Core.Frame := if c then [.letBody (.var 0) bound] else []
    let cps : List (Nat × Core.State) := [(10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [w 14,.bool false],.letBody afterCore env],allocated⟩),
      (17,⟨.eval afterCore bound,[],allocated⟩),(19,⟨.ret (.bool c),[.ifBranches branchCore callCore bound],allocated⟩),
      ((if c then 26 else 25),⟨.eval gBody [w 15,.cellRef .word l],gK,allocated⟩)] ++
      (if write then [((if c then 32 else 31),⟨.ret .unit,.letBody (.loadCell (.var 2)) [w 15,.cellRef .word l]::gK,final⟩)] else [])
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have _ := runComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source args spent s
        check (decide (runRecursiveComputationFunction? types (shift owner) source args spent s=some (.word,.outOfFuel cp) ∧ Core.runStateful (cost-spent) cp=.done value final)) "genuine original caller/captures/allocation checkpoint"
      else throw (IO.userError "literal checkpoint")
    have _ := literal [.pairApply (.cellRef .word 700)]; have _ := sourcePath [.pairApply (.cellRef .word 700)]
    check (decide (Core.runStateful (cost+1) ⟨.eval core env,[.pairApply (.cellRef .word 700)],s⟩=.done (.pair (.cellRef .word 700) value) final)) "pending caller outside original body cost"
  else throw (IO.userError "independent original raw/manual fixed expectations")
private def fault (mode : Nat) (c : Bool) : IO Unit := do
  let g := if mode=0 then reader 700 else if mode=1 then writer 700 else checkedReader 0
  let s := if mode=2 then [Core.Value.bool false,w 99] else [w 41,w 99]
  let source ← parsed; let args ← arguments g c; let p ← prepare source args; let env := p.prepared.inputs.environment.values
  let bound := w 15::env; let l := if mode=2 then 0 else 700; let captured := [w 15,Core.Value.cellRef .word l]
  let outer : List Core.Frame := if c then [.letBody (.var 0) bound] else []
  let frames : List Core.Frame := (if mode=0 then [.loadCellApply] else if mode=1 then [.storeCellValue (.var 0) captured,.letBody (.loadCell (.var 2)) captured] else [.binaryApply .wordAdd (.bool false)])++outer
  let spent := (if mode=0 then 27 else if mode=1 then 28 else 31)+(if c then 1 else 0)
  let value := if mode=2 then w 15 else Core.Value.cellRef .word 700; let final := s++[w 14]
  let error := if mode=2 then Core.MachineFault.invalidBinaryOperands .wordAdd (.bool false) (w 15) else .invalidCellLocation 700
  let before : Core.State := ⟨.eval (.var (if mode=2 then 0 else 1)) captured,frames,final⟩
  let failed : Core.StatefulRunResult := .fault error ⟨.ret value,frames,final⟩
  check (decide (Core.runStateful (spent-1) (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "actual missing reference or checked-reader payload fault preserves allocation"
  transport source args p s (spent+2)
  for fuel in List.range (spent+2) do
    match genuine : Core.runStateful fuel (.initial core env s) with
    | .outOfFuel cp => have _ := Core.runStateful_resume genuine spent; check (decide (fuel<spent ∧ Core.runStateful spent cp=failed)) "all genuine pre-fault resumptions"
    | result => check (decide (spent≤fuel ∧ result=failed)) "first fault and complete later result"
end ParsedComputationFunctionOwnerEffects
open ParsedComputationFunctionOwnerEffects in
def frontendParsedComputationFunctionOwnerEffectTests : IO Unit := do
  have _ := non_surjective
  for c in [false,true] do
    verify false 0 c [w 41,w 99] [w 41,w 99,w 14] (w 41)
    verify false 1 c [w 41,w 99] [w 41,w 99,w 14] (w 99)
    verify true 2 c [w 41,w 99] [w 41,w 99,w 15] (w 15)
    verify false 1 c [w 41,.bool false] [w 41,.bool false,w 14] (.bool false)
    verify true 0 c [.bool false,w 99] [w 15,w 99,w 14] (w 15)
    for mode in [0,1,2] do fault mode c
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationOwnerBoundaries
/-! Original source rejection remains distinct from selected raw success.
Owner covariance preserves scope guards; it is not arbitrary-child correctness. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationOwnerBoundaries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"OwnerBoundary",by decide⟩],by decide⟩⟩,128⟩
private def lid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 900},999999⟩
private def mapping (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective mapping := by rintro ⟨a,n⟩ ⟨b,m⟩ same; simpa [mapping] using same
private def relabel := ownerLocalIdMap mapping
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective mapping injective
private def inputs : LocalTypeInputs := ⟨[⟨"x",lid 7,.word⟩,⟨"c",foreign,.bool⟩,⟨"x",lid 2,.bool⟩],by decide⟩
private def renamed := inputs.mapIds relabel relabel_injective
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool)]
private def word := Core.Value.word (Core.Word.ofNatModulo 14)
private def env (c : Bool) : Resolved.Environment := [(lid 7,word),(foreign,.bool c),(lid 2,.bool false)]
private def core : Core.Expr := .ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-owner-boundary.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) | throw (IO.userError "parser")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (body.span=⟨file.id,0,text.utf8ByteSize⟩)) "original full block bytes"
  return body
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context s)) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : i.names.lookup? name.value with
    | some localId => match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | _ => throw (IO.userError "static name")
  | _ => throw (IO.userError "static child")
private def body (i : LocalTypeInputs) (s : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i s)) := do
  check (s.value.all fun st => s.span.contains st.span) "original statement ranges"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ => let c ← child i expression; return ⟨c.core,c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let b ← body i ⟨span,statements⟩; return ⟨b.core,b.type,by rw [shape]; exact .block b.evidence⟩
  | ⟨span,⟨ls,.letDecl name none (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span && decide (name.span.endByte≤init.span.startByte)) "original inferred initializer before binding"
      let c ← child i init; let b ← body (i.bindFresh owner name.value c.type) ⟨span,rest⟩
      return ⟨.letE c.core b.core,b.type,by rw [shape]; exact .inferred c.evidence b.evidence⟩
  | ⟨_,[⟨span,.ifThen condition yes (some no)⟩]⟩ =>
      check (span.contains condition.span && span.contains yes.span && span.contains no.span && decide (condition.span.endByte≤yes.span.startByte ∧ yes.span.endByte≤no.span.startByte)) "original branch order"
      let c ← child i condition; let a ← body i yes; let b ← body i no
      if same : c.type=.bool ∧ b.type=a.type then
        if guard : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then
          return ⟨.ifE c.core a.core b.core,a.type,by rw [shape]; exact .conditional (same.1 ▸ c.evidence) (computationBlockPreservesNames_iff.mp guard) a.evidence (same.2 ▸ b.evidence)⟩
        else throw (IO.userError "exposed original name")
      else throw (IO.userError "branch types")
  | _ => throw (IO.userError "static body")
termination_by sizeOf s
private structure Atom (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost table e store s value store 1
private def atom (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (Atom table e s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some localId => match found : e.lookup? localId with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | _ => throw (IO.userError "raw row")
    | _ => throw (IO.userError "raw name")
  | _ => throw (IO.userError "raw atom")
private structure Raw (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table e store s value store cost
private def raw (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Block) : IO (Raw table e s) := do
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ => let c ← atom table e expression; return ⟨c.value,1,fun st => by rw [shape]; exact .expression (c.evidence st)⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let b ← raw table e ⟨span,statements⟩; return ⟨b.value,b.cost,fun st => by rw [shape]; exact .block (b.evidence st)⟩
  | ⟨span,⟨_,.letDecl name ann (some init)⟩::rest⟩ =>
      let c ← atom table e init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let b ← raw ((name.value,fresh)::table) ((fresh,c.value)::e) ⟨span,rest⟩
      return ⟨b.value,1+b.cost+2,fun st => by
        rw [shape]; cases ann with
        | none => exact .inferred (c.evidence st) (b.evidence st)
        | some _ => exact .binding (c.evidence st) (b.evidence st)⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let c ← atom table e condition
      match selected : c.value with
      | .bool true => let b ← raw table e yes; return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifTrue (selected ▸ c.evidence st) (b.evidence st)⟩
      | .bool false => let b ← raw table e no; return ⟨b.value,1+b.cost+2,fun st => by rw [shape]; exact .ifFalse (selected ▸ c.evidence st) (b.evidence st)⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf s
private theorem path (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (if c then 7 else 4) ⟨.eval core (env c).values,k,store⟩ ⟨.ret word,k,store⟩ := by
  cases c
  · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
  · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
private def positive : IO Unit := do
  let s ← parsed "{if(c){{let x=x;return x;}}else{return x;}}"
  let p ← body inputs s
  if fixed : p.core=core ∧ p.type=.word then
    have original : RecursiveComputationReturnTreeElaborates types owner inputs s core .word := by simpa only [fixed.1,fixed.2] using p.evidence
    have preserved := (computationReturnTreeElaborates_mapOwner_iff mapping injective (recursiveLocalComputationElaborates_mapIds_iff _ relabel_injective)).mpr original
    have _ := (computationReturnTreeElaborates_mapOwner_iff mapping injective (recursiveLocalComputationElaborates_mapIds_iff _ relabel_injective)).mp preserved
    have typed := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,original⟩
    have _ := (computationReturnTreeHasType_mapOwner_iff mapping injective (recursiveLocalComputationHasType_mapIds_iff _ relabel_injective)).mpr typed
    have accepted := (elaborateComputationReturnTree?_mapOwner mapping injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner inputs s).trans
      ((elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original)
    for c in [false,true] do
      let r ← raw inputs.names (env c) s; let cost := if c then 7 else 4
      if independent : r.value=word ∧ r.cost=cost then
        for store in [[],[Core.Value.bool true,.cellRef .word 700]] do
          have _ : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env c) store s word store cost := by simpa only [independent.1,independent.2] using r.evidence store
          for fuel in List.range (cost+2) do
            have _ := (path c store []).runStateful_done_iff (fuel := fuel)
            have _ := accepted
            check (decide ((elaborateRecursiveComputationReturnTree? types (mapping owner) renamed s).map
              (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel (env c)).values store)))=
              some (.word,Core.runStateful fuel (.initial core (env c).values store)))) "original exact Core and complete mapped run"
            match genuine : Core.runStateful fuel (.initial core (env c).values store) with
            | .done v st => check (decide (cost≤fuel ∧ v=word ∧ st=store)) "independent original completion"
            | .outOfFuel cp =>
                have _ := (path c store []).residual_of_outOfFuel genuine
                for more in [0,1,cost-fuel] do
                  check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core (Resolved.LocalScope.mapIds relabel (env c)).values store))) "genuine checkpoint full resumption"
            | .fault _ _ => throw (IO.userError "unexpected static fixture fault")
      else throw (IO.userError "independent raw cost/value")
  else throw (IO.userError "independent original static Core/type")
private def rejected (text : String) (yesCost noCost : Nat) (yesValue noValue : Core.Value) : IO Unit := do
  let s ← parsed text
  if absence : elaborateRecursiveComputationReturnTree? types owner inputs s=none then
    have equality := elaborateComputationReturnTree?_mapOwner mapping injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds _ relabel_injective) types owner inputs s
    have noOriginal : ¬ ∃ ce ty, RecursiveComputationReturnTreeElaborates types owner inputs s ce ty := by
      rintro ⟨ce,ty,h⟩; have impossible := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr h
      change elaborateRecursiveComputationReturnTree? types owner inputs s=some (ce,ty) at impossible
      rw [absence] at impossible; cases impossible
    have noMapped : ¬ ∃ ce ty, RecursiveComputationReturnTreeElaborates types (mapping owner) renamed s ce ty := by
      rintro ⟨ce,ty,h⟩; exact noOriginal ⟨ce,ty,(computationReturnTreeElaborates_mapOwner_iff mapping injective (recursiveLocalComputationElaborates_mapIds_iff _ relabel_injective)).mp h⟩
    have _ := noMapped
    check (decide (elaborateRecursiveComputationReturnTree? types (mapping owner) renamed s=none)) "whole rejection retained"
    have _ := equality
    for c in [false,true] do
      let r ← raw inputs.names (env c) s
      if independent : r.cost=(if c then yesCost else noCost) ∧ r.value=(if c then yesValue else noValue) then
        have _ : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env c) store s (if c then yesValue else noValue) store (if c then yesCost else noCost) := by simpa only [independent.1,independent.2] using r.evidence
        pure ()
      else throw (IO.userError "selected raw path must remain separate")
  else throw (IO.userError "whole source unexpectedly accepted")
private def identitySensitive (table : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  if table.lookup? "x"=some (lid 7) then some (.var 99,.word) else none
private def arbitraryCheckerBoundary : IO Unit := do
  let s ← parsed "{return x;}"
  check (decide (elaborateComputationReturnTree? identitySensitive types owner inputs s=some (.var 99,.word) ∧
    elaborateComputationReturnTree? identitySensitive types (mapping owner) renamed s=none)) "injective owner map alone does not imply arbitrary checker covariance"
  let constant := fun (_ : LocalNameTable) (_ : Resolved.Context) (_ : Syntax.Expr) => some (Core.Expr.var 99,Core.Ty.word)
  have _ := elaborateComputationReturnTree?_mapOwner mapping injective constant (fun _ _ _ => rfl) types owner inputs s
  for fuel in [0,1,2] do
    let initial := Core.State.initial (.var 99) (env true).values []
    let expected := Core.StatefulRunResult.fault (.unboundVariable 99) initial
    check (decide (Core.runStateful fuel initial=expected)) "literal arbitrary-child failure threshold"
    check (decide ((elaborateComputationReturnTree? constant types (mapping owner) renamed s).map
      (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel (env true)).values [])))=
      some (.word,Core.runStateful fuel (.initial (.var 99) (env true).values [])))) "covariant arbitrary checker may preserve failure"
end ParsedComputationOwnerBoundaries
open ParsedComputationOwnerBoundaries in
def frontendParsedComputationOwnerBoundaryTests : IO Unit := do
  check (decide ((inputs.bindFresh owner "x" .word).ids=[lid 8,lid 7,foreign,lid 2] ∧
    (renamed.bindFresh (mapping owner) "x" .word).ids=[relabel (lid 8),relabel (lid 7),relabel foreign,relabel (lid 2)])) "foreign high index never drives local fresh allocation"
  positive
  rejected "{if(c){let x=x;return x;}else{return x;}}" 7 4 word word
  rejected "{if(c){return x;}else{let y:Missing=x;return y;}}" 4 7 word word
  rejected "{if(c){return c;}else{return x;}}" 4 4 (.bool true) word
  arbitraryCheckerBoundary
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationOwnerEffects
/-! Original repeated-name lets retain old-input initializers and fresh indices
under owner-only relabeling. Actual cells and captures are never mapped. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationOwnerEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationOwnerEffects",by decide⟩],by decide⟩⟩,128⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 903}
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by rintro ⟨lm,li⟩ ⟨rm,ri⟩ same; simpa [shift] using same
private theorem non_surjective : ¬ Function.Surjective shift := by
  intro h; obtain ⟨o,same⟩ := h {owner with declarationIndex := 0}
  have h := congrArg Resolved.DeclarationId.declarationIndex same; simp [shift] at h
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",⟨owner,7⟩,.word⟩,⟨"c",⟨foreign,4⟩,.bool⟩,⟨"a",⟨owner,31⟩,.function .word .word⟩,
  ⟨"w",⟨foreign,700⟩,.function .word .word⟩,⟨"r",⟨owner,3⟩,.function .word .word⟩,⟨"x",⟨foreign,21⟩,.bool⟩],by decide⟩
private def mapped := inputs.mapIds relabel relabel_injective
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def word (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def environment (c : Core.Value) (w r : Nat) (x : Core.Value := word 14) : Resolved.Environment :=
  [(⟨owner,7⟩,x),(⟨foreign,4⟩,c),(⟨owner,31⟩,allocator),(⟨foreign,700⟩,writer w),(⟨owner,3⟩,reader r),(⟨foreign,21⟩,.bool true)]
private def yesCore : Core.Expr := .letE (.apply (.var 6) (.var 0)) (.var 0)
private def noCore : Core.Expr := .letE (.apply (.var 5) (.apply (.var 6) (.var 0))) (.var 0)
private def afterCore : Core.Expr := .ifE (.var 3) yesCore noCore
private def tailCore : Core.Expr := .letE (.apply (.var 4) (.var 0)) afterCore
private def core : Core.Expr := .letE (.apply (.var 2) (.var 0)) tailCore
private def parsed : IO Syntax.Block := do
  let text := "{let x:Word=a(x);let x=w(x);if(c){{let x:Word=r(x);return x;}}else{{let x=w(r(x));return x;}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-owner-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok b next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original block")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (b.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original block/range"
  return b
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | _ => throw (IO.userError "annotation shape")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← body i ⟨span,statements⟩; return ⟨r.core,r.type,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      let fresh := 32+(i.bindings.length-inputs.bindings.length)
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,fresh⟩ ∧ i.names.lookup? "x"=some ⟨owner,if fresh=32 then 7 else fresh-1⟩)) "old initializer and fresh32/33/34 tail row"
      have commutes := LocalTypeInputs.bindFresh_mapOwner i owner shift injective name.value a.type
      check (decide (((i.mapIds relabel relabel_injective).bindFresh (shift owner) name.value a.type).ids.head?=some ⟨shift owner,fresh⟩)) "foreign binder700 ignored; same fresh index after owner map"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← child i c; let t ← body i yes; let e ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : a.type=.bool ∧ t.type=e.type then return ⟨.ifE a.core t.core e.core,t.type,by rw [shape]; exact .conditional (same.1 ▸ a.evidence) protection t.evidence (same.2.symm ▸ e.evidence)⟩ else throw (IO.userError "branch type")
      | _ => throw (IO.userError "original explicit then scope barrier")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← rawBody table env s ⟨span,statements⟩; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← rawChild table env s c
      match cv : a.value with
      | .bool true => let r ← rawBody table env a.final yes; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifTrue (cv ▸ a.evidence) r.evidence⟩
      | .bool false => let r ← rawBody table env a.final no; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifFalse (cv ▸ a.evidence) r.evidence⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b

private def exercise (c : Bool) (w r : Nat) (store middle final : Core.Store) (value : Core.Value) : IO Unit := do
  let b ← parsed; let p ← body inputs b; let env := environment (.bool c) w r
  let m ← path 70 core env.values store; let a ← rawBody inputs.names env store b
  let cost := if c then 48 else 62
  if fixed : p.core=core ∧ p.type=.word ∧ m.value=value ∧ m.final=final ∧ m.cost=cost ∧ a.value=value ∧ a.final=final ∧ a.cost=cost then
    have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [fixed.1,fixed.2.1] using p.evidence
    have typed := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,original⟩
    have renamed := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
    have _ := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mp renamed
    have _ := (computationReturnTreeHasType_mapOwner_iff shift injective (recursiveLocalComputationHasType_mapIds_iff relabel relabel_injective)).mpr typed
    have old := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have accepted := (elaborateComputationReturnTree?_mapOwner shift injective elaborateRecursiveLocalComputation?
      (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner inputs b).trans old
    have mappedAccepted : elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b=some (core,.word) := by simpa only [mapped,relabel] using accepted
    have values : (Resolved.LocalScope.mapIds relabel env).values=env.values := Resolved.LocalScope.values_mapIds relabel env
    have literal : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,final⟩ := by simpa only [fixed.2.2.1,fixed.2.2.2.1,fixed.2.2.2.2.1] using m.evidence
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names env store b value final cost := by simpa only [fixed.2.2.2.2.2.1,fixed.2.2.2.2.2.2.1,fixed.2.2.2.2.2.2.2] using a.evidence
    have sourcePath (k : List Core.Frame) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation counted original (by rfl) k
    have _ := (sourcePath []).final_unique (literal [])
    have records : ∀ fuel, (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store))) =
        some (.word,Core.runStateful fuel (.initial core env.values store)) := by intro fuel; rw [mappedAccepted,Option.map_some,values]
    let e1 := word 15::env.values; let e2 := word 15::e1
    let cps : List (Nat × Core.State) := [
      (10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [word 14,.bool false],.letBody tailCore env.values],store++[word 14]⟩),
      (17,⟨.eval tailCore e1,[],store++[word 14]⟩),(29,⟨.ret .unit,[.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody afterCore e1],middle⟩),
      (34,⟨.eval afterCore e2,[],middle⟩),
      (36,⟨.ret (.bool c),[.ifBranches yesCore noCore e2],middle⟩),(cost-1,⟨.eval (.var 0) (value::e2),[],final⟩)]
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env.values store)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have mappedCheckpoint := (records spent).trans (congrArg (fun result => some (Core.Ty.word,result)) genuine)
        check (decide (Core.runStateful spent (.initial core (Resolved.LocalScope.mapIds relabel env).values store)=.outOfFuel cp ∧ Core.runStateful (cost-spent) cp=.done value final)) "same literal fresh-tail/conditional/final-let checkpoint"
      else throw (IO.userError "literal checkpoint")
    for fuel in List.range (cost+2) do
      have _ := records fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,Core.runStateful fuel (.initial core env.values store)))) "same full checker/code/tag/run"
      match stopped : Core.runStateful fuel (.initial core env.values store) with
      | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=final)) "fixed actual value/store/threshold"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel stopped
          for more in [0,1,cost-fuel,cost+2] do
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core (Resolved.LocalScope.mapIds relabel env).values store))) "genuine full saved/resumed state"
      | .fault _ _ => throw (IO.userError "success fault")
    let k := [Core.Frame.pairApply (.cellRef .word 700)]
    have _ := literal k; have _ := sourcePath k
    check (decide (Core.runStateful (cost+1) ⟨.eval core (Resolved.LocalScope.mapIds relabel env).values,k,store⟩=.done (.pair (.cellRef .word 700) value) final)) "literal pending caller untouched"
  else throw (IO.userError "original raw/static/manual fixed expectations")
private def faults : IO Unit := do
  let b ← parsed; let p ← body inputs b
  for mode in List.range 4 do
    let w := if mode=0 then 700 else 2; let r := if mode=1 then 700 else 2
    let c := if mode=2 then word 14 else Core.Value.bool true; let x := if mode=3 then Core.Value.bool false else word 14
    let env := environment c w r x; let store := [word 41,word 99]
    let e1 := word 15::env.values; let e2 := word 15::e1
    let written := [word 41,word 99,word 15]; let allocated := store++[x]
    let writeK : List Core.Frame := [.storeCellValue (.var 0) [word 15,.cellRef .word w],.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody afterCore e1]
    let loadK : List Core.Frame := [.loadCellApply,.letBody (.var 0) e2]
    let ifK : List Core.Frame := [.ifBranches yesCore noCore e2]
    let addK : List Core.Frame := [.binaryApply .wordAdd (.bool false),.letBody tailCore env.values]
    let (threshold,cp,failed,error) : Nat × Core.State × Core.State × Core.MachineFault :=
      if mode=0 then (26,⟨.eval (.var 1) [word 15,.cellRef .word w],writeK,allocated⟩,⟨.ret (.cellRef .word w),writeK,allocated⟩,.invalidCellLocation 700)
      else if mode=1 then (45,⟨.eval (.var 1) [word 15,.cellRef .word r],loadK,written⟩,⟨.ret (.cellRef .word r),loadK,written⟩,.invalidCellLocation 700)
      else if mode=2 then (36,⟨.eval (.var 3) e2,ifK,written⟩,⟨.ret c,ifK,written⟩,.expectedBool c)
      else (15,⟨.eval (.word (Core.Word.ofNatModulo 1)) [.cellRef .word 2,x,.bool false],addK,allocated⟩,⟨.ret (word 1),addK,allocated⟩,.invalidBinaryOperands .wordAdd x (word 1))
    if fixed : p.core=core ∧ p.type=.word then
      have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [fixed.1,fixed.2] using p.evidence
      have _ := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
      have _ := elaborateComputationReturnTree?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner inputs b
      check (decide (Core.runStateful (threshold-1) (.initial core env.values store)=.outOfFuel cp ∧ Core.runStateful 1 cp=.fault error failed)) "original malformed actual values/captures fault after preserved effects"
      for fuel in List.range (threshold+3) do
        let actual := Core.runStateful fuel (.initial core env.values store)
        check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
          (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,actual))) "same complete mapped fault/absence/checkpoint record"
        match actual with
        | .fault err st => check (decide (threshold≤fuel ∧ err=error ∧ st=failed)) "first fault cost/full state"
        | .outOfFuel saved => check (decide (fuel<threshold ∧ Core.runStateful (threshold-fuel) saved=.fault error failed ∧
            Core.runStateful 1 saved=Core.runStateful (fuel+1) (.initial core (Resolved.LocalScope.mapIds relabel env).values store))) "all genuine fault resumptions"
        | .done _ _ => throw (IO.userError "malformed actual input completed")
    else throw (IO.userError "actual input changed original body typing")
end ParsedComputationOwnerEffects
open ParsedComputationOwnerEffects in
def frontendParsedComputationOwnerEffectTests : IO Unit := do
  have _ := non_surjective
  for c in [false,true] do
    exercise c 0 1 [word 41,word 99] [word 15,word 99,word 14] (if c then [word 15,word 99,word 14] else [word 99,word 99,word 14]) (word 99)
    exercise c 2 2 [word 41,word 99] [word 41,word 99,word 15] [word 41,word 99,word 15] (word 15)
    -- Raw reads/writes may carry Bool under a static Word tag; no runtime-world premise is supplied.
    exercise c 0 1 [word 41,.bool false] [word 15,.bool false,word 14] (if c then [word 15,.bool false,word 14] else [.bool false,.bool false,word 14]) (.bool false)
  faults
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationRawOwnerEffects
/-! Original allocation/write/read and literal-to-grouped-wildcard selection have
independent raw and cost witnesses before owner transport or Core observations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRawOwnerEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationRawOwnerEffects",by decide⟩],by decide⟩⟩,132⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 903}
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by rintro ⟨lm,li⟩ ⟨rm,ri⟩ same; simpa [shift] using same
private theorem non_surjective : ¬ Function.Surjective shift := by
  intro h; obtain ⟨o,same⟩ := h {owner with declarationIndex := 0}
  have h := congrArg Resolved.DeclarationId.declarationIndex same; simp [shift] at h
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",⟨owner,7⟩,.word⟩,⟨"a",⟨owner,31⟩,.function .word .word⟩,
  ⟨"w",⟨foreign,700⟩,.function .word .word⟩,⟨"r",⟨owner,3⟩,.function .word .word⟩,⟨"x",⟨foreign,21⟩,.bool⟩],by decide⟩
private def mapped := inputs.mapIds relabel relabel_injective
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def word (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def environment (w r : Nat) (x : Core.Value := word 14) : Resolved.Environment :=
  [(⟨owner,7⟩,x),(⟨owner,31⟩,allocator),(⟨foreign,700⟩,writer w),(⟨owner,3⟩,reader r),(⟨foreign,21⟩,.bool true)]
private def compareCore : Core.Expr := .binary .wordEq (.var 0) (.word (Core.Word.ofNatModulo 15))
private def chooseCore : Core.Expr := .ifE compareCore (.var 1) (.apply (.var 6) (.var 1))
private def matchCore : Core.Expr := .letE (.apply (.var 5) (.var 0)) chooseCore
private def tailCore : Core.Expr := .letE (.apply (.var 3) (.var 0)) matchCore
private def core : Core.Expr := .letE (.apply (.var 1) (.var 0)) tailCore
private def parsed : IO Syntax.Block := do
  let text := "{let x:Word=a(x);let x=w(x);match(r(x)){case 15{return x;}case ((_)){return r(x);}default{return w(x);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-raw-owner-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok b next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original block")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (b.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original block/range"
  return b
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | _ => throw (IO.userError "annotation shape")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private structure Returned (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Returned (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.type=.word then return ⟨r.core,by rw [shape]; exact .expression (same ▸ r.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p with
  | ⟨_,.wildcard _⟩ => return ⟨none,⟨by rw [shape]; exact .wildcard rfl⟩⟩
  | ⟨_,.literal literal⟩ => match decoded : interpretWordLiteral? literal with | some v => return ⟨some v,⟨by rw [shape]; exact .literal ⟨literal,rfl,interpretWordLiteral?_sound decoded⟩⟩⟩ | none => throw (IO.userError "strict Word literal")
  | ⟨_,.group inner⟩ => check (p.span.contains inner.span && decide (p.span.startByte<inner.span.startByte ∧ inner.span.endByte<p.span.endByte)) "original nested group ranges"; let c ← pattern inner; return ⟨c.1,⟨by rw [shape]; exact .group c.2.down⟩⟩
  | _ => throw (IO.userError "unsupported grouped or bare leaf")
termination_by sizeOf p
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,d⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && cs.all (fun c => armsSpan.contains c.span) && d.toList.all (fun b => armsSpan.contains b.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match and optional default ranges"
      let sc ← child i e; let bs ← arms i cs
      let dc : Σ de : Option (Syntax.Block × Core.Expr), PLift (de.map Prod.fst=d ∧ ∀ en ∈ de.toList, RecursiveComputationReturnTreeElaborates types owner i en.1 en.2 .word) ← match present : d with | none => pure ⟨none,⟨by simp [present]⟩⟩ | some b => do let c ← returned i b; pure ⟨some (b,c.core),⟨by refine ⟨present.symm,?_⟩; intro en h; cases List.mem_singleton.mp h; exact c.evidence⟩⟩
      match lowered : bs.1.foldr (fun en t => match en.2.1 with | none => some (en.2.2.weakenAt 0) | some v => t.map (fun t => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t)) (dc.1.map (fun en => en.2.weakenAt 0)) with
      | some t => if same : sc.type=.word then return ⟨.letE sc.core t,.word,by rw [shape]; exact .wordMatch (defaultEntry := dc.1) (same ▸ sc.evidence) bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inl rfl) (fun e h => (bs.2.down.2 e h).2) dc.2.down.1 dc.2.down.2 lowered⟩ else throw (IO.userError "scrutinee type")
      | none => throw (IO.userError "uncovered original arms")
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      let fresh := 32+(i.bindings.length-inputs.bindings.length)
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,fresh⟩ ∧ i.names.lookup? "x"=some ⟨owner,if fresh=32 then 7 else fresh-1⟩)) "old initializer and fresh32/33 tail row"
      check (decide (((i.mapIds relabel relabel_injective).bindFresh (shift owner) name.value a.type).ids.head?=some ⟨shift owner,fresh⟩)) "foreign binder700 ignored; same fresh index after owner map"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | _ => throw (IO.userError "original typed/inferred/match body")
termination_by sizeOf b
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) (U : Core.Value → Core.Store → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
  uncosted : U value final
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e) (RecursiveLocalComputationEvaluates table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)),by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence []),by rw [shape]; exact .application (fv ▸ l.uncosted) r.uncosted (Core.steps_from_initial_sound (p.evidence []))⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Option Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs d selected.1 selected.2)) := do
  match shape : cs with
  | [] => match present : d with | some fallback => return ⟨(fallback,0),⟨by rw [shape,present]; exact .fallback⟩⟩ | none => throw (IO.userError "no raw fallback")
  | c::rest =>
      let p ← pattern c.value.pattern
      match tag : p.1 with
      | none => return ⟨(c.value.body,0),⟨by rw [shape]; exact .wildcard (by simpa only [tag] using p.2.down)⟩⟩
      | some literal => match actual : v with
        | .word w =>
            have meaning : WordMatchPatternClassifies c.value.pattern (some literal) := by simpa only [tag] using p.2.down
            if same : w=literal then return ⟨(c.value.body,1),⟨by rw [shape,actual]; exact .hit (same.symm ▸ meaning)⟩⟩
            else let tail ← choose (.word w) rest d; return ⟨(tail.1.1,tail.1.2+1),⟨by rw [shape,actual]; exact .miss meaning same tail.2.down⟩⟩
        | _ => throw (IO.userError "actual non-Word comparison before wildcard")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b) (RecursiveComputationReturnTreeEvaluates owner table env s b)) := do
  match shape : b with
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence,by rw [shape,ann]; exact .inferred a.uncosted r.uncosted⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence,by rw [shape,ann]; exact .binding a.uncosted r.uncosted⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      check (decide (c.1.2=1)) "original selected match visits exactly one literal"
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
          let r ← rawChild table env sc.final child
          return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence),
            by rw [shape]; exact .wordMatch sc.uncosted c.2.down (by rw [selected]; exact .expression r.uncosted)⟩
      | _ => throw (IO.userError "selected original return")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def exercise (w r : Nat) (store final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let b ← parsed; let p ← body inputs b; let env := environment w r
  let a ← rawBody inputs.names env store b; let m ← path 70 core env.values store
  if fixed : p.core=core ∧ p.type=.word ∧ m.value=value ∧ m.final=final ∧ m.cost=cost ∧ a.value=value ∧ a.final=final ∧ a.cost=cost then
    have ⟨pc,pt,mv,ms,mc,av,ast,ac⟩ := fixed
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names env store b value final cost := by simpa only [av,ast,ac] using a.evidence
    have evaluated : RecursiveComputationReturnTreeEvaluates owner inputs.names env store b value final := by simpa only [av,ast] using a.uncosted
    have renamedCost := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mpr counted
    have renamedRaw := (computationReturnTreeEvaluates_mapOwner_iff shift injective (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mpr evaluated
    have _ := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mp renamedCost
    have _ := (computationReturnTreeEvaluates_mapOwner_iff shift injective (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mp renamedRaw
    have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [pc,pt] using p.evidence
    have mappedElab := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
    have accepted : elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b=some (core,.word) := by simpa only [mapped,relabel] using (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr mappedElab
    have literal : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,final⟩ := by simpa only [mv,ms,mc] using m.evidence
    have sourcePath (k : List Core.Frame) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation counted original (by rfl) k
    have mappedPath (k : List Core.Frame) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation renamedCost mappedElab (by rfl) k
    have _ := (sourcePath []).final_unique (literal [])
    have records : ∀ fuel, (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store))) =
        some (.word,Core.runStateful fuel (.initial core env.values store)) := by
      intro fuel; rw [accepted,Option.map_some,Resolved.LocalScope.values_mapIds]
    let e1 := word 15::env.values; let e2 := word 15::e1
    let scr := if cost=52 then word 15 else value; let e3 := scr::e2
    let cps : List (Nat × Core.State) := [
      (10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [word 14,.bool false],.letBody tailCore env.values],store++[word 14]⟩),
      (17,⟨.eval tailCore e1,[],store++[word 14]⟩),(29,⟨.ret .unit,[.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody matchCore e1],final⟩),
      (34,⟨.eval matchCore e2,[],final⟩),(43,⟨.ret scr,[.letBody chooseCore e2],final⟩),
      (49,⟨.ret (word 15),[.binaryApply .wordEq scr,.ifBranches (.var 1) (.apply (.var 6) (.var 1)) e3],final⟩),
      (51,⟨.eval (if cost=52 then .var 1 else .apply (.var 6) (.var 1)) e3,[],final⟩)]
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env.values store)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have _ := (records spent).trans (congrArg (fun result => some (Core.Ty.word,result)) genuine)
        check (decide (Core.runStateful (cost-spent) cp=.done value final)) "original saved allocator/writer/scrutinee/comparison/selected body"
      else throw (IO.userError "literal checkpoint")
    for fuel in List.range (cost+2) do
      have _ := records fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,Core.runStateful fuel (.initial core env.values store)))) "same complete code/tag/store/checkpoint"
      match stopped : Core.runStateful fuel (.initial core env.values store) with
      | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=final)) "fixed original value/store/exact cost"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel stopped
          for more in [0,1,cost-fuel,cost+2] do
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core (Resolved.LocalScope.mapIds relabel env).values store))) "all genuine full resumptions"
      | .fault _ _ => throw (IO.userError "success fault")
    let k := [Core.Frame.pairApply (.cellRef .word 700)]
    have _ := literal k; have _ := sourcePath k; have _ := mappedPath k
    check (decide (Core.runStateful (cost+1) ⟨.eval core (Resolved.LocalScope.mapIds relabel env).values,k,store⟩=.done (.pair (.cellRef .word 700) value) final)) "unchanged actual pending caller"
  else throw (IO.userError "independent original source and literal Core expectations")
private def faults : IO Unit := do
  let b ← parsed; let p ← body inputs b
  for mode in List.range 4 do
    let w := if mode=0 then 700 else if mode=2 then 0 else 2; let r := if mode=1 then 700 else if mode=2 then 1 else 2
    let x := if mode=3 then Core.Value.bool false else word 14; let env := environment w r x
    let store := if mode=2 then [word 41,.bool false] else [word 41,word 99]
    let e1 := word 15::env.values; let e2 := word 15::e1; let e3 := Core.Value.bool false::e2
    let final := if mode=0 ∨ mode=3 then store++[x] else if mode=2 then [word 15,.bool false,word 14] else [word 41,word 99,word 15]
    let (threshold,cp,failed,error) : Nat × Core.State × Core.State × Core.MachineFault :=
      if mode=0 then
        let k := [Core.Frame.storeCellValue (.var 0) [word 15,.cellRef .word w],.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody matchCore e1]
        (26,⟨.eval (.var 1) [word 15,.cellRef .word w],k,final⟩,⟨.ret (.cellRef .word w),k,final⟩,.invalidCellLocation 700)
      else if mode=1 then
        let k := [Core.Frame.loadCellApply,.letBody chooseCore e2]
        (42,⟨.eval (.var 1) [word 15,.cellRef .word r],k,final⟩,⟨.ret (.cellRef .word r),k,final⟩,.invalidCellLocation 700)
      else if mode=2 then
        let k := [Core.Frame.binaryApply .wordEq (.bool false),.ifBranches (.var 1) (.apply (.var 6) (.var 1)) e3]
        (49,⟨.eval (.word (Core.Word.ofNatModulo 15)) e3,k,final⟩,⟨.ret (word 15),k,final⟩,.invalidBinaryOperands .wordEq (.bool false) (word 15))
      else
        let k := [Core.Frame.binaryApply .wordAdd (.bool false),.letBody tailCore env.values]
        (15,⟨.eval (.word (Core.Word.ofNatModulo 1)) [.cellRef .word 2,x,.bool false],k,final⟩,⟨.ret (word 1),k,final⟩,.invalidBinaryOperands .wordAdd x (word 1))
    if fixed : p.core=core ∧ p.type=.word then
      have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [fixed.1,fixed.2] using p.evidence
      have _ := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
      check (decide (Core.runStateful (threshold-1) (.initial core env.values store)=.outOfFuel cp ∧ Core.runStateful 1 cp=.fault error failed)) "independently fixed first fault and preserved earlier effects"
      for fuel in List.range (threshold+2) do
        check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,Core.runStateful fuel (.initial core env.values store)))) "same mapped code/tag/full fault records"
        match Core.runStateful fuel (.initial core env.values store) with
        | .fault err st => check (decide (threshold≤fuel ∧ err=error ∧ st=failed)) "fixed first fault and entire saved state"
        | .outOfFuel saved => check (decide (fuel<threshold ∧ Core.runStateful (threshold-fuel) saved=.fault error failed)) "all fault checkpoint resumptions"
        | .done _ _ => throw (IO.userError "invalid actual input completed")
    else throw (IO.userError "actual inputs changed original static evidence")
end ParsedComputationRawOwnerEffects
open ParsedComputationRawOwnerEffects in
def frontendParsedComputationRawOwnerEffectTests : IO Unit := do
  have _ := non_surjective
  exercise 2 2 [word 41,word 99] [word 41,word 99,word 15] (word 15) 52
  exercise 0 1 [word 41,word 99] [word 15,word 99,word 14] (word 99) 59
  exercise 0 1 [word 41,word 15] [word 15,word 15,word 14] (word 15) 52
  exercise 2 2 [.bool true,word 99] [.bool true,word 99,word 15] (word 15) 52
  faults
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedComputationRawOwnerRows
/-! Raw names and actual rows are deliberately not aligned or repaired.
Original annotations and exposed then bindings do not constrain raw paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRawOwnerRows
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RawOwnerRows",by decide⟩],by decide⟩⟩,132⟩
private def lid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 902},999999⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+20}
private theorem injective : Function.Injective shift := by rintro ⟨a,n⟩ ⟨b,m⟩ same; simpa [shift] using same
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def checkedInputs : LocalTypeInputs := ⟨[⟨"x",lid 7,.word⟩,⟨"c",foreign,.bool⟩,⟨"x",lid 2,.bool⟩],by decide⟩
private def names (duplicate : Bool) : LocalNameTable := checkedInputs.names ++ if duplicate then [("x",lid 7)] else []
private def oldEight : Core.Value := .bool false
private def oldNine : Core.Value := .cellRef .word 700
private def env (reordered : Bool) (c : Bool) (v : Core.Value) : Resolved.Environment :=
  let rows := [(lid 8,oldEight),(foreign,.bool c),(lid 7,v),(lid 7,.word (Core.Word.ofNatModulo 99)),(lid 9,oldNine)]
  if reordered then rows.reverse else rows
private def payloads : List Core.Value := [.word (Core.Word.ofNatModulo 14),.bool true,.cellRef .word 701,
  .closure .word .word (.var 0) [.cellRef .word 702,.bool false]]
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-raw-owner-rows.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok b next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) | throw (IO.userError "parser")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (b.span=⟨file.id,0,text.utf8ByteSize⟩)) "original full source range"
  return b
private structure Atom (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost table environment store s value store 1
private def atom (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Expr) : IO (Atom table environment s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : environment.lookup? id with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "missing actual row")
    | none => throw (IO.userError "missing name")
  | _ => throw (IO.userError "original raw atom")
private structure Raw (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Block) where
  value : Core.Value
  cost : Nat
  introduced : List (Resolved.LocalId × Core.Value)
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table environment store s value store cost
private def raw (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Block) : IO (Raw table environment s) := do
  check (s.value.all fun st => s.span.contains st.span) "original statement spans"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let a ← atom table environment e; return ⟨a.value,1,[],fun st => by rw [shape]; exact .expression (a.evidence st)⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← raw table environment ⟨span,statements⟩; return ⟨r.value,r.cost,r.introduced,fun st => by rw [shape]; exact .block (r.evidence st)⟩
  | ⟨span,⟨ls,.letDecl name annotation (some e)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains e.span && decide (name.span.endByte≤e.span.startByte)) "original initializer order"
      let a ← atom table environment e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let next : Resolved.Environment := (id,a.value)::environment
      check (decide (next.tail=environment ∧ next.lookup? id=some a.value)) "new row prepended without removing old collision"
      let r ← raw ((name.value,id)::table) next ⟨span,rest⟩
      return ⟨r.value,1+r.cost+2,(id,a.value)::r.introduced,fun st => by
        rw [shape]; cases annotation with
        | none => exact .inferred (a.evidence st) (r.evidence st)
        | some _ => exact .binding (a.evidence st) (r.evidence st)⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← atom table environment c
      match cv : a.value with
      | .bool true => let r ← raw table environment yes; return ⟨r.value,1+r.cost+2,r.introduced,fun st => by rw [shape]; exact .ifTrue (cv ▸ a.evidence st) (r.evidence st)⟩
      | .bool false => let r ← raw table environment no; return ⟨r.value,1+r.cost+2,r.introduced,fun st => by rw [shape]; exact .ifFalse (cv ▸ a.evidence st) (r.evidence st)⟩
      | _ => throw (IO.userError "raw actual condition")
  | _ => throw (IO.userError "original raw body")
termination_by sizeOf s
private def exercise (s : Syntax.Block) (duplicate reordered c : Bool) (v : Core.Value) : IO Unit := do
  let table := names duplicate; let e := env reordered c v
  let expected := if reordered then Core.Value.word (Core.Word.ofNatModulo 99) else v
  let cost := if c then 13 else 10
  check (decide (table.lookup? "x"=some (lid 7) ∧ e.lookup? (lid 7)=some expected ∧
    e.lookup? (lid 8)=some oldEight ∧ e.lookup? (lid 9)=some oldNine ∧ e.lookup? (lid 2)=none ∧
    Resolved.freshLocalId owner (table.map Prod.snd)=lid 8)) "first duplicate, missing unused row and environment-only fresh collisions"
  check (decide (table.map Prod.snd ≠ e.map Prod.fst ∧
    (LocalNameTable.mapIds relabel table).map Prod.fst=table.map Prod.fst ∧
    (Resolved.LocalScope.mapIds relabel e).values=e.values)) "no row alignment or value reconstruction"
  let r ← raw table e s
  if fixed : r.value=expected ∧ r.cost=cost ∧ r.introduced=[(lid 8,expected),(lid 9,expected)]++(if c then [(lid 10,expected)] else []) then
    for store in [[],[Core.Value.bool false,.cellRef .word 999],payloads] do
      have original : RecursiveComputationReturnTreeEvaluatesWithCost owner table e store s expected store cost := by simpa only [fixed.1,fixed.2.1] using r.evidence store
      have mapped := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mpr original
      have reflected := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mp mapped
      have _ := ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        (fun left right => left.deterministic right) original reflected
      have ordinary := (computationReturnTreeEvaluates_iff_exists_cost recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨cost,original⟩
      have mappedOrdinary := (computationReturnTreeEvaluates_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mpr ordinary
      have _ := (computationReturnTreeEvaluates_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mp mappedOrdinary
      have existsExact : ∃ result final count, RecursiveComputationReturnTreeEvaluatesWithCost (shift owner)
          (LocalNameTable.mapIds relabel table) (Resolved.LocalScope.mapIds relabel e) store s result final count ∧
          result=expected ∧ final=store ∧ count=cost := ⟨expected,store,cost,mapped,rfl,rfl,rfl⟩
      have _ := existsExact
      check (decide ((Resolved.LocalScope.mapIds relabel ((lid 8,expected)::(lid 9,expected)::e)).values=
        expected::expected::e.values)) "all old actual rows retained behind new heads"
  else throw (IO.userError "independent original raw value/cost/fresh sequence")
private def naivePositionIsNotRawLookup : IO Unit := do
  let b ← parsed "{return x;}"; let e := env false true (.word (Core.Word.ofNatModulo 14))
  let r ← raw (names true) e b
  check (decide (r.value=.word (Core.Word.ofNatModulo 14) ∧ r.cost=1 ∧
    Core.runStateful 1 (.initial (.var 0) e.values [])=.done oldEight [] ∧ oldEight≠r.value)) "raw ID lookup is not positional Core execution on unaligned rows"
private def missingSelectedRow : IO Unit := do
  let s ← parsed "{return x;}"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier _⟩)⟩]⟩ =>
      for store in [[],payloads] do
        have absent : ¬ ∃ value final cost, RecursiveComputationReturnTreeEvaluatesWithCost owner (names true) [] store s value final cost := by
          rintro ⟨value,final,cost,evaluation⟩
          rw [shape] at evaluation
          cases evaluation with
          | expression child => cases child with
            | pure leaf => cases leaf with
              | identifier _ found => cases found
        have noMappedCost : ¬ ∃ value final cost, RecursiveComputationReturnTreeEvaluatesWithCost (shift owner)
            (LocalNameTable.mapIds relabel (names true)) [] store s value final cost := by
          rintro ⟨value,final,cost,evaluation⟩
          exact absent ⟨value,final,cost,(computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective
            (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mp evaluation⟩
        have noMappedRaw : ¬ ∃ value final, RecursiveComputationReturnTreeEvaluates (shift owner)
            (LocalNameTable.mapIds relabel (names true)) [] store s value final := by
          rintro ⟨value,final,evaluation⟩
          have original : RecursiveComputationReturnTreeEvaluates owner (names true) [] store s value final :=
            (computationReturnTreeEvaluates_mapOwner_iff shift injective
            (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mp evaluation
          obtain ⟨cost,counted⟩ := (computationReturnTreeEvaluates_iff_exists_cost recursiveLocalComputationEvaluates_iff_exists_cost).mp original
          exact absent ⟨value,final,cost,counted⟩
        have _ := noMappedCost; have _ := noMappedRaw
        pure ()
  | _ => throw (IO.userError "original missing-row return shape")
end ParsedComputationRawOwnerRows
open ParsedComputationRawOwnerRows in
def frontendParsedComputationRawOwnerRowTests : IO Unit := do
  let s ← parsed "{let x:Missing=x;let x=x;if(c){let x=x;return x;}else{return x;}}"
  check (decide (elaborateRecursiveComputationReturnTree? [] owner checkedInputs s=none)) "unknown annotation still rejects whole source on independent type inputs"
  for duplicate in [false,true] do
    for reordered in [false,true] do
      for c in [false,true] do
        for v in payloads do exercise s duplicate reordered c v
  let guard ← parsed "{let x=x;let x=x;if(c){let x=x;return x;}else{return x;}}"
  check (decide (elaborateRecursiveComputationReturnTree? [] owner checkedInputs guard=none)) "exposed then shadow still rejects without an annotation"
  exercise guard true true true (.bool false)
  exercise guard true false false (.bool true)
  naivePositionIsNotRawLookup
  missingSelectedRow
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedScopedShadowingBoundaries
/-! Original parsed branches distinguish scope guards from selected raw paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedScopedShadowingBoundaries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ShadowBoundary", by decide⟩], by decide⟩⟩, 73⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def inputs := (LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" .word
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def word := Core.Value.word (Core.Word.ofNatModulo 17)
private def env (choice : Bool) : Resolved.Environment := [(id 1, word), (id 0, .bool choice)]
private def parsed (body : String) (parameters : String := "") : IO Syntax.FunctionDecl := do
  let text := "function guard(" ++ parameters ++ "){" ++ body ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main, "shadow-boundary.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lex")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original source bytes"
  return source
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveLocalComputationElaborates i.names i.context s core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some localId =>
          match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId with
          | some type, some index => return ⟨.var index, type, by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _, _ => throw (IO.userError "original row")
      | _ => throw (IO.userError "unresolved original name")
  | _ => throw (IO.userError "fixture child")
private structure Body (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveComputationReturnTreeElaborates types owner i b core type
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Body i b) := do
  for statement in b.value do check (b.span.contains statement.span) "original statement span"
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ =>
      let c ← child i s; return ⟨c.core, c.type, by rw [shape]; exact .expression c.evidence⟩
  | ⟨_, [⟨inner, .block statements⟩]⟩ =>
      let c ← body i ⟨inner, statements⟩; return ⟨c.core, c.type, by rw [shape]; exact .block c.evidence⟩
  | ⟨span, ⟨_, .letDecl name none (some init)⟩ :: rest⟩ =>
      let c ← child i init; let tail ← body (i.bindFresh owner name.value c.type) ⟨span, rest⟩
      return ⟨.letE c.core tail.core, tail.type, by rw [shape]; exact .inferred c.evidence tail.evidence⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← child i condition; let a ← body i yes; let d ← body i no
      if valid : c.type = .bool ∧ d.type = a.type then
        if guard : computationBlockPreservesNames (i.names.map Prod.fst) yes = true then
          return ⟨.ifE c.core a.core d.core, a.type, by
            rw [shape]
            exact .conditional (valid.1 ▸ c.evidence) (computationBlockPreservesNames_iff.mp guard)
              a.evidence (valid.2 ▸ d.evidence)⟩
        else throw (IO.userError "exposed then shadow")
      else throw (IO.userError "conditional types")
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨s, []⟩⟩ ⟨_, ⟨[], some defaultBody⟩⟩⟩]⟩ =>
      let c ← child i s; let d ← body i defaultBody
      return ⟨.letE c.core (d.core.weakenAt 0), d.type, by
        rw [shape]
        exact .wordMatch (entries := []) (defaultEntry := some (defaultBody, d.core)) c.evidence rfl (by simp)
          (.inr (by simp)) (by simp) rfl (by intro entry member; cases List.mem_singleton.mp member; exact d.evidence) rfl⟩
  | _ => throw (IO.userError "fixture body")
termination_by sizeOf b
private structure AtomValue (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost table e store s value store 1
private def atomValue (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (AtomValue table e s) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match found : e.lookup? localId with
          | some value => return ⟨value, fun _ => by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
          | _ => throw (IO.userError "missing actual row")
      | _ => throw (IO.userError "missing actual name")
  | _ => throw (IO.userError "raw atom")
private structure Raw (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table e store b value store cost
private def raw (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) : IO (Raw table e b) := do
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ =>
      let c ← atomValue table e s; return ⟨c.value, 1, fun store => by rw [shape]; exact .expression (c.evidence store)⟩
  | ⟨_, [⟨inner, .block statements⟩]⟩ =>
      let c ← raw table e ⟨inner, statements⟩; return ⟨c.value, c.cost, fun store => by rw [shape]; exact .block (c.evidence store)⟩
  | ⟨span, ⟨_, .letDecl name none (some init)⟩ :: rest⟩ =>
      let c ← atomValue table e init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let d ← raw ((name.value, fresh) :: table) ((fresh, c.value) :: e) ⟨span, rest⟩
      return ⟨d.value, 1 + d.cost + 2, fun store => by rw [shape]; exact .inferred (c.evidence store) (d.evidence store)⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← atomValue table e condition
      match selected : c.value with
      | .bool true => let d ← raw table e yes; return ⟨d.value, 1 + d.cost + 2,
          fun store => by rw [shape]; exact .ifTrue (selected ▸ c.evidence store) (d.evidence store)⟩
      | .bool false => let d ← raw table e no; return ⟨d.value, 1 + d.cost + 2,
          fun store => by rw [shape]; exact .ifFalse (selected ▸ c.evidence store) (d.evidence store)⟩
      | _ => throw (IO.userError "raw condition")
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨s, []⟩⟩ ⟨_, ⟨[], some defaultBody⟩⟩⟩]⟩ =>
      let c ← atomValue table e s; let d ← raw table e defaultBody
      return ⟨d.value, 1 + d.cost + 2, fun store => by rw [shape]; exact .wordMatch (c.evidence store) .fallback (d.evidence store)⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def shadow : Core.Expr := .letE (.var 0) (.var 0)
private def matched : Core.Expr := .letE (.var 0) (.letE (.var 1) (.var 0))
private theorem shadowPath (value : Core.Value) (retained : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 4 ⟨.eval shadow (value :: retained), k, store⟩ ⟨.ret value, k, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
private theorem matchPath (value : Core.Value) (retained : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 7 ⟨.eval matched (value :: retained), k, store⟩ ⟨.ret value, k, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl)
    (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
private def positive (text : String) (core : Core.Expr) (yesCost noCost : Nat)
    (manual : ∀ choice store k, Core.Steps (if choice then yesCost else noCost)
      ⟨.eval core (env choice).values, k, store⟩ ⟨.ret word, k, store⟩) : IO Unit := do
  let source ← parsed text; let b := source.value.body; let static ← body inputs b
  if fixed : static.core = core ∧ static.type = .word then
    have provenance : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by
      simpa only [fixed.1, fixed.2] using static.evidence
    have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance
    have _ := ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType provenance
    check (decide (elaborateRecursiveComputationReturnTree? types owner inputs b = some (core, .word))) "exact original Core"
    for choice in [false, true] do
      let r ← raw inputs.names (env choice) b; let cost := if choice then yesCost else noCost
      if actual : r.value = word ∧ r.cost = cost then
        for store in [[], [Core.Value.bool true, .unit]] do
          have _ : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env choice) store b word store cost := by
            simpa only [actual.1, actual.2] using r.evidence store
          for fuel in List.range (cost + 2) do
            have _ := (manual choice store []).runStateful_done_iff (fuel := fuel)
            let result := Core.runStateful fuel (.initial core (env choice).values store)
            check (decide (result = .done word store) == decide (cost ≤ fuel)) "literal Core exact threshold"
            match result with
            | .outOfFuel checkpoint =>
                check (decide (Core.runStateful (cost - fuel) checkpoint = .done word store)) "genuine checkpoint/residual"
            | .done value finalStore => check (decide (value = word ∧ finalStore = store)) "actual retained store"
            | .fault _ _ => throw (IO.userError "unexpected fault")
      else throw (IO.userError "independent raw value/cost")
  else throw (IO.userError "independent source/Core mismatch")
private def rejection (text : String) : IO Unit := do
  let source ← parsed text; let b := source.value.body; let r ← raw inputs.names (env false) b
  check (decide (r.value = word ∧ r.cost = 4 ∧ elaborateRecursiveComputationReturnTree? types owner inputs b = none)) "false selected path succeeds but static guard rejects"
  match shape : b with
  | ⟨bs, [⟨ss, .ifThen condition yes (some no)⟩]⟩ =>
      if failed : computationBlockPreservesNames (inputs.names.map Prod.fst) yes = false then
        have forbidden : ¬ ∃ core type, RecursiveComputationReturnTreeElaborates types owner inputs
            ⟨bs, [⟨ss, .ifThen condition yes (some no)⟩]⟩ core type := by
          obtain ⟨name, present, exposed⟩ := computationBlockPreservesNames_eq_false_iff.mp failed
          exact (FrontendComputationScopeBoundary.exposed_then_shadow_rejects_independently_of_child_checking
            elaborateRecursiveLocalComputation? RecursiveLocalComputationElaborates types owner inputs bs ss condition yes no name present exposed).2
        have _ := forbidden
        for store in [[], [Core.Value.bool true]] do have _ := r.evidence store; pure ()
      else throw (IO.userError "expected source occurrence witness")
  | _ => throw (IO.userError "original if shape")
end ParsedScopedShadowingBoundaries
open ParsedScopedShadowingBoundaries
def frontendParsedScopedShadowingBoundaryTests : IO Unit := do
  positive "if(c){{let x=x;return x;}}else{return x;}" (.ifE (.var 1) shadow (.var 0)) 7 4 (by
    intro choice store k; cases choice
    · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (shadowPath _ _ _ _))
  positive "if(c){return x;}else{let x=x;return x;}" (.ifE (.var 1) (.var 0) shadow) 4 7 (by
    intro choice store k; cases choice
    · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (shadowPath _ _ _ _)
    · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
  positive "if(c){match(x){default{let x=x;return x;}}}else{return x;}" (.ifE (.var 1) matched (.var 0)) 10 4 (by
    intro choice store k; cases choice
    · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (matchPath _ _ _ _))
  rejection "if(c){let x=x;return x;}else{return x;}"
  rejection "if(c){if(c){return x;}else{let x=x;return x;}}else{return x;}"
  for text in ["if(c){let y=x;return y;}else{return y;}", "let missing=missing;return missing;",
      "if(c){{let y=x;return y;}}else{return y;}", "{let x=x;}return x;"] do
    let source ← parsed text
    check ((elaborateRecursiveComputationReturnTree? types owner inputs source.value.body).isNone) "retained incomplete/outside profile"
  let source ← parsed "return x;" "x:Word,x:Word"
  check ((declareRuntimeParameters? types owner source.value.signature.parameters.elements).isNone) "original duplicate parameters remain rejected"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedCompilationOwners
/-! Compilation owner laws are consumed without constructing runtime arguments.
Nominal and mixed type-only declarations retain exact Core/type projections;
their identity-bearing rows change, while written names and order do not. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def baseOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"CompilationOwners", by decide⟩], by decide⟩⟩, 4⟩
private def owners : List Resolved.DeclarationId :=
  [baseOwner, { baseOwner with declarationIndex := 52 },
    ⟨⟨.main, ⟨[⟨"OtherModule", by decide⟩], by decide⟩⟩, 4⟩]
private def shiftOwner (owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { owner with declarationIndex := owner.declarationIndex + 17 }
private theorem shiftOwnerInjective : Function.Injective shiftOwner := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; simp_all [shiftOwner]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pair"], .product .word .bool), (["Choice"], .sum .word .bool), (["Pkg", "Flag"], .bool)]
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)
private def projection (compiled : CompiledRuntimeFunction) : Core.Expr × Core.Ty × List Core.Ty :=
  (compiled.core, compiled.returnType, compiled.inputs.context.values)

/-- The finite parsed grid below consumes an unrestricted owner theorem. There
are no argument values, inhabitation hypotheses, or successful-check premises. -/
private theorem arbitraryOwnerProjections (table : TypeNameTable)
    (left right : Resolved.DeclarationId) (source : Syntax.FunctionDecl) :
    (compileRuntimeFunction? table left source).map projection =
      (compileRuntimeFunction? table right source).map projection :=
  compileRuntimeFunction?_owner_projection_eq table left right source

private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-compilation-owners.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkProjections (source : Syntax.FunctionDecl)
    (expected : Option (Core.Expr × Core.Ty × List Core.Ty)) : IO Unit := do
  for left in owners do
    for right in owners do
      have _ := arbitraryOwnerProjections types left right source
      let first := (compileRuntimeFunction? types left source).map projection
      let second := (compileRuntimeFunction? types right source).map projection
      assertTrue (decide (first = second ∧ first = expected))
        "owner change altered complete Option projection or hid unexpected rejection/acceptance"
      match compileRuntimeFunction? types left source, compileRuntimeFunction? types right source with
      | some first, some second =>
          assertTrue (decide (first.inputs.names.map Prod.fst = second.inputs.names.map Prod.fst ∧
            first.inputs.ids.map (·.binderIndex) = second.inputs.ids.map (·.binderIndex)))
            "source spellings, row order, or binder indices changed"
          if left != right && !first.inputs.bindings.isEmpty then
            assertTrue (decide (first.inputs.ids ≠ second.inputs.ids ∧ first.inputs.names ≠ second.inputs.names ∧
              first.inputs.context ≠ second.inputs.context)) "distinct owners were erased from identity-bearing data"
      | none, none => pure ()
      | _, _ => throw (IO.userError "one-sided compilation failure")

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (core : Core.Expr) (returnType : Core.Ty) : IO Unit := do
  let some source ← parsed? content | throw (IO.userError s!"{content}: expected complete declaration")
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "unexpected static parameter shape")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span &&
      parameter.span.contains annotation.span) "canonical parameter spans changed"
    pure name.value
  assertTrue (names.length == parameterTypes.length) "static parameter count changed"
  checkProjections source (some (core, returnType, parameterTypes.reverse))
  for owner in owners do
    match compiledAtOwner : compileRuntimeFunction? types owner source with
    | none => throw (IO.userError "value-free compilation unexpectedly failed")
    | some compiled =>
        let provenance := compileRuntimeFunction?_sound compiledAtOwner
        have _ := provenance.core_hasType
        let expectedRows := ((names.zip parameterTypes).zipIdx.map fun (entry, index) =>
          (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2)).reverse
        assertTrue (decide (rows compiled.inputs = expectedRows ∧
          compiled.inputs.context.values = parameterTypes.reverse ∧
          Core.infer? parameterTypes.reverse core = some returnType ∧
          elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body =
            some (core, returnType))) "static rows, open Core typing, or original whole body changed"
        let mapping := ownerLocalIdMap shiftOwner
        let injective := ownerLocalIdMap_injective shiftOwner shiftOwnerInjective
        let mapped := compiled.inputs.mapIds mapping injective
        let declaredMapped := provenance.parameters.map_owner shiftOwner shiftOwnerInjective
        let compiledMapped := provenance.mapOwner shiftOwner shiftOwnerInjective
        have _ := declaredMapped.complete
        have _ := compiledMapped.complete
        assertTrue (decide (mapped.ids = compiled.inputs.ids.map mapping ∧
          mapped.names = LocalNameTable.mapIds mapping compiled.inputs.names ∧
          mapped.context = Resolved.LocalScope.mapIds mapping compiled.inputs.context ∧
          mapped.context.values = compiled.inputs.context.values ∧
          mapped.names.map Prod.fst = names.reverse)) "type-only map failed to retain source spelling/type order"
        assertTrue (decide ((declareRuntimeParameters? types (shiftOwner owner)
          source.value.signature.parameters.elements).map rows = some (rows mapped)))
          "independent declaration covariance changed the exact mapped rows"
        let some shifted := compileRuntimeFunction? types (shiftOwner owner) source
          | throw (IO.userError "injective owner map lost independent compilation")
        assertTrue (decide (rows shifted.inputs = rows mapped ∧ projection shifted = projection compiled))
          "compiled evidence covariance changed the mapped inputs, exact Core, or return contract"
        let identityMapped := compiled.inputs.mapIds id (fun _ _ same => same)
        let twice := mapped.mapIds mapping injective
        let composed := compiled.inputs.mapIds (mapping ∘ mapping) (injective.comp injective)
        assertTrue (decide (rows identityMapped = rows compiled.inputs ∧ rows twice = rows composed))
          "type-only identity or composition changed rows"
        if !compiled.inputs.bindings.isEmpty then
          assertTrue (decide (mapped.ids ≠ compiled.inputs.ids ∧
            mapped.ids.map (·.binderIndex) = compiled.inputs.ids.map (·.binderIndex)))
            "owner relabeling was trivial or changed source positions"

private def rejected (content : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed? content location | throw (IO.userError s!"{content}: semantic rejection did not fully parse")
  checkProjections source none
  for owner in owners do
    assertTrue (compileRuntimeFunction? types owner source).isNone "owner change enabled a rejected whole declaration"

private def terminalBlock : IO Unit := do
  let some source ← parsed? "function nested(){{return;}}"
    | throw (IO.userError "original terminal wrapper did not parse")
  checkProjections source (some (.unit, .unit, []))
  for owner in owners do
    match atBody : source.value.body with
    | ⟨outerSpan, [⟨innerSpan, .block [⟨returnSpan, .returnStmt none⟩]⟩]⟩ =>
        have _ : TypedLetReturnTreeElaborates types owner .empty source.value.body .unit .unit := by
          rw [atBody]; exact .block (.single .bare)
        assertTrue (outerSpan.contains innerSpan && innerSpan.contains returnSpan &&
          decide (outerSpan.startByte < innerSpan.startByte ∧ innerSpan.endByte < outerSpan.endByte))
          "original inner block range changed"
    | _ => throw (IO.userError "original lexical wrapper AST changed")
    let some compiled := compileRuntimeFunction? types owner source
      | throw (IO.userError "terminal block lost owner-independent compilation")
    assertTrue (decide (compiled.core = .unit ∧ compiled.returnType = .unit ∧ rows compiled.inputs = []) &&
      (elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body).isNone)
      "wrapper introduced a parameter row or widened the old tree adapter"
    have _ (definitions : Core.DataEnvironment) : Core.HasType [] .unit .unit definitions := .unit
    have _ := arbitraryOwnerProjections types owner (shiftOwner owner) source

def frontendParsedCompilationOwnersTests : IO Unit := do
  terminalBlock
  accepted "function bare(){return;}" [] .unit .unit
  accepted "function literal() returns (Word){return 7;}" [] (.word (Core.Word.ofNatModulo 7)) .word
  accepted "function opaque(x: Opaque) returns (Opaque){return x;}" [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  accepted "function unused(x: Opaque){return;}" [.namedData ⟨91⟩] .unit .unit
  for body in ["{return c ? x : y;}", "{if(c){return x;}else{return y;}}"] do
    accepted ("function nominal(c: Bool,x: Opaque,y: Opaque) returns (Opaque)" ++ body)
      [.bool, .namedData ⟨91⟩, .namedData ⟨91⟩] (.ifE (.var 2) (.var 1) (.var 0)) (.namedData ⟨91⟩)
  accepted "function units(c: Bool){if(c){return;}else{return;}}" [.bool] (.ifE (.var 0) .unit .unit) .unit
  accepted "function nested(c: Bool){if(c){if(c){return;}else{return;}}else{return;}}"
    [.bool] (.ifE (.var 0) (.ifE (.var 0) .unit .unit) .unit) .unit
  accepted "function alias(c: Pkg /* same spelling */ . Flag,x: Word,y: Word,) returns (Word){if(c){return x / y;}else{return x % y;}}"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordDiv (.var 1) (.var 0))
      (.binary .wordMod (.var 1) (.var 0))) .word
  let pool : List (String × Core.Ty) := [("Bool", .bool), ("Word", .word), ("Unit", .unit),
    ("Cell", .cell .word), ("Fn", .function .bool .bool), ("Opaque", .namedData ⟨91⟩),
    ("Pair", .product .word .bool), ("Choice", .sum .word .bool)]
  for arity in [1, 2, 4, 6, 8] do
    let inputs := pool.take arity
    let parameters := String.intercalate ", " (inputs.zipIdx.map fun (row, index) => s!"p{index}: {row.1}")
    for (selected, index) in inputs.zipIdx do
      accepted (s!"function position({parameters}) returns ({selected.1})" ++ "{return " ++ s!"p{index};" ++ "}")
        (inputs.map Prod.snd) (.var (arity - 1 - index)) selected.2
  -- Return-clause arity belongs to static header policy; supplied-argument arity does not.
  for content in ["function absent(){return 7;}", "function mismatch() returns (Bool){return 7;}",
      "function empty() returns (){return;}", "function many() returns (Word,Bool){return 7;}",
      "function unknown() returns (Unknown){return;}", "function generic<T>(){return;}",
      "function constrained() where Word: Eq {return;}", "function duplicate(x: Bool,x: Bool){return;}",
      "function duplicate(x: Word,y: Bool,x: Opaque){return;}", "function staged(comptime x: Bool){return;}",
      "function unknown(x: Unknown){return;}", "function unsupported(x: Word<Bool>){return;}",
      "function emptyBody(){}", "function extra(){return;return;}",
      "function call(f: Fn) returns (Bool){return f();}",
      "function missing(c: Bool,x: Opaque) returns (Opaque){return c ? x : missing;}",
      "function missing(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}",
      "function wrong(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return 0;}}",
      "function wrong(c: Word,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}",
      "function noElse(c: Bool){if(c){return;}}", "function extra(c: Bool){if(c){return;}else{return;}return;}"] do
    rejected content
  for content in ["function publicOnly() public {return;}", "function payableOnly() payable {return;}"] do
    rejected content .contract
  -- Missing annotations are parser failures, not type-only argument-guard failures.
  for content in ["", "function missing(x){return;}", "function missing(x:){return;}", "function f()",
      "function f(){return;", "function f(){return 7}", "function f(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "malformed, diagnosed, or incompletely consumed declaration accepted"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedScopedShadowingEffects
/-! Old initializer x and fresh Word/Bool rows coexist; explicit blocks protect the outer scope. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedScopedShadowingEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ScopedShadowingEffects",by decide⟩],by decide⟩⟩,124⟩
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["Word"],.word),(["Bool"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def output : Core.Ty := .product .bool .word
private def reader (l : Nat) : Core.Value := .closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def writer (l : Nat) (v : Core.Value) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.var 3)) [.cellRef .word l,v]
private def pairCore : Core.Expr := .pair (.var 0) (.var 2)
private def testCore (f : Nat) : Core.Expr := .binary .wordEq (.apply (.var f) (.var 0)) (.var 0)
private def branchCore (f : Nat) : Core.Expr := .letE (testCore f) pairCore
private def afterCore : Core.Expr := .ifE (.var 2) (branchCore 4) (branchCore 5)
private def tailCore : Core.Expr := .letE (.apply (.var 4) (.var 2)) afterCore
private def core : Core.Expr := .letE (.var 1) tailCore
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,x:Word,c:Bool) returns((Bool,Word)){let prior=x;let x:Word=f(x);if(c){{let x=w(x)==x;return(x,prior);}}else{{let x:Bool=f(x)==x;return(x,prior);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"scoped-shadowing-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a,b]⟩ => let x ← meaning a; let y ← meaning b; return ⟨.product x.1 y.1,⟨by rw [shape]; exact .pair x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _,_ => throw (IO.userError "original arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | ⟨span,.tuple ⟨ts,[a,b]⟩⟩ =>
      check (span.contains ts && ts.contains a.span && ts.contains b.span && decide (a.span.endByte≤b.span.startByte)) "original pair order"
      let x ← child i a; let y ← child i b; return ⟨.pair x.core y.core,.product x.type y.type,by rw [shape]; exact .pair x.evidence y.evidence⟩
  | ⟨_,.binary a ⟨_,.equal⟩ b⟩ =>
      let x ← child i a; let y ← child i b
      if same : x.type=.word ∧ y.type=.word then return ⟨.binary .wordEq x.core y.core,.bool,by rw [shape]; exact .binary .equal (by simpa only [Core.BinaryOp.leftType,same.1] using x.evidence) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType,same.2] using y.evidence)⟩ else throw (IO.userError "old Word initializer operands")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← body i ⟨span,statements⟩; return ⟨r.core,r.type,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.length=i.ids.length+1 ∧ next.ids.head?=some ⟨owner,if name.value="prior" then 4 else if a.type=.word then 5 else 6⟩)) "scope-local fresh IDs retain every old name/type row"
      if name.value="x" then check (decide (i.names.lookup? "x"=some ⟨owner,if a.type=.word then 2 else 5⟩ ∧ next.names.lookup? "x"=next.ids.head?)) "initializer sees old x; tail selects the newly prepended x"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← child i c; let t ← body i yes; let e ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : a.type=.bool ∧ t.type=e.type then return ⟨.ifE a.core t.core e.core,t.type,by rw [shape]; exact .conditional (same.1 ▸ a.evidence) protection t.evidence (same.2.symm ▸ e.evidence)⟩ else throw (IO.userError "branch type")
      | _ => throw (IO.userError "original explicit then scope barrier")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=output)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=output ∧ b.core=core ∧ b.type=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature (output) := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,output⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("c",⟨owner,3⟩),("x",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original declarations and actual reverse once"
          return ⟨⟨ps.actual,core,output⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core and outer single annotation")
  | _ => throw (IO.userError "outer single return policy")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .pair a b =>
        let l ← path n a env s; let r ← path n b env l.final
        return ⟨.pair l.value r.value,r.final,l.cost+r.cost+3,fun k => by rw [shape]; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (Core.Steps.cons .enterPair ((l.evidence _).trans (.cons .enterPairRight ((r.evidence _).trans (.cons .applyPair .refl)))))⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | .binary .wordEq a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : Core.BinaryOp.wordEq.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual equality fault")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | ⟨_,.tuple ⟨_,[a,b]⟩⟩ => let l ← rawChild table env s a; let r ← rawChild table env l.final b; return ⟨.pair l.value r.value,r.final,l.cost+r.cost+3,by rw [shape]; exact .pair l.evidence r.evidence⟩
  | ⟨_,.binary a ⟨_,.equal⟩ b⟩ =>
      let l ← rawChild table env s a; let r ← rawChild table env l.final b
      match applied : Core.BinaryOp.wordEq.apply l.value r.value with
      | some v => return ⟨v,r.final,l.cost+r.cost+3,by rw [shape]; exact .binary .equal l.evidence r.evidence applied⟩
      | none => throw (IO.userError "raw equality fault")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← rawBody table env s ⟨span,statements⟩; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← rawChild table env s c
      match cv : a.value with
      | .bool true => let r ← rawBody table env a.final yes; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifTrue (cv ▸ a.evidence) r.evidence⟩
      | .bool false => let r ← rawBody table env a.final no; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifFalse (cv ▸ a.evidence) r.evidence⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument) (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with | nil => exact .nil | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (c : Bool) (s final : Core.Store) (value : Core.Value) : IO Unit := do
  let source ← parsed; let rawValues := [reader 0,writer 1 (w 73),w 14,.bool c]; let cost := 45
  let manual ← path 80 (core) rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal calls, captures, store and cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original constructed fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval (core) env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body (core) (output) := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,original⟩; have _ := original.core_hasType RecursiveLocalComputationElaborates.core_hasType
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval (core) env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have _ := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ validateRuntimeInputs [.word,.word] args s=true)) "independent source cost and opt-in world boundary"
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    have _ := prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args
    have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have whole (fuel) : runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial (core) env s)) := by simp only [runRecursiveComputationFunction?,runComputationFunction?,accepted,p.2.down.2.1,p.2.down.2.2,bind,Option.bind_some,pure]; rfl
    for fuel in List.range (cost+2) do
      have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
      have _ := whole fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial (core) env s)))) "same prepared full entry result"
      match stopped : Core.runStateful fuel (.initial (core) env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "fixed completion threshold"
      | .fault _ _ => throw (IO.userError "successful raw path fault")
      | .outOfFuel cp =>
          for extra in [0,1,7,cost] do
            have _ := (literal []).residual_of_outOfFuel stopped; have _ := Core.runStateful_resume stopped extra
            check (decide (fuel<cost ∧ Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    if validated : validateRuntimeInputs [.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have finitePath : Core.Steps manual.cost
          (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
        rw [p.2.down.2.1]
        exact literal []
      have safe := p.2.down.1.runtime_typed_execution (F := RecursiveLocalComputationFragment) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
      have agreement : ∃ future, Core.WorldExtends [.word,.word] future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ Core.RuntimeValueHasType future manual.value (output) ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost ∧
          ∀ fuel, (Core.runStateful fuel (.initial (core) env s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧ ((∃ cp, Core.runStateful fuel (.initial (core) env s)=.outOfFuel cp) ↔ fuel<manual.cost) := by
        obtain ⟨future,t,v,n,extension,stored,typed,sourceCost,paths,thresholds,_⟩ := safe.2
        have closed : Core.Steps manual.cost (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact literal []
        obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
        exact ⟨future,extension,stored,by simpa only [p.2.down.2.2] using typed,sourceCost,by simpa only [p.2.down.2.1] using thresholds⟩
      have _ := agreement; have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word] env i.toTypeInputs.context.values := by simpa only [env,i,LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial (core) env s) with
        | .outOfFuel cp =>
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 Core.ContinuationHasType.nil stopped
            have future : ∃ savedWorld finalWorld, Core.WorldExtends [.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld manual.final := by
              obtain ⟨savedWorld,ext,storeTyped,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed ((literal []).residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,ext,storeTyped,growth,finalTyped⟩
            have _ := future
        | _ => throw (IO.userError "genuine typed checkpoint")
    have _ := (literal [.pairApply .unit]).trans (.cons .applyPair .refl)
    check (decide (Core.runStateful cost ⟨.eval (core) env,[.pairApply .unit],s⟩=.outOfFuel ⟨.ret value,[.pairApply .unit],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core) env,[.pairApply .unit],s⟩=.done (.pair .unit value) final)) "retained frame is outside original source cost"
    let outerEnv := w 41::w 14::env; let allocated := s++[w 14]; let left := if c then w 73 else w 41
    let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),[.letBody tailCore env],s⟩),(17,⟨.ret (w 41),[.letBody afterCore (w 14::env)],allocated⟩),(20,⟨.ret (.bool c),[.ifBranches (branchCore 4) (branchCore 5) outerEnv],allocated⟩),(36,⟨.ret left,[.binaryRight .wordEq (.var 0) outerEnv,.letBody pairCore outerEnv],final⟩),(38,⟨.ret (w 41),[.binaryApply .wordEq left,.letBody pairCore outerEnv],final⟩),(39,⟨.ret (.bool (!c)),[.letBody pairCore outerEnv],final⟩)]
    for (spent,cp) in checkpoints do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        check (decide (Core.runStateful (cost-spent) cp=.done value final)) "actual old x, preserved captured callee, changed Bool x before fresh binding"
      else throw (IO.userError "literal checkpoint fields")
  else throw (IO.userError "actual reverse once")
private def fault (c : Bool) : IO Unit := do
  let source ← parsed; let rawValues := [reader 0,writer 1 (w 73),w 14,.bool c]
  let args ← rawValues.mapM fun v => match buildRuntimeArgument? v with | some a => pure a | none => throw (IO.userError "fault structural construction")
  let p ← prepare source args; let env := p.1.inputs.environment.values; let old := Core.Value.bool false
  let s := [old,w 99]; let t := if c then [old,old,w 14] else [old,w 99,w 14,old]
  let outerEnv := old::w 14::env; let left := if c then w 73 else old
  let frames := [.binaryApply .wordEq left,.letBody pairCore outerEnv]
  let failed : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq left old) ⟨.ret old,frames,t⟩
  let before : Core.State := ⟨.eval (.var 0) outerEnv,frames,t⟩
  check (decide (validateRuntimeInputs [.word,.word] args s=false ∧ Core.runStateful 37 (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "initializer fault precedes new Bool shadow and retains selected effects"
  for fuel in List.range 40 do
    let result := Core.runStateful fuel (.initial core env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,result))) "same static shadow preparation is not a raw value guard"
    if fuel<38 then match stopped : result with
      | .outOfFuel cp => have _ := Core.runStateful_resume (by simpa only [result] using stopped) 38; check (decide (Core.runStateful 38 cp=failed)) "all genuine pre-fault states retain old rows and store effects"
      | _ => throw (IO.userError "first corrupt-store fault")
    else check (decide (result=failed)) "exact fault and later fuels"
end ParsedScopedShadowingEffects
open ParsedScopedShadowingEffects
def frontendParsedScopedShadowingEffectTests : IO Unit := do
  verify true [w 41,w 99] [w 41,w 41,w 14] (.pair (.bool false) (w 14)); verify false [w 41,w 99] [w 41,w 99,w 14,w 41] (.pair (.bool true) (w 14))
  fault true; fault false
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedScopedShadowingMigrations
/-! Three exact old rejections become positives without replacing their original
owners, source files, caller rows or annotations. Store invariance below belongs
only to the original identity/constant closure fixture, not arbitrary callees. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment RecursiveLocalComputationEvaluatesWithCost
namespace ParsedScopedShadowingMigrations
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def shared : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Shared",by decide⟩],by decide⟩⟩,54⟩
private def compileOwner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"CompileRecursive",by decide⟩],by decide⟩⟩,4⟩
private def id (n : Nat) : Resolved.LocalId := ⟨shared,n⟩
private def foreign : Resolved.LocalId := ⟨{shared with declarationIndex := 91},302⟩
private def inputs : LocalTypeInputs := ⟨[⟨"x",id 4,.word⟩,⟨"f",foreign,.function .word .word⟩,
  ⟨"g",id 9,.function .word .word⟩,⟨"h",id 12,.function .word .word⟩,⟨"k",id 15,.function .word .word⟩,
  ⟨"p",id 20,.function .word .bool⟩,⟨"f",id 25,.bool⟩],by change [id 4,foreign,id 9,id 12,id 15,id 20,id 25].Nodup; decide⟩
private def types : TypeNameTable := [(["Word"],.word),(["A"],.word),(["A"],.bool)]
private def value : Core.Value := .word (Core.Word.ofNatModulo 17)
private def identity : Core.Value := .closure .word .word (.var 0) [.bool false]
private def environment : Resolved.Environment := [(id 4,value),(foreign,identity),(id 9,identity),
  (id 12,identity),(id 15,identity),(id 20,.closure .word .bool (.bool true) [.unit]),(id 25,.bool false)]
private def parsed (fileName text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,fileName⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "parser")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span &&
    source.span.contains source.value.signature.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original declaration ranges"
  return source
private structure Child (i : LocalTypeInputs) (e : Resolved.Environment) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : RecursiveLocalComputationElaborates i.names i.context source core type
  counted : ∀ store, RecursiveLocalComputationEvaluatesWithCost i.names e store source value store cost
private def child (i : LocalTypeInputs) (e : Resolved.Environment) (source : Syntax.Expr) : IO (Child i e source) := do
  match shape : source with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some localId =>
          match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId, actual : e.lookup? localId with
          | some type,some index,some value =>
              return ⟨.var index,type,value,1,by
                rw [shape]
                exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                  (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
                fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original static/actual row")
      | none => throw (IO.userError "original name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span &&
        decide (fn.span.endByte≤argsSpan.startByte)) "original call order/ranges"
      let f ← child i e fn; let a ← child i e arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then
            have el : RecursiveLocalComputationElaborates i.names i.context source (.apply f.core a.core) output := by
              rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration)
            match actual : f.value with
            | .closure _ _ (.var 0) captures =>
                return ⟨.apply f.core a.core,output,a.value,f.cost+a.cost+4,el,fun s => by
                  rw [shape]
                  exact .application (actual ▸ f.counted s) (a.counted s) (.cons (.var rfl) .refl)⟩
            | .closure _ _ (.bool flag) captures =>
                return ⟨.apply f.core a.core,output,.bool flag,f.cost+a.cost+4,el,fun s => by
                  rw [shape]
                  exact .application (actual ▸ f.counted s) (a.counted s) (.cons .bool .refl)⟩
            | _ => throw (IO.userError "original closure body")
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | _ => throw (IO.userError "original child shape")
termination_by sizeOf source
private structure Body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (e : Resolved.Environment) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : RecursiveComputationReturnTreeElaborates ts o i source core type
  counted : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost o i.names e store source value store cost
private def body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (e : Resolved.Environment) (source : Syntax.Block) : IO (Body ts o i e source) := do
  for statement in source.value do check (source.span.contains statement.span) "original statement ranges"
  match shape : source with
  | ⟨_,[⟨rs,.returnStmt (some expression)⟩]⟩ =>
      check (rs.contains expression.span) "original return range"; let a ← child i e expression
      return ⟨a.core,a.type,a.value,a.cost,by rw [shape]; exact .expression a.elaboration,
        fun s => by rw [shape]; exact .expression (a.counted s)⟩
  | ⟨span,⟨ls,.letDecl name none (some initializer)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span && decide (name.span.endByte≤initializer.span.startByte)) "original initializer before new binding"
      let a ← child i e initializer; let fresh := Resolved.freshLocalId o i.ids
      let b ← body ts o (i.bindFresh o name.value a.type) ((fresh,a.value)::e) ⟨span,rest⟩
      return ⟨.letE a.core b.core,b.type,b.value,a.cost+b.cost+2,by rw [shape]; exact .inferred a.elaboration b.elaboration,
        fun s => by rw [shape]; exact .inferred (a.counted s) (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.counted s)⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then
        pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child i e guard; let a ← body ts o i e yes; let b ← body ts o i e no
      if same : c.type=.bool ∧ b.type=a.type then
        have el : RecursiveComputationReturnTreeElaborates ts o i source (.ifE c.core a.core b.core) a.type := by
          rw [shape]; exact .conditional (same.1 ▸ c.elaboration) protection.down a.elaboration (same.2 ▸ b.elaboration)
        match actual : c.value with
        | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,c.cost+a.cost+2,el,
            fun s => by rw [shape]; exact .ifTrue (actual ▸ c.counted s) (a.counted s)⟩
        | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,c.cost+b.cost+2,el,
            fun s => by rw [shape]; exact .ifFalse (actual ▸ c.counted s) (b.counted s)⟩
        | _ => throw (IO.userError "actual guard")
      else throw (IO.userError "both original branch types")
  | _ => throw (IO.userError "original body shape")
termination_by sizeOf source
private def nested (f g : Nat) : Core.Expr := .apply (.var f) (.apply (.var g) (.var 0))
private def core (branch : Bool) : Core.Expr := if branch then
  .ifE (nested 5 2) (.var 0) (.letE (.var 0) (.var 0)) else .letE (nested 1 2) (.var 0)
private theorem invoke {e : Core.Environment} {s : Core.Store} {k : List Core.Frame} {f n : Nat}
    {arg : Core.Expr} {a b : Core.Ty} {actual : Core.Expr} {captures : Core.Environment} {x v : Core.Value}
    (found : e[f]?=some (.closure a b actual captures))
    (argument : Core.Steps n ⟨.eval arg e,.applyClosure a b actual captures::k,s⟩ ⟨.ret x,.applyClosure a b actual captures::k,s⟩)
    (closure : Core.Steps 1 (.initial actual (x::captures) s) (.final v s)) :
    Core.Steps (1+n+1+3) ⟨.eval (.apply (.var f) arg) e,k,s⟩ ⟨.ret v,k,s⟩ :=
  CostStepComposition.apply (.cons (.var found) .refl) argument closure
private theorem manual (branch : Bool) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 14 ⟨.eval (core branch) environment.values,k,s⟩ ⟨.ret value,k,s⟩ := by
  cases branch
  · exact CostStepComposition.letE (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)
  · exact CostStepComposition.ifTrue (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons .bool .refl)) (.cons (.var rfl) .refl)
private def originalBody (branch : Bool) := if branch then
  "if(p(g(x))){return x;}else{let x=x;return x;}" else "let x=f(g(x));return x;"
private def exercise (branch : Bool) : IO Unit := do
  let declaration ← parsed "shared-body.sol" ("function original(){"++originalBody branch++"}")
  let source := declaration.value.body; let b ← body types shared inputs environment source
  if fixed : b.core=core branch ∧ b.type=.word ∧ b.value=value ∧ b.cost=14 then
    have el : RecursiveComputationReturnTreeElaborates types shared inputs source (core branch) .word := by
      simpa only [fixed.1,fixed.2.1] using b.elaboration
    have _ := ComputationReturnTreeElaborates.core_hasType core_hasType el
    have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,el⟩
    have accepted := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr el
    check (decide (elaborateRecursiveComputationReturnTree? types shared inputs source=some (core branch,.word) ∧
      (inputs.bindFresh shared "x" .word).names.lookup? "x"=some (id 26) ∧ inputs.names.lookup? "f"=some foreign ∧
      types.lookup? ["A"]=some .word)) "same sparse duplicate tables/new exact binder"
    for store in [[],[Core.Value.bool true,.unit]] do
      have raw : RecursiveComputationReturnTreeEvaluatesWithCost shared inputs.names environment store source value store 14 := by
        simpa only [fixed.2.2.1,fixed.2.2.2] using b.counted store
      have _ := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := RecursiveLocalComputationEvaluates)
        (ChildCost := RecursiveLocalComputationEvaluatesWithCost) recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨_,raw⟩
      have costLaw := ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps (F := RecursiveLocalComputationFragment)
        (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        core_fragment weakenAt evaluates_insert_iff evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost insertion_paths toStepsWithContinuation el (environment := environment) rfl
      have _ := ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost) deterministic raw (costLaw.mpr (manual branch store []))
      have _ := costLaw.mp raw
      have fragment := ComputationReturnTreeElaborates.core_fragment (ChildElab := RecursiveLocalComputationElaborates)
        (F := RecursiveLocalComputationFragment) core_fragment weakenAt el
      let inserted := Core.Value.cellRef (.namedData ⟨99⟩) 404
      have paired : ∀ k, Core.Steps 14 ⟨.eval (core branch) environment.values,k,store⟩ ⟨.ret value,k,store⟩ ∧
          Core.Steps 14 ⟨.eval ((core branch).weakenAt 0) (inserted::environment.values),k,store⟩ ⟨.ret value,k,store⟩ := by
        obtain ⟨n,paths⟩ := ComputationBodyFragment.insertion_paths (F := RecursiveLocalComputationFragment)
          insertion_paths fragment [] environment.values inserted (Core.steps_from_initial_sound (manual branch store []))
        have same := ((manual branch store []).final_unique (paths []).1).1
        exact same.symm ▸ paths
      have _ := (paired []).2.runStateful_done_iff (fuel := 14)
      let cp : Core.State := if branch then ⟨.ret (.bool true),[.ifBranches (.var 0) (.letE (.var 0) (.var 0)) environment.values],store⟩
        else ⟨.ret value,[.letBody (.var 0) environment.values],store⟩
      check (decide (Core.runStateful 12 (.initial (core branch) environment.values store)=.outOfFuel cp ∧
        Core.runStateful 1 cp=.outOfFuel ⟨.eval (.var 0) (if branch then environment.values else value::environment.values),[],store⟩ ∧
        Core.runStateful 2 cp=.done value store)) "literal genuine guard/binder checkpoint and old/new environment"
      for k in [[],[Core.Frame.letBody .unit []]] do
        have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
          (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          core_fragment weakenAt insertion_paths toStepsWithContinuation raw el rfl k
        check (decide (Core.runStateful 14 ⟨.eval (core branch) environment.values,k,store⟩=
          if k=[] then .done value store else .outOfFuel ⟨.ret value,k,store⟩)) "manual same cost/pending actual endpoint"
      for fuel in List.range 16 do
        have _ := (manual branch store []).runStateful_done_iff (fuel := fuel)
        let start := Core.State.initial (core branch) environment.values store
        match genuine : Core.runStateful fuel start with
        | .done result final => check (decide (14≤fuel ∧ result=value ∧ final=store)) "original value/store/full fuel"
        | .outOfFuel cp =>
            have _ := (manual branch store []).residual_of_outOfFuel genuine
            for more in List.range 16 do
              have _ := Core.runStateful_resume genuine more
              check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) start)) "genuine full resumption"
            check (decide (fuel<14 ∧ Core.runStateful (14-fuel) cp=.done value store)) "exact residual"
        | .fault _ _ => throw (IO.userError "original success faulted")
  else throw (IO.userError "independent original static/raw differs")
private def compileTypes : TypeNameTable := [(["F"],.function .word .word),(["F"],.bool),
  (["G"],.function .word .word),(["A"],.word),(["B"],.word),(["R"],.word),
  (["Unit"],.unit),(["Word"],.word),(["mod","F"],.function .word .word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes compileTypes source type)) := do
  match shape : source with
  | ⟨_,.named name none⟩ =>
      match found : compileTypes.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation lookup")
  | _ => throw (IO.userError "original annotation shape")
private def declare (i : LocalTypeInputs) (ps : List Syntax.FunctionParameter) :
    IO (Σ result, PLift (RuntimeParametersDeclareFrom compileTypes compileOwner i ps result)) := do
  match shape : ps with
  | [] => return ⟨i,⟨by rw [shape]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte≤annotation.span.startByte)) "original parameter ranges/order"
      let m ← meaning annotation
      if unused : name.value ∉ i.names.map Prod.fst then
        let tail ← declare (i.bindFresh compileOwner name.value m.1) rest
        return ⟨tail.1,⟨by rw [shape]; exact .cons m.2.down unused tail.2.down⟩⟩
      else throw (IO.userError "duplicate parameters remain excluded")
  | _ => throw (IO.userError "original parameter shape")
private def compilation : IO Unit := do
  let source ← parsed "compile-recursive.sol" "function example(f:F,g:G,x:A) returns(R){let x=f(g(x));return x;}"
  let sig := source.value.signature; let declared ← declare .empty sig.parameters.elements
  let expectedInputs := ((LocalTypeInputs.empty.bindFresh compileOwner "f" (.function .word .word)).bindFresh compileOwner "g" (.function .word .word)).bindFresh compileOwner "x" .word
  if original : declared.1.names=expectedInputs.names ∧ declared.1.context=expectedInputs.context then
    let env : Resolved.Environment := [(⟨compileOwner,2⟩,value),(⟨compileOwner,1⟩,identity),(⟨compileOwner,0⟩,identity)]
    let b ← body compileTypes compileOwner declared.1 env source.value.body
    if policy : sig.genericParameters=none ∧ sig.whereClause=none ∧ sig.modifiers.publicMarker=none ∧ sig.modifiers.payableMarker=none then
      match returns : sig.returnsClause with
      | some ⟨_,⟨_,[annotation]⟩⟩ =>
          let m ← meaning annotation
          if fixed : m.1=.word ∧ b.type=.word ∧ b.core=.letE (nested 2 1) (.var 0) then
            have header : RuntimeFunctionHeader compileTypes sig .word :=
              ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [returns]; exact .single (fixed.1 ▸ m.2.down)⟩
            let compiled : CompiledRuntimeFunction := ⟨declared.1,.letE (nested 2 1) (.var 0),.word⟩
            have certificate : RecursiveComputationFunctionCompiles compileTypes compileOwner source compiled :=
              ⟨header,declared.2.down,by simpa only [compiled,fixed.2.1,fixed.2.2] using b.elaboration⟩
            have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr certificate
            check (decide ((compileRecursiveComputationFunction? compileTypes compileOwner source).map (fun c => (c.inputs.names,c.inputs.context,c.core,c.returnType))=
              some (expectedInputs.names,expectedInputs.context,.letE (nested 2 1) (.var 0),.word) ∧
              (declared.1.bindFresh compileOwner "x" .word).names.lookup? "x"=some ⟨compileOwner,3⟩ ∧
              compileRuntimeComputationFunction? compileTypes compileOwner source=none ∧
              compileComputationFunction? elaborateLocalComputation? compileTypes compileOwner source=none)) "original full declaration/exact compile/old endpoints"
          else throw (IO.userError "independent original compile differs")
      | _ => throw (IO.userError "original returns clause")
    else throw (IO.userError "original whole header")
  else throw (IO.userError "original parameters reverse once")
end ParsedScopedShadowingMigrations
open ParsedScopedShadowingMigrations
def frontendParsedScopedShadowingMigrationTests : IO Unit := do
  exercise true
  exercise false
  compilation
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedSourceComputationBodyEffects
set_option autoImplicit false
namespace Tests
namespace ParsedSourceComputationBodyEffects
open Solcore Solcore.Frontend
private abbrev Store := List RuntimeValue
private abbrev Captures := Resolved.LocalScope RuntimeValue
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def word (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def w (n : Nat) : RuntimeValue := .word (word n)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"MixedSourceBodies",by decide⟩],by decide⟩⟩,155⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=156}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def names : LocalNameTable := [("x",sid 7),("r",sid 31),("c",sid 3),("r",sid 8),("x",foreign)]
private def captured (c : Bool) : Captures :=
  [(sid 32,.bool false),(sid 31,.cellRef (.function .word .word) 0),(sid 7,w 5),(sid 31,w 99),(sid 3,.bool c),(foreign,.unit)]
private def ns0 := ("x",sid 32)::names
private def ns1 := ("x",sid 33)::ns0
private def ns2 := ("x",sid 34)::ns1
private def es0 (q : RuntimeValue) (c : Bool) := (sid 32,q)::captured c
private def es1 (q : RuntimeValue) (c : Bool) := (sid 33,q)::es0 q c
private def es2 (q r : RuntimeValue) (c : Bool) := (sid 34,r)::es1 q c
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (ns0.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (ns1.map Prod.snd)=sid 34 := by decide
private def finalStore (r : RuntimeValue) : Store := [r,.unit,.bool true,w 7]
private def refName (e : Syntax.Expr) : Option String := match e.value with | .identifier n => some n.value | _ => none
private def callShape (e : Syntax.Expr) (name : String) (args : List String) : Bool :=
  match e.value with | .call ⟨_,.identifier n⟩ ⟨_,es⟩ => n.value == name && es.map refName == args.map some | _ => false

/- These six independent callbacks describe only the named fixture operations.
They do not recursively close expression/body evaluation or enforce runtime typing. -/
private inductive Child (o : Resolved.DeclarationId) (ns : LocalNameTable) (es : Captures) :
    Store → Syntax.Expr → RuntimeValue → Store → Prop where
  | reference {s e n i v} (shape : refName e = some n) (name : LocalNameTable.Lookup ns n i)
      (value : Resolved.LocalScope.Lookup es i v) : Child o ns es s e v s
  | fetch {s e i v} (shape : callShape e "fetch" [] = true) (name : LocalNameTable.Lookup ns "fetch" i)
      (value : Resolved.LocalScope.Lookup es i v) : Child o ns es s e v (s ++ [.unit])
  | argument {s e i j q r} (shape : callShape e "argument" [] = true)
      (name : LocalNameTable.Lookup ns "argument" i) (value : Resolved.LocalScope.Lookup es i q)
      (writtenName : LocalNameTable.Lookup ns "written" j) (written : Resolved.LocalScope.Lookup es j r) :
      Child o ns es s e q (s.set 0 r)
  | load {s e i tag location v} (shape : callShape e "load" ["r"] = true)
      (name : LocalNameTable.Lookup ns "r" i) (reference : Resolved.LocalScope.Lookup es i (.cellRef tag location))
      (read : s[location]? = some v) : Child o ns es s e v s
  | touch {s e} (shape : callShape e "touch" [] = true) : Child o ns es s e .unit (s ++ [.bool true])
  | observe {s e i v} (shape : callShape e "observe" ["x"] = true)
      (name : LocalNameTable.Lookup ns "x" i) (value : Resolved.LocalScope.Lookup es i v) :
      Child o ns es s e v (s ++ [w 7])
private abbrev Body := SourceComputationBodyEvaluates Child
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p with
  | ⟨_,.wildcard _⟩ => return ⟨none,⟨by rw [shape]; exact .wildcard rfl⟩⟩
  | ⟨_,.group inner⟩ =>
    check (p.span.contains inner.span) "original grouped pattern ranges"
    let child ← pattern inner
    return ⟨child.1,⟨by rw [shape]; exact .group child.2.down⟩⟩
  | ⟨_,.literal ⟨s,.decimal "0"⟩⟩ =>
    return ⟨some (word 0),⟨by rw [shape]; exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩⟩⟩
  | ⟨_,.literal ⟨s,.hexadecimal "0x00"⟩⟩ =>
    return ⟨some (word 0),⟨by rw [shape]; exact .literal ⟨_,rfl,.hexadecimal rfl (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) (.cons (.decimal (digit:=0) (by decide) rfl) .nil))⟩⟩⟩
  | _ => throw (IO.userError "outside independently supported fixture patterns")
termination_by sizeOf p
private def choice (r : RuntimeValue) (cs : List Syntax.MatchCase) (d : Option Syntax.Block) :
    IO (Σ selected : Syntax.Block, Σ tests : Nat, PLift (RuntimeWordMatchChooses r cs d selected tests)) := do
  match casesShape : cs with
  | [] => match defaultShape : d with
    | some b => return ⟨b,0,⟨by rw [casesShape,defaultShape]; exact .fallback⟩⟩
    | none => throw (IO.userError "no original fallback")
  | first::rest =>
    let p ← pattern first.value.pattern
    match tag : p.1 with
    | none => return ⟨first.value.body,0,⟨by rw [casesShape]; exact .wildcard (tag ▸ p.2.down)⟩⟩
    | some literal => match actual : r with
      | .word value =>
        if same : value = literal then
          return ⟨first.value.body,1,⟨by rw [casesShape,actual,same]; exact .hit (tag ▸ p.2.down)⟩⟩
        else
          let tail ← choice (.word value) rest d
          return ⟨tail.1,tail.2.1+1,⟨by rw [casesShape]; simpa only [actual] using RuntimeWordMatchChooses.miss (tag ▸ p.2.down) same tail.2.2.down⟩⟩
      | _ => throw (IO.userError "no successful literal choice, not a runtime fault")
termination_by cs.length
private def returned (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns2 (es2 q r c) (finalStore r) b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨true,⟨by rw [shape]; exact .bare⟩⟩
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
    if ref : refName e = some "x" then return ⟨false,⟨by rw [shape]; exact .expression (.reference ref .head .head)⟩⟩
    else throw (IO.userError "unselected or unsupported returned expression")
  | _ => throw (IO.userError "fixture return shape")
private def matched (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns2 (es2 q r c) [r,.unit,.bool true] b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,d⟩⟩⟩]⟩ =>
    check (b.span.contains e.span && cs.all (fun arm => b.span.contains arm.span &&
      arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span) &&
      d.toList.all (fun branch => b.span.contains branch.span)) "original scrutinee, arms and optional default spans"
    if observed : callShape e "observe" ["x"] = true then
      let selected ← choice r cs d
      let result ← returned q r c selected.1
      have _ : ∀ b n, RuntimeWordMatchChooses r cs d b n → b=selected.1 ∧ n=selected.2.1 :=
        fun _ _ other => RuntimeWordMatchChooses.deterministic other selected.2.2.down
      return ⟨result.1,⟨by rw [shape]; exact .wordMatch (.observe observed .head .head) selected.2.2.down result.2.down⟩⟩
    else throw (IO.userError "original single effectful scrutinee")
  | _ => throw (IO.userError "original singleton match")
private def terminal (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns2 (es2 q r c) [r,.unit,.bool true] b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨_,[⟨_,.ifThen condition thenBody (some elseBody)⟩]⟩ =>
    if ref : refName condition = some "c" then
      have evaluated : Child owner ns2 (es2 q r c) [r,.unit,.bool true] condition (.bool c) [r,.unit,.bool true] :=
        .reference ref (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))))
      match branch : c with
      | true =>
        match explicit : thenBody with
        | ⟨_,[⟨innerSpan,.block statements⟩]⟩ =>
          let result ← matched q r c ⟨innerSpan,statements⟩
          return ⟨result.1,⟨by rw [shape]; exact .ifTrue (by simpa only [branch] using evaluated) (by rw [explicit]; exact .block result.2.down)⟩⟩
        | _ => throw (IO.userError "original explicit then block")
      | false =>
        let result ← matched q r c elseBody
        return ⟨result.1,⟨by rw [shape]; exact .ifFalse (by simpa only [branch] using evaluated) result.2.down⟩⟩
    else throw (IO.userError "captured condition")
  | _ => matched q r c b
private def body (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns0 (es0 q c) [r,.unit] b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨span,⟨_,.letDecl n (some _) (some init)⟩::⟨ms,.letDecl m none (some load)⟩::⟨ds,.expression touch true⟩::rest⟩ =>
    check (span.contains n.span && span.contains m.span && span.contains init.span && span.contains load.span &&
      span.contains touch.span && rest.all (fun statement => span.contains statement.span)) "original initializer and tail ranges"
    if valid : n.value="x" ∧ m.value="x" ∧ refName init=some "x" ∧
        callShape load "load" ["r"]=true ∧ callShape touch "touch" []=true then
      have hn := valid.1; have hm := valid.2.1
      let result ← terminal q r c ⟨span,rest⟩
      have first : Child owner ns0 (es0 q c) [r,.unit] init q [r,.unit] := .reference valid.2.2.1 .head .head
      have second : Child owner ns1 (es1 q c) [r,.unit] load r [r,.unit] :=
        .load valid.2.2.2.1 (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) rfl
      have last : Body owner ns2 (es2 q r c) [r,.unit] ⟨span,⟨ds,.expression touch true⟩::rest⟩ (if result.1 then .unit else r) (finalStore r) :=
        .discard (.touch valid.2.2.2.2) result.2.down
      have next : Body owner ns1 (es1 q c) [r,.unit] ⟨span,⟨ms,.letDecl m none (some load)⟩::⟨ds,.expression touch true⟩::rest⟩ (if result.1 then .unit else r) (finalStore r) :=
        .inferred second (by simpa only [hm,fresh2,ns2,es2] using last)
      return ⟨result.1,⟨by rw [shape]; exact .binding first (by simpa only [hn,fresh1,ns1,es1] using next)⟩⟩
    else throw (IO.userError "original same-name binders, old initializer, load and discard")
  | _ => throw (IO.userError "independent typed/inferred/discard original prefix")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"mixed-source-body-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span == Syntax.SourceSpan.fullFile file) "full original source and diagnostics"
    return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private def inspect (source callSource : Syntax.Expr) (q r : RuntimeValue) (c : Bool) (bare : Bool := false) : IO Unit := do
  match original : source, callShapeEq : callSource with
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ savedBody⟩,⟨callSpan,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
    if valid : name.value="x" ∧ callShape callee "fetch" []=true ∧ callShape argument "argument" []=true then
      have parameter := valid.1; have fetch := valid.2.1; have arg := valid.2.2
      have saved : SourceUnaryLambdaShape source name savedBody := by rw [original]; exact .typed
      check (source.span.contains name.span && source.span.contains savedBody.span &&
        savedBody.span.startByte==23 && savedBody.span.endByte==source.span.endByte) "whole saved original lambda and body"
      have created : SourceLambdaEvaluates Child Body owner names (captured c) [w 5] source
          (.sourceClosure source owner names (captured c)) [w 5] := .creation saved
      have _ := (SourceLambdaEvaluates.creation_iff saved).mp created
      let result ← body q r c savedBody
      let callerNames : LocalNameTable := [("fetch",cid 7),("argument",cid 900),("written",cid 42)]
      let callerValues : Captures := [(cid 900,q),(cid 42,r),(cid 7,.sourceClosure source owner names (captured c))]
      have first : Child caller callerNames callerValues [w 23] callee
          (.sourceClosure source owner names (captured c)) [w 23,.unit] :=
        .fetch fetch .head (.tail (by decide) (.tail (by decide) .head))
      have second : Child caller callerNames callerValues [w 23,.unit] argument q [r,.unit] :=
        .argument arg (.tail (by decide) .head) .head (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) .head)
      have actual : SourceLambdaEvaluates Child Body caller callerNames callerValues [w 23] callSource (if result.1 then .unit else r) (finalStore r) := by
        rw [callShapeEq]; exact .call saved first second (by simpa only [parameter,fresh0,ns0,es0] using result.2.down)
      have literal : SourceLambdaEvaluates Child Body caller callerNames callerValues [w 23]
          ⟨callSpan,.call callee ⟨argumentsSpan,[argument]⟩⟩ (if result.1 then .unit else r) (finalStore r) := by
        simpa only [callShapeEq] using actual
      have exposed := SourceLambdaEvaluates.call_iff.mp literal
      have _ := (SourceLambdaEvaluates.call_iff (span:=callSpan) (argumentsSpan:=argumentsSpan)).mpr exposed
      check (decide (owner≠caller ∧ Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 ∧
        Resolved.freshLocalId owner (ns0.map Prod.snd)=sid 33 ∧ Resolved.freshLocalId owner (ns1.map Prod.snd)=sid 34)) "saved-owner names-only freshness"
      check (decide ((es2 q r c).map Prod.fst=[sid 34,sid 33,sid 32,sid 32,sid 31,sid 7,sid 31,sid 3,foreign])) "all old and colliding captures retained"
      have _ : Resolved.LocalScope.Lookup (es2 q r c) (sid 34) r := .head
      have _ : Resolved.LocalScope.Lookup (es2 q r c) (sid 33) q := .tail (by decide) .head
      have _ : Resolved.LocalScope.Lookup (es2 q r c) (sid 32) q := .tail (by decide) (.tail (by decide) .head)
      check ((finalStore r).map RuntimeValue.toCore? == [r.toCore?,some .unit,some (.bool true),some (.word (word 7))]) "distinct argument/discard/scrutinee effects"
      if exactReturn : result.1=bare then
        have _ : SourceLambdaEvaluates Child Body caller callerNames callerValues [w 23] callSource
            (if bare then .unit else r) (finalStore r) := by simpa only [exactReturn] using actual
        pure ()
      else throw (IO.userError "wrong original selected return")
    else throw (IO.userError "original parameter/callee/argument callback shapes")
  | _,_ => throw (IO.userError "independent original lambda/call shape")
private theorem no_literal_choice {r : RuntimeValue} (nonword : ∀ v, r ≠ .word v)
    {first : Syntax.MatchCase} {rest : List Syntax.MatchCase} {d : Option Syntax.Block}
    (meaning : WordMatchPatternClassifies first.value.pattern (some (word 0))) :
    ∀ b n, ¬ RuntimeWordMatchChooses r (first::rest) d b n := by
  intro b n chosen
  cases chosen with
  | wildcard other => cases meaning.tag_unique other
  | hit => exact nonword _ rfl
  | miss => exact nonword _ rfl
private def literalBoundary (source : Syntax.Expr) (q r : RuntimeValue) (nonword : ∀ v, r ≠ .word v) : IO Unit := do
  match source.value with
  | .lambda _ _ _ ⟨_,[_,_,_,⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[first,duplicate,wildcard],none⟩⟩⟩]⟩ =>
    let p ← pattern first.value.pattern; let d ← pattern duplicate.value.pattern; let wild ← pattern wildcard.value.pattern
    if tags : p.1=some (word 0) ∧ d.1=some (word 0) ∧ wild.1=none then
      have pm := tags.1 ▸ p.2.down; have dm := tags.2.1 ▸ d.2.down; have wm := tags.2.2 ▸ wild.2.down
      have firstHit : RuntimeWordMatchChooses (w 0) [first,duplicate,wildcard] none first.value.body 1 := .hit pm
      have misses : RuntimeWordMatchChooses (w 1) [first,duplicate,wildcard] none wildcard.value.body 2 :=
        .miss pm (by decide) (.miss dm (by decide) (.wildcard wm))
      let a ← choice (w 0) [first,duplicate,wildcard] none
      let b ← choice (w 1) [first,duplicate,wildcard] none
      have _ := a.2.2.down.deterministic firstHit
      have _ := b.2.2.down.deterministic misses
      have oldHit : WordMatchChooses (.word (word 0)) [first,duplicate,wildcard] none first.value.body 1 := .hit pm
      have _ := runtimeWordMatchChooses_ofCore_iff.mpr oldHit
      have _ : WordMatchChooses (.word (word 1)) [first,duplicate,wildcard] none wildcard.value.body 2 :=
        runtimeWordMatchChooses_ofCore_iff.mp (by simpa only [RuntimeValue.ofCore,w] using misses)
      have _ : ∀ selected tests, ¬ RuntimeWordMatchChooses r [first,duplicate,wildcard] none selected tests :=
        no_literal_choice nonword pm
      if observed : callShape scrutinee "observe" ["x"]=true then
        have _ : Child owner ns2 (es2 q r true) [r,.unit,.bool true] scrutinee r (finalStore r) :=
          .observe observed .head .head
        check (a.1 == first.value.body && a.2.1==1 && b.1 == wildcard.value.body && b.2.1==2)
          "independent original first hit/miss counts; non-Word choice absent, not a fault-store claim"
      else throw (IO.userError "original literal-first scrutinee")
    else throw (IO.userError "independent 0/0x00/grouped-wildcard meanings")
  | _ => throw (IO.userError "original literal-first lambda body")
end ParsedSourceComputationBodyEffects

open ParsedSourceComputationBodyEffects in
/-- Bounded original callback/body witnesses, not a recursively closed evaluator or safety claim. -/
def frontendParsedSourceComputationBodyEffectTests : IO Unit := do
  let conditional ← parsed "lam(x:Unknown)->Unknown{let x:Missing=x;let x=load(r);touch();if(c){{match(observe(x)){case ((_)){return x;}case Missing{return absent;}}}}else{match(observe(x)){default{return x;}}}}"
  let literals ← parsed "lam(x:Unknown)->Unknown{let x:Missing=x;let x=load(r);touch();match(observe(x)){case 0{return x;}case 0x00{return absent;}case ((_)){return x;}}}"
  let bare ← parsed "lam(x:Unknown)->Unknown{let x:Missing=x;let x=load(r);touch();match(observe(x)){default{return;}}}"
  let callSource ← parsed "fetch()(argument())"
  let payload ← parsed "lam(){return absent;}"
  let q := Solcore.Frontend.RuntimeValue.sourceClosure payload caller [] [(sid 99,.bool false)]
  let r := Solcore.Frontend.RuntimeValue.sourceClosure payload owner [("saved",sid 7)] [(sid 7,w 41)]
  for actual in [r,.coreClosure .bool .unit (.var 99) [r,.cellRef .word 700]] do
    for c in [true,false] do inspect conditional callSource q actual c
    inspect bare callSource q actual true true
  inspect literals callSource q (w 0) true
  inspect literals callSource q (w 1) false
  literalBoundary literals q r (by intro value; dsimp only [r]; intro impossible; cases impossible)
  literalBoundary literals q (.coreClosure .bool .unit (.var 99) [r,.cellRef .word 700])
    (by intro value impossible; cases impossible)

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendScopedShadowingProperties
/-! Arbitrary repeated spellings retain old initializer scope and exact rows.
These symbolic spans are original fields, not a claim of parser validity. -/

set_option autoImplicit false
namespace Tests.FrontendScopedShadowing
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Shadowing", by decide⟩], by decide⟩⟩, 73⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 74}, 900⟩
private def inputs (a b : Core.Ty) : LocalTypeInputs := ⟨
  [⟨"x", id 7, a⟩, ⟨"next", id 2, b⟩, ⟨"x", foreign, .bool⟩],
  by change [id 7, id 2, foreign].Nodup; decide⟩
private def ref (span : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (span : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Payload"], .unit)]
private def statements (span : Syntax.SourceSpan) (annotated : Bool) : List String → String → List Syntax.Statement
  | [], previous => [⟨span, .returnStmt (some (ref span previous))⟩]
  | name :: rest, previous =>
      ⟨span, .letDecl ⟨span, name⟩ (if annotated then some (annotation span) else none)
        (some (ref span previous))⟩ :: statements span annotated rest name
private def core : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (core count)

private theorem elaboration (span : Syntax.SourceSpan) (annotated : Bool) (names : List String)
    (previous : String) (type : Core.Ty) (initial : LocalTypeInputs)
    (child : RecursiveLocalComputationElaborates initial.names initial.context (ref span previous) (.var 0) type) :
    RecursiveComputationReturnTreeElaborates (types type) owner initial
      ⟨span, statements span annotated names previous⟩ (core names.length) type := by
  induction names generalizing previous initial with
  | nil => exact .expression child
  | cons name rest ih =>
      have tail := ih name (initial.bindFresh owner name type)
        (.pure (.identifier .head) (.var .head) (.var .head))
      cases annotated with
      | false => exact .inferred child tail
      | true => exact .binding (.named .head) child tail

theorem arbitrary_repeated_names_have_independent_exact_typing
    (span : Syntax.SourceSpan) (annotated : Bool) (names : List String) (type other : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types type) owner (inputs type other)
      ⟨span, statements span annotated names "x"⟩ (core names.length) type ∧
    RecursiveComputationReturnTreeHasType (types type) owner (inputs type other)
      ⟨span, statements span annotated names "x"⟩ type ∧
    elaborateRecursiveComputationReturnTree? (types type) owner (inputs type other)
      ⟨span, statements span annotated names "x"⟩ = some (core names.length, type) ∧
    Core.HasType [type, other, .bool] (core names.length) type := by
  have exact := elaboration span annotated names "x" type (inputs type other)
    (.pure (.identifier .head) (.var .head) (.var .head))
  exact ⟨exact, (computationReturnTreeHasType_iff_elaborates
    recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_, exact⟩,
    (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr exact,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType exact⟩

private theorem raw (span : Syntax.SourceSpan) (annotated : Bool) (names : List String)
    (previous : String) (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (value : Core.Value)
    (child : RecursiveLocalComputationEvaluatesWithCost table environment store (ref span previous) value store 1) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner table environment store
      ⟨span, statements span annotated names previous⟩ value store (3 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .expression child
  | cons name rest ih =>
      let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      have tail := ih name ((name, fresh) :: table) ((fresh, value) :: environment)
        (.pure (.identifier .head .head))
      have count : 3 * (name :: rest).length + 1 = 1 + (3 * rest.length + 1) + 2 := by
        simp only [List.length_cons]; omega
      rw [count]
      cases annotated with
      | false => exact .inferred child tail
      | true => exact .binding child tail

private theorem path (count : Nat) (value : Core.Value) (retained : Core.Environment)
    (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps (3 * count + 1) ⟨.eval (core count) (value :: retained), continuation, store⟩
      ⟨.ret value, continuation, store⟩ := by
  induction count generalizing retained continuation with
  | zero => exact .cons (.var rfl) .refl
  | succ count ih =>
      have costs : 3 * (count + 1) + 1 = 1 + (3 * count + 1) + 2 := by omega
      rw [costs]
      exact CostStepComposition.letE (.cons (.var rfl) .refl) (ih (value :: retained) continuation)

theorem arbitrary_repeated_names_preserve_actual_values_stores_and_exact_cost
    (span : Syntax.SourceSpan) (annotated : Bool) (names : List String)
    (value next captured : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs .word .word).names
      [(id 7, value), (id 2, next), (foreign, captured)] store
      ⟨span, statements span annotated names "x"⟩ value store (3 * names.length + 1) ∧
    Core.Steps (3 * names.length + 1)
      ⟨.eval (core names.length) [value, next, captured], continuation, store⟩
      ⟨.ret value, continuation, store⟩ :=
  ⟨raw span annotated names "x" _ _ store value (.pure (.identifier .head .head)),
    path names.length value [next, captured] store continuation⟩

private theorem changedType (span : Syntax.SourceSpan) (annotated : Bool) (old next : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types next) owner (inputs old next)
      ⟨span, statements span annotated ["x"] "next"⟩ (.letE (.var 1) (.var 0)) next := by
  have child : RecursiveLocalComputationElaborates (inputs old next).names (inputs old next).context
      (ref span "next") (.var 1) next :=
    .pure (.identifier (.tail (by change "x" ≠ "next"; decide) .head))
      (.var (.tail (by change id 7 ≠ id 2; decide) .head))
      (.var (.tail (by change id 7 ≠ id 2; decide) .head))
  have tail : RecursiveComputationReturnTreeElaborates (types next) owner
      ((inputs old next).bindFresh owner "x" next) ⟨span, statements span annotated [] "x"⟩ (.var 0) next :=
    .expression (.pure (.identifier .head) (.var .head) (.var .head))
  cases annotated with
  | false => exact .inferred child tail
  | true => exact .binding (.named .head) child tail

theorem a_new_type_shadows_the_name_without_overwriting_old_rows
    (span : Syntax.SourceSpan) (annotated : Bool) (old next : Core.Ty) :
    elaborateRecursiveComputationReturnTree? (types next) owner (inputs old next)
      ⟨span, statements span annotated ["x"] "next"⟩ = some (.letE (.var 1) (.var 0), next) ∧
    ((inputs old next).bindFresh owner "x" next).names =
      [("x", id 8), ("x", id 7), ("next", id 2), ("x", foreign)] ∧
    ((inputs old next).bindFresh owner "x" next).context =
      [(id 8, next), (id 7, old), (id 2, next), (foreign, .bool)] :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr
    (changedType span annotated old next), rfl, rfl⟩

theorem original_initializer_and_shadowed_tail_select_different_rows
    (span : Syntax.SourceSpan) (old next : Core.Ty) :
    elaborateRecursiveLocalComputation? (inputs old next).names (inputs old next).context
      (ref span "x") = some (.var 0, old) ∧
    elaborateRecursiveLocalComputation? ((inputs old next).bindFresh owner "x" next).names
      ((inputs old next).bindFresh owner "x" next).context (ref span "x") = some (.var 0, next) ∧
    (inputs old next).names.lookup? "x" = some (id 7) ∧
    ((inputs old next).bindFresh owner "x" next).names.lookup? "x" = some (id 8) ∧
    ((inputs old next).bindFresh owner "x" next).context.lookup? (id 7) = some old ∧
    Resolved.freshLocalId owner (inputs old next).ids = id 8 ∧
    ((inputs old next).bindFresh owner "x" next).context.values = [next, old, next, .bool] :=
  ⟨elaborateRecursiveLocalComputation?_iff.mpr (.pure (.identifier .head) (.var .head) (.var .head)),
    elaborateRecursiveLocalComputation?_iff.mpr (.pure (.identifier .head) (.var .head) (.var .head)),
    rfl, rfl, rfl, rfl, rfl⟩

end Tests.FrontendScopedShadowing
end

section
-- leanmerge: from Solcore.Test.FrontendSourceComputationBodyBoundaryProperties
/-! A real source-lambda callback can discard a non-Core intermediate value.
These independent boundary witnesses do not define a closed expression evaluator. -/

set_option autoImplicit false

open Solcore

namespace Tests.MixedBodyBoundaries

private def NoOld : Frontend.LocalNameTable → Resolved.Environment → Core.Store →
    Syntax.Expr → Core.Value → Core.Store → Prop := fun _ _ _ _ _ _ => False

private def NoChild : Resolved.DeclarationId → List (String × Resolved.LocalId) →
    List (Resolved.LocalId × Frontend.RuntimeValue) → List Frontend.RuntimeValue →
    Syntax.Expr → Frontend.RuntimeValue → List Frontend.RuntimeValue → Prop :=
  fun _ _ _ _ _ _ _ => False

private def NoBody : Resolved.DeclarationId → List (String × Resolved.LocalId) →
    List (Resolved.LocalId × Frontend.RuntimeValue) → List Frontend.RuntimeValue →
    Syntax.Block → Frontend.RuntimeValue → List Frontend.RuntimeValue → Prop :=
  fun _ _ _ _ _ _ _ => False

private abbrev LambdaChild := Frontend.SourceLambdaEvaluates NoChild NoBody

/-- This is the existing raw lambda judgment, with genuinely empty callbacks. -/
theorem actual_lambda_child_is_deterministic
    {owner names captured store source left leftStore right rightStore}
    (first : LambdaChild owner names captured store source left leftStore)
    (second : LambdaChild owner names captured store source right rightStore) :
    left = right ∧ leftStore = rightStore :=
  Frontend.SourceLambdaEvaluates.deterministic
    (ChildEval := NoChild) (BodyEval := NoBody)
    (fun impossible _ => False.elim impossible)
    (fun impossible _ => False.elim impossible) first second

/-- Agreement checked only at old-image outputs misses every source creation. -/
theorem lambda_child_agrees_with_empty_old_child_on_embedded_outputs
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store finalStore : Core.Store)
    (source : Syntax.Expr) (value : Core.Value) :
    LambdaChild owner names
      (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
      (store.map Frontend.RuntimeValue.ofCore) source
      (Frontend.RuntimeValue.ofCore value) (finalStore.map Frontend.RuntimeValue.ofCore) ↔
      NoOld names captured store source value finalStore := by
  constructor
  · intro evaluated
    generalize embedded : Frontend.RuntimeValue.ofCore value = mixed at evaluated
    generalize finalImage : finalStore.map Frontend.RuntimeValue.ofCore = actualFinal at evaluated
    cases evaluated with
    | creation shape =>
        have projected := Frontend.RuntimeValue.toCore?_ofCore value
        rw [embedded] at projected
        simp only [Frontend.RuntimeValue.toCore?, reduceCtorEq] at projected
    | call shape callee argument body => exact False.elim callee
  · exact False.elim

/-- Creation really occurs from arbitrary old inputs, outside every old value image. -/
theorem actual_source_creation_has_no_old_result_preimage
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store : Core.Store)
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : Frontend.SourceUnaryLambdaShape source name body) :
    ∃ mixed,
      LambdaChild owner names
        (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
        (store.map Frontend.RuntimeValue.ofCore) source mixed
        (store.map Frontend.RuntimeValue.ofCore) ∧
      ∀ old : Core.Value, mixed ≠ Frontend.RuntimeValue.ofCore old := by
  refine ⟨_, .creation shape, ?_⟩
  intro old equality
  have projected := Frontend.RuntimeValue.toCore?_ofCore old
  rw [← equality] at projected
  simp only [Frontend.RuntimeValue.toCore?, reduceCtorEq] at projected

/-- The old relation cannot discard an expression without its old child evidence. -/
theorem empty_old_child_prevents_discard_then_bare
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store finalStore : Core.Store)
    (blockSpan statementSpan returnSpan : Syntax.SourceSpan)
    (source : Syntax.Expr) (value : Core.Value) :
    ¬ Frontend.ComputationReturnTreeEvaluates NoOld owner names captured store
      ⟨blockSpan, [⟨statementSpan, .expression source true⟩, ⟨returnSpan, .returnStmt none⟩]⟩
      value finalStore := by
  intro evaluated
  cases evaluated with
  | discard child tail => exact False.elim child

/-- Discard hides a genuine newly created closure, leaving literal old-image endpoints. -/
theorem discarding_actual_source_creation_returns_embedded_unit
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store : Core.Store)
    (blockSpan statementSpan returnSpan : Syntax.SourceSpan)
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    (shape : Frontend.SourceUnaryLambdaShape source name body) :
    Frontend.SourceComputationBodyEvaluates LambdaChild owner names
      (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
      (store.map Frontend.RuntimeValue.ofCore)
      ⟨blockSpan, [⟨statementSpan, .expression source true⟩, ⟨returnSpan, .returnStmt none⟩]⟩
      (Frontend.RuntimeValue.ofCore .unit) (store.map Frontend.RuntimeValue.ofCore) := by
  simpa only [Frontend.RuntimeValue.ofCore] using
    (Frontend.SourceComputationBodyEvaluates.discard
      (Frontend.SourceLambdaEvaluates.creation shape) Frontend.SourceComputationBodyEvaluates.bare)

/-- A uniform exact body image law exposes the strong child condition through return. -/
theorem uniform_actual_body_image_exactness_forces_child_image_exactness
    {OldChild : Frontend.LocalNameTable → Resolved.Environment → Core.Store →
      Syntax.Expr → Core.Value → Core.Store → Prop}
    {MixedChild : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × Frontend.RuntimeValue) → List Frontend.RuntimeValue →
      Syntax.Expr → Frontend.RuntimeValue → List Frontend.RuntimeValue → Prop}
    (owner : Resolved.DeclarationId) (names : Frontend.LocalNameTable)
    (captured : Resolved.Environment) (store : Core.Store)
    (span : Syntax.SourceSpan)
    (bodyExact : ∀ body value finalStore,
      Frontend.SourceComputationBodyEvaluates MixedChild owner names
        (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
        (store.map Frontend.RuntimeValue.ofCore) body value finalStore ↔
      ∃ oldValue oldStore, value = Frontend.RuntimeValue.ofCore oldValue ∧
        finalStore = oldStore.map Frontend.RuntimeValue.ofCore ∧
        Frontend.ComputationReturnTreeEvaluates OldChild owner names captured store
          body oldValue oldStore)
    (source : Syntax.Expr) (value : Frontend.RuntimeValue)
    (finalStore : List Frontend.RuntimeValue) :
    MixedChild owner names
      (captured.map fun row => (row.1, Frontend.RuntimeValue.ofCore row.2))
      (store.map Frontend.RuntimeValue.ofCore) source value finalStore ↔
      ∃ oldValue oldStore, value = Frontend.RuntimeValue.ofCore oldValue ∧
        finalStore = oldStore.map Frontend.RuntimeValue.ofCore ∧
        OldChild names captured store source oldValue oldStore := by
  constructor
  · intro child
    obtain ⟨oldValue, oldStore, resultImage, storeImage, oldBody⟩ :=
      (bodyExact ⟨span, [⟨span, .returnStmt (some source)⟩]⟩ value finalStore).mp
        (.expression child)
    cases oldBody with
    | expression oldChild => exact ⟨oldValue, oldStore, resultImage, storeImage, oldChild⟩
  · rintro ⟨oldValue, oldStore, resultImage, storeImage, oldChild⟩
    have mixedBody :=
      (bodyExact ⟨span, [⟨span, .returnStmt (some source)⟩]⟩ value finalStore).mpr
        ⟨oldValue, oldStore, resultImage, storeImage, .expression oldChild⟩
    cases mixedBody with
    | expression child => exact child

end Tests.MixedBodyBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendSourceComputationBodyImageProperties
/-! Independent old/mixed reference callbacks establish the strong all-actual
image contract by first-ID lookup inversion. They do not assume typed rows,
alignment, child determinism, or that actual outputs are already Core images. -/
set_option autoImplicit false
namespace Tests.FrontendSourceComputationBodyImage
open Solcore Solcore.Frontend

private def embedded (environment : Resolved.LocalScope Core.Value) :
    Resolved.LocalScope RuntimeValue :=
  environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))

private inductive OldRef (names : LocalNameTable) (environment : Resolved.LocalScope Core.Value) :
    List Core.Value → Syntax.Expr → Core.Value → List Core.Value → Prop where
  | reference {store : List Core.Value} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : Core.Value}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      OldRef names environment store ⟨span,.identifier name⟩ value store

private inductive ImageRef (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | reference {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : RuntimeValue}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      ImageRef owner names environment store ⟨span,.identifier name⟩ value store

private theorem mapped_lookup_forward {environment : Resolved.LocalScope Core.Value}
    {id : Resolved.LocalId} {value : Core.Value}
    (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (embedded environment) id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem mapped_lookup_reflection (environment : Resolved.LocalScope Core.Value)
    {id : Resolved.LocalId} {actual : RuntimeValue}
    (found : Resolved.LocalScope.Lookup (embedded environment) id actual) :
    ∃ value, actual=RuntimeValue.ofCore value ∧ Resolved.LocalScope.Lookup environment id value := by
  induction environment with
  | nil => cases found
  | cons entry rest ih =>
      rcases entry with ⟨candidate,headValue⟩
      cases found with
      | head => exact ⟨headValue,rfl,.head⟩
      | tail different tail =>
          obtain ⟨value,equality,old⟩ := ih tail
          exact ⟨value,equality,.tail different old⟩

private theorem child_forward (owner : Resolved.DeclarationId)
    {names : LocalNameTable} {environment : Resolved.LocalScope Core.Value}
    {store final : List Core.Value} {source : Syntax.Expr} {value : Core.Value}
    (evaluated : OldRef names environment store source value final) :
    ImageRef owner names (embedded environment) (store.map RuntimeValue.ofCore)
      source (RuntimeValue.ofCore value) (final.map RuntimeValue.ofCore) := by
  cases evaluated with
  | reference named found => exact .reference named (mapped_lookup_forward found)

/- The result and final store below are arbitrary mixed data, not assumed images.
Their literal image equalities are obtained by inversion, with no determinism premise. -/
private theorem all_actual_outputs_image_contract (owner : Resolved.DeclarationId)
    {names : LocalNameTable} {environment : Resolved.LocalScope Core.Value}
    {store : List Core.Value} {source : Syntax.Expr}
    {actual : RuntimeValue} {actualFinal : List RuntimeValue} :
    ImageRef owner names (embedded environment) (store.map RuntimeValue.ofCore)
      source actual actualFinal ↔
      ∃ value final, actual=RuntimeValue.ofCore value ∧ actualFinal=final.map RuntimeValue.ofCore ∧
        OldRef names environment store source value final := by
  constructor
  · intro evaluated
    cases evaluated with
    | reference named found =>
        obtain ⟨value,equality,old⟩ := mapped_lookup_reflection environment found
        exact ⟨value,store,equality,rfl,.reference named old⟩
  · rintro ⟨value,final,rfl,rfl,old⟩
    exact child_forward owner old

private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def spine (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) : Nat → Syntax.Block
  | 0 => ⟨span,[⟨span,.returnStmt (some (ref span name))⟩]⟩
  | n+1 => ⟨span,[⟨name.span,.letDecl name (some annotation) (some (ref span name))⟩,
      ⟨name.span,.letDecl name none (some (ref span name))⟩,
      ⟨span,.expression (ref span name) true⟩,
      ⟨span,.block (spine span name annotation n).value⟩]⟩
private theorem oldPath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (environment : Resolved.LocalScope Core.Value)
    (store : List Core.Value) (id : Resolved.LocalId) (value : Core.Value)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    ComputationReturnTreeEvaluates OldRef o names environment store
      (spine span name annotation n) value store := by
  induction n generalizing names environment id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      apply ComputationReturnTreeEvaluates.binding (.reference named found)
      apply ComputationReturnTreeEvaluates.inferred (.reference .head .head)
      apply ComputationReturnTreeEvaluates.discard (.reference .head .head)
      cases n <;> exact .block (ih _ _ _ .head .head)
private theorem mixedPath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates ImageRef o names environment store
      (spine span name annotation n) value store := by
  induction n generalizing names environment id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      apply SourceComputationBodyEvaluates.binding (.reference named found)
      apply SourceComputationBodyEvaluates.inferred (.reference .head .head)
      apply SourceComputationBodyEvaluates.discard (.reference .head .head)
      cases n <;> exact .block (ih _ _ _ .head .head)

theorem original_and_mixed_shadow_paths_are_independent
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (tail : Resolved.LocalScope Core.Value) (store : List Core.Value)
    (id : Resolved.LocalId) (value ignored : Core.Value) :
    let names' := (name.value,id)::names
    let environment := (id,value)::(id,ignored)::tail
    ComputationReturnTreeEvaluates OldRef o names' environment store
      (spine span name annotation n) value store ∧
    SourceComputationBodyEvaluates ImageRef o names' (embedded environment)
      (store.map RuntimeValue.ofCore) (spine span name annotation n)
      (RuntimeValue.ofCore value) (store.map RuntimeValue.ofCore) :=
  ⟨oldPath _ _ _ _ _ _ _ _ _ _ .head .head,
    mixedPath _ _ _ _ _ _ _ _ _ _ .head .head⟩

/- Unlike an endpoint-only agreement, this law recovers both images from arbitrary
actual outputs. The independently proved callback contract has no such premises. -/
theorem all_actual_body_outputs_factor_through_the_original_relation
    (o : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope Core.Value) (store : List Core.Value)
    (body : Syntax.Block) (actual : RuntimeValue) (actualFinal : List RuntimeValue) :
    SourceComputationBodyEvaluates ImageRef o names (embedded environment)
      (store.map RuntimeValue.ofCore) body actual actualFinal ↔
    ∃ value final, actual=RuntimeValue.ofCore value ∧ actualFinal=final.map RuntimeValue.ofCore ∧
      ComputationReturnTreeEvaluates OldRef o names environment store body value final :=
  sourceComputationBodyEvaluates_ofCore_inputs_iff (all_actual_outputs_image_contract o)

theorem each_literal_old_endpoint_has_exactly_its_original_derivations
    (o : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope Core.Value) (store final : List Core.Value)
    (body : Syntax.Block) (value : Core.Value) :
    SourceComputationBodyEvaluates ImageRef o names (embedded environment)
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore value)
      (final.map RuntimeValue.ofCore) ↔
    ComputationReturnTreeEvaluates OldRef o names environment store body value final := by
  constructor
  · intro evaluated
    obtain ⟨oldValue,oldFinal,sameValue,sameFinal,old⟩ :=
      (all_actual_body_outputs_factor_through_the_original_relation o names environment store body _ _).mp evaluated
    have same := RuntimeValue.ofCore_injective sameValue
    subst oldValue
    have sameStores : final=oldFinal :=
      (List.map_inj_right (fun _ _ equal => RuntimeValue.ofCore_injective equal)).mp sameFinal
    subst oldFinal
    exact old
  · intro old
    exact (all_actual_body_outputs_factor_through_the_original_relation o names environment store body _ _).mpr
      ⟨value,final,rfl,rfl,old⟩

/- An opt-in extension may create source closures. Only the one-way body law is
applied to this callback; we do not assert the strong image contract for it. -/
private def Extended (o : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (source : Syntax.Expr) (value : RuntimeValue) (final : List RuntimeValue) : Prop :=
  ImageRef o names environment store source value final ∨
    SourceLambdaEvaluates (fun _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ => False)
      o names environment store source value final

theorem source_creating_extension_preserves_every_old_body_derivation
    {o : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.LocalScope Core.Value} {store final : List Core.Value}
    {body : Syntax.Block} {value : Core.Value}
    (old : ComputationReturnTreeEvaluates OldRef o names environment store body value final) :
    SourceComputationBodyEvaluates Extended o names (embedded environment)
      (store.map RuntimeValue.ofCore) body (RuntimeValue.ofCore value) (final.map RuntimeValue.ofCore) :=
  SourceComputationBodyEvaluates.ofCore (fun child => Or.inl (child_forward o child)) old

theorem extension_also_returns_new_source_closures_without_projecting_them
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (names : LocalNameTable)
    (environment : Resolved.LocalScope Core.Value) (store : List Core.Value)
    (source : Syntax.Expr) (name : Syntax.Identifier) (body : Syntax.Block)
    (shape : SourceUnaryLambdaShape source name body) :
    let closure := RuntimeValue.sourceClosure source o names (embedded environment)
    SourceComputationBodyEvaluates Extended o names (embedded environment)
      (store.map RuntimeValue.ofCore) ⟨span,[⟨span,.returnStmt (some source)⟩]⟩
      closure (store.map RuntimeValue.ofCore) ∧ closure.toCore?=none :=
  ⟨.expression (Or.inr (.creation shape)),by simp only [RuntimeValue.toCore?]⟩

end Tests.FrontendSourceComputationBodyImage
end

section
-- leanmerge: from Solcore.Test.FrontendSourceComputationBodyProperties
/-! Independent reference callbacks exercise all nine successful original body
rules. Mixed captures and stores are unrestricted data; no closed interpreter,
static acceptance, cost, typing or Core projection is asserted. -/
set_option autoImplicit false
namespace Tests.FrontendSourceComputationBody
open Solcore Solcore.Frontend

private inductive Ref (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | reference {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : RuntimeValue}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      Ref owner names environment store ⟨span,.identifier name⟩ value store
private theorem refDet {o names environment store source value final other otherStore}
    (first : Ref o names environment store source value final)
    (second : Ref o names environment store source other otherStore) :
    value=other ∧ final=otherStore := by
  cases first with
  | reference named found =>
      cases second with
      | reference otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound,rfl⟩
private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def returned (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨span,[⟨span,.returnStmt (some (ref span name))⟩]⟩
private def spine (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) : Nat → Syntax.Block
  | 0 => returned span name
  | n+1 => ⟨span,[⟨name.span,.letDecl name (some annotation) (some (ref span name))⟩,
      ⟨name.span,.letDecl name none (some (ref span name))⟩,
      ⟨span,.expression (ref span name) true⟩,
      ⟨span,.block (spine span name annotation n).value⟩]⟩
private theorem spinePath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      (spine span name annotation n) value store := by
  induction n generalizing names environment id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      apply SourceComputationBodyEvaluates.binding (.reference named found)
      apply SourceComputationBodyEvaluates.inferred (.reference .head .head)
      apply SourceComputationBodyEvaluates.discard (.reference .head .head)
      cases n <;> exact .block (ih _ _ _ .head .head)

private def wrap : List Syntax.SourceSpan → Syntax.Pattern → Syntax.Pattern
  | [],pattern => pattern
  | outer::rest,pattern => ⟨outer,.group (wrap rest pattern)⟩
private theorem wrapped {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (meaning : WordMatchPatternClassifies pattern tag) (groups : List Syntax.SourceSpan) :
    WordMatchPatternClassifies (wrap groups pattern) tag := by
  induction groups with | nil => exact meaning | cons _ _ ih => exact .group ih
private def zeroCase (span : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨span,⟨wrap groups ⟨span,.literal ⟨span,.decimal "0"⟩⟩,body⟩⟩
private def wildCase (span marker : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (body : Syntax.Block) : Syntax.MatchCase := ⟨span,⟨wrap groups ⟨span,.wildcard marker⟩,body⟩⟩
private theorem zeroMeaning (span : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (body : Syntax.Block) :
    WordMatchPatternClassifies (zeroCase span groups body).value.pattern (some .zero) :=
  wrapped (.literal ⟨⟨span,.decimal "0"⟩,rfl,
    .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩) groups
private def misses (span : Syntax.SourceSpan) (groups : Nat → List Syntax.SourceSpan)
    (unused : Syntax.Block) : Nat → List Syntax.MatchCase → List Syntax.MatchCase
  | 0,tail => tail
  | n+1,tail => zeroCase span (groups n) unused :: misses span groups unused n tail
private def one : Core.Word := ⟨1,by decide⟩
private theorem prefixChoice (span marker : Syntax.SourceSpan)
    (groups : Nat → List Syntax.SourceSpan) (wildGroups : List Syntax.SourceSpan)
    (unused selected : Syntax.Block) (suffix : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) (n : Nat) :
    RuntimeWordMatchChooses (.word one)
      (misses span groups unused n (wildCase span marker wildGroups selected :: suffix))
      defaultBody selected n := by
  induction n with
  | zero => exact .wildcard (wrapped (.wildcard rfl) wildGroups)
  | succ n ih => exact .miss (zeroMeaning _ _ _) (by decide) ih
private def matched (span : Syntax.SourceSpan) (scrutinee : Syntax.Expr)
    (cases : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨scrutinee,[]⟩⟩ ⟨span,⟨cases,defaultBody⟩⟩⟩]⟩

theorem arbitrary_shadow_depth_preserves_actual_mixed_payload
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      (spine span name annotation n) value store := spinePath o span name annotation n _ _ _ _ _ named found

theorem actual_body_result_and_store_are_unique
    {o names environment store body value final other otherStore}
    (first : SourceComputationBodyEvaluates Ref o names environment store body value final)
    (second : SourceComputationBodyEvaluates Ref o names environment store body other otherStore) :
    value=other ∧ final=otherStore := SourceComputationBodyEvaluates.deterministic refDet first second

theorem strict_discard_then_bare_return_keeps_arbitrary_raw_store
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id actual) :
    SourceComputationBodyEvaluates Ref o names environment store
      ⟨span,[⟨span,.expression (ref span name) true⟩,⟨span,.returnStmt none⟩]⟩ .unit store :=
  .discard (.reference named found) .bare

theorem actual_bool_selects_only_its_original_branch
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (condition name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (side : Bool) (unused : Syntax.Block)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (conditionId id : Resolved.LocalId) (value : RuntimeValue)
    (conditionNamed : LocalNameTable.Lookup names condition.value conditionId)
    (conditionFound : Resolved.LocalScope.Lookup environment conditionId (.bool side))
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      ⟨span,[⟨span,.ifThen (ref span condition)
        (if side then spine span name annotation n else unused)
        (some (if side then unused else spine span name annotation n))⟩]⟩ value store := by
  cases side
  · exact .ifFalse (.reference conditionNamed conditionFound) (spinePath _ _ _ _ _ _ _ _ _ _ named found)
  · exact .ifTrue (.reference conditionNamed conditionFound) (spinePath _ _ _ _ _ _ _ _ _ _ named found)

theorem first_literal_hit_ignores_arbitrary_original_suffix
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (scrutinee name : Syntax.Identifier) (suffix : List Syntax.MatchCase) (defaultBody : Option Syntax.Block)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (scrutineeId id : Resolved.LocalId) (value : RuntimeValue)
    (scrutineeNamed : LocalNameTable.Lookup names scrutinee.value scrutineeId)
    (scrutineeFound : Resolved.LocalScope.Lookup environment scrutineeId (.word .zero))
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup environment id value) :
    RuntimeWordMatchChooses (.word .zero) (zeroCase span groups (returned span name)::suffix)
      defaultBody (returned span name) 1 ∧
    WordMatchChooses (.word .zero) (zeroCase span groups (returned span name)::suffix)
      defaultBody (returned span name) 1 ∧
    SourceComputationBodyEvaluates Ref o names environment store
      (matched span (ref span scrutinee) (zeroCase span groups (returned span name)::suffix) defaultBody) value store := by
  have choice : RuntimeWordMatchChooses (.word .zero)
      (zeroCase span groups (returned span name)::suffix) defaultBody (returned span name) 1 :=
    .hit (zeroMeaning _ _ _)
  have original := runtimeWordMatchChooses_ofCore_iff.mp
    (show RuntimeWordMatchChooses (RuntimeValue.ofCore (.word .zero)) _ _ _ _ from
      by simpa only [RuntimeValue.ofCore] using choice)
  exact ⟨choice,original,.wordMatch (.reference scrutineeNamed scrutineeFound)
    choice (.expression (.reference named found))⟩

theorem arbitrary_literal_misses_then_grouped_wildcard
    (o : Resolved.DeclarationId) (span marker : Syntax.SourceSpan)
    (groups : Nat → List Syntax.SourceSpan) (wildGroups : List Syntax.SourceSpan)
    (scrutinee name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n depth : Nat)
    (unused : Syntax.Block) (suffix : List Syntax.MatchCase) (defaultBody : Option Syntax.Block)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (scrutineeId id : Resolved.LocalId) (value : RuntimeValue)
    (scrutineeNamed : LocalNameTable.Lookup names scrutinee.value scrutineeId)
    (scrutineeFound : Resolved.LocalScope.Lookup environment scrutineeId (.word one))
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup environment id value) :
    let selected := spine span name annotation depth
    let cases := misses span groups unused n (wildCase span marker wildGroups selected :: suffix)
    RuntimeWordMatchChooses (.word one) cases defaultBody selected n ∧
    SourceComputationBodyEvaluates Ref o names environment store
      (matched span (ref span scrutinee) cases defaultBody) value store :=
  ⟨prefixChoice _ _ _ _ _ _ _ _ _,.wordMatch (.reference scrutineeNamed scrutineeFound)
    (prefixChoice _ _ _ _ _ _ _ _ _) (spinePath _ _ _ _ _ _ _ _ _ _ named found)⟩

theorem default_only_accepts_every_actual_scrutinee
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (scrutinee name : Syntax.Identifier)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (scrutineeId id : Resolved.LocalId) (actual value : RuntimeValue)
    (scrutineeNamed : LocalNameTable.Lookup names scrutinee.value scrutineeId)
    (scrutineeFound : Resolved.LocalScope.Lookup environment scrutineeId actual)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      (matched span (ref span scrutinee) [] (some (returned span name))) value store :=
  .wordMatch (.reference scrutineeNamed scrutineeFound) .fallback (.expression (.reference named found))

theorem selected_original_block_and_count_are_jointly_unique
    {actual cases defaultBody selected other tests otherTests}
    (first : RuntimeWordMatchChooses actual cases defaultBody selected tests)
    (second : RuntimeWordMatchChooses actual cases defaultBody other otherTests) :
    selected=other ∧ tests=otherTests := first.deterministic second

theorem duplicate_capture_and_environment_only_fresh_collision_remain_literal
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (tail : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual ignored collision : RuntimeValue) :
    let rows := (id,actual)::(id,ignored)::
      (Resolved.freshLocalId o (((name.value,id)::names).map Prod.snd),collision)::tail
    SourceComputationBodyEvaluates Ref o ((name.value,id)::names) rows store
      (spine span name annotation n) actual store :=
  spinePath _ _ _ _ _ _ _ _ _ _ .head .head

theorem the_same_original_conditional_runs_with_both_actual_boolean_rows
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (annotation : Syntax.TypeExpr)
    (n : Nat) (side : Bool) (conditionId valueId : Resolved.LocalId) (different : conditionId≠valueId)
    (names : LocalNameTable) (tail : Resolved.LocalScope RuntimeValue)
    (actual : RuntimeValue) (store : List RuntimeValue) :
    SourceComputationBodyEvaluates Ref o (("c",conditionId)::("x",valueId)::names)
      ((conditionId,.bool side)::(valueId,actual)::tail) store
      ⟨span,[⟨span,.ifThen (ref span ⟨span,"c"⟩)
        (spine span ⟨span,"x"⟩ annotation n)
        (some (spine span ⟨span,"x"⟩ annotation (n+1)))⟩]⟩ actual store := by
  cases side
  · exact .ifFalse (.reference .head .head)
      (spinePath _ _ _ _ _ _ _ _ _ _ (.tail (by change "c" ≠ "x"; decide) .head) (.tail different .head))
  · exact .ifTrue (.reference .head .head)
      (spinePath _ _ _ _ _ _ _ _ _ _ (.tail (by change "c" ≠ "x"; decide) .head) (.tail different .head))

end Tests.FrontendSourceComputationBody
end
