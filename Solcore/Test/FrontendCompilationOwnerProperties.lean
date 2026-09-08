import Solcore.Frontend.RuntimeFunctionCompilationOwnerProperties
import Solcore.Frontend.LocalInputsTypeErasureRenamingProperties
import Solcore.Frontend.RuntimeParametersOwnerProperties

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
    declared id type, .terminal (elaborated id type conditional)⟩
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
    simp [elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?, elaborateReturnBody?,
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
