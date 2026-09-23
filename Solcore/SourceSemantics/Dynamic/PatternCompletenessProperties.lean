import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.SourceSemantics.Dynamic.Typing

/-!
Canonical-value and completeness properties for declarative source patterns.

These lemmas connect catalog-backed deep value typing to the prefix-program
pattern dynamics.  In particular, irrefutable patterns match every value of
their static input type, constructor coverage matches every value built by the
covered constructor, and a statically exhaustive match cannot select
`noBranch`.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

private def applicationHead : Ty → Ty
  | .application function _ => applicationHead function
  | type => type

private theorem applicationHead_applyMany (head : Ty) (arguments : List Ty) :
    applicationHead (Ty.applyMany head arguments) = applicationHead head := by
  unfold Ty.applyMany
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments induction =>
      simp only [List.foldl_cons]
      rw [induction]
      rfl

private theorem nominal_ne_of_head
    (declaration : Resolved.DeclarationId) (arguments : List Ty) (other : Ty)
    (different :
      Ty.constructor (.declaration declaration) ≠ applicationHead other) :
    Ty.nominal declaration arguments ≠ other := by
  intro equality
  have heads := congrArg applicationHead equality
  apply different
  simpa [Ty.nominal, applicationHead_applyMany, applicationHead] using heads

private def applicationArguments : Ty → List Ty
  | .application function argument => applicationArguments function ++ [argument]
  | _ => []

private theorem applicationArguments_applyMany (head : Ty)
    (arguments : List Ty) :
    applicationArguments (Ty.applyMany head arguments) =
      applicationArguments head ++ arguments := by
  unfold Ty.applyMany
  induction arguments generalizing head with
  | nil => simp
  | cons argument arguments induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp [applicationArguments, List.append_assoc]

private theorem nominal_injective
    {leftDeclaration rightDeclaration : Resolved.DeclarationId}
    {leftArguments rightArguments : List Ty}
    (equal : Ty.nominal leftDeclaration leftArguments =
      Ty.nominal rightDeclaration rightArguments) :
    leftDeclaration = rightDeclaration ∧ leftArguments = rightArguments := by
  constructor
  · have heads := congrArg applicationHead equal
    simpa [Ty.nominal, applicationHead_applyMany, applicationHead] using heads
  · have arguments := congrArg applicationArguments equal
    simpa [Ty.nominal, applicationArguments_applyMany, applicationArguments]
      using arguments

private theorem sublist_flatMap_of_mem
    {alpha beta : Type} (f : alpha → List beta)
    {value : alpha} {values : List alpha} (member : value ∈ values) :
    (f value).Sublist (values.flatMap f) := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact List.sublist_append_left _ _
      · exact (induction member).trans (List.sublist_append_right _ _)

private theorem foldlApplication_ne_comptime
    (head : Ty) (arguments : List Ty)
    (head_ne : ∀ inner, head ≠ .comptime inner) (inner : Ty) :
    arguments.foldl Ty.application head ≠ .comptime inner := by
  induction arguments generalizing head with
  | nil => exact head_ne inner
  | cons argument arguments inductionHypothesis =>
      exact inductionHypothesis (.application head argument)
        (by intro candidate equality; cases equality)

private theorem nominal_ne_comptime
    (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .comptime inner := by
  apply foldlApplication_ne_comptime
  intro candidate equality
  cases equality

private theorem global_type_eq_function
    {context : Context} {function : GlobalFunction}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (valid : DeclarationInstantiation.Valid context function.instantiation) :
    ∃ parameter result,
      function.instantiation.type = Ty.function parameter result := by
  cases valid with
  | intro signature signature_mem declaration_eq substitution_exact
      substitution_range instantiation_type_eq predicates_eq
      parameterComptime_eq returnComptime_eq =>
      have signature_valid := catalog.functions_semantic signature signature_mem
      refine ⟨function.instantiation.parameterSubstitution.apply
          (Ty.productMany signature.parameterTypes),
        function.instantiation.parameterSubstitution.apply
          (Ty.productMany signature.returnTypes), ?_⟩
      rw [instantiation_type_eq, signature_valid.scheme_body]
      rfl

theorem ValueHasType.nominal_value
    {context : Context} {heap : Heap} {value : Value}
    {declaration : Resolved.DeclarationId} {arguments : List Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : ValueHasType context heap value (Ty.nominal declaration arguments)) :
    ∃ instantiation payloads,
      value = .constructed instantiation payloads ∧
      DataConstructorInstantiation.Valid context instantiation ∧
      ValuesHaveTypes context heap payloads instantiation.payloadTypes ∧
      instantiation.resultType = Ty.nominal declaration arguments := by
  generalize type_eq : Ty.nominal declaration arguments = type at typed
  cases typed with
  | unit => exact (nominal_ne_of_head _ _ _ (by simp [Ty.unit, applicationHead]) type_eq).elim
  | bool => exact (nominal_ne_of_head _ _ _ (by simp [Ty.bool, applicationHead]) type_eq).elim
  | word => exact (nominal_ne_of_head _ _ _ (by simp [Ty.word, applicationHead]) type_eq).elim
  | integer => exact (nominal_ne_of_head _ _ _ (by simp [Ty.integer, applicationHead]) type_eq).elim
  | product => exact (nominal_ne_of_head _ _ _ (by simp [applicationHead]) type_eq).elim
  | proxy => exact (nominal_ne_of_head _ _ _ (by simp [applicationHead]) type_eq).elim
  | constructed valid arguments_typed =>
      exact ⟨_, _, rfl, valid, arguments_typed, rfl⟩
  | mapping => exact (nominal_ne_of_head _ _ _ (by simp [applicationHead]) type_eq).elim
  | closure => exact (nominal_ne_of_head _ _ _ (by simp [applicationHead]) type_eq).elim
  | global valid evidence_covers =>
      rcases global_type_eq_function catalog valid with
        ⟨parameter, result, function_eq⟩
      rw [function_eq] at type_eq
      exact (nominal_ne_of_head _ _ _ (by simp [applicationHead]) type_eq).elim
  | builtin function =>
      exact (nominal_ne_of_head _ _ _
        (by simp [BuiltinFunctionId.type, applicationHead]) type_eq).elim
  | comptime inner_typed =>
      exact (nominal_ne_comptime declaration arguments _ type_eq).elim

theorem ValueHasType.unit_value
    {context : Context} {heap : Heap} {value : Value}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : ValueHasType context heap value .unit) :
    value = .unit := by
  generalize type_eq : Ty.unit = type at typed
  cases typed with
  | unit => rfl
  | bool => simp [Ty.unit, Ty.bool] at type_eq
  | word => simp [Ty.unit, Ty.word] at type_eq
  | integer => simp [Ty.unit, Ty.integer] at type_eq
  | product => cases type_eq
  | proxy => cases type_eq
  | constructed valid arguments_typed =>
      cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner
          constructor_eq substitution_exact substitution_range payloadTypes_eq
          resultType_eq =>
          rw [resultType_eq] at type_eq
          exact (nominal_ne_of_head _ _ _
            (by simp [Ty.unit, applicationHead]) type_eq.symm).elim
  | mapping => cases type_eq
  | closure => cases type_eq
  | global valid evidence_covers =>
      rcases global_type_eq_function catalog valid with
        ⟨parameter, result, function_eq⟩
      rw [function_eq] at type_eq
      cases type_eq
  | builtin function =>
      rw [BuiltinFunctionId.type] at type_eq
      cases type_eq
  | comptime => cases type_eq

theorem ValueHasType.product_value
    {context : Context} {heap : Heap} {value : Value}
    {leftType rightType : Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : ValueHasType context heap value (.product leftType rightType)) :
    ∃ left right,
      value = .product left right ∧
      ValueHasType context heap left leftType ∧
      ValueHasType context heap right rightType := by
  generalize type_eq : Ty.product leftType rightType = type at typed
  cases typed with
  | unit => cases type_eq
  | bool => cases type_eq
  | word => cases type_eq
  | integer => cases type_eq
  | product left_typed right_typed =>
      cases type_eq
      exact ⟨_, _, rfl, left_typed, right_typed⟩
  | proxy => cases type_eq
  | constructed valid arguments_typed =>
      cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner
          constructor_eq substitution_exact substitution_range payloadTypes_eq
          resultType_eq =>
          rw [resultType_eq] at type_eq
          exact (nominal_ne_of_head _ _ _
            (by simp [applicationHead]) type_eq.symm).elim
  | mapping => cases type_eq
  | closure => cases type_eq
  | global valid evidence_covers =>
      rcases global_type_eq_function catalog valid with
        ⟨parameter, result, function_eq⟩
      rw [function_eq] at type_eq
      cases type_eq
  | builtin function =>
      rw [BuiltinFunctionId.type] at type_eq
      cases type_eq
  | comptime => cases type_eq

theorem ValuesPack.exists_typed
    {context : Context} {heap : Heap} {value : Value} {types : List Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : ValueHasType context heap value (Ty.productMany types)) :
    ∃ values,
      ValuesPack values value ∧ ValuesHaveTypes context heap values types := by
  induction types generalizing value with
  | nil =>
      have value_eq := typed.unit_value catalog
      subst value
      exact ⟨[], .nil, .nil⟩
  | cons first rest induction =>
      cases rest with
      | nil => exact ⟨[value], .singleton value, .cons typed .nil⟩
      | cons second rest =>
          rcases typed.product_value catalog with
            ⟨firstValue, packedTail, value_eq, first_typed, tail_typed⟩
          subst value
          rcases induction tail_typed with
            ⟨tailValues, tailPack, tailValuesTyped⟩
          cases tailValues with
          | nil => cases tailValuesTyped
          | cons secondValue restValues =>
              cases tailValuesTyped with
              | cons second_typed rest_typed =>
                  exact ⟨firstValue :: secondValue :: restValues,
                    .cons tailPack,
                    .cons first_typed (.cons second_typed rest_typed)⟩

namespace ValueHasType

theorem constructed_payloads_of_agreement
    {context : Context} {heap : Heap}
    {actual expected : DataConstructorInstantiation} {arguments : List Value}
    (valid : DataConstructorInstantiation.Valid context expected)
    (agreement : ConstructorInstantiationsAgree actual expected)
    (typed : ValueHasType context heap (.constructed actual arguments)
      expected.resultType) :
    ValuesHaveTypes context heap arguments expected.payloadTypes := by
  rcases typed.constructed_inv with ordinary | staged
  · simpa [agreement.payload_types_eq] using ordinary.2.2
  · rcases staged with ⟨inner, result_eq, _⟩
    cases valid with
    | intro dataType signature dataType_mem signature_mem signature_owner
        constructor_eq substitution_exact substitution_range payloadTypes_eq
        resultType_eq =>
        have impossible :
            Ty.nominal dataType.id
                (ParameterSubstitution.orderedArguments
                  expected.parameterSubstitution dataType.parameters) =
              .comptime inner := by
          exact resultType_eq.symm.trans result_eq
        exact (nominal_ne_comptime _ _ _ impossible).elim

end ValueHasType

namespace ValuesPack

theorem unpack_types
    {context : Context} {heap : Heap} {values : List Value}
    {types : List Ty} {packed : Value}
    (packing : ValuesPack values packed)
    (packed_typed : ValueHasType context heap packed (Ty.productMany types))
    (same_length : values.length = types.length) :
    ValuesHaveTypes context heap values types := by
  induction packing generalizing types with
  | nil =>
      cases types with
      | nil => exact .nil
      | cons type types => simp at same_length
  | singleton value =>
      cases types with
      | nil => simp at same_length
      | cons type types =>
          cases types with
          | nil => exact .cons packed_typed .nil
          | cons second rest => simp at same_length
  | @cons first second rest packed tail induction =>
      cases types with
      | nil => simp at same_length
      | cons firstType types =>
          cases types with
          | nil => simp at same_length
          | cons secondType restTypes =>
              rcases packed_typed.product_inv with
                ⟨first_typed, tail_typed⟩
              have tail_length :
                  (second :: rest).length =
                    (secondType :: restTypes).length := by
                simpa using Nat.succ.inj same_length
              exact .cons first_typed
                (induction tail_typed tail_length)

end ValuesPack

theorem DataConstructorInstantiation.Valid.agrees_of_constructor_eq_of_result_eq
    {context : Context} {left right : DataConstructorInstantiation}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (left_valid : DataConstructorInstantiation.Valid context left)
    (right_valid : DataConstructorInstantiation.Valid context right)
    (constructor_eq : left.constructor = right.constructor)
    (result_eq : left.resultType = right.resultType) :
    ConstructorInstantiationsAgree left right := by
  cases left_valid with
  | intro leftData leftSignature leftDataMem leftSignatureMem leftOwner
      leftConstructorEq leftExact leftRange leftPayloadEq leftResultEq =>
    cases right_valid with
    | intro rightData rightSignature rightDataMem rightSignatureMem rightOwner
        rightConstructorEq rightExact rightRange rightPayloadEq rightResultEq =>
      have signatureIdEq : leftSignature.id = rightSignature.id := by
        exact leftConstructorEq.symm.trans
          (constructor_eq.trans rightConstructorEq)
      have dataIdEq : leftData.id = rightData.id := by
        exact leftOwner.symm.trans
          ((congrArg ProgramDataConstructorId.dataType signatureIdEq).trans
            rightOwner)
      have dataEq : leftData = rightData :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup catalog.data_ids
          leftDataMem rightDataMem dataIdEq
      subst rightData
      have constructorIdSublist :
          (leftData.constructors.map fun signature => signature.id).Sublist
            (context.signatures.dataTypes.flatMap fun dataType =>
              dataType.constructors.map fun signature => signature.id) :=
        sublist_flatMap_of_mem
          (fun dataType =>
            dataType.constructors.map fun signature => signature.id)
          leftDataMem
      have constructorIdsNodup :
          (leftData.constructors.map fun signature => signature.id).Nodup :=
        constructorIdSublist.nodup catalog.constructor_ids
      have signatureEq : leftSignature = rightSignature :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup constructorIdsNodup
          leftSignatureMem rightSignatureMem signatureIdEq
      subst rightSignature
      have nominalEq :
          Ty.nominal leftData.id
              (ParameterSubstitution.orderedArguments
                left.parameterSubstitution leftData.parameters) =
            Ty.nominal leftData.id
              (ParameterSubstitution.orderedArguments
                right.parameterSubstitution leftData.parameters) := by
        exact leftResultEq.symm.trans (result_eq.trans rightResultEq)
      have orderedArgumentsEq := (nominal_injective nominalEq).2
      have payloadWellFormed :=
        (catalog.data_semantic leftData leftDataMem).constructor_payloads
          leftSignature leftSignatureMem
      have payloadMapsEq :
          leftSignature.payloadTypes.map left.parameterSubstitution.apply =
            leftSignature.payloadTypes.map right.parameterSubstitution.apply := by
        apply List.map_congr_left
        intro payload payloadMem
        exact
          StructuralSubstitution.TypeWellScoped.applyParameters_eq_of_orderedArguments_eq
            (context := signatureContext context.signatures leftData.id
              leftData.parameters)
            (flexibleVariables := []) left.parameterSubstitution
            right.parameterSubstitution
            (by
              simpa [signatureContext, Context.ofSignatures,
                Context.forDeclaration, Context.withAssumptions] using leftExact)
            (by
              simpa [signatureContext, Context.ofSignatures,
                Context.forDeclaration, Context.withAssumptions] using rightExact)
            orderedArgumentsEq
            (payloadWellFormed payload payloadMem).typeWellScoped
      exact {
        constructor_eq
        payload_types_eq := leftPayloadEq.trans
          (payloadMapsEq.trans rightPayloadEq.symm)
        result_type_eq := result_eq
      }

private theorem patternInstruction_typedRest_length_lt
    {context : Context} {instructions rest : List MatchPatternInstruction}
    {type : Ty} {requirements : List RequirementId}
    {binders : List TypedBinder}
    (typing : PatternInstructionHasType context instructions type requirements
      binders rest) :
    rest.length < instructions.length := by
  refine PatternInstructionHasType.rec
    (motive_1 := fun instructions _ _ _ rest _ =>
      rest.length < instructions.length)
    (motive_2 := fun instructions _ _ _ rest _ =>
      rest.length ≤ instructions.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  all_goals intros
  all_goals try simp_all only [List.length_cons]
  all_goals omega

private theorem matchPattern_rootArity_eq
    {context : Context} {source : MatchPatternSource}
    {resolution : MatchPatternResolution} {left right : Nat}
    (left_represents :
      MatchPatternSourceRepresents context source resolution left)
    (right_represents :
      MatchPatternSourceRepresents context source resolution right) :
    left = right := by
  induction left_represents generalizing right with
  | wildcard => cases right_represents; rfl
  | integerLiteral => cases right_represents; rfl
  | binder => cases right_represents; rfl
  | constructor => cases right_represents; rfl
  | tuple => cases right_represents; rfl
  | group _ induction =>
      cases right_represents with
      | group inner => exact induction inner

private theorem bindingValues_append
    {context : Context} {heap : Heap}
    {left right : List (TypedBinder × Value)}
    (left_typed : BindingValuesHaveTypes context heap left)
    (right_typed : BindingValuesHaveTypes context heap right) :
    BindingValuesHaveTypes context heap (left ++ right) := by
  induction left_typed with
  | nil => exact right_typed
  | cons head tail induction => exact .cons head induction

set_option maxHeartbeats 800000 in
mutual

  theorem PatternInstructionMatches.preservesTyping
      {context : Context} {heap : Heap} {value : Value}
      {instructions typedRest matchedRest : List MatchPatternInstruction}
      {type : Ty} {requirements : List RequirementId}
      {binders : List TypedBinder} {bindings : List (TypedBinder × Value)}
      (typing : PatternInstructionHasType context instructions type
        requirements binders typedRest)
      (value_typed : ValueHasType context heap value type)
      (matched : PatternInstructionMatches context value instructions
        bindings matchedRest) :
      matchedRest = typedRest ∧
        BindingValuesHaveTypes context heap bindings ∧
        bindings.map Prod.fst = binders := by
    cases typing with
    | wildcard =>
        cases matched
        exact ⟨rfl, .nil, rfl⟩
    | integerLiteral =>
        cases matched
        exact ⟨rfl, .nil, rfl⟩
    | binder valid =>
        cases matched
        refine ⟨rfl, .cons ?_ .nil, rfl⟩
        rw [valid.scheme_eq]
        exact value_typed
    | constructor valid arity arguments_type =>
        cases matched with
        | constructor agreement dynamic_arity children =>
            exact PatternInstructionsMatch.preservesTyping arguments_type
              (value_typed.constructed_payloads_of_agreement valid agreement)
              children
    | tuple arity elements_type =>
        cases matched with
        | tuple packing dynamic_arity children =>
            have same_length := dynamic_arity.trans arity
            exact PatternInstructionsMatch.preservesTyping elements_type
              (packing.unpack_types value_typed same_length) children
    termination_by instructions.length * 2
    decreasing_by
      all_goals simp_all
      all_goals omega

  theorem PatternInstructionsMatch.preservesTyping
      {context : Context} {heap : Heap} {values : List Value}
      {instructions typedRest matchedRest : List MatchPatternInstruction}
      {types : List Ty} {requirements : List RequirementId}
      {binders : List TypedBinder} {bindings : List (TypedBinder × Value)}
      (typing : PatternInstructionsHaveTypes context instructions types
        requirements binders typedRest)
      (values_typed : ValuesHaveTypes context heap values types)
      (matched : PatternInstructionsMatch context values instructions
        bindings matchedRest) :
      matchedRest = typedRest ∧
        BindingValuesHaveTypes context heap bindings ∧
        bindings.map Prod.fst = binders := by
    cases typing with
    | nil =>
        cases values_typed
        cases matched
        exact ⟨rfl, .nil, rfl⟩
    | cons head_type tail_type =>
        cases values_typed with
        | cons head_value_typed tail_values_typed =>
            cases matched with
            | cons head_match tail_match =>
                rcases head_match.preservesTyping head_type head_value_typed with
                  ⟨middle_eq, head_bindings_typed, head_binders_eq⟩
                subst middle_eq
                rcases tail_match.preservesTyping tail_type tail_values_typed with
                  ⟨rest_eq, tail_bindings_typed, tail_binders_eq⟩
                refine ⟨rest_eq,
                  bindingValues_append head_bindings_typed tail_bindings_typed,
                  ?_⟩
                simp [head_binders_eq, tail_binders_eq]
    termination_by instructions.length * 2 + 1
    decreasing_by
      · omega
      · have shorter := patternInstruction_typedRest_length_lt head_type
        omega

end

namespace PatternMatches

theorem preservesTyping
    {context : Context} {heap : Heap} {pattern : TypedMatchPattern}
    {type : Ty} {binders : List TypedBinder} {rootArity : Nat}
    {value : Value} {bindings : List (TypedBinder × Value)}
    (typing : TypedMatchPatternHasType context pattern type binders rootArity)
    (value_typed : ValueHasType context heap value type)
    (matched : PatternMatches context pattern value bindings) :
    BindingValuesHaveTypes context heap bindings ∧
      bindings.map Prod.fst = binders := by
  cases matched with
  | intro dynamic_source dynamic_match =>
      rename_i dynamicArity
      have arity_eq := matchPattern_rootArity_eq
        typing.source_represents dynamic_source
      subst dynamicArity
      rcases dynamic_match.preservesTyping typing.resolution_type value_typed with
        ⟨_, bindings_typed, binders_eq⟩
      exact ⟨bindings_typed, binders_eq⟩

end PatternMatches

set_option maxHeartbeats 400000 in
mutual

  theorem PatternInstructionHasType.patternBinders_monomorphic
      {context : Context} {instructions rest : List MatchPatternInstruction}
      {type : Ty} {requirements : List RequirementId}
      {binders : List TypedBinder}
      (typing : PatternInstructionHasType context instructions type requirements
        binders rest) :
      ∀ binder, binder ∈ binders → binder.scheme.quantified = [] := by
    cases typing with
    | wildcard => simp
    | integerLiteral valid => simp
    | binder valid =>
        intro binder member
        simp only [List.mem_singleton] at member
        subst binder
        simp [valid.scheme_eq, TypeSystem.Scheme.mono]
    | constructor valid arity arguments =>
        exact PatternInstructionsHaveTypes.patternBinders_monomorphic arguments
    | tuple arity elements =>
        exact PatternInstructionsHaveTypes.patternBinders_monomorphic elements
    termination_by instructions.length * 2
    decreasing_by all_goals simp_all; all_goals omega

  theorem PatternInstructionsHaveTypes.patternBinders_monomorphic
      {context : Context} {instructions rest : List MatchPatternInstruction}
      {types : List Ty} {requirements : List RequirementId}
      {binders : List TypedBinder}
      (typing : PatternInstructionsHaveTypes context instructions types
        requirements binders rest) :
      ∀ binder, binder ∈ binders → binder.scheme.quantified = [] := by
    cases typing with
    | nil => simp
    | cons head tail =>
        intro binder member
        simp only [List.mem_append] at member
        exact member.elim
          (PatternInstructionHasType.patternBinders_monomorphic head binder)
          (PatternInstructionsHaveTypes.patternBinders_monomorphic tail binder)
    termination_by instructions.length * 2 + 1
    decreasing_by
      · simp_all
      · have shorter := patternInstruction_typedRest_length_lt head
        simp_all

end

namespace TypedMatchPatternHasType

theorem patternBinders_monomorphic
    {context : Context} {pattern : TypedMatchPattern} {type : Ty}
    {binders : List TypedBinder} {rootArity : Nat}
    (typing : TypedMatchPatternHasType context pattern type binders rootArity) :
    ∀ binder, binder ∈ binders → binder.scheme.quantified = [] :=
  PatternInstructionHasType.patternBinders_monomorphic
    typing.resolution_type

end TypedMatchPatternHasType

set_option maxHeartbeats 800000 in
mutual

  theorem PatternInstructionIrrefutable.matchesTyped
      {context : Context} {heap : Heap} {value : Value}
      {instructions typedRest irrefutableRest : List MatchPatternInstruction}
      {type : Ty} {requirements : List RequirementId}
      {binders : List TypedBinder}
      (catalog : SignatureCatalogWellFormed context.signatures)
      (typing : PatternInstructionHasType context instructions type requirements
        binders typedRest)
      (value_typed : ValueHasType context heap value type)
      (irrefutable : PatternInstructionIrrefutable instructions irrefutableRest) :
      ∃ bindings,
        PatternInstructionMatches context value instructions bindings typedRest ∧
        typedRest = irrefutableRest := by
    cases typing with
    | wildcard =>
        cases irrefutable
        exact ⟨[], .wildcard, rfl⟩
    | integerLiteral => cases irrefutable
    | binder valid =>
        cases irrefutable
        exact ⟨[(_, value)], .binder, rfl⟩
    | constructor => cases irrefutable
    | tuple arity elements_type =>
        cases irrefutable with
        | tuple elements_irrefutable =>
            rw [arity] at elements_irrefutable
            rcases ValuesPack.exists_typed catalog value_typed with
              ⟨values, packed, values_typed⟩
            rcases PatternInstructionsIrrefutable.matchesTyped catalog
                elements_type values_typed elements_irrefutable with
              ⟨bindings, children, rest_eq⟩
            exact ⟨bindings, .tuple packed
              (values_typed.length_eq.trans arity.symm) children, rest_eq⟩
    termination_by instructions.length * 2
    decreasing_by
      all_goals simp_all
      all_goals omega

  theorem PatternInstructionsIrrefutable.matchesTyped
      {context : Context} {heap : Heap} {values : List Value}
      {instructions typedRest irrefutableRest : List MatchPatternInstruction}
      {types : List Ty} {requirements : List RequirementId}
      {binders : List TypedBinder}
      (catalog : SignatureCatalogWellFormed context.signatures)
      (typing : PatternInstructionsHaveTypes context instructions types
        requirements binders typedRest)
      (values_typed : ValuesHaveTypes context heap values types)
      (irrefutable : PatternInstructionsIrrefutable instructions types.length
        irrefutableRest) :
      ∃ bindings,
        PatternInstructionsMatch context values instructions bindings typedRest ∧
        typedRest = irrefutableRest := by
    cases typing with
    | nil =>
        cases values_typed
        cases irrefutable
        exact ⟨[], .nil, rfl⟩
    | cons head_type tail_type =>
        cases values_typed with
        | cons head_typed tail_typed =>
            cases irrefutable with
            | succ head_irrefutable tail_irrefutable =>
                rcases PatternInstructionIrrefutable.matchesTyped catalog
                    head_type head_typed head_irrefutable with
                  ⟨headBindings, head_match, middle_eq⟩
                rw [← middle_eq] at tail_irrefutable
                rcases PatternInstructionsIrrefutable.matchesTyped catalog
                    tail_type tail_typed tail_irrefutable with
                  ⟨tailBindings, tail_match, rest_eq⟩
                exact ⟨headBindings ++ tailBindings,
                  .cons head_match tail_match, rest_eq⟩
    termination_by instructions.length * 2 + 1
    decreasing_by
      · omega
      · have shorter :=
          patternInstruction_typedRest_length_lt head_type
        omega

end

namespace MatchPatternSourceRepresents

/-- The retained pattern source determines the root arity used to decode its
flattened instruction stream. -/
theorem rootArity_eq
    {context : Context} {source : MatchPatternSource}
    {resolution : MatchPatternResolution} {left right : Nat}
    (left_represents :
      MatchPatternSourceRepresents context source resolution left)
    (right_represents :
      MatchPatternSourceRepresents context source resolution right) :
    left = right := by
  induction left_represents generalizing right with
  | wildcard => cases right_represents; rfl
  | integerLiteral => cases right_represents; rfl
  | binder => cases right_represents; rfl
  | constructor => cases right_represents; rfl
  | tuple => cases right_represents; rfl
  | group _ induction =>
      cases right_represents with
      | group inner => exact induction inner

end MatchPatternSourceRepresents

namespace TypedMatchPatternHasType

/-- A statically typed irrefutable pattern matches every value of its input
type. -/
theorem matches_irrefutable
    {context : Context} {heap : Heap} {pattern : TypedMatchPattern}
    {type : Ty} {binders : List TypedBinder} {rootArity : Nat}
    {value : Value}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typing : TypedMatchPatternHasType context pattern type binders rootArity)
    (value_typed : ValueHasType context heap value type)
    (irrefutable : TypedMatchPatternIrrefutable context pattern) :
    ∃ bindings, PatternMatches context pattern value bindings := by
  rcases irrefutable with
    ⟨dynamicArity, dynamicSource, dynamicIrrefutable⟩
  have arity_eq :=
    Solcore.SourceSemantics.Dynamic.MatchPatternSourceRepresents.rootArity_eq
      typing.source_represents dynamicSource
  subst dynamicArity
  unfold MatchPatternResolutionIrrefutable at dynamicIrrefutable
  rcases PatternInstructionIrrefutable.matchesTyped catalog
      typing.resolution_type value_typed dynamicIrrefutable with
    ⟨bindings, matched, rest_eq⟩
  exact ⟨bindings, .intro typing.source_represents matched⟩

end TypedMatchPatternHasType

namespace PatternCoversConstructor

/-- A constructor-covering arm matches every well-typed value built by the
covered constructor. -/
theorem matches_value
    {context : Context} {heap : Heap} {pattern : TypedMatchPattern}
    {type : Ty} {binders : List TypedBinder} {rootArity : Nat}
    {actual : DataConstructorInstantiation} {arguments : List Value}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typing : TypedMatchPatternHasType context pattern type binders rootArity)
    (actual_valid : DataConstructorInstantiation.Valid context actual)
    (arguments_typed :
      ValuesHaveTypes context heap arguments actual.payloadTypes)
    (actual_result_eq : actual.resultType = type)
    (covers : PatternCoversConstructor pattern actual.constructor) :
    ∃ bindings,
      PatternMatches context pattern (.constructed actual arguments) bindings := by
  rcases covers with
    ⟨expected, instructions, resolution_eq, constructor_eq,
      children_irrefutable⟩
  cases typing with
  | mk type_eq source_represents resolution_type binders_distinct =>
      rw [resolution_eq] at resolution_type
      unfold MatchPatternResolutionHasType at resolution_type
      simp only [matchPatternResolutionInstructions] at resolution_type
      cases resolution_type with
      | constructor expected_valid arity children_type =>
          have agreement :=
            Solcore.SourceSemantics.Dynamic.DataConstructorInstantiation.Valid.agrees_of_constructor_eq_of_result_eq
              catalog actual_valid expected_valid constructor_eq.symm
              actual_result_eq
          have arguments_typed_expected :
              ValuesHaveTypes context heap arguments expected.payloadTypes := by
            simpa [agreement.payload_types_eq] using arguments_typed
          rcases PatternInstructionsIrrefutable.matchesTyped catalog children_type
              arguments_typed_expected children_irrefutable with
            ⟨bindings, children_match, rest_eq⟩
          have dynamic_arity : arguments.length = rootArity :=
            arguments_typed.length_eq.trans
              ((congrArg List.length agreement.payload_types_eq).trans
                arity.symm)
          refine ⟨bindings, .intro source_represents ?_⟩
          rw [resolution_eq]
          exact .constructor agreement dynamic_arity children_match

end PatternCoversConstructor

namespace PatternDoesNotMatch

/-- A semantic non-match and a semantic match for the same retained pattern
are contradictory. -/
theorem excludes
    {context : Context} {pattern : TypedMatchPattern} {value : Value}
    (failure : PatternDoesNotMatch context pattern value)
    {bindings : List (TypedBinder × Value)}
    (matched : PatternMatches context pattern value bindings) : False := by
  cases failure with
  | intro failedSource failedResolution =>
      cases matched with
      | intro matchedSource matchedResolution =>
          have arity_eq :=
            Solcore.SourceSemantics.Dynamic.MatchPatternSourceRepresents.rootArity_eq
              failedSource matchedSource
          subst_vars
          exact failedResolution.excludes matchedResolution

end PatternDoesNotMatch

namespace MatchCasesHaveType

theorem member
    {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {matchCase : TypedMatchCase}
    (typing : MatchCasesHaveType source control context scrutineeType cases
      caseFacts)
    (member : matchCase ∈ cases) :
    ∃ facts,
      MatchCaseHasType source control context scrutineeType matchCase facts := by
  cases typing with
  | nil => simp at member
  | cons head tail =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, head⟩
      · exact
          Solcore.SourceSemantics.Dynamic.MatchCasesHaveType.member tail member
termination_by cases.length
decreasing_by simp_all

end MatchCasesHaveType

namespace MatchCasesSelect

theorem arm_preserves_typing
    {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Value} {body : List StatementId}
    {bindings : List (TypedBinder × Value)} {heap : Heap}
    (cases_typed : MatchCasesHaveType source control context scrutineeType cases
      caseFacts)
    (value_typed : ValueHasType context heap value scrutineeType)
    (selected : MatchCasesSelect context value cases fallback
      (.arm body bindings)) :
    ∃ binders armContext finalContext facts,
      BindingValuesHaveTypes context heap bindings ∧
        bindings.map Prod.fst = binders ∧
        BindersExtend source.owner context binders armContext ∧
        StatementsHaveType source control armContext body finalContext facts ∧
        facts ∈ caseFacts ∧
        (∀ binder, binder ∈ binders →
          binder.scheme.quantified = []) := by
  cases selected with
  | head matched =>
      cases cases_typed with
      | cons head_type tail_type =>
          cases head_type with
          | intro pattern_type binders_extend body_type =>
              rcases matched.preservesTyping pattern_type value_typed with
                ⟨bindings_typed, binders_eq⟩
              exact ⟨_, _, _, _, bindings_typed, binders_eq, binders_extend,
                body_type, by simp,
                Solcore.SourceSemantics.Dynamic.TypedMatchPatternHasType.patternBinders_monomorphic
                  pattern_type⟩
  | tail does_not_match tail_selected =>
      cases cases_typed with
      | cons head_type tail_type =>
          rcases MatchCasesSelect.arm_preserves_typing tail_type value_typed
              tail_selected with
            ⟨binders, armContext, finalContext, facts, bindings_typed,
              binders_eq, binders_extend, body_type, member, monomorphic⟩
          exact ⟨binders, armContext, finalContext, facts, bindings_typed,
            binders_eq, binders_extend, body_type,
            List.mem_cons_of_mem _ member, monomorphic⟩
termination_by cases.length
decreasing_by simp_all

/-- A `noBranch` selection records a non-match for every explicit arm. -/
theorem excludes_member_match
    {context : Context} {value : Value} {cases : List TypedMatchCase}
    {matchCase : TypedMatchCase}
    (selected : MatchCasesSelect context value cases none .noBranch)
    (member : matchCase ∈ cases)
    {bindings : List (TypedBinder × Value)}
    (matched : PatternMatches context matchCase.pattern value bindings) : False := by
  cases selected with
  | noBranch => simp at member
  | tail does_not_match selected =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact does_not_match.excludes matched
      · exact
          Solcore.SourceSemantics.Dynamic.MatchCasesSelect.excludes_member_match
            selected member matched
termination_by cases.length
decreasing_by simp_all

/-- Static exhaustiveness excludes the dynamic `noBranch` outcome for every
well-typed scrutinee. -/
theorem noBranch_impossible_of_exhaustive
    {source : TypedSource} {control : ControlContext} {context : Context}
    {heap : Heap} {value : Value} {scrutineeType : Ty}
    {cases : List TypedMatchCase} {caseFacts : List BodyFacts}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (cases_typed : MatchCasesHaveType source control context scrutineeType
      cases caseFacts)
    (value_typed : ValueHasType context heap value scrutineeType)
    (exhaustive : MatchExhaustive context scrutineeType cases none)
    (selected : MatchCasesSelect context value cases none .noBranch) : False := by
  cases exhaustive with
  | catchall member irrefutable =>
      rcases
          Solcore.SourceSemantics.Dynamic.MatchCasesHaveType.member cases_typed
            member with
        ⟨facts, case_typed⟩
      cases case_typed with
      | intro pattern_typed binders_extend body_type =>
          rcases
              Solcore.SourceSemantics.Dynamic.TypedMatchPatternHasType.matches_irrefutable
                catalog pattern_typed value_typed irrefutable with
            ⟨bindings, matched⟩
          exact selected.excludes_member_match member matched
  | @constructors dataType substitution cataloged substitution_exact
      scrutinee_eq covered =>
      subst scrutineeType
      rcases value_typed.nominal_value catalog with
        ⟨actual, arguments, value_eq, actual_valid, arguments_typed,
          actual_result_eq⟩
      subst value
      have actual_valid_copy := actual_valid
      cases actual_valid with
      | intro actualData actualSignature actualDataMem actualSignatureMem
          actualOwner actualConstructorEq actualExact actualRange
          actualPayloadEq actualCatalogResultEq =>
          have nominalEq :
              Ty.nominal actualData.id
                  (ParameterSubstitution.orderedArguments
                    actual.parameterSubstitution actualData.parameters) =
                Ty.nominal dataType.id
                  (ParameterSubstitution.orderedArguments substitution
                    dataType.parameters) :=
            actualCatalogResultEq.symm.trans actual_result_eq
          have dataIdEq := (nominal_injective nominalEq).1
          have dataEq : actualData = dataType :=
            StructuralSubstitution.eq_of_mem_of_mapped_nodup catalog.data_ids
              actualDataMem cataloged dataIdEq
          subst actualData
          rcases covered actualSignature actualSignatureMem with
            ⟨matchCase, member, coversSignature⟩
          have coversActual :
              PatternCoversConstructor matchCase.pattern actual.constructor := by
            simpa [actualConstructorEq] using coversSignature
          rcases
              Solcore.SourceSemantics.Dynamic.MatchCasesHaveType.member
                cases_typed member with
            ⟨facts, case_typed⟩
          cases case_typed with
          | intro pattern_typed binders_extend body_type =>
              rcases
                  Solcore.SourceSemantics.Dynamic.PatternCoversConstructor.matches_value
                    catalog pattern_typed actual_valid_copy arguments_typed
                    actual_result_eq coversActual with
                ⟨bindings, matched⟩
              exact selected.excludes_member_match member matched

end MatchCasesSelect

end Solcore.SourceSemantics.Dynamic
