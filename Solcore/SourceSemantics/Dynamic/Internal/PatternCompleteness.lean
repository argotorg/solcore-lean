import Solcore.SourceSemantics.Internal.Substitution.StructuralLaws
import Solcore.SourceSemantics.Dynamic.Typing

/-!
# Completeness of pattern matching

A well-typed value under an exhaustive match selects a case, and pattern instructions preserve
typing.
-/

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
  | fixed => exact (nominal_ne_of_head _ _ _ (by simp [Ty.fixed, applicationHead]) type_eq).elim
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
  | arrayRef =>
      exact (nominal_ne_of_head _ _ _ (by simp [Ty.array, applicationHead]) type_eq).elim
  | arrayObject =>
      exact (nominal_ne_of_head _ _ _
        (by simp [Ty.arrayObject, applicationHead]) type_eq).elim
  | arraySlice =>
      exact (nominal_ne_of_head _ _ _
        (by simp [Ty.arraySlice, applicationHead]) type_eq).elim
  | memref =>
      exact (nominal_ne_of_head _ _ _
        (by simp [Ty.memref, applicationHead]) type_eq).elim
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
  | fixed => simp [Ty.unit, Ty.fixed] at type_eq
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
  | arrayRef => simp [Ty.unit, Ty.array] at type_eq
  | arrayObject => simp [Ty.unit, Ty.arrayObject] at type_eq
  | arraySlice => simp [Ty.unit, Ty.arraySlice] at type_eq
  | memref => simp [Ty.unit, Ty.memref] at type_eq
  | comptime => cases type_eq

/-- A value of a fixed-width integer type is a word. -/
theorem ValueHasType.fixed_value
    {context : Context} {heap : Heap} {value : Value} {fixed : TypeSystem.FixedInteger}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : ValueHasType context heap value (.fixed fixed)) :
    ∃ word, value = .word word := by
  generalize type_eq : Ty.fixed fixed = type at typed
  cases typed with
  | unit => simp [Ty.unit, Ty.fixed] at type_eq
  | bool => simp [Ty.bool, Ty.fixed] at type_eq
  | word value => exact ⟨value, rfl⟩
  | fixed value => exact ⟨value, rfl⟩
  | integer => simp [Ty.integer, Ty.fixed] at type_eq
  | product => cases type_eq
  | proxy => cases type_eq
  | constructed valid arguments_typed =>
      cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner
          constructor_eq substitution_exact substitution_range payloadTypes_eq
          resultType_eq =>
          rw [resultType_eq] at type_eq
          exact (nominal_ne_of_head _ _ _
            (by simp [Ty.fixed, applicationHead]) type_eq.symm).elim
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
  | arrayRef => simp [Ty.fixed, Ty.array] at type_eq
  | arrayObject => simp [Ty.fixed, Ty.arrayObject] at type_eq
  | arraySlice => simp [Ty.fixed, Ty.arraySlice] at type_eq
  | memref => simp [Ty.fixed, Ty.memref] at type_eq
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
  | fixed => cases type_eq
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
  | arrayRef => simp [Ty.array] at type_eq
  | arrayObject => simp [Ty.arrayObject] at type_eq
  | arraySlice => simp [Ty.arraySlice] at type_eq
  | memref => simp [Ty.memref] at type_eq
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
    (valid : DataConstructorInstantiation.Admissible context expected)
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
    (right_valid : DataConstructorInstantiation.Admissible context right)
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
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
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
  | uint256Word => cases right_represents; rfl
  | boolLiteral => cases right_represents; rfl
  | sameNameConstructor => cases right_represents; rfl
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
    | uint256Word argument_type =>
        cases matched with
        | uint256Word argument_matched =>
            exact PatternInstructionsMatch.preservesTyping argument_type (.cons (.word _) .nil)
              argument_matched
    | boolLiteral =>
        cases matched
        exact ⟨rfl, .nil, rfl⟩
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
    | uint256Word argument =>
        exact PatternInstructionsHaveTypes.patternBinders_monomorphic argument
    | boolLiteral => simp
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
    | uint256Word argument_type =>
        cases irrefutable with
        | uint256Word argument_irrefutable =>
            obtain ⟨word, rfl⟩ := ValueHasType.fixed_value catalog value_typed
            rcases PatternInstructionsIrrefutable.matchesTyped (heap := heap) catalog
                argument_type (.cons (.word word) .nil) argument_irrefutable with
              ⟨bindings, argument_matched, rest_eq⟩
            exact ⟨bindings, .uint256Word argument_matched, rest_eq⟩
    | boolLiteral => cases irrefutable
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

/-- A value of `bool` is a boolean. -/
theorem ValueHasType.bool_value
    {context : Context} {heap : Heap} {value : Value}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : ValueHasType context heap value .bool) :
    ∃ literal, value = .bool literal := by
  generalize type_eq : Ty.bool = type at typed
  cases typed with
  | bool literal => exact ⟨literal, rfl⟩
  | unit => simp [Ty.unit, Ty.bool] at type_eq
  | word => simp [Ty.bool, Ty.word] at type_eq
  | fixed => simp [Ty.bool, Ty.fixed] at type_eq
  | integer => simp [Ty.bool, Ty.integer] at type_eq
  | product => cases type_eq
  | proxy => cases type_eq
  | constructed valid arguments_typed =>
      cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner
          constructor_eq substitution_exact substitution_range payloadTypes_eq
          resultType_eq =>
          rw [resultType_eq] at type_eq
          exact (nominal_ne_of_head _ _ _
            (by simp [Ty.bool, applicationHead]) type_eq.symm).elim
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
  | arrayRef => simp [Ty.bool, Ty.array] at type_eq
  | arrayObject => simp [Ty.bool, Ty.arrayObject] at type_eq
  | arraySlice => simp [Ty.bool, Ty.arraySlice] at type_eq
  | memref => simp [Ty.bool, Ty.memref] at type_eq
  | comptime => cases type_eq

/-- Typed value vectors concatenate at the concatenated types. -/
theorem ValuesHaveTypes.append
    {context : Context} {heap : Heap} :
    ∀ {front back : List Value} {frontTypes backTypes : List Ty},
      ValuesHaveTypes context heap front frontTypes →
      ValuesHaveTypes context heap back backTypes →
      ValuesHaveTypes context heap (front ++ back) (frontTypes ++ backTypes)
  | _, _, _, _, .nil, back => back
  | _, _, _, _, .cons head tail, back => .cons head (ValuesHaveTypes.append tail back)

/-- Typed pattern sequences concatenate, the second consuming what the first leaves. -/
theorem PatternInstructionsHaveTypes.append
    {context : Context} :
    ∀ {instructions middle rest : List MatchPatternInstruction}
      {front back : List Ty} {frontRequirements backRequirements : List RequirementId}
      {frontBinders backBinders : List TypedBinder},
      PatternInstructionsHaveTypes context instructions front frontRequirements frontBinders
        middle →
      PatternInstructionsHaveTypes context middle back backRequirements backBinders rest →
      PatternInstructionsHaveTypes context instructions (front ++ back)
        (frontRequirements ++ backRequirements) (frontBinders ++ backBinders) rest
  | _, _, _, _, _, _, _, _, _, .nil, back => by simpa using back
  | _, _, _, _, _, _, _, _, _, .cons head tail, back => by
      simpa [List.append_assoc] using
        (PatternInstructionsHaveTypes.cons head (PatternInstructionsHaveTypes.append tail back))

/-- One wildcard per column types at those columns, with no requirement and no binder. -/
theorem PatternInstructionsHaveTypes.replicate_wildcard
    {context : Context} :
    ∀ (types : List Ty) (rest : List MatchPatternInstruction),
      PatternInstructionsHaveTypes context
        (List.replicate types.length .wildcard ++ rest) types [] [] rest
  | [], _ => .nil
  | _ :: types, rest => by
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      exact PatternInstructionsHaveTypes.cons PatternInstructionHasType.wildcard
        (PatternInstructionsHaveTypes.replicate_wildcard (context := context) types rest)

/-- Leading wildcards match their values and bind nothing, so they can be dropped. -/
theorem PatternInstructionsMatch.drop_wildcards
    {context : Context} :
    ∀ {front back : List Value} {rest out : List MatchPatternInstruction}
      {bindings : List (TypedBinder × Value)},
      PatternInstructionsMatch context (front ++ back)
        (List.replicate front.length .wildcard ++ rest) bindings out →
      PatternInstructionsMatch context back rest bindings out
  | [], _, _, _, _, matched => by simpa using matched
  | value :: front, back, rest, out, bindings, matched => by
      simp only [List.cons_append, List.length_cons, List.replicate_succ] at matched
      cases matched with
      | cons head tail =>
          cases head with
          | wildcard => simpa using PatternInstructionsMatch.drop_wildcards tail

/-- A match of concatenated values splits where the values do. -/
theorem PatternInstructionsMatch.append_split
    {context : Context} :
    ∀ {front back : List Value} {instructions rest : List MatchPatternInstruction}
      {bindings : List (TypedBinder × Value)},
      PatternInstructionsMatch context (front ++ back) instructions bindings rest →
      ∃ middle frontBindings backBindings,
        PatternInstructionsMatch context front instructions frontBindings middle ∧
        PatternInstructionsMatch context back middle backBindings rest ∧
        bindings = frontBindings ++ backBindings
  | [], _, instructions, _, bindings, matched => ⟨instructions, [], bindings, .nil, matched, rfl⟩
  | value :: front, back, instructions, rest, bindings, matched => by
      cases matched with
      | cons head tail =>
          rename_i afterHead headBindings tailBindings
          obtain ⟨middle, frontBindings, backBindings, frontMatch, backMatch, bindingsEq⟩ :=
            PatternInstructionsMatch.append_split tail
          exact ⟨middle, headBindings ++ frontBindings, backBindings,
            .cons head frontMatch, backMatch, by simp [bindingsEq]⟩


/-- An admissible instantiation of a cataloged constructor at the nominal type of a substitution
has that constructor's payload types under the substitution. -/
theorem DataConstructorInstantiation.Admissible.payloadTypes_eq_of_resultType_eq
    {context : Context} {instantiation : DataConstructorInstantiation}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (admissible : DataConstructorInstantiation.Admissible context instantiation)
    {dataType : ProgramDataSignature} {substitution : TypeSystem.ParameterSubstitution}
    {constructor : ProgramDataConstructorSignature}
    (cataloged : dataType ∈ context.signatures.dataTypes)
    (constructorMem : constructor ∈ dataType.constructors)
    (exact : ParameterSubstitution.Exact substitution dataType.parameters)
    (constructor_eq : instantiation.constructor = constructor.id)
    (result_eq : instantiation.resultType = Ty.nominal dataType.id
      (ParameterSubstitution.orderedArguments substitution dataType.parameters)) :
    instantiation.payloadTypes =
      constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply substitution) := by
  cases admissible with
  | intro instData instSignature instDataMem instSignatureMem instOwner
      instConstructorEq instExact instRange instPayloadEq instResultEq =>
    have signatureIdEq : instSignature.id = constructor.id :=
      instConstructorEq.symm.trans constructor_eq
    have dataIdEq : instData.id = dataType.id := by
      exact instOwner.symm.trans
        ((congrArg ProgramDataConstructorId.dataType signatureIdEq).trans
          ((catalog.data_semantic dataType cataloged).constructor_owners constructor constructorMem))
    have dataEq : instData = dataType :=
      StructuralSubstitution.eq_of_mem_of_mapped_nodup catalog.data_ids
        instDataMem cataloged dataIdEq
    subst instData
    have constructorIdSublist :
        (dataType.constructors.map fun signature => signature.id).Sublist
          (context.signatures.dataTypes.flatMap fun dataType =>
            dataType.constructors.map fun signature => signature.id) :=
      sublist_flatMap_of_mem
        (fun dataType => dataType.constructors.map fun signature => signature.id)
        cataloged
    have constructorIdsNodup :
        (dataType.constructors.map fun signature => signature.id).Nodup :=
      constructorIdSublist.nodup catalog.constructor_ids
    have signatureEq : instSignature = constructor :=
      StructuralSubstitution.eq_of_mem_of_mapped_nodup constructorIdsNodup
        instSignatureMem constructorMem signatureIdEq
    subst instSignature
    have nominalEq :
        Ty.nominal dataType.id
            (ParameterSubstitution.orderedArguments
              instantiation.parameterSubstitution dataType.parameters) =
          Ty.nominal dataType.id
            (ParameterSubstitution.orderedArguments substitution dataType.parameters) :=
      instResultEq.symm.trans result_eq
    have orderedArgumentsEq := (nominal_injective nominalEq).2
    have payloadWellFormed :=
      (catalog.data_semantic dataType cataloged).constructor_payloads
        constructor constructorMem
    rw [instPayloadEq]
    apply List.map_congr_left
    intro payload payloadMem
    exact
      StructuralSubstitution.TypeWellScoped.applyParameters_eq_of_orderedArguments_eq
        (context := signatureContext context.signatures dataType.id dataType.parameters)
        (flexibleVariables := []) instantiation.parameterSubstitution substitution
        (by
          simpa [signatureContext, Context.ofSignatures,
            Context.forDeclaration, Context.withAssumptions] using instExact)
        (by
          simpa [signatureContext, Context.ofSignatures,
            Context.forDeclaration, Context.withAssumptions] using exact)
        orderedArgumentsEq
        (payloadWellFormed payload payloadMem).typeWellScoped

/-- A typed row's head and the rest of its row. -/
private theorem row_cons_typed
    {context : Context} {row : List MatchPatternInstruction} {type : Ty} {types : List Ty}
    {requirements : List RequirementId} {binders : List TypedBinder}
    (typed : PatternInstructionsHaveTypes context row (type :: types) requirements binders []) :
    ∃ afterHead headRequirements headBinders tailRequirements tailBinders,
      PatternInstructionHasType context row type headRequirements headBinders afterHead ∧
      PatternInstructionsHaveTypes context afterHead types tailRequirements tailBinders [] := by
  cases typed with
  | cons head tail => exact ⟨_, _, _, _, _, head, tail⟩

/-- The default specialization of a typed row is typed at the remaining columns. -/
theorem coverageDefaultRow_typed
    {context : Context} {row row' : List MatchPatternInstruction} {type : Ty} {types : List Ty}
    (typed : ∃ requirements binders,
      PatternInstructionsHaveTypes context row (type :: types) requirements binders [])
    (specialized : coverageDefaultRow row = some row') :
    ∃ requirements binders,
      PatternInstructionsHaveTypes context row' types requirements binders [] := by
  obtain ⟨_, _, typed⟩ := typed
  obtain ⟨afterHead, _, _, _, _, head, tail⟩ := row_cons_typed typed
  cases row with
  | nil => simp [coverageDefaultRow] at specialized
  | cons instruction rest =>
      cases instruction <;> simp [coverageDefaultRow] at specialized
      all_goals subst specialized
      all_goals cases head
      all_goals exact ⟨_, _, tail⟩

/-- A boolean specialization of a typed row is typed at the remaining columns. -/
theorem coverageBoolRow_typed
    {context : Context} {value : Bool} {row row' : List MatchPatternInstruction}
    {types : List Ty}
    (typed : ∃ requirements binders,
      PatternInstructionsHaveTypes context row (Ty.bool :: types) requirements binders [])
    (specialized : coverageBoolRow value row = some row') :
    ∃ requirements binders,
      PatternInstructionsHaveTypes context row' types requirements binders [] := by
  obtain ⟨_, _, typed⟩ := typed
  obtain ⟨afterHead, _, _, _, _, head, tail⟩ := row_cons_typed typed
  cases row with
  | nil => simp [coverageBoolRow] at specialized
  | cons instruction rest =>
      cases instruction <;> simp [coverageBoolRow] at specialized
      all_goals
        first
          | (obtain ⟨_, rfl⟩ := specialized)
          | subst specialized
      all_goals cases head
      all_goals exact ⟨_, _, tail⟩

/-- The word specialization of a typed row at `uint256` is typed at the word and the remaining
columns. -/
theorem coverageWordRow_typed
    {context : Context} {row row' : List MatchPatternInstruction} {types : List Ty}
    (typed : ∃ requirements binders,
      PatternInstructionsHaveTypes context row (Ty.fixed .uint256 :: types) requirements binders [])
    (specialized : coverageWordRow row = some row') :
    ∃ requirements binders,
      PatternInstructionsHaveTypes context row' (Ty.word :: types) requirements binders [] := by
  obtain ⟨_, _, typed⟩ := typed
  obtain ⟨afterHead, _, _, _, _, head, tail⟩ := row_cons_typed typed
  cases row with
  | nil => simp [coverageWordRow] at specialized
  | cons instruction rest =>
      cases instruction <;> simp [coverageWordRow] at specialized
      all_goals subst specialized
      · cases head
        exact ⟨_, _, .cons .wildcard tail⟩
      · cases head
        exact ⟨_, _, .cons .wildcard tail⟩
      · generalize typeEq : Ty.fixed FixedInteger.uint256 = columnType at head
        cases head with
        | uint256Word argument =>
            exact ⟨_, _, PatternInstructionsHaveTypes.append argument tail⟩

/-- The tuple specialization of a typed row is typed at the tuple's elements and the remaining
columns. -/
theorem coverageTupleRow_typed
    {context : Context} {elementTypes : List Ty} {row row' : List MatchPatternInstruction}
    {types : List Ty}
    (typed : ∃ requirements binders,
      PatternInstructionsHaveTypes context row (Ty.productMany elementTypes :: types)
        requirements binders [])
    (specialized : coverageTupleRow elementTypes.length row = some row') :
    ∃ requirements binders,
      PatternInstructionsHaveTypes context row' (elementTypes ++ types) requirements binders [] := by
  obtain ⟨_, _, typed⟩ := typed
  obtain ⟨afterHead, _, _, _, _, head, tail⟩ := row_cons_typed typed
  cases row with
  | nil => simp [coverageTupleRow] at specialized
  | cons instruction rest =>
      cases instruction <;> simp [coverageTupleRow] at specialized
      · subst specialized
        cases head
        exact ⟨_, _, PatternInstructionsHaveTypes.append
          (PatternInstructionsHaveTypes.replicate_wildcard elementTypes _) tail⟩
      · subst specialized
        cases head
        exact ⟨_, _, PatternInstructionsHaveTypes.append
          (PatternInstructionsHaveTypes.replicate_wildcard elementTypes _) tail⟩
      · rename_i count
        obtain ⟨countEq, rfl⟩ := specialized
        generalize typeEq : Ty.productMany elementTypes = columnType at head
        cases head with
        | tuple arity elements =>
            rename_i actualTypes
            have sameTypes : actualTypes = elementTypes :=
              Ty.productMany_inj (by rw [← arity, countEq]) typeEq.symm
            subst sameTypes
            exact ⟨_, _, PatternInstructionsHaveTypes.append elements tail⟩

/-- A constructor's specialization of a typed row at its data type is typed at the constructor's
payloads under the type's substitution and the remaining columns. -/
theorem coverageConstructorRow_typed
    {context : Context} (catalog : SignatureCatalogWellFormed context.signatures)
    {dataType : ProgramDataSignature} {substitution : TypeSystem.ParameterSubstitution}
    {constructor : ProgramDataConstructorSignature}
    {row row' : List MatchPatternInstruction} {types : List Ty}
    (cataloged : dataType ∈ context.signatures.dataTypes)
    (constructorMem : constructor ∈ dataType.constructors)
    (exact : ParameterSubstitution.Exact substitution dataType.parameters)
    (typed : ∃ requirements binders,
      PatternInstructionsHaveTypes context row
        (Ty.nominal dataType.id
          (ParameterSubstitution.orderedArguments substitution dataType.parameters) :: types)
        requirements binders [])
    (specialized :
      coverageConstructorRow constructor.id constructor.payloadTypes.length row = some row') :
    ∃ requirements binders,
      PatternInstructionsHaveTypes context row'
        (constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply substitution) ++
          types) requirements binders [] := by
  obtain ⟨_, _, typed⟩ := typed
  obtain ⟨afterHead, _, _, _, _, head, tail⟩ := row_cons_typed typed
  have wildcards := PatternInstructionsHaveTypes.replicate_wildcard (context := context)
    (constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply substitution))
  simp only [List.length_map] at wildcards
  cases row with
  | nil => simp [coverageConstructorRow] at specialized
  | cons instruction rest =>
      cases instruction <;> simp [coverageConstructorRow] at specialized
      · subst specialized
        cases head
        exact ⟨_, _, PatternInstructionsHaveTypes.append (wildcards _) tail⟩
      · subst specialized
        cases head
        exact ⟨_, _, PatternInstructionsHaveTypes.append (wildcards _) tail⟩
      · rename_i instantiation count
        obtain ⟨constructorEq, rfl⟩ := specialized
        generalize typeEq : Ty.nominal dataType.id
          (ParameterSubstitution.orderedArguments substitution dataType.parameters) =
            columnType at head
        cases head with
        | constructor valid arity arguments =>
            have payloadEq :=
              DataConstructorInstantiation.Admissible.payloadTypes_eq_of_resultType_eq
                catalog valid cataloged constructorMem exact constructorEq typeEq.symm
            rw [payloadEq] at arguments
            exact ⟨_, _, PatternInstructionsHaveTypes.append arguments tail⟩


/-- Rows that cover a vector of column types match every vector of values of those types: the
completeness of the coverage judgment. -/
theorem RowsCover.complete
    {context : Context} {heap : Heap}
    (catalog : SignatureCatalogWellFormed context.signatures) :
    ∀ {types : List Ty} {rows : List (List MatchPatternInstruction)},
      RowsCover context types rows →
      (∀ row, row ∈ rows → ∃ requirements binders,
        PatternInstructionsHaveTypes context row types requirements binders []) →
      ∀ {values : List Value}, ValuesHaveTypes context heap values types →
      ∃ row, row ∈ rows ∧ ∃ bindings, PatternInstructionsMatch context values row bindings [] := by
  intro types rows covers
  induction covers with
  | done member =>
      intro _ values typed
      cases typed
      exact ⟨[], member, [], .nil⟩
  | default rest ih =>
      intro rowsTyped values typed
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨row', rowMem', bindings, matched⟩ := ih
            (fun row' member => by
              obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp member
              exact coverageDefaultRow_typed (rowsTyped row rowMem) specialized)
            tailTyped
          obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp rowMem'
          cases row with
          | nil => simp [coverageDefaultRow] at specialized
          | cons instruction rest =>
              cases instruction <;> simp [coverageDefaultRow] at specialized
              · subst specialized
                exact ⟨_, rowMem, _, .cons .wildcard matched⟩
              · subst specialized
                exact ⟨_, rowMem, _, .cons .binder matched⟩
  | @constructors dataType substitution type types rows cataloged exact type_eq each ih =>
      intro rowsTyped values typed
      subst type_eq
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨actual, payloads, value_eq, actualValid, payloadsTyped, actualResultEq⟩ :=
            headTyped.nominal_value catalog
          subst value_eq
          have actualValidCopy := actualValid
          cases actualValid with
          | intro actualData actualSignature actualDataMem actualSignatureMem actualOwner
              actualConstructorEq actualExact actualRange actualPayloadEq actualResultEq' =>
            have nominalEq := actualResultEq'.symm.trans actualResultEq
            have dataIdEq := (nominal_injective nominalEq).1
            have dataEq : actualData = dataType :=
              StructuralSubstitution.eq_of_mem_of_mapped_nodup catalog.data_ids
                actualDataMem cataloged dataIdEq
            subst actualData
            have payloadEq :=
              DataConstructorInstantiation.Admissible.payloadTypes_eq_of_resultType_eq
                catalog actualValidCopy.toAdmissible cataloged actualSignatureMem exact
                actualConstructorEq actualResultEq
            have payloadsTyped' : ValuesHaveTypes context heap payloads
                (actualSignature.payloadTypes.map
                  (TypeSystem.ParameterSubstitution.apply substitution)) := by
              rw [← payloadEq]
              exact payloadsTyped
            obtain ⟨row', rowMem', bindings, matched⟩ := ih actualSignature actualSignatureMem
              (fun row' member => by
                obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp member
                exact coverageConstructorRow_typed catalog cataloged actualSignatureMem exact
                  (rowsTyped row rowMem) specialized)
              (ValuesHaveTypes.append payloadsTyped' tailTyped)
            obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp rowMem'
            have payloadsLength : payloads.length = actualSignature.payloadTypes.length := by
              simpa using payloadsTyped'.length_eq
            cases row with
            | nil => simp [coverageConstructorRow] at specialized
            | cons instruction rest =>
                cases instruction <;> simp [coverageConstructorRow] at specialized
                · subst specialized
                  rw [← payloadsLength] at matched
                  exact ⟨_, rowMem, _,
                    .cons .wildcard (PatternInstructionsMatch.drop_wildcards matched)⟩
                · subst specialized
                  rw [← payloadsLength] at matched
                  exact ⟨_, rowMem, _,
                    .cons .binder (PatternInstructionsMatch.drop_wildcards matched)⟩
                · rename_i expected count
                  obtain ⟨constructorEq, rfl⟩ := specialized
                  obtain ⟨middle, frontBindings, backBindings, frontMatch, backMatch,
                      bindingsEq⟩ := PatternInstructionsMatch.append_split matched
                  obtain ⟨_, _, rowTyped⟩ := rowsTyped _ rowMem
                  obtain ⟨afterHead, _, _, _, _, head, _⟩ := row_cons_typed rowTyped
                  generalize typeEq : Ty.nominal dataType.id
                    (ParameterSubstitution.orderedArguments substitution dataType.parameters) =
                      columnType at head
                  cases head with
                  | constructor expectedValid arity arguments =>
                      have agreement :=
                        DataConstructorInstantiation.Valid.agrees_of_constructor_eq_of_result_eq
                          catalog actualValidCopy expectedValid
                          (actualConstructorEq.trans constructorEq.symm)
                          (actualResultEq.trans typeEq)
                      have dynamicArity : payloads.length = count :=
                        payloadsTyped.length_eq.trans
                          ((congrArg List.length agreement.payload_types_eq).trans arity.symm)
                      exact ⟨_, rowMem, _,
                        .cons (.constructor agreement dynamicArity frontMatch) backMatch⟩
  | booleans onTrue onFalse ihTrue ihFalse =>
      intro rowsTyped values typed
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨literal, value_eq⟩ := headTyped.bool_value catalog
          subst value_eq
          cases literal with
          | true =>
              obtain ⟨row', rowMem', bindings, matched⟩ := ihTrue
                (fun row' member => by
                  obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp member
                  exact coverageBoolRow_typed (rowsTyped row rowMem) specialized)
                tailTyped
              obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp rowMem'
              cases row with
              | nil => simp [coverageBoolRow] at specialized
              | cons instruction rest =>
                  cases instruction <;> simp [coverageBoolRow] at specialized
                  · subst specialized
                    exact ⟨_, rowMem, _, .cons .wildcard matched⟩
                  · subst specialized
                    exact ⟨_, rowMem, _, .cons .binder matched⟩
                  · obtain ⟨rfl, rfl⟩ := specialized
                    exact ⟨_, rowMem, _, .cons .boolLiteral matched⟩
          | false =>
              obtain ⟨row', rowMem', bindings, matched⟩ := ihFalse
                (fun row' member => by
                  obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp member
                  exact coverageBoolRow_typed (rowsTyped row rowMem) specialized)
                tailTyped
              obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp rowMem'
              cases row with
              | nil => simp [coverageBoolRow] at specialized
              | cons instruction rest =>
                  cases instruction <;> simp [coverageBoolRow] at specialized
                  · subst specialized
                    exact ⟨_, rowMem, _, .cons .wildcard matched⟩
                  · subst specialized
                    exact ⟨_, rowMem, _, .cons .binder matched⟩
                  · obtain ⟨rfl, rfl⟩ := specialized
                    exact ⟨_, rowMem, _, .cons .boolLiteral matched⟩
  | @tuple elementTypes types rows elements ih =>
      intro rowsTyped values typed
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨elementValues, packed, elementsTyped⟩ := ValuesPack.exists_typed catalog headTyped
          obtain ⟨row', rowMem', bindings, matched⟩ := ih
            (fun row' member => by
              obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp member
              exact coverageTupleRow_typed (rowsTyped row rowMem) specialized)
            (ValuesHaveTypes.append elementsTyped tailTyped)
          obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp rowMem'
          have elementsLength : elementValues.length = elementTypes.length :=
            elementsTyped.length_eq
          cases row with
          | nil => simp [coverageTupleRow] at specialized
          | cons instruction rest =>
              cases instruction <;> simp [coverageTupleRow] at specialized
              · subst specialized
                rw [← elementsLength] at matched
                exact ⟨_, rowMem, _,
                  .cons .wildcard (PatternInstructionsMatch.drop_wildcards matched)⟩
              · subst specialized
                rw [← elementsLength] at matched
                exact ⟨_, rowMem, _,
                  .cons .binder (PatternInstructionsMatch.drop_wildcards matched)⟩
              · rename_i count
                obtain ⟨countEq, rfl⟩ := specialized
                obtain ⟨middle, frontBindings, backBindings, frontMatch, backMatch, _⟩ :=
                  PatternInstructionsMatch.append_split matched
                exact ⟨_, rowMem, _,
                  .cons (.tuple packed (elementsLength.trans countEq.symm) frontMatch) backMatch⟩
  | word argument ih =>
      intro rowsTyped values typed
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨word, value_eq⟩ := headTyped.fixed_value catalog
          subst value_eq
          obtain ⟨row', rowMem', bindings, matched⟩ := ih
            (fun row' member => by
              obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp member
              exact coverageWordRow_typed (rowsTyped row rowMem) specialized)
            (.cons (.word word) tailTyped)
          obtain ⟨row, rowMem, specialized⟩ := List.mem_filterMap.mp rowMem'
          cases row with
          | nil => simp [coverageWordRow] at specialized
          | cons instruction rest =>
              cases instruction <;> simp [coverageWordRow] at specialized
              · subst specialized
                cases matched with
                | cons head tail =>
                    cases head
                    exact ⟨_, rowMem, _, .cons .wildcard tail⟩
              · subst specialized
                cases matched with
                | cons head tail =>
                    cases head
                    exact ⟨_, rowMem, _, .cons .binder tail⟩
              · subst specialized
                obtain ⟨middle, frontBindings, backBindings, frontMatch, backMatch, _⟩ :=
                  PatternInstructionsMatch.append_split (front := [.word word]) matched
                exact ⟨_, rowMem, _, .cons (.uint256Word frontMatch) backMatch⟩

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
  | uint256Word => cases right_represents; rfl
  | boolLiteral => cases right_represents; rfl
  | sameNameConstructor => cases right_represents; rfl
  | group _ induction =>
      cases right_represents with
      | group inner => exact induction inner

/-- The root arity a pattern's source represents is the one it spells. -/
theorem rootArity_eq_source {context : Context} {source : MatchPatternSource}
    {resolution : MatchPatternResolution} {rootArity : Nat}
    (represents : MatchPatternSourceRepresents context source resolution rootArity) :
    rootArity = source.rootArity := by
  induction represents with
  | group _ induction => exact induction
  | _ => rfl

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
  | covered rows_cover =>
      have rows_typed : ∀ row, row ∈ (cases.map fun matchCase =>
          matchPatternResolutionInstructions matchCase.pattern.resolution
            matchCase.pattern.source.rootArity) →
          ∃ requirements binders,
            PatternInstructionsHaveTypes context row [scrutineeType] requirements binders [] := by
        intro row member
        rcases List.mem_map.mp member with ⟨matchCase, case_member, rfl⟩
        rcases
            Solcore.SourceSemantics.Dynamic.MatchCasesHaveType.member cases_typed
              case_member with
          ⟨facts, case_typed⟩
        cases case_typed with
        | intro pattern_typed binders_extend body_type =>
            have arity_eq :=
              Solcore.SourceSemantics.Dynamic.MatchPatternSourceRepresents.rootArity_eq_source
                pattern_typed.source_represents
            have resolution_type := pattern_typed.resolution_type
            unfold MatchPatternResolutionHasType at resolution_type
            rw [arity_eq] at resolution_type
            exact ⟨_, _, by
              simpa using PatternInstructionsHaveTypes.cons resolution_type .nil⟩
      rcases RowsCover.complete catalog rows_cover rows_typed (.cons value_typed .nil) with
        ⟨row, member, bindings, matched⟩
      rcases List.mem_map.mp member with ⟨matchCase, case_member, rfl⟩
      rcases
          Solcore.SourceSemantics.Dynamic.MatchCasesHaveType.member cases_typed
            case_member with
        ⟨facts, case_typed⟩
      cases case_typed with
      | intro pattern_typed binders_extend body_type =>
          cases matched with
          | cons head_match tail_match =>
              cases tail_match
              have source_represents := pattern_typed.source_represents
              rw [Solcore.SourceSemantics.Dynamic.MatchPatternSourceRepresents.rootArity_eq_source
                source_represents] at source_represents
              exact selected.excludes_member_match case_member
                (.intro source_represents head_match)

end MatchCasesSelect

end Solcore.SourceSemantics.Dynamic
