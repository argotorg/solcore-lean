import Solcore.Frontend

set_option autoImplicit false

namespace Tests

example := @Solcore.Frontend.LocalNameTable
example := @Solcore.Frontend.LocalNameTable.lookup?
example := @Solcore.Frontend.LocalNameTable.Lookup
example := @Solcore.Frontend.resolveLocalReference?
example := @Solcore.Frontend.ResolvesLocalReference
example := @Solcore.Frontend.LocalNameTable.lookup?_iff
example := @Solcore.Frontend.LocalNameTable.Lookup.id_unique
example := @Solcore.Frontend.LocalNameTable.Lookup.mem
example := @Solcore.Frontend.LocalNameTable.lookup?_eq_none_iff
example := @Solcore.Frontend.ResolvesLocalReference.complete
example := @Solcore.Frontend.resolveLocalReference?_sound
example := @Solcore.Frontend.resolveLocalReference?_iff
example := @Solcore.Frontend.resolveLocalReference?_eq_some_iff
example := @Solcore.Frontend.ResolvesLocalReference.id_unique
example := @Solcore.Frontend.ResolvesLocalReference.mem
example := @Solcore.Frontend.resolveLocalReference?_eq_none_iff
example := @Solcore.Frontend.resolveLocalReference?_span
example := @Solcore.Frontend.resolveLocalReference?_identifier_value_eq
example := @Solcore.Frontend.resolveLocalReference?_group
example := @Solcore.Frontend.elaborateLocalReference?
example := @Solcore.Frontend.LocalReferenceHasType
example := @Solcore.Frontend.elaborateLocalReference?_sound
example := @Solcore.Frontend.elaborateLocalReference?_complete
example := @Solcore.Frontend.elaborateLocalReference?_iff
example := @Solcore.Frontend.localReferenceHasType_iff_elaborates
example := @Solcore.Frontend.elaborateLocalReference?_core_hasType
example := @Solcore.Frontend.elaborateLocalReference?_eq_none_of_missing_id
example := @Solcore.Frontend.elaborateLocalReference?_eq_none_iff
example := @Solcore.Frontend.LocalReferenceEvaluates
example := @Solcore.Frontend.LocalReferenceEvaluates.deterministic
example := @Solcore.Frontend.LocalReferenceEvaluates.toCore
example := @Solcore.Frontend.LocalReferenceEvaluates.exact_run
example := @Solcore.Frontend.elaborateLocalReference?_evaluates_iff
example := @Solcore.Frontend.LocalReferenceHasType.evaluates
example := @Solcore.Frontend.LocalReferenceEvaluates.preserves_type
example := @Solcore.Frontend.elaborateLocalReference?_exact_run
example := @Solcore.Frontend.elaborateLocalReference?_typed_execution

end Tests
