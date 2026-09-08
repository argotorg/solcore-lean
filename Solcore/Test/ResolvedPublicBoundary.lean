import Solcore.Resolved

set_option autoImplicit false

namespace Tests

example := @Solcore.Resolved.DeclarationId
example := @Solcore.Resolved.LocalId
example := @Solcore.Resolved.LocalScope
example := @Solcore.Resolved.LocalScope.ids
example := @Solcore.Resolved.LocalScope.values
example := @Solcore.Resolved.LocalScope.lookup?
example := @Solcore.Resolved.LocalScope.index?
example := @Solcore.Resolved.LocalScope.Lookup
example := @Solcore.Resolved.LocalScope.IndexOf
example := @Solcore.Resolved.LocalScope.lookup?_iff
example := @Solcore.Resolved.LocalScope.index?_iff
example := @Solcore.Resolved.LocalScope.Lookup.indexed
example := @Solcore.Resolved.LocalScope.lookup_of_indexed
example := @Solcore.Resolved.LocalScope.index_lookup
example := @Solcore.Resolved.LocalScope.Lookup.value_unique
example := @Solcore.Resolved.LocalScope.IndexOf.index_unique
example := @Solcore.Resolved.LocalScope.lookup_iff_getElem?
example := @Solcore.Resolved.LocalScope.IndexOf.getElem?
example := @Solcore.Resolved.LocalScope.IndexOf.lt_length
example := @Solcore.Resolved.LocalScope.Lookup.mem
example := @Solcore.Resolved.LocalScope.index?_eq_none_iff
example := @Solcore.Resolved.LocalScope.lookup?_eq_none_iff
example := @Solcore.Resolved.LocalScope.ids_length
example := @Solcore.Resolved.LocalScope.values_length
example := @Solcore.Resolved.Expr
example := @Solcore.Resolved.Expr.lower?
example := @Solcore.Resolved.Lowers
example := @Solcore.Resolved.Lowers.complete
example := @Solcore.Resolved.Expr.lower?_sound
example := @Solcore.Resolved.Expr.lower?_iff
example := @Solcore.Resolved.Lowers.deterministic
example := @Solcore.Resolved.Expr.lower?_eq_none_iff
example := @Solcore.Resolved.Context
example := @Solcore.Resolved.HasType
example := @Solcore.Resolved.infer?
example := @Solcore.Resolved.HasType.lowers
example := @Solcore.Resolved.Lowers.reflects_type
example := @Solcore.Resolved.Lowers.preserves_type
example := @Solcore.Resolved.Lowers.typing_iff
example := @Solcore.Resolved.infer_sound
example := @Solcore.Resolved.infer_complete
example := @Solcore.Resolved.typing_iff_infer
example := @Solcore.Resolved.typing_deterministic
example := @Solcore.Resolved.Environment
example := @Solcore.Resolved.Evaluates
example := @Solcore.Resolved.Evaluates.toCore
example := @Solcore.Resolved.Evaluates.ofCore
example := @Solcore.Resolved.Lowers.evaluates_iff
example := @Solcore.Resolved.Evaluates.store_eq
example := @Solcore.Resolved.evaluation_deterministic
example := @Solcore.Resolved.Lowers.run_done_sound
example := @Solcore.Resolved.Evaluates.run_has_sufficient_fuel
example := @Solcore.Resolved.Lowers.evaluates_iff_run_done
example := @Solcore.Resolved.HasType.closed_evaluates
example := @Solcore.Resolved.HasType.closed_run_has_sufficient_fuel
example := @Solcore.Resolved.Lowers.closed_run_never_faults

end Tests
