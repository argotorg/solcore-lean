import Solcore.ContractRuntime

/-!
Deprecated import-only compatibility umbrella. New code must import
`Solcore.ContractRuntime`. The former `Solcore.Semantics.*` submodules and
namespace are intentionally not retained.
-/

deprecated_module "use `Solcore.ContractRuntime` instead" (since := "2026-09-23")
