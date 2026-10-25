import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Source.InputEmitter
import Solcore.Synthesis.Source.Cases
import Solcore.Synthesis.Source.InputCases
import Solcore.Synthesis.Source.FunctionEmitter
import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationEmitter
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateEmitter
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopEmitter
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.GenericEmitter
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureEmitter
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeEmitter
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleEmitter
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.StorageEmitter
import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.StorageRollbackEmitter
import Solcore.Synthesis.Source.StorageRollbackCases
import Solcore.Synthesis.Source.NestedCallEmitter
import Solcore.Synthesis.Source.NestedCallCases

/-! Checked Core cases, deterministic Solcore source emission and replay. -/
