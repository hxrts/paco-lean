import Paco.Basic
import Paco.Companion
import Paco.Compat
import Paco.GPaco
import Paco.Tactic
import Paco.UpTo
import Paco.Coind

/-!
# Deprecated names

`gpaco_clo` and `gupaco_clo` were renamed to `gpacoClo` and `gupacoClo` to follow
Mathlib's naming convention (definitions are lowerCamelCase), and lemmas about
them were renamed to match. The old names remain as deprecated aliases.
-/

namespace Paco

@[deprecated clo_le_gupacoClo (since := "2026-10-28")] alias clo_le_gupaco_clo := clo_le_gupacoClo
@[nolint defsWithUnderscore, deprecated gpacoClo (since := "2026-10-28")] alias gpaco_clo := gpacoClo
@[deprecated gpacoClo_cofix (since := "2026-10-28")] alias gpaco_clo_cofix := gpacoClo_cofix
@[deprecated gpacoClo_coind (since := "2026-10-28")] alias gpaco_clo_coind := gpacoClo_coind
@[deprecated gpacoClo_coind' (since := "2026-10-28")] alias gpaco_clo_coind' := gpacoClo_coind'
@[deprecated gpacoClo_def (since := "2026-10-28")] alias gpaco_clo_def := gpacoClo_def
@[deprecated gpacoClo_final (since := "2026-10-28")] alias gpaco_clo_final := gpacoClo_final
@[deprecated gpacoClo_gupaco (since := "2026-10-28")] alias gpaco_clo_gupaco := gpacoClo_gupaco
@[deprecated gpacoClo_gupaco_cpn (since := "2026-10-28")] alias gpaco_clo_gupaco_cpn := gpacoClo_gupaco_cpn
@[deprecated gpacoClo_id (since := "2026-10-28")] alias gpaco_clo_id := gpacoClo_id
@[deprecated gpacoClo_mon (since := "2026-10-28")] alias gpaco_clo_mon := gpacoClo_mon
@[deprecated gpacoClo_mon_r (since := "2026-10-28")] alias gpaco_clo_mon_r := gpacoClo_mon_r
@[deprecated gpacoClo_mon_rg (since := "2026-10-28")] alias gpaco_clo_mon_rg := gpacoClo_mon_rg
@[deprecated gpacoClo_mult (since := "2026-10-28")] alias gpaco_clo_mult := gpacoClo_mult
@[nolint defsWithUnderscore, deprecated gupacoClo (since := "2026-10-28")] alias gupaco_clo := gupacoClo
@[deprecated gupacoClo_cloMono (since := "2026-10-28")] alias gupaco_clo_cloMono := gupacoClo_cloMono
@[deprecated gupacoClo_def (since := "2026-10-28")] alias gupaco_clo_def := gupacoClo_def
@[deprecated gupacoClo_mono_clo (since := "2026-10-28")] alias gupaco_clo_mono_clo := gupacoClo_mono_clo
@[deprecated paco_le_gpacoClo (since := "2026-10-28")] alias paco_le_gpaco_clo := paco_le_gpacoClo
@[deprecated r_le_gpacoClo (since := "2026-10-28")] alias r_le_gpaco_clo := r_le_gpacoClo
@[deprecated rclo_gpacoClo_le (since := "2026-10-28")] alias rclo_gpaco_clo_le := rclo_gpacoClo_le

end Paco
