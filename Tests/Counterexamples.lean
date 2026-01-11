import Paco

/-!
# Counterexample Coverage

This file checks that `PRespectful` alone does not yield `Compatible'`.
The test fails if a global instance or lemma makes the implication automatic.
-/

namespace Paco.Tests.Counterexamples

open Paco

variable {α : Type}

/-- The plain implication `PRespectful → Compatible'` should not be derivable. -/
example (F : MonoRel α) (clo : Rel α → Rel α) : True := by
  have _ := F ⊥
  have _ := clo
  fail_if_success
    exact (fun h => prespect_compatible'_tagged (F := F) (clo := clo) h)
  trivial

end Paco.Tests.Counterexamples
