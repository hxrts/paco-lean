/-!
# Mutual Inductive Sanity Test

A lightweight mutual recursion test to ensure the environment supports
mutual inductive definitions and recursion.
-/

mutual
  inductive MyA : Type
  | mk : MyB → MyA

  inductive MyB : Type
  | nil : MyB
  | cons : MyA → MyB → MyB
end

mutual
  def sizeA : MyA → Nat
  | MyA.mk b => sizeB b

  def sizeB : MyB → Nat
  | MyB.nil => 0
  | MyB.cons a b => sizeA a + sizeB b + 1
end

example : sizeB MyB.nil = 0 := rfl

example (a : MyA) : sizeA a = sizeB (match a with | MyA.mk b => b) := by
  cases a
  rfl
