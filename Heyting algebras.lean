/-Heyting algebras display calculus proofs in Lean -- Peter Jipsen -- April 30, 2018-/

set_option default_priority 100
set_option old_structure_cmd true

universe u
variables {α: Type u}

class has_join (α : Type u) := (join : α → α → α)
infix `⊔` : 65 := has_join.join
class has_meet (α : Type u) := (meet : α → α → α)
infix `⊓` : 65 := has_meet.meet

class Lattice (α : Type u) extends partial_order α, has_join α, has_meet α :=
(join_l : ∀ x y z:α, x ≤ z /\ y ≤ z → x⊔y ≤ z)
(join_r1 : ∀ x y z:α, x ≤ y → x ≤ y⊔z)
(join_r2 : ∀ x y z:α, x ≤ z → x ≤ y⊔z)
(meet_l1 : ∀ x y z:α, x ≤ z → x⊓y ≤ z)
(meet_l2 : ∀ x y z:α, y ≤ z → x⊓y ≤ z)
(meet_r : ∀ x y z:α, x ≤ y /\ x ≤ z → x ≤ y⊓z)

class has_impl (α : Type u) := (impl : α → α → α)
infix `→` : 65 := has_impl.impl

class Heyting_algebra α extends Lattice α, has_impl α :=
(meet_res : ∀x y z:α, x ⊓ y ≤ z -> y ≤ x → z)
(res_meet : ∀x y z:α, y ≤ x → z -> x ⊓ y ≤ z)

open Heyting_algebra

lemma HA_distributive [Heyting_algebra α]: ∀x y z:α, x⊓(y ⊔ z) ≤ (x⊓y) ⊔ (x⊓z) :=
assume x y z,
have h1: x⊓y ≤ (x⊓y) ⊔ (x⊓z),         from join_r1 _ _ _ (Lattice.le_refl _),
have h2: y ≤ x → ((x⊓y) ⊔ (x⊓z)),     from meet_res _ _ _ h1,
have h3: x⊓z ≤ (x⊓y) ⊔ (x⊓z),         from join_r2 _ _ _ (Lattice.le_refl _),
have h4: z ≤ x → ((x⊓y) ⊔ (x⊓z)),     from meet_res _ _ _ h3,
have h5: y ⊔ z ≤ x → ((x⊓y) ⊔ (x⊓z)), from join_l _ _ _ (and.intro h2 h4),
show x⊓(y ⊔ z) ≤ (x⊓y) ⊔ (x⊓z),       from res_meet _ _ _ h5

lemma HA_distributive1 [Heyting_algebra α]: ∀x y z:α, x⊓(y ⊔ z) ≤ (x⊓y) ⊔ (x⊓z) :=
assume x y z,
begin
apply res_meet,
apply join_l,
apply and.intro,
apply meet_res,
apply join_r1,
apply Lattice.le_refl,
apply meet_res,
apply join_r2,
apply Lattice.le_refl,
end

#print classes
