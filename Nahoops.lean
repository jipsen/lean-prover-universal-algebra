--Right nonassociative hoops in Lean
--Author: Peter Jipsen

set_option old_structure_cmd true

universe u
variables {α: Type u}
reserve infix ` ≼ `:50
class has_pre (α : Type u) := (pre : α → α → Prop)
infix ≼ := has_pre.pre

reserve infix ` ∧ ` : 60
class has_qmt (α: Type u) := (qmt : α → α → α)
infix ∧ := has_qmt.qmt
--local notation x ∧ y := (x/y)*y

-- Right residuated magmas
class RResMag(α: Type u) extends 
has_mul α, has_div α, partial_order α, has_qmt α, has_pre α :=
(rres: ∀x y z:α, x*y ≤ z ↔ x ≤ z/y)
(qmt1: ∀x y:α,   (x ∧ y) = (x/y)*y)
(pre1: ∀x y:α,   x ≼ y ↔ x ∧ y = x)

lemma rres [RResMag α]: ∀x y z:α, x*y ≤ z ↔ x ≤ z/y := RResMag.rres

lemma qmt [RResMag α]: ∀x y:α, (x ∧ y) = (x/y)*y := RResMag.qmt1

@[simp] lemma L1_2L [RResMag α]: ∀x y:α, x/y*y ≤ x :=
assume x y:α,
have h: x/y ≤ x/y, from le_refl (x/y),
show    x/y*y ≤ x, from iff.mpr (rres (x/y) y x) h

lemma L1_2R [RResMag α]: ∀x y:α, x ≤ (x*y)/y :=
assume x y:α,
have h: x*y ≤ x*y, from le_refl (x*y),
show    x ≤ x*y/y, from iff.mp (rres x y (x*y)) h

lemma L1_3 [RResMag α]: ∀x y z:α, x ≤ y → x*z ≤ y*z :=
assume x y z:α,
  (assume h₀: x ≤ y,
     have h₁: y ≤ y*z/z, from L1_2R y z,
     have h₂: x ≤ y*z/z, from le_trans h₀ h₁,
     show   x*z ≤ y*z,   from iff.mpr (rres x z (y*z)) h₂)

lemma L1_4 [RResMag α]: ∀x y z:α, x ≤ y → x/z ≤ y/z :=
assume x y z:α,
  (assume h₀:       x ≤ y,
     have h₁: (x/z)*z ≤ x,   from L1_2L x z,
     have h₂: (x/z)*z ≤ y,   from le_trans h₁ h₀,
     show         x/z ≤ y/z, from iff.mp (rres (x/z) z y) h₂)

class RResMagEq(α: Type u) extends has_mul α, has_div α, partial_order α :=
(E1_2L: ∀x y:α, x/y*y ≤ x)
(E1_2R: ∀x y:α, x ≤ x*y/y)
(E1_3:  ∀x y z:α, x ≤ y → x*z ≤ y*z)
(E1_4:  ∀x y z:α, x ≤ y → x/z ≤ y/z)

lemma eqrres [RResMagEq α]: ∀x y z:α, x*y ≤ z ↔ x ≤ z/y :=
assume x y z:α,
  (iff.intro
    (assume h:   x*y ≤ z,
      have h1: x*y/y ≤ z/y, from (RResMagEq.E1_4 (x*y) z y) h, 
      show         x ≤ z/y, from le_trans (RResMagEq.E1_2R x y) h1)
    (assume h:     x ≤ z/y,
      have h1:   x*y ≤ (z/y)*y, from (RResMagEq.E1_3 x (z/y) y) h, 
      show       x*y ≤ z,       from le_trans h1 (RResMagEq.E1_2L z y)))

lemma L1_5 [RResMag α]: ∀x y:α, (x*y/y)*y = x*y :=
assume x y:α,
have h₁: (x*y/y)*y ≤ x*y, from L1_2L (x*y) y,
have h₂: x ≤ x*y/y,       from L1_2R x y,
have h₃: x*y ≤ (x*y/y)*y, from (L1_3 x (x*y/y) y) h₂,
show     (x*y/y)*y = x*y, from le_antisymm h₁ h₃

lemma L1_6 [RResMag α]: ∀x y:α, (x/y)*y/y = x/y :=
assume x y:α,
have h₁: x/y ≤ (x/y)*y/y, from L1_2R (x/y) y,
have h₂: x/y*y ≤ x,       from L1_2L x y,
have h₃: (x/y)*y/y ≤ x/y, from (L1_4 (x/y*y) x y) h₂,
show     (x/y)*y/y = x/y, from le_antisymm h₃ h₁

lemma L1_8 [RResMag α]: ∀x y:α, x*y ∧ y = x*y := 
assume x y:α,
calc
  x*y ∧ y = x*y/y*y : by rw qmt
      ... = x*y     : by rw L1_5

lemma L1_9 [RResMag α]: ∀x y:α, (x ∧ y)/y = x/y :=
assume x y:α,
calc
  (x ∧ y)/y = x/y*y/y : by rw qmt
        ... = x/y     : by rw L1_6

lemma L1_10 [RResMag α]: ∀x y:α, x ∧ y ≤ x := 
assume x y:α,
have h: x/y*y ≤ x, from L1_2L x y,
show x ∧ y ≤ x, from (qmt x y).symm ▸ h

lemma L1_11 [RResMag α]:  ∀x y z:α, x ∧ y ≤ z ↔ x/y ≤ z/y :=
assume x y z:α,
have h: x/y*y ≤ z ↔ x/y ≤ z/y, from rres (x/y) y z,
show  x ∧ y ≤ z ↔ x/y ≤ z/y, from (qmt x y).symm ▸ h

lemma L1_12 [RResMag α]:  ∀x y z:α, x ≤ y → x ∧ z ≤ y ∧ z :=
assume x y z:α,
  (assume h₀: x ≤ y,
     have h₁: x/z ≤ y/z, from (L1_4 x y z) h₀,
     have h₂: x/z*z ≤ y/z*z, from (L1_3(x/z)(y/z)z) h₁,
     have h₃: x ∧ z ≤ y/z*z, from (qmt x z).symm ▸ h₂,
     show     x ∧ z ≤ y ∧ z, from (qmt y z).symm ▸ h₃)

class PreMag (α: Type u) extends RResMag α :=
(refl: ∀x:α, x≼x) 
(tran: ∀x y z:α, x≼y → y≼z → x≼z)

class Dtoid (α: Type u) extends has_mul α, has_div α, has_pre α, has_qmt α:=
(pre1: ∀x y:α,   x ≼ y ↔ x ∧ y = x)
(idem: ∀x:α, x ∧ x = x)
(dass: ∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))

lemma dass [Dtoid α]: ∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z) := Dtoid.dass

lemma L1_13 [PreMag α]:  ∀x y:α, x ≼ y ↔ x ∧ y = x := PreMag.pre1

lemma L1_14 [PreMag α]:  ∀x y:α, x*y ≼ y := 
assume x y:α,
have h: x*y ∧ y = x*y, from L1_8 x y,
show  x*y ≼ y, from iff.mpr (L1_13 (x*y) y) h

lemma L1_15 [PreMag α]:  ∀x y:α, x ∧ y ≼ y :=
assume x y:α,
have h: x/y*y ≼ y, from L1_14 (x/y) y,
show x ∧ y ≼ y, from (qmt x y).symm ▸ h

lemma L1a [PreMag α]: ∀x:α, x ∧ x = x :=
assume x:α,
have h: x≼x, from PreMag.refl x,
show x ∧ x = x, from iff.mp (PreMag.pre1 x x) h

lemma L1b [PreMag α]: ∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z) :=
assume x y z:α,
have h₁: x/(y/z*z)*(y/z*z) ≼ y/z*z, from L1_14 (x/(y/z*z)) (y/z*z),
have h₂: y/z*z ≼ z, from L1_14 (y/z) z,
have h₃: x/(y/z*z)*(y/z*z) ≼ z, 
                       from (PreMag.tran (x/(y/z*z)*(y/z*z)) (y/z*z) z) h₁ h₂,
have h₄: x/(y ∧ z)*(y ∧ z) ≼ z, from (qmt y z).symm ▸ h₃,
have h₅: x ∧ (y ∧ z) ≼ z, from (qmt x (y ∧ z)).symm ▸ h₄,
show (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z), 
                       from iff.mp (PreMag.pre1 (x ∧ (y ∧ z)) z) h₅

lemma L1c [Dtoid α]: ∀x:α, x ≼ x := 
assume x:α,
have h: x ∧ x = x, from Dtoid.idem x,
show x ≼ x, from iff.mpr (Dtoid.pre1 x x) h

lemma L1d [Dtoid α]: ∀x y z:α, x ≼ y → y ≼ z → x ≼ z := 
assume x y z:α,
  (assume h₀: x ≼ y,
    (assume h₁: y ≼ z,
     have h₂: x ∧ y = x, from iff.mp (Dtoid.pre1 x y) h₀,
     have h₃: y ∧ z = y, from iff.mp (Dtoid.pre1 y z) h₁,
     have h₄: x ∧ z = x, from 
     calc
       x ∧ z = (x ∧ y) ∧ z : by rw h₂
         ... = (x ∧ (y ∧ z)) ∧ z : by rw h₃
         ... = x ∧ (y ∧ z)       : by rw dass
         ... = x ∧ y             : by rw h₃
         ... = x                 : by rw h₂,
     show x ≼ z, from iff.mpr (Dtoid.pre1 x z) h₄))

lemma L2a [RResMag α]:
(∀x y:α, x ≤ y → x ≼ y) → (∀x y:α, (x ∧ y) ∧ x = x ∧ y) :=
--Proof:
assume h: (∀x y:α, x ≤ y → x ≼ y),
  (assume x y:α,
     have h: x ∧ y ≼ x, from (h (x ∧ y) x) (L1_10 x y),
     show (x ∧ y) ∧ x = x ∧ y, from iff.mp (RResMag.pre1 (x ∧ y) x) h)

lemma L2b [RResMag α]: (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y) 
→ (∀x y z:α, (x ∧ y) ∧ z = (x ∧ z) ∧ y) := 
assume h: (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y),
  (assume x y z:α,
    have h₁: (x ∧ y) ∧ z = ((x ∧ y) ∧ z) ∧ y, from calc
      (x ∧ y) ∧ z = ((x ∧ y) ∧ z) ∧ (x ∧ y)       : by rw L2a h.2
              ... = (((x ∧ y) ∧ z) ∧ (x ∧ y)) ∧ y : by rw (h.1)
              ... = ((x ∧ y) ∧ z) ∧ y             : by rw L2a h.2,
    have h₂: (x ∧ y) ∧ z ≤ x ∧ z, from (L1_12 (x ∧ y) x z) (L1_10 x y),
    have h₃: ((x ∧ y) ∧ z) ∧ y ≤ (x ∧ z) ∧ y, from (L1_12 ((x∧y)∧z) (x∧z) y) h₂,
    have h₄: ((x ∧ y) ∧ z) ≤ (x ∧ z) ∧ y, from h₁.symm ▸ h₃,

    have h₅: (x ∧ z) ∧ y = ((x ∧ z) ∧ y) ∧ z, from calc
      (x ∧ z) ∧ y = ((x ∧ z) ∧ y) ∧ (x ∧ z)       : by rw L2a h.2
              ... = (((x ∧ z) ∧ y) ∧ (x ∧ z)) ∧ z : by rw (h.1)
              ... = ((x ∧ z) ∧ y) ∧ z             : by rw L2a h.2,
    have h₆: (x ∧ z) ∧ y ≤ x ∧ y, from (L1_12 (x ∧ z) x y) (L1_10 x z),
    have h₇: ((x ∧ z) ∧ y) ∧ z ≤ (x ∧ y) ∧ z, from (L1_12 ((x∧z)∧y) (x∧y) z) h₆,
    have h₈: ((x ∧ z) ∧ y) ≤ (x ∧ y) ∧ z, from h₅.symm ▸ h₇,
    show (x ∧ y) ∧ z = (x ∧ z) ∧ y, from le_antisymm h₄ h₈)

variables (R: α→α → Prop)

lemma L3_1 [RResMag α]: (∀x:α, x ∧ x = x)
/\ (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y)
/\ (∀x y:α, R x y ↔ x = y ∧ x)
→ (∀x y:α, R x y → x ≤ y) := 
assume h: (∀x:α, x ∧ x = x)
/\ (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y)
/\ (∀x y:α, R x y ↔ x = y ∧ x),
assume x y:α,
assume h₀: R x y,
have h₁: x = y ∧ x, from iff.mp (h.2.2.2 x y) h₀,
show x ≤ y, from h₁.symm ▸ (L1_10 y x)

#print L3_1 

lemma L3_2 [RResMag α]: (∀x:α, x ∧ x = x)
/\ (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y)
/\ (∀x y:α, R x y ↔ x = y ∧ x)
→ (∀x y:α, R x y ↔ y/x = x/x) := 
assume h: (∀x:α, x ∧ x = x)
/\ (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y)
/\ (∀x y:α, R x y ↔ x = y ∧ x),
assume x y:α,
iff.intro
  (assume h₀: R x y,
  have x = y ∧ x, from iff.mp (h.2.2.2 x y) (by assumption),
  have x = y/x*x, from (RResMag.qmt1 y x) ▸ this,
  have y/x*x ≤ x, from le_of_eq this.symm,
  have y/x ≤ x/x, from iff.mp (rres (y/x) x x) this,
  have x ≤ y,     from L3_1 R h x y h₀, 
  have x ∧ x ≤ y, from (h.1 x).symm ▸ this,
  have x/x*x ≤ y, from (RResMag.qmt1 x x) ▸ this,
  have x/x ≤ y/x, from iff.mp (rres (x/x) x y) this,
  show y/x = x/x, from le_antisymm (by assumption) this)
  (assume h₀: y/x = x/x,
  have y/x*x = x/x*x, by rw h₀,
  have y/x*x = x ∧ x, from (RResMag.qmt1 x x).symm ▸ this,
  have y ∧ x = x ∧ x, from (RResMag.qmt1 y x).symm ▸ this,
  have y ∧ x = x, from eq.trans this (h.1 x),
  show R x y,     from iff.mpr (h.2.2.2 x y) this.symm)

lemma L3_3 [RResMag α]: (∀x:α, x ∧ x = x)
/\ (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y)
/\ (∀x y:α, R x y ↔ x = y ∧ x)
→ (∀x y z:α, R x y → R y z → R x z) := 
assume h: (∀x:α, x ∧ x = x)
/\ (∀x y z:α, (x ∧ (y ∧ z)) ∧ z = x ∧ (y ∧ z))
/\ (∀x y:α, x ≤ y → x ≼ y)
/\ (∀x y:α, R x y ↔ x = y ∧ x),
assume x y z:α,
assume h₀: R x y,
assume h₁: R y z,
have x ≤ y, from L3_1 R h x y h₀, 
have x ≼ y, from (h.2.2.1 x y) this,
have h₂: x ∧ y = x, from iff.mp (RResMag.pre1 x y) this,
have h₃: z ∧ y = y, from (iff.mp (h.2.2.2 y z) h₁).symm,
have h₄: y ∧ x = x, from (iff.mp (h.2.2.2 x y) h₀).symm,
have h₅: z ∧ x = x, from calc
  z ∧ x = z ∧ (x ∧ y) : by rw h₂
    ... = (z ∧ (x ∧ y)) ∧ y : by rw h.2.1
    ... = (z ∧ x) ∧ y : by rw h₂
    ... = (z ∧ y) ∧ x : by rw L2b (and.intro h.2.1 h.2.2.1)
    ... = y ∧ x       : by rw h₃
    ... = x           : by rw h₄,
show R x z, from iff.mpr (h.2.2.2 x z) h₅.symm
