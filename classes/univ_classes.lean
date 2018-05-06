/-
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Jipsen
Names based on http://math.chapman.edu/~jipsen/structures/doku.php
-/

import init.logic init.algebra.classes
universe u
set_option default_priority 100
set_option old_structure_cmd true

variables {α: Type u}(f:α→α → α)
--local infix  ⊕  := f

--Magmas (= binars = groupoids)

class Mag(α:Type u) := (o:α→α → α)
infix ⬝ := Mag.o

--variables {α :Type u} 
variables [Mag α ] --(a b : α) 
variables a b : α

#check Mag.o a b

--Semigroups
class Sgrp(α:Type u) extends Mag α := (asso: ∀x y z: α, x⬝y⬝z = x⬝(y⬝z))

@[simp] lemma assoc [Sgrp α]: ∀x y z:α, x⬝y⬝z = x⬝(y⬝z) := Sgrp.asso
instance Sgrp_to_is_associative [Sgrp α] : is_associative α (⬝) := ⟨assoc⟩

#check Sgrp_to_is_associative

--Commutative semigroups
class CSgrp(α: Type u) extends Sgrp α := (comm: ∀x y:α, x⬝y = y⬝x)

@[simp] lemma comm [CSgrp α]: ∀x y:α, x⬝y = y⬝x := CSgrp.comm
instance CSgrp_to_is_commutative [CSgrp α] : is_commutative α (⬝) := ⟨comm⟩

--Bands (= idempotent semigroups)
class Band(α:Type u) extends Sgrp α := (idem: ∀ x:α, x⬝x = x)

--Semilattices
class Slat(α:Type u) extends Band α :=
(comm: ∀x y:α, x⬝y = y⬝x)
-- use coersion to tell Lean that every Slat is an idempotent CSgrp

--Double magmas
class DMag(α:Type u) := (o₁:α→α → α)(o₂:α→α → α)
local infix ∧ :65 := DMag.o₁
local infix ∨ :65 := DMag.o₂

--Lattices
class Lat(α:Type u) extends DMag α:=
(asso₁: ∀x y z: α, (x∧y)∧z = x∧(y∧z))(asso₂: ∀x y z: α, (x∨y)∨z = x∨(y∨z))
(comm₁: ∀x y:α, x∧y = y∧x)           (comm₂: ∀x y:α, x∨y = y∨x)
(abso₁: ∀x y:α, (x∧y)∨x = x)         (abso₂: ∀x y:α, (x∨y)∧x = x)

--Monoids
class Mon(α:Type u) extends Sgrp α := (e:α)
(l_id: ∀x:α, e⬝x = x) (r_id: ∀x:α, x⬝e = x)

--Commutative monoids
class CMon(α:Type u) extends Sgrp α := (e:α)
(l_id: ∀x:α, e⬝x = x)
(comm: ∀x y:α, x⬝y = y⬝x)

--Magmas with unary operation
class Mag₁(α:Type u) extends Mag α := (i:α → α)
postfix ⁻¹ := Mag₁.i

--Commutative magmas
class CMag(α:Type u) := (p:α→α → α)
(comm: ∀x y:α, p x y = p y x)
local infix ⊕ :65 := CMag.p

--Commutative magmas with unary operation
class CMag₁(α:Type u) extends CMag α := (n:α → α)(d:α)
prefix ¬   := CMag₁.n



--MV-algebras
class MValg(α:Type u) extends CMag₁ α :=
(dneg: ∀x:α, ¬¬x = x)
(l_id: ∀x:α, x⊕d = x)
(meet: ∀x y:α, ¬(¬x⊕y)⊕y = ¬(¬y⊕x)⊕x)
#print MValg

--Groups
class Grp(α:Type u) extends Mag₁ α := (e:α)
(asso:  ∀x y z: α, x⬝y⬝z = x⬝(y⬝z))
(l_id:  ∀x:α, e⬝x = x)
(l_inv: ∀x:α, x⁻¹⬝x = e)


-- Some small models

inductive M₂: Type | e:M₂ | a:M₂
export M₂ (e a)
namespace M₂            -- 2-elt idempotent monoid
  def cdot:  M₂→M₂ → M₂ | e x := x  | x e := x | a a := a
  instance: Mag M₂ := ⟨cdot⟩
#check Mag.o
  lemma asso (x y z:M₂): (x⬝y)⬝z = x⬝(y⬝z) :=  by cases x; cases y; cases z; refl
  instance: Sgrp M₂ := ⟨(⬝), asso⟩
  lemma idem (x:M₂): x⬝x = x := by cases x; refl
  instance: Band M₂ := ⟨(⬝), asso, idem⟩
  lemma comm (x y:M₂): x⬝y = y⬝x :=  by cases x; cases y; refl
  instance: Slat M₂ := ⟨(⬝), asso, idem, comm⟩
  lemma l_id (x:M₂): e⬝x = x := by cases x; refl
  lemma r_id (x:M₂): x⬝e = x := by cases x; refl
  instance: Mon M₂ := ⟨(⬝), asso, e, l_id, r_id⟩

#check M₂ 
variables c d : M₂ 
#reduce M₂.cdot M₂.a M₂.a
#print classes
end M₂



inductive Z₃: Type | e:Z₃ | a:Z₃ | b:Z₃
export Z₃ (e a b)
namespace Z₃            -- 3-elt group
  def cdot:  Z₃→Z₃ → Z₃ | e x := x | x e := x
                        | a a := b | a b := e
                        | b a := e | b b := a
  def inv:  Z₃→ Z₃ | e := e | a := b | b := a
  instance: Mag₁ Z₃ := ⟨cdot, inv⟩
  lemma asso (x y z:Z₃): (x⬝y)⬝z = x⬝(y⬝z) :=  by cases x; cases y; cases z; refl
  lemma l_id (x:Z₃): e⬝x = x := by cases x; refl
  lemma l_inv (x:Z₃): x⁻¹⬝x = e := by cases x; refl
  instance: Grp Z₃ := ⟨(⬝), inv, e, asso, l_id, l_inv⟩
end Z₃

variable x:int



/-
variables (f g o:α→α → α)(h k:α → α)(d e:α)(R S:α→α → Prop)
local infix `⬝`:70  := o
local notation x+y := f x y
local notation x⊕y := g x y
local notation x\y := f x y
local notation x/y := g x y
local notation x⁻¹ := h x
local notation ¬x  := h x
local notation 1   := e
local notation 0   := d
local notation x≤y := R x y
local infix `≺`:50 := R

def involutive            := ∀x,     h(h x) = x
def inverse_ops           := ∀x,     h(k x) = x
def l_unary_absorption    := ∀x,     h(k x) = k x
def r_unary_absorption    := ∀x,     h(k x) = h x
def unary_idempotent      := ∀x,     h(h x) = h x
def idempotent            := ∀x,     x⬝x = x
def l_identity            := ∀x,     1⬝x = x
def r_identity            := ∀x,     x⬝1 = x
def l_zero                := ∀x,     0⬝x = 0
def r_zero                := ∀x,     x⬝0 = 0
def l_inverse             := ∀x,     x⁻¹⬝x = 1
def r_inverse             := ∀x,     x⬝x⁻¹ = 1
def l_const_mult          := ∀x,     c⬝x = h x
def r_const_mult          := ∀x,     x⬝c = h x
def square_constant       := ∀x,     x⬝x = c
def square_unary          := ∀x,     x⬝x = h x
def l_unary_identity      := ∀x,     (h x)⬝x = x
def r_unary_identity      := ∀x,     x⬝(h x) = x
def l_unary_const_mult    := ∀x,     h(c⬝x) = c⬝(h x)
def r_unary_const_mult    := ∀x,     h(x⬝c) = (h x)⬝c

--def commutative           := ∀x y,   x⬝y = y⬝x  defined in logic.lean
def l_unary_projection    := ∀x y,   x⬝y = h x
def r_unary_projection    := ∀x y,   x⬝y = h y
def l_idempotent          := ∀x y,   x⬝(x⬝y) = x⬝y
def r_idempotent          := ∀x y,   (x⬝y)⬝y = x⬝y
def l_idempotent'         := ∀x y,   x⬝(y⬝x) = x⬝y
def r_idempotent'         := ∀x y,   (x⬝y)⬝x = x⬝y
def l_rectangular         := ∀x y,   (x⬝y)⬝x = x
def r_rectangular         := ∀x y,   x⬝(y⬝x) = x
def absorption            := ∀x y,   (x⬝y)+x = x
def absorption'           := ∀x y,   x+(y⬝x) = x
def l_division            := ∀x y,   x⬝(x\y) = y
def r_division            := ∀x y,   (x/y)⬝y = x
def l_division'           := ∀x y,   x\(x⬝y) = y
def r_division'           := ∀x y,   (x⬝y)/y = x
def unary_commutative     := ∀x y,   (h x)⬝(h y) = (h y)⬝(h x)
def unary_involutive      := ∀x y,   h(x⬝y) = (h y)⬝(h x)
def interdistributive     := ∀x y,   h(x⬝y) = (h x)+(h y)
def unary_distributive    := ∀x y,   h(x⬝y) = (h x)⬝(h y) 
def l_twisted             := ∀x y,   (h(x⬝y))⬝x = x⬝(h y) 
def r_twisted             := ∀x y,   x⬝(h(y⬝x)) = (h y)⬝x
def l_locality            := ∀x y,   h((h x)⬝y) = h(x⬝y)
def r_locality            := ∀x y,   h(x⬝(h y)) = h(x⬝y)
def l_unary_distributive  := ∀x y,   h((h x)⬝y) = (h x)⬝(h y)
def r_unary_distributive  := ∀x y,   h(x⬝(h y)) = (h x)⬝(h y)
def l_absorbtive          := ∀x y,   (h x)⬝(h(x⬝y)) = h(x⬝y)
def r_absorbtive          := ∀x y,   (h(x⬝y))⬝(h y) = h(x⬝y)
def flexible              := ∀x y,   (x⬝y)⬝x = x⬝(y⬝x)

--def associative           := ∀x y z, x⬝(y⬝z) = (x⬝y)⬝z  defined in logic.lean
def l_commutative         := ∀x y z, x⬝(y⬝z) = y⬝(x⬝z)
def r_commutative         := ∀x y z, (x⬝y)⬝z = (x⬝z)⬝y
def interassociative1     := ∀x y z, x⬝(y+z) = (x⬝y)+z
def interassociative2     := ∀x y z, x⬝(y+z) = (x+y)⬝z
def l_distributive        := ∀x y z, x⬝(y+z) = (x⬝y)+(x⬝z)
def r_distributive        := ∀x y z, (x+y)⬝z = (x⬝z)+(y⬝z)
def l_self_distributive   := ∀x y z, x⬝(y⬝z) = (x⬝y)⬝(x⬝z)
def r_self_distributive   := ∀x y z, (x⬝y)⬝z = (x⬝z)⬝(y⬝z)
def directoid_absorption  := ∀x y z, x⬝((x⬝y)⬝z) = (x⬝y)⬝z
def directoid_absorbtion' := ∀x y z, (x⬝(y⬝z))⬝z = x⬝(y⬝z)
def Moufang1              := ∀x y z, ((x⬝y)⬝x)⬝z = x⬝(y⬝(x⬝z))
def Moufang2              := ∀x y z, ((x⬝y)⬝z)⬝y = x⬝(y⬝(z⬝y))
def Moufang3              := ∀x y z, (x⬝y)⬝(z⬝x) = (x⬝(y⬝z))⬝x
def Moufang4              := ∀x y z, (x⬝y)⬝(z⬝x) = x⬝((y⬝z)⬝x)
def l_cancelative         := ∀x y z, x⬝y = x⬝z → y = z
def r_cancelative         := ∀x y z, x⬝y = z⬝y → x = z
-/

