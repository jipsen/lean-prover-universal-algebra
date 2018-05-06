/-
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Jipsen
Names based on http://math.chapman.edu/~jipsen/structures/doku.php
-/

import init.logic .identities
universes u

class Mag {α:Type u}(o:α→α → α)                         --Magmas (=Binars)

class Sgrp{α:Type u}(o:α→α → α) :=                      --Semigroups
(asso: associative o)

lemma asso_sgrp {α : Type}{o:α→α → α}{e:α} [Sgrp o]:  --sgrps are associative
    ∀a b c:α, o(o a b)c = o a(o b c) := Sgrp.asso o

class CSgrp{α:Type u}(o:α→α → α) extends Sgrp o :=      --Commutative semigroups
(comm: commutative o)

class Band {α:Type u}(m:α→α → α) extends Sgrp m :=      --Bands
(idem: idempotent m)

class Slat {α:Type u}(m:α→α → α) extends Band m :=      --Semiattices
(comm: commutative m)
-- use coersion to tell Lean that every Slat is an idempotent CSgrp

class Lat {α:Type u}(j:α→α → α)(m:α→α → α) :=           --Lattices
(asso_j: associative j)(asso_m: associative m)
(comm_j: commutative j)(comm_m: commutative m)
(abs_jm: absorption j m)(abs_mj: absorption m j)

class Mon {α:Type u}(o:α→α → α)(e:α) extends Sgrp o :=  --Monoids
(id_l: identity_l o e)
(id_r: identity_r o e)

lemma asso {α : Type}{o:α→α → α}{e:α} [Mon o e]:  -- monoids are associative
    ∀a b c:α, o(o a b)c = o a(o b c) := Sgrp.asso o

class CMon {α:Type u}(o:α→α → α)(e:α) extends Mon o e :=--Commutative monoids
(comm: commutative o)

--class MValg {α:Type u}(o:α→α → α)(i:α → α)(e:α) extends Sgrp o := --MV-algebras


class Grp {α:Type u}(o:α→α → α)(i:α → α)(e:α) extends Sgrp o := --Groups
(id_l : identity_l o e)
(inv_l: inverse_r o i e)


-- Some small models

inductive M₂: Type | e:M₂ | a:M₂
export M₂ (e a)
namespace M₂            -- 2-elt idempotent monoid
  def cdot:  M₂→M₂ → M₂ | e x := x  | x e := x | a a := a

  lemma cdot_id: identity_r cdot e := assume x, by cases x; refl
  lemma id_cdot: identity_l cdot e := assume x, by cases x; refl
  lemma cdot_asso: associative cdot := 
    assume x y z, by cases x; cases y; cases z; refl
  lemma cdot_idem: idempotent cdot := assume x, by cases x; refl

  instance: Sgrp cdot := ⟨cdot_asso⟩
  instance: Band cdot := ⟨cdot_idem⟩   -- removed 1st component ⟨cdot_asso⟩, 
  instance: Mon cdot e := ⟨id_cdot, cdot_id⟩  -- removed 1st component ⟨cdot_asso⟩, 
end M₂


inductive Z₂: Type | e:Z₂ | a:Z₂
export Z₂ (e a)
namespace Z₂            -- 2-elt group
  def add:  Z₂→Z₂ → Z₂ | e x := x  | x e := x | a a := e

  lemma add_zero: right_identity add e := assume x, by cases x; refl
  lemma zero_add: left_identity add e := assume x, by cases x; refl
  lemma add_assoc: associative add := 
  assume x y z, by cases x; cases y; cases z; refl

  instance: Sgrp add := ⟨add_assoc⟩
  instance: Mon add e := ⟨zero_add, add_zero⟩   -- removed 1st component ⟨add_asso⟩, 
end Z₂