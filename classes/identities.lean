universes u v

section formulas

variables {α: Type u} {β: Type v}
variables f g: α → α → α
variables h k: α → α
variable  c: α
variables R S: α → α → Prop
local infix `⬝`:70  := f
local notation x+y := g x y
local notation x\y := g x y
local notation x/y := g x y
local notation x⁻¹ := h x
local notation 1   := c
local notation 0   := c
local notation x≤y := R x y
local infix `≺`:50 := R

def involutive            := ∀x,     h(h x) = x
def inverse_ops           := ∀x,     h(k x) = x
def unary_absorption_l    := ∀x,     h(k x) = k x
def unary_absorption_r    := ∀x,     h(k x) = h x
def unary_idempotent      := ∀x,     h(h x) = h x
def idempotent            := ∀x,     x⬝x = x
def identity_l            := ∀x,     1⬝x = x
def identity_r            := ∀x,     x⬝1 = x
def zero_l                := ∀x,     0⬝x = 0
def zero_r                := ∀x,     x⬝0 = 0
def inverse_l             := ∀x,     x⁻¹⬝x = 1
def inverse_r             := ∀x,     x⬝x⁻¹ = 1
def const_mult_l          := ∀x,     c⬝x = h x
def const_mult_r          := ∀x,     x⬝c = h x
def square_constant       := ∀x,     x⬝x = c
def square_unary          := ∀x,     x⬝x = h x
def unary_identity_l      := ∀x,     (h x)⬝x = x
def unary_identity_r      := ∀x,     x⬝(h x) = x
def unary_const_mult_l    := ∀x,     h(c⬝x) = c⬝(h x)
def unary_const_mult_r    := ∀x,     h(x⬝c) = (h x)⬝c

--def commutative           := ∀x y,   x⬝y = y⬝x  defined in logic.lean
def unary_projection_l    := ∀x y,   x⬝y = h x
def unary_projection_r    := ∀x y,   x⬝y = h y
def idempotent_l          := ∀x y,   x⬝(x⬝y) = x⬝y
def idempotent_r          := ∀x y,   (x⬝y)⬝y = x⬝y
def idempotent_l'         := ∀x y,   x⬝(y⬝x) = x⬝y
def idempotent_r'         := ∀x y,   (x⬝y)⬝x = x⬝y
def rectangular_l         := ∀x y,   (x⬝y)⬝x = x
def rectangular_r         := ∀x y,   x⬝(y⬝x) = x
def absorption            := ∀x y,   (x⬝y)+x = x
def absorption'           := ∀x y,   x+(y⬝x) = x
def division_l            := ∀x y,   x⬝(x\y) = y
def division_r            := ∀x y,   (x/y)⬝y = x
def division_l'           := ∀x y,   x\(x⬝y) = y
def division_r'           := ∀x y,   (x⬝y)/y = x
def unary_commutative     := ∀x y,   (h x)⬝(h y) = (h y)⬝(h x)
def unary_involutive      := ∀x y,   h(x⬝y) = (h y)⬝(h x)
def interdistributive     := ∀x y,   h(x⬝y) = (h x)+(h y)
def unary_distributive    := ∀x y,   h(x⬝y) = (h x)⬝(h y) 
def twisted_l             := ∀x y,   (h(x⬝y))⬝x = x⬝(h y) 
def twisted_r             := ∀x y,   x⬝(h(y⬝x)) = (h y)⬝x
def locality_l            := ∀x y,   h((h x)⬝y) = h(x⬝y)
def locality_r            := ∀x y,   h(x⬝(h y)) = h(x⬝y)
def unary_distributive_l  := ∀x y,   h((h x)⬝y) = (h x)⬝(h y)
def unary_distributive  := ∀x y,   h(x⬝(h y)) = (h x)⬝(h y)
def absorbtive_l          := ∀x y,   (h x)⬝(h(x⬝y)) = h(x⬝y)
def absorbtive_r          := ∀x y,   (h(x⬝y))⬝(h y) = h(x⬝y)
def flexible              := ∀x y,   (x⬝y)⬝x = x⬝(y⬝x)

--def associative           := ∀x y z, x⬝(y⬝z) = (x⬝y)⬝z  defined in logic.lean
def commutative_l         := ∀x y z, x⬝(y⬝z) = y⬝(x⬝z)
def commutative_r         := ∀x y z, (x⬝y)⬝z = (x⬝z)⬝y
def interassociative1     := ∀x y z, x⬝(y+z) = (x⬝y)+z
def interassociative2     := ∀x y z, x⬝(y+z) = (x+y)⬝z
def distributive_l        := ∀x y z, x⬝(y+z) = (x⬝y)+(x⬝z)
def distributive_r        := ∀x y z, (x+y)⬝z = (x⬝z)+(y⬝z)
def self_distributive_l   := ∀x y z, x⬝(y⬝z) = (x⬝y)⬝(x⬝z)
def self_distributive_r   := ∀x y z, (x⬝y)⬝z = (x⬝z)⬝(y⬝z)
def directoid_absorption  := ∀x y z, x⬝((x⬝y)⬝z) = (x⬝y)⬝z
def directoid_absorbtion' := ∀x y z, (x⬝(y⬝z))⬝z = x⬝(y⬝z)
def Moufang1              := ∀x y z, ((x⬝y)⬝x)⬝z = x⬝(y⬝(x⬝z))
def Moufang2              := ∀x y z, ((x⬝y)⬝z)⬝y = x⬝(y⬝(z⬝y))
def Moufang3              := ∀x y z, (x⬝y)⬝(z⬝x) = (x⬝(y⬝z))⬝x
def Moufang4              := ∀x y z, (x⬝y)⬝(z⬝x) = x⬝((y⬝z)⬝x)
def cancelative_l         := ∀x y z, x⬝y = x⬝z → y = z
def cancelative_r         := ∀x y z, x⬝y = z⬝y → x = z

def entropic              := ∀x y z w, (x⬝y)⬝(z⬝w) = (x⬝z)⬝(y⬝w)
def paramedial            := ∀x y z w, (x⬝y)⬝(z⬝w) = (w⬝y)⬝(z⬝x)

def commutative1_l (h: α→β → β) := ∀x₁ x₂ y, h x₁(h x₂ y) = h x₂(h x₁ y)
def commutative1_r (h: β→α → β) := ∀y x₁ x₂, h(h y x₁) x₂ = h(h y x₂) x₁

-- example proofs from logic.lean
lemma comm : commutative f → associative f → commutative1_l f :=
assume hcomm hassoc, assume x y z, calc
  x⬝(y⬝z) = (x⬝y)⬝z  : (hassoc x y z).symm
    ...  = (y⬝x)⬝z  : hcomm x y ▸ rfl
    ...  = y⬝(x⬝z)  : hassoc y x z

lemma comm : commutative f → associative f → commutative1 f :=
assume hcomm hassoc, assume x y z, calc
  (x⬝y)⬝z = x⬝(y⬝z) : hassoc x y z
    ...  = x⬝(z⬝y) : hcomm y z ▸ rfl
    ...  = (x⬝z)⬝y : (hassoc x z y).symm

/-
def reflexive           := ∀x,     x ≤ x                  defined in logic.lean
def irreflexive         := ∀x,     ¬ x ≤ x
def symmetric           := ∀x y,   x ≤ y → y ≤ x
def anti_symmetric      := ∀x y,   x ≤ y → y ≤ x → x = y
def total               := ∀x y,   x ≤ y ∨ y ≤ x
-/
def naturally_ordered_l := ∀x y,   x ≤ y ↔ ∃z, z⬝x = y
def naturally_ordered := ∀x y,   x ≤ y ↔ ∃z, x⬝z = y

--def transitive          := ∀x y z, x ≤ y → y ≤ z → x ≤ z defined in logic.lean
def order_preserving_l  := ∀x y z, x ≤ y → z⬝x ≤ z⬝y
def order_preserving_r  := ∀x y z, x ≤ y → x⬝z ≤ y⬝z
def residuated_l        := ∀x y z, x⬝y ≤ z ↔ y ≤ x\z
def residuated_r        := ∀x y z, x⬝y ≤ z ↔ x ≤ z/y

/-  some more definitions from logic.lean

def equivalence := reflexive R ∧ symmetric R ∧ transitive R
def mk_equivalence (refl: reflexive R)(symm: symmetric R)(tran: transitive R): 
equivalence R := ⟨refl, symm, tran⟩

def empty_relation := λx₁ x₂:α, false
def subrelation (R S: α→α → Prop) := ∀⦃x y⦄, R x y → S x y
def inv_image (f: β → α): β→β → Prop := λx₁ x₂, f x₁ ≤ f x₂

lemma inv_image.trans (f:β → α) (h: transitive R): transitive (inv_image R f) :=
λ(x₁ x₂ x₃:β) (h₁: inv_image R f x₁ x₂) (h₂: inv_image R f x₂ x₃), h h₁ h₂

lemma inv_image.irreflexive (f:β → α)(h: irreflexive R): 
irreflexive (inv_image R f) := λ(x:β)(h₁: inv_image R f x x), h(f x)h₁

--transitive closure of R
inductive tc {α: Sort u}(R: α→α → Prop): α→α → Prop
| base  : ∀ x y, R x y → tc x y
| trans : ∀ x y z, tc x y → tc y z → tc y z
-/
end formulas
