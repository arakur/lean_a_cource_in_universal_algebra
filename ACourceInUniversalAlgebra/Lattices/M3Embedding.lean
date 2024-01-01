import Paperproof

import «ACourceInUniversalAlgebra».Lattices.N5Embedding

section «Nondistributive modular lattices have M₃»

  structure Lattice.NondistribCE (α) [Lattice α] [IsModularLattice α] where
    a: α
    b: α
    c: α
    nondistrib: ¬ a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)

  def Lattice.NondistribCE.mk' {α} [Lattice α] [IsModularLattice α]
    {a b c: α} (h: ¬ a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)):
    Lattice.NondistribCE α
    := by
      apply Lattice.NondistribCE.mk a b c
      rintro h': a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)
      apply h
      apply le_antisymm h' ?ge
      apply sup_le ?left ?right
      exact inf_le_inf_left a le_sup_left
      exact inf_le_inf_left a le_sup_right

  namespace Lattice.NondistribCE

  variable {α} [Lattice α] [IsModularLattice α] {ce: NondistribCE α}

  def d' (x y z: α) := (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x)

  def e' (x y z: α) := (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)

  def x₁' (x y z: α) := (x ⊓ e' x y z) ⊔ d' x y z

  def y₁' (x y z: α) := x₁' y z x

  def z₁' (x y z: α) := x₁' z x y

  def nondistrib' (x y z: α) := ¬ x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z)

  @[simp]
  def d (ce: NondistribCE α) := d' ce.a ce.b ce.c
  @[simp]
  def e (ce: NondistribCE α) := e' ce.a ce.b ce.c
  @[simp]
  def a₁ (ce: NondistribCE α) := x₁' ce.a ce.b ce.c
  @[simp]
  def b₁ (ce: NondistribCE α) := y₁' ce.a ce.b ce.c
  @[simp]
  def c₁ (ce: NondistribCE α) := z₁' ce.a ce.b ce.c

  section rotation
    @[simp]
    lemma d'_rot₁ {x y z: α}:
      d' x y z = d' y z x
      := Eq.trans sup_assoc sup_comm

    @[simp]
    lemma d'_rot₂ {x y z: α}:
      d' x y z = d' z x y
      := Eq.trans sup_comm sup_assoc.symm

    @[simp]
    lemma e'_rot₁ {x y z: α}:
      e' x y z = e' y z x
      := Eq.trans inf_assoc inf_comm

    @[simp]
    lemma e'_rot₂ {x y z: α}:
      e' x y z = e' z x y
      := Eq.trans inf_comm inf_assoc.symm
  end rotation

  section le
    @[simp]
    lemma x_inf_y_le_d' {x y z: α}:
      x ⊓ y ≤ d' x y z
      := le_trans le_sup_left le_sup_left

    @[simp]
    lemma y_inf_z_le_d' {x y z: α}:
      y ⊓ z ≤ d' x y z
      := by rw [d'_rot₁]; exact x_inf_y_le_d'

    @[simp]
    lemma z_inf_x_le_d' {x y z: α}:
      z ⊓ x ≤ d' x y z
      := by rw [d'_rot₂]; exact x_inf_y_le_d'

    @[simp]
    lemma x_inf_y_le_e' {x y z: α}:
      x ⊓ y ≤ e' x y z
      := by
        show x ⊓ y ≤ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)
        apply le_inf (le_inf ?c₁ ?c₂) ?c₃
        case c₁ => exact le_trans inf_le_left le_sup_left
        case c₂ => exact le_trans inf_le_right le_sup_left
        case c₃ => exact le_trans inf_le_left le_sup_right

    @[simp]
    lemma y_inf_z_le_e' {x y z: α}:
      y ⊓ z ≤ e' x y z
      := by rw [e'_rot₁]; exact x_inf_y_le_e'


    @[simp]
    lemma d'_le_x_sup_y {x y z: α}:
      d' x y z ≤ x ⊔ y
      := by
        show (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ x ⊔ y
        apply sup_le (sup_le ?c₁ ?c₂) ?c₃
        case c₁ => exact le_trans inf_le_left le_sup_left
        case c₂ => exact le_trans inf_le_left le_sup_right
        case c₃ => exact le_trans inf_le_right le_sup_left

    @[simp]
    lemma d'_le_y_sup_z {x y z: α}:
      d' x y z ≤ y ⊔ z
      := by rw [d'_rot₁]; exact d'_le_x_sup_y

    @[simp]
    lemma d'_le_z_sup_x {x y z: α}:
      d' x y z ≤ z ⊔ x
      := by rw [d'_rot₂]; exact d'_le_x_sup_y

    @[simp]
    lemma d'_le_e' {x y z: α}:
      d' x y z ≤ e' x y z
      := by
        show (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ e' x y z
        apply sup_le (sup_le ?c₁ ?c₂) ?c₃
        case c₁ => exact x_inf_y_le_e'
        case c₂ => rw [e'_rot₁]; exact x_inf_y_le_e'
        case c₃ => rw [e'_rot₂]; exact x_inf_y_le_e'

    @[simp]
    lemma d'_le_x₁' {x y z: α}:
      d' x y z ≤ x₁' x y z
      := calc
        d' x y z
        _ ≤ _ ⊔ d' x y z := le_sup_right

    @[simp]
    lemma d'_le_y₁' {x y z: α}:
      d' x y z ≤ y₁' x y z
      := by rw [d'_rot₁]; exact d'_le_x₁'

    @[simp]
    lemma d'_le_z₁' {x y z: α}:
      d' x y z ≤ z₁' x y z
      := by rw [d'_rot₂]; exact d'_le_x₁'

    @[simp]
    lemma x₁'_le_e' {x y z: α}:
      x₁' x y z ≤ e' x y z
      := by
        show (x ⊓ e' x y z) ⊔ d' x y z ≤ e' x y z
        apply sup_le ?left ?right
        case left => exact inf_le_right
        case right => exact d'_le_e'

    @[simp]
    lemma y₁'_le_e' {x y z: α}:
      y₁' x y z ≤ e' x y z
      := by rw [e'_rot₁]; exact x₁'_le_e'

    @[simp]
    lemma z₁'_le_e' {x y z: α}:
      z₁' x y z ≤ e' x y z
      := by rw [e'_rot₂]; exact x₁'_le_e'
  end le

  section alt
    lemma x₁'_alt₁ {x y z: α}:
      x₁' x y z = (x ⊔ d' x y z) ⊓ e' x y z
      := calc
        x₁' x y z
        _ = (x ⊓ e' x y z) ⊔ d' x y z := rfl
        _ = (e' x y z ⊓ x) ⊔ d' x y z := by congr 1; exact inf_comm
        _ = e' x y z ⊓ (x ⊔ d' x y z) := inf_sup_assoc_of_le _ d'_le_e'
        _ = (x ⊔ d' x y z) ⊓ e' x y z := inf_comm
  end alt

  section sup
    @[simp]
    lemma e'_sup_x {x y z: α}:
      e' x y z ⊔ x = (x ⊔ y) ⊓ (z ⊔ x)
      := by
        let e := e' x y z
        calc
          e ⊔ x
          _ = ((x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)) ⊔ x
              := rfl
          _ = ((z ⊔ x) ⊓ (x ⊔ y) ⊓ (y ⊔ z)) ⊔ x
              := by rw [inf_comm, inf_assoc]
          _ = (z ⊔ x) ⊓ (x ⊔ y) ⊓ ((y ⊔ z) ⊔ x)
              := inf_sup_assoc_of_le _ (le_inf le_sup_right le_sup_left)
          _ = (z ⊔ x) ⊓ ((x ⊔ y) ⊓ ((y ⊔ z) ⊔ x))
              := by rw [inf_assoc]
          _ = (z ⊔ x) ⊓ (x ⊔ y)
              := by
                congr 1; apply inf_eq_left.mpr; calc
                  x ⊔ y ≤ x ⊔ y ⊔ z   := le_sup_left
                  _     = (y ⊔ z) ⊔ x := by rw [sup_assoc, sup_comm]
          _ = (x ⊔ y) ⊓ (z ⊔ x)
              := inf_comm

    @[simp]
    lemma d'_sup_x {x y z: α}:
      d' x y z ⊔ x = x ⊔ (y ⊓ z)
      := by
        let d := d' x y z
        calc
          d ⊔ x
          _ = ((x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x)) ⊔ x
              := rfl
          _ = (x ⊓ y) ⊔ (y ⊓ z) ⊔ (x ⊔ (x ⊓ z))
              := by
              repeat rw [sup_assoc]
              congr 2; rw [inf_comm]; exact sup_comm
          _ = (x ⊓ y) ⊔ (y ⊓ z) ⊔ x
              := by congr 1; exact sup_inf_self
          _ = x ⊔ (x ⊓ y) ⊔ (y ⊓ z)
              := by rw [sup_comm, sup_assoc]
          _ = x ⊔ (y ⊓ z)
              := by congr 1; exact sup_inf_self

    @[simp]
    lemma d'_sup_y {x y z: α}:
      d' x y z ⊔ y = y ⊔ (z ⊓ x)
      := calc
        d' x y z ⊔ y
        _ = d' y z x ⊔ y  := by congr 1; exact d'_rot₁
        _ = y ⊔ (z ⊓ x)   := d'_sup_x

    @[simp]
    lemma y_sup_d' {x y z: α}:
      y ⊔ d' x y z = y ⊔ (z ⊓ x)
      := Eq.trans sup_comm d'_sup_y

    lemma x_inf_e' {x y z: α}:
      x ⊓ e' x y z = x ⊓ (y ⊔ z)
      := calc
        x ⊓ e' x y z
        _ = x ⊓ ((x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)) := rfl
        _ = x ⊓ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)   := by repeat rw [inf_assoc]
        _ = x ⊓ (y ⊔ z) ⊓ (z ⊔ x)             := by rw [inf_sup_self]
        _ = (z ⊔ x) ⊓ x ⊓ (y ⊔ z)             := by rw [inf_comm, inf_assoc]
        _ = x ⊓ (x ⊔ z) ⊓ (y ⊔ z)             := by congr 1; rw [inf_comm, sup_comm]
        _ = x ⊓ (y ⊔ z)                       := by rw [inf_sup_self]

    lemma d'_inf_x {x y z: α}:
      d' x y z ⊓ x = (x ⊓ y) ⊔ (z ⊓ x)
      := calc
        d' x y z ⊓ x
        _ = (x ⊓ y ⊔ y ⊓ z ⊔ z ⊓ x) ⊓ x   := rfl
        _ = (y ⊓ z ⊔ x ⊓ y ⊔ z ⊓ x) ⊓ x   := by congr 2; exact sup_comm
        _ = (y ⊓ z ⊔ (x ⊓ y ⊔ z ⊓ x)) ⊓ x := by congr 1; exact sup_assoc
        _ = (x ⊓ y ⊔ z ⊓ x ⊔ y ⊓ z) ⊓ x   := by congr 1; exact sup_comm
        _ = (x ⊓ y ⊔ z ⊓ x) ⊔ (y ⊓ z) ⊓ x := sup_inf_assoc_of_le _ (sup_le inf_le_left inf_le_right)
        _ = x ⊓ y ⊔ z ⊓ x                 := by apply sup_eq_left.mpr; calc
              (y ⊓ z) ⊓ x ≤ z ⊓ x         := inf_le_inf_right _ inf_le_right
              _           ≤ x ⊓ y ⊔ z ⊓ x := le_sup_right

    lemma x_inf_d' {x y z: α}:
      x ⊓ d' x y z = (x ⊓ y) ⊔ (z ⊓ x)
      := Eq.trans inf_comm d'_inf_x

    lemma x₁'_alt₂ {x y z: α}:
      x₁' x y z = (x ⊓ (y ⊔ z)) ⊔ (y ⊓ z)
      := calc
        x₁' x y z
        _ = (x ⊔ d' x y z) ⊓ e' x y z
            := x₁'_alt₁
        _ = (x ⊔ (y ⊓ z)) ⊓ e' x y z
            := by congr 1; exact Eq.trans sup_comm d'_sup_x
        _ = ((y ⊓ z) ⊔ x) ⊓ e' x y z
            := by congr 1; exact sup_comm
        _ = (y ⊓ z) ⊔ (x ⊓ e' x y z)
            := sup_inf_assoc_of_le _ y_inf_z_le_e'
        _ = (y ⊓ z) ⊔ (x ⊓ (y ⊔ z))
            := by congr 1; exact x_inf_e'
        _ = (x ⊓ (y ⊔ z)) ⊔ (y ⊓ z)
            := sup_comm

    lemma y₁'_alt₂ {x y z: α}:
      y₁' x y z = (y ⊓ (z ⊔ x)) ⊔ (z ⊓ x)
      := x₁'_alt₂

    @[simp]
    lemma x₁'_sup_y₁' {x y z: α}:
      x₁' x y z ⊔ y₁' x y z = e' x y z
      := calc
        x₁' x y z ⊔ y₁' x y z
        _ = (x ⊓ (y ⊔ z)) ⊔ (y ⊓ z) ⊔ ((y ⊓ (z ⊔ x)) ⊔ (z ⊓ x))
            := by rw [x₁'_alt₂, y₁'_alt₂]
        _ = (x ⊓ (y ⊔ z)) ⊔ (y ⊓ z) ⊔ ((z ⊓ x) ⊔ (y ⊓ (z ⊔ x)))
            := by congr 1; exact sup_comm
        _ = (x ⊓ (y ⊔ z)) ⊔ ((y ⊓ z) ⊔ (z ⊓ x)) ⊔ (y ⊓ (z ⊔ x))
            := by repeat rw [sup_assoc]
        _ = (x ⊓ (y ⊔ z)) ⊔ ((z ⊓ x) ⊔ (y ⊓ z)) ⊔ (y ⊓ (z ⊔ x))
            := by congr 2; exact sup_comm
        _ = (x ⊓ (y ⊔ z)) ⊔ (z ⊓ x) ⊔ ((y ⊓ z) ⊔ (y ⊓ (z ⊔ x)))
            := by repeat rw [sup_assoc]
        _ = ((y ⊔ z) ⊓ x) ⊔ (z ⊓ x) ⊔ ((y ⊓ z) ⊔ (y ⊓ (z ⊔ x)))
            := by congr 2; exact inf_comm
        _ = (y ⊔ z) ⊓ (x ⊔ (z ⊓ x)) ⊔ (((y ⊓ z) ⊔ y) ⊓ (z ⊔ x))
            := by
              congr 1
              apply inf_sup_assoc_of_le _ _
              exact le_trans inf_le_left le_sup_right
              apply sup_inf_assoc_of_le _ _ |>.symm
              exact le_trans inf_le_right le_sup_left
        _ = (y ⊔ z) ⊓ (x ⊔ (x ⊓ z)) ⊔ ((y ⊔ (y ⊓ z)) ⊓ (z ⊔ x))
            := by simp [inf_comm, sup_comm]
        _ = (y ⊔ z) ⊓ x ⊔ (y ⊓ (z ⊔ x))
            := by repeat rw [sup_inf_self]
        _ = (y ⊔ z) ⊓ (x ⊔ (y ⊓ (z ⊔ x)))
            := inf_sup_assoc_of_le _ (le_trans inf_le_left le_sup_left)
        _ = (y ⊔ z) ⊓ ((x ⊔ y) ⊓ (z ⊔ x))
            := by congr 1; exact sup_inf_assoc_of_le _ le_sup_right |>.symm
        _ = (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)
            := by rw [← inf_assoc]; congr 1; exact inf_comm
        _ = e' x y z
            := rfl

      @[simp]
      lemma y₁'_sup_z₁' {x y z: α}:
        y₁' x y z ⊔ z₁' x y z = e' x y z
        := Eq.trans x₁'_sup_y₁' e'_rot₁.symm

      @[simp]
      lemma z₁'_sup_x₁' {x y z: α}:
        z₁' x y z ⊔ x₁' x y z = e' x y z
        := Eq.trans x₁'_sup_y₁' e'_rot₂.symm

      @[simp]
      lemma y₁'_sup_x₁' {x y z: α}:
        y₁' x y z ⊔ x₁' x y z = e' x y z
        := Eq.trans sup_comm x₁'_sup_y₁'

      @[simp]
      lemma z₁'_sup_y₁' {x y z: α}:
        z₁' x y z ⊔ y₁' x y z = e' x y z
        := Eq.trans sup_comm y₁'_sup_z₁'

      @[simp]
      lemma x₁'_sup_z₁' {x y z: α}:
        x₁' x y z ⊔ z₁' x y z = e' x y z
        := Eq.trans sup_comm z₁'_sup_x₁'

  end sup

  section inf
    @[simp]
    lemma x₁'_inf_y₁' {x y z: α}:
      x₁' x y z ⊓ y₁' x y z = d' x y z
      := by
        let x₁ := x₁' x y z; let y₁ := y₁' x y z
        let d₀ := d' x y z; let e₀ := e' x y z
        calc
          x₁ ⊓ y₁
          _ = (x ⊓ e₀ ⊔ d₀) ⊓ (y ⊓ e' y z x ⊔ d' y z x)
              := rfl
          _ = (x ⊓ e₀ ⊔ d₀) ⊓ (y ⊓ e₀ ⊔ d₀)
              := by rw [← e'_rot₁, ← d'_rot₁]
          _ = (d₀ ⊔ x ⊓ e₀) ⊓ (y ⊓ e₀ ⊔ d₀)
              := by congr 1; exact sup_comm
          _ = d₀ ⊔ x ⊓ e₀ ⊓ (y ⊓ e₀ ⊔ d₀)
              := sup_inf_assoc_of_le _ le_sup_right
          _ = d₀ ⊔ x ⊓ e₀ ⊓ (e₀ ⊓ y ⊔ d₀)
              := by congr 3; exact inf_comm
          _ = d₀ ⊔ x ⊓ e₀ ⊓ (e₀ ⊓ (y ⊔ d₀))
              := by congr 2; exact inf_sup_assoc_of_le _ d'_le_e'
          _ = d₀ ⊔ x ⊓ (e₀ ⊓ e₀) ⊓ (y ⊔ d₀)
              := by congr 1; repeat rw [inf_assoc]
          _ = d₀ ⊔ x ⊓ e₀ ⊓ (y ⊔ d₀)
              := by congr 3; exact inf_idem
          _ = d₀ ⊔ x ⊓ (y ⊔ z) ⊓ (y ⊔ (z ⊓ x))
              := by congr 2; exact x_inf_e'; exact y_sup_d'
          _ = d₀ ⊔ x ⊓ ((y ⊔ z) ⊓ (y ⊔ (z ⊓ x)))
              := by congr 1; exact inf_assoc
          _ = d₀ ⊔ x ⊓ ((y ⊔ z) ⊓ ((z ⊓ x) ⊔ y))
              := by congr 3; exact sup_comm
          _ = d₀ ⊔ x ⊓ ((y ⊔ z) ⊓ (z ⊓ x) ⊔ y)
              := by congr 2; exact inf_sup_assoc_of_le _ le_sup_left |>.symm
          _ = d₀ ⊔ x ⊓ (z ⊓ x ⊔ y)
              := by
                congr 3
                exact inf_eq_right.mpr (le_trans inf_le_left le_sup_right)
          _ = d₀ ⊔ (z ⊓ x ⊔ y) ⊓ x
              := by congr 1; exact inf_comm
          _ = d₀ ⊔ z ⊓ x ⊔ y ⊓ x
              := by rw [sup_inf_assoc_of_le _ inf_le_right, ← sup_assoc]
          _ = d₀ ⊔ y ⊓ x
              := by congr 1; exact sup_eq_left.mpr z_inf_x_le_d'
          _ = d₀
              := by rw [inf_comm]; exact sup_eq_left.mpr x_inf_y_le_d'

    @[simp]
    lemma y₁'_inf_z₁' {x y z: α}:
      y₁' x y z ⊓ z₁' x y z = d' x y z
      := Eq.trans x₁'_inf_y₁' d'_rot₁.symm

    @[simp]
    lemma z₁'_inf_x₁' {x y z: α}:
      z₁' x y z ⊓ x₁' x y z = d' x y z
      := Eq.trans x₁'_inf_y₁' d'_rot₂.symm

    @[simp]
    lemma x₁'_inf_z₁' {x y z: α}:
      x₁' x y z ⊓ z₁' x y z = d' x y z
      := Eq.trans inf_comm z₁'_inf_x₁'

    @[simp]
    lemma y₁'_inf_x₁' {x y z: α}:
      y₁' x y z ⊓ x₁' x y z = d' x y z
      := Eq.trans inf_comm x₁'_inf_y₁'

    @[simp]
    lemma z₁'_inf_y₁' {x y z: α}:
      z₁' x y z ⊓ y₁' x y z = d' x y z
      := Eq.trans inf_comm y₁'_inf_z₁'
  end inf

  section not
    @[simp]
    lemma d'_ne_e' {x y z: α} (h_nondistrib: nondistrib' x y z):
      d' x y z ≠ e' x y z
      := by
        let d₀ := d' x y z; let e₀ := e' x y z
        rintro h: d₀ = e₀
        have: x ⊓ d₀ = x ⊓ e₀ := by congr
        have: x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := calc
          x ⊓ (y ⊔ z) = x ⊓ e₀        := by rw [x_inf_e']
          _           = x ⊓ d₀        := by rw [h]
          _           = (x ⊓ y) ⊔ z ⊓ x := by rw [x_inf_d']
          _           = (x ⊓ y) ⊔ (x ⊓ z) := by congr 1; exact inf_comm
        have: x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z) := by rw [this]
        exact h_nondistrib this

    @[simp]
    lemma d'_ne_x₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      d' x y z ≠ x₁' x y z
      := by
        let d₀ := d' x y z; let e₀ := e' x y z
        rintro h: d₀ = (x ⊓ e₀) ⊔ d₀
        have: x ⊓ e₀ ≤ d₀ := sup_eq_right.mp h.symm
        have: x ⊓ e₀ ≤ x ⊓ d₀ := calc
          x ⊓ e₀  = x ⊓ x ⊓ e₀    := by congr 1; exact inf_idem.symm
          _       = x ⊓ (x ⊓ e₀)  := inf_assoc
          _       ≤ x ⊓ d₀       := inf_le_inf_left _ this
        have: x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z) := calc
          x ⊓ (y ⊔ z) = x ⊓ e₀        := by rw [x_inf_e']
          _           ≤ x ⊓ d₀        := this
          _           = x ⊓ y ⊔ z ⊓ x := x_inf_d'
          _           = x ⊓ y ⊔ x ⊓ z := by congr 1; exact inf_comm
        exact h_nondistrib this

    @[simp]
    lemma e'_ne_y₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      e' x y z ≠ y₁' x y z
      := by
        let d₀ := d' x y z; let e₀ := e' x y z
        let x₁ := x₁' x y z; let y₁ := y₁' x y z
        rintro h: e₀ = y₁
        have: d₀ = x₁ := calc
          d₀  = x₁ ⊓ y₁ := x₁'_inf_y₁'.symm
          _   = x₁ ⊓ e₀ := by congr 1; exact h.symm
          _   = x₁      := inf_eq_left.mpr x₁'_le_e'
        exact d'_ne_x₁' h_nondistrib this

    @[simp]
    lemma d'_ne_z₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      d' x y z ≠ z₁' x y z
      := by
        let d₀ := d' x y z; let e₀ := e' x y z
        let y₁ := y₁' x y z; let z₁ := z₁' x y z
        rintro h: d₀ = z₁
        have: e₀ = y₁ := calc
          e₀  = y₁ ⊔ z₁ := y₁'_sup_z₁'.symm
          _   = y₁ ⊔ d₀ := by congr 1; exact h.symm
          _   = y₁      := sup_eq_left.mpr d'_le_y₁'
        exact e'_ne_y₁' h_nondistrib this

    @[simp]
    lemma e'_ne_z₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      e' x y z ≠ z₁' x y z
      := by
        let d₀ := d' x y z; let e₀ := e' x y z
        let x₁ := x₁' x y z; let z₁ := z₁' x y z
        rintro h: e₀ = z₁
        have: d₀ = x₁ := calc
          d₀  = x₁ ⊓ z₁ := x₁'_inf_z₁'.symm
          _   = x₁ ⊓ e₀ := by congr 1; exact h.symm
          _   = x₁      := inf_eq_left.mpr x₁'_le_e'
        exact d'_ne_x₁' h_nondistrib this

    @[simp]
    lemma d'_ne_y₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      d' x y z ≠ y₁' x y z
      := by
        let d₀ := d' x y z; let e₀ := e' x y z
        let y₁ := y₁' x y z; let z₁ := z₁' x y z
        rintro h: d₀ = y₁
        have: e₀ = z₁ := calc
          e₀  = y₁ ⊔ z₁ := y₁'_sup_z₁'.symm
          _   = z₁ ⊔ y₁ := sup_comm
          _   = z₁ ⊔ d₀ := by congr 1; exact h.symm
          _   = z₁      := sup_eq_left.mpr d'_le_z₁'
        exact e'_ne_z₁' h_nondistrib this

    @[simp]
    lemma e'_ne_x₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      e' x y z ≠ x₁' x y z
      := by
        let d₀ := d' x y z; let e₀ := e' x y z
        let x₁ := x₁' x y z; let y₁ := y₁' x y z
        rintro h: e₀ = x₁
        have: d₀ = y₁ := calc
          d₀  = x₁ ⊓ y₁ := x₁'_inf_y₁'.symm
          _   = y₁ ⊓ x₁ := inf_comm
          _   = y₁ ⊓ e₀ := by congr 1; exact h.symm
          _   = y₁      := inf_eq_left.mpr y₁'_le_e'
        exact d'_ne_y₁' h_nondistrib this

    @[simp]
    lemma x₁'_ne_y₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      x₁' x y z ≠ y₁' x y z
      := by
        let x₁ := x₁' x y z; let y₁ := y₁' x y z
        let d₀ := d' x y z
        rintro h: x₁ = y₁
        have: d₀ = y₁ := calc
          d₀  = x₁ ⊓ y₁ := x₁'_inf_y₁'.symm
          _   = y₁ ⊓ y₁ := by congr
          _   = y₁      := inf_idem
        exact d'_ne_y₁' h_nondistrib this

    @[simp]
    lemma y₁'_ne_z₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      y₁' x y z ≠ z₁' x y z
      := by
        let y₁ := y₁' x y z; let z₁ := z₁' x y z
        let d₀ := d' x y z
        rintro h: y₁ = z₁
        have: d₀ = z₁ := calc
          d₀  = y₁ ⊓ z₁ := y₁'_inf_z₁'.symm
          _   = z₁ ⊓ z₁ := by congr
          _   = z₁      := inf_idem
        exact d'_ne_z₁' h_nondistrib this

    @[simp]
    lemma z₁'_ne_x₁' {x y z: α} (h_nondistrib: nondistrib' x y z):
      z₁' x y z ≠ x₁' x y z
      := by
        let x₁ := x₁' x y z; let z₁ := z₁' x y z
        let d₀ := d' x y z
        rintro h: z₁ = x₁
        have: d₀ = x₁ := calc
          d₀  = z₁ ⊓ x₁ := z₁'_inf_x₁'.symm
          _   = x₁ ⊓ x₁ := by congr
          _   = x₁      := inf_idem
        exact d'_ne_x₁' h_nondistrib this
  end not

  @[simp]
  def M₃embedding (ce: NondistribCE α):
    M₃ ↪ℒ α := {
      toFun := λ
        | M₃.bot => ce.d
        | M₃.top => ce.e
        | M₃.a   => ce.a₁
        | M₃.b   => ce.b₁
        | M₃.c   => ce.c₁
      inj' := by
        intro x y h
        cases x; all_goals cases y
        case bot.bot | top.top | a.a | b.b | c.c => rfl
        all_goals apply False.elim
        case bot.top => exact d'_ne_e' ce.nondistrib h
        case bot.a => exact d'_ne_x₁' ce.nondistrib h
        case bot.b => exact d'_ne_y₁' ce.nondistrib h
        case bot.c => exact d'_ne_z₁' ce.nondistrib h
        case top.bot => exact (d'_ne_e' ce.nondistrib).symm h
        case top.a => exact e'_ne_x₁' ce.nondistrib h
        case top.b => exact e'_ne_y₁' ce.nondistrib h
        case top.c => exact e'_ne_z₁' ce.nondistrib h
        case a.bot => exact (d'_ne_x₁' ce.nondistrib).symm h
        case a.top => exact (e'_ne_x₁' ce.nondistrib).symm h
        case a.b => exact x₁'_ne_y₁' ce.nondistrib h
        case a.c => exact (z₁'_ne_x₁' ce.nondistrib).symm h
        case b.bot => exact (d'_ne_y₁' ce.nondistrib).symm h
        case b.top => exact (e'_ne_y₁' ce.nondistrib).symm h
        case b.a => exact (x₁'_ne_y₁' ce.nondistrib).symm h
        case b.c => exact y₁'_ne_z₁' ce.nondistrib h
        case c.bot => exact (d'_ne_z₁' ce.nondistrib).symm h
        case c.top => exact (e'_ne_z₁' ce.nondistrib).symm h
        case c.a => exact z₁'_ne_x₁' ce.nondistrib h
        case c.b => exact (y₁'_ne_z₁' ce.nondistrib).symm h
      map_sup' := by
        intro x y
        cases x; all_goals cases y
        case top.top | bot.bot | a.a | b.b | c.c =>
          rw [sup_idem, sup_idem]
        all_goals simp; rfl
      map_inf' := by
        intro x y
        cases x; all_goals cases y
        case top.top | bot.bot | a.a | b.b | c.c =>
          rw [inf_idem, inf_idem]
        all_goals simp; rfl
    }

  end Lattice.NondistribCE

  -- Theorem 3.6

  theorem Lattice.nondistrib_iff_either_M₃_or_N₅ {α} [Lattice α]:
    ¬ IsDistribLattice α ↔ Nonempty (M₃ ↪ℒ α) ∨ Nonempty (N₅ ↪ℒ α)
    := by
      apply Iff.intro ?mp ?mpr
      case mp =>
        intro h
        have: ¬ ∀ x y z, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
          intro h'; exact h ⟨h' _ _ _⟩
        have ⟨x, this⟩ := Classical.not_forall.mp this
        have ⟨y, this⟩ := Classical.not_forall.mp this
        have ⟨z, this⟩ := Classical.not_forall.mp this
        by_cases modular: IsModularLattice α
        case neg =>
          apply Or.inr
          exact Lattice.nonmodular_iff_has_N₅ |>.mp modular
        case pos =>
          apply Or.inl
          let ce := NondistribCE.mk' this
          exact ⟨ce.M₃embedding⟩
      case mpr =>
        rintro h: Nonempty (M₃ ↪ℒ α) ∨ Nonempty (N₅ ↪ℒ α)
        cases h
        case inr h =>
          have: ¬ IsModularLattice α := Lattice.nonmodular_iff_has_N₅.mpr h
          intro h'; exact IsDistribLattice.modular h' |> this
        case inl h =>
          let ⟨(ι: M₃ ↪ℒ α)⟩ := h
          let a := ι M₃.a; let b := ι M₃.b; let c := ι M₃.c
          intro h'
          have: ∀ {x y z: α}, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z := h'.inf_sup_left
          have: a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := this
          have: a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c := le_of_eq this
          have: ι (M₃.a ⊓ (M₃.b ⊔ M₃.c)) ≤ ι (M₃.a ⊓ M₃.b ⊔ M₃.a ⊓ M₃.c) := calc
            ι (M₃.a ⊓ (M₃.b ⊔ M₃.c))
            _ = a ⊓ (b ⊔ c)
                := by rw [map_inf, map_sup]
            _ ≤ a ⊓ b ⊔ a ⊓ c
                := this
            _ = ι (M₃.a ⊓ M₃.b ⊔ M₃.a ⊓ M₃.c)
                := by rw [map_sup, map_inf, map_inf]
          have: M₃.a ⊓ (M₃.b ⊔ M₃.c) ≤ M₃.a ⊓ M₃.b ⊔ M₃.a ⊓ M₃.c :=
            ι.le_iff_le.mp this
          contradiction

end «Nondistributive modular lattices have M₃»
