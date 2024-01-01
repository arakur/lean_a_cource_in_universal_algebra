import Paperproof

import «ACourceInUniversalAlgebra».Lattices.Basic

section «Nonmodular lattices have N₅»

  structure Lattice.NonmodularCE (α) [Lattice α] where
    a: α
    b: α
    c: α
    hab: a ≤ b
    nonmodular: ¬ (a ⊔ c) ⊓ b ≤ a ⊔ c ⊓ b

  namespace Lattice.NonmodularCE

  variable {α} [Lattice α] {ce: NonmodularCE α}

  @[reducible]
  def a₁ (ce: NonmodularCE α): α :=
    ce.a ⊔ ce.b ⊓ ce.c

  @[reducible]
  def b₁ (ce: NonmodularCE α): α :=
    ce.b ⊓ (ce.a ⊔ ce.c)

  @[reducible]
  def bot (ce: NonmodularCE α): α :=
    ce.c ⊓ ce.b

  @[reducible]
  def top (ce: NonmodularCE α): α :=
    ce.c ⊔ ce.a

  section le

    @[simp]
    lemma bot_le_c:
      ce.bot ≤ ce.c
      := inf_le_left

    @[simp]
    lemma c_le_top:
      ce.c ≤ ce.top
      := le_sup_left

    @[simp]
    lemma bot_le_a₁:
      ce.bot ≤ ce.a₁
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        show c ⊓ b ≤ a ⊔ b ⊓ c
        calc
          c ⊓ b = b ⊓ c       := inf_comm
          _     ≤ a ⊔ (b ⊓ c) := le_sup_right

    @[simp]
    lemma b₁_le_top:
      ce.b₁ ≤ ce.top
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        show b ⊓ (a ⊔ c) ≤ c ⊔ a
        calc
          b ⊓ (a ⊔ c)
          _ ≤ a ⊔ c := inf_le_right
          _ = c ⊔ a := sup_comm

    @[simp]
    lemma a₁_le_b₁:
      ce.a₁ ≤ ce.b₁
      := by
        apply sup_le ?left ?right
        case left => exact le_inf ce.hab le_sup_left
        case right => exact inf_le_inf_left _ le_sup_right

    @[simp]
    lemma bot_le_b₁:
      ce.bot ≤ ce.b₁
      := le_trans bot_le_a₁ a₁_le_b₁

    @[simp]
    lemma a₁_le_top:
      ce.a₁ ≤ ce.top
      := le_trans a₁_le_b₁ b₁_le_top

    @[simp]
    lemma bot_le_top:
      ce.bot ≤ ce.top
      := le_trans bot_le_c c_le_top

  end le

  section sup

    @[simp]
    lemma bot_sup_top:
      ce.bot ⊔ ce.top = ce.top
      := sup_eq_right.mpr ce.bot_le_top

    @[simp]
    lemma top_sup_bot:
      ce.top ⊔ ce.bot = ce.top
      := sup_eq_left.mpr ce.bot_le_top

    @[simp]
    lemma bot_sup_a₁:
      ce.bot ⊔ ce.a₁ = ce.a₁
      := sup_eq_right.mpr ce.bot_le_a₁

    @[simp]
    lemma a₁_sup_bot:
      ce.a₁ ⊔ ce.bot = ce.a₁
      := sup_eq_left.mpr ce.bot_le_a₁

    @[simp]
    lemma bot_sup_b₁:
      ce.bot ⊔ ce.b₁ = ce.b₁
      := sup_eq_right.mpr ce.bot_le_b₁

    @[simp]
    lemma b₁_sup_bot:
      ce.b₁ ⊔ ce.bot = ce.b₁
      := sup_eq_left.mpr ce.bot_le_b₁

    @[simp]
    lemma bot_sup_c:
      ce.bot ⊔ ce.c = ce.c
      := sup_eq_right.mpr ce.bot_le_c

    @[simp]
    lemma c_sup_bot:
      ce.c ⊔ ce.bot = ce.c
      := sup_eq_left.mpr ce.bot_le_c

    @[simp]
    lemma top_sup_a₁:
      ce.top ⊔ ce.a₁ = ce.top
      := sup_eq_left.mpr ce.a₁_le_top

    @[simp]
    lemma a₁_sup_top:
      ce.a₁ ⊔ ce.top = ce.top
      := sup_eq_right.mpr ce.a₁_le_top

    @[simp]
    lemma top_sup_b₁:
      ce.top ⊔ ce.b₁ = ce.top
      := sup_eq_left.mpr ce.b₁_le_top

    @[simp]
    lemma b₁_sup_top:
      ce.b₁ ⊔ ce.top = ce.top
      := sup_eq_right.mpr ce.b₁_le_top

    @[simp]
    lemma top_sup_c:
      ce.top ⊔ ce.c = ce.top
      := sup_eq_left.mpr ce.c_le_top

    @[simp]
    lemma c_sup_top:
      ce.c ⊔ ce.top = ce.top
      := sup_eq_right.mpr ce.c_le_top

    @[simp]
    lemma a₁_sup_b₁:
      ce.a₁ ⊔ ce.b₁ = ce.b₁
      := sup_eq_right.mpr ce.a₁_le_b₁

    @[simp]
    lemma b₁_sup_a₁:
      ce.b₁ ⊔ ce.a₁ = ce.b₁
      := sup_eq_left.mpr ce.a₁_le_b₁

    @[simp]
    lemma c_sup_a₁:
      ce.c ⊔ ce.a₁ = ce.top
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        let a₁ := ce.a₁
        calc
          c ⊔ a₁
          _ = c ⊔ (a ⊔ b ⊓ c) := rfl
          _ = c ⊔ (a ⊔ c ⊓ b) := by congr 2; exact inf_comm
          _ = c ⊔ (c ⊓ b ⊔ a) := by congr 1; exact sup_comm
          _ = c ⊔ c ⊓ b ⊔ a   := sup_assoc.symm
          _ = c ⊔ a           := by congr 1; exact sup_inf_self

    @[simp]
    lemma a₁_sup_c:
      ce.a₁ ⊔ ce.c = ce.top
      := calc
        ce.a₁ ⊔ ce.c  = ce.c ⊔ ce.a₁  := sup_comm
        _             = ce.top        := ce.c_sup_a₁

    @[simp]
    lemma c_sup_b₁:
      ce.c ⊔ ce.b₁ = ce.top
      := by
        let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        apply le_antisymm ?le ?ge
        case le => exact sup_le c_le_top b₁_le_top
        case ge => calc
          ce.top
          _ = c ⊔ a₁  := c_sup_a₁.symm
          _ ≤ c ⊔ b₁  := sup_le_sup_left a₁_le_b₁ c

    @[simp]
    lemma b₁_sup_c:
      ce.b₁ ⊔ ce.c = ce.top
      := calc
        ce.b₁ ⊔ ce.c  = ce.c ⊔ ce.b₁  := sup_comm
        _             = ce.top        := ce.c_sup_b₁

  end sup

  section inf

    @[simp]
    lemma bot_inf_top:
      ce.bot ⊓ ce.top = ce.bot
      := inf_eq_left.mpr ce.bot_le_top

    @[simp]
    lemma top_inf_bot:
      ce.top ⊓ ce.bot = ce.bot
      := inf_eq_right.mpr ce.bot_le_top

    @[simp]
    lemma bot_inf_a₁:
      ce.bot ⊓ ce.a₁ = ce.bot
      := inf_eq_left.mpr ce.bot_le_a₁

    @[simp]
    lemma a₁_inf_bot:
      ce.a₁ ⊓ ce.bot = ce.bot
      := inf_eq_right.mpr ce.bot_le_a₁

    @[simp]
    lemma bot_inf_b₁:
      ce.bot ⊓ ce.b₁ = ce.bot
      := inf_eq_left.mpr ce.bot_le_b₁

    @[simp]
    lemma b₁_inf_bot:
      ce.b₁ ⊓ ce.bot = ce.bot
      := inf_eq_right.mpr ce.bot_le_b₁

    @[simp]
    lemma bot_inf_c:
      ce.bot ⊓ ce.c = ce.bot
      := inf_eq_left.mpr ce.bot_le_c

    @[simp]
    lemma c_inf_bot:
      ce.c ⊓ ce.bot = ce.bot
      := inf_eq_right.mpr ce.bot_le_c

    @[simp]
    lemma top_inf_a₁:
      ce.top ⊓ ce.a₁ = ce.a₁
      := inf_eq_right.mpr ce.a₁_le_top

    @[simp]
    lemma a₁_inf_top:
      ce.a₁ ⊓ ce.top = ce.a₁
      := inf_eq_left.mpr ce.a₁_le_top

    @[simp]
    lemma top_inf_b₁:
      ce.top ⊓ ce.b₁ = ce.b₁
      := inf_eq_right.mpr ce.b₁_le_top

    @[simp]
    lemma b₁_inf_top:
      ce.b₁ ⊓ ce.top = ce.b₁
      := inf_eq_left.mpr ce.b₁_le_top

    @[simp]
    lemma top_inf_c:
      ce.top ⊓ ce.c = ce.c
      := inf_eq_right.mpr ce.c_le_top

    @[simp]
    lemma c_inf_top:
      ce.c ⊓ ce.top = ce.c
      := inf_eq_left.mpr ce.c_le_top

    @[simp]
    lemma a₁_inf_b₁:
      ce.a₁ ⊓ ce.b₁ = ce.a₁
      := inf_eq_left.mpr ce.a₁_le_b₁

    @[simp]
    lemma b₁_inf_a₁:
      ce.b₁ ⊓ ce.a₁ = ce.a₁
      := inf_eq_right.mpr ce.a₁_le_b₁

    @[simp]
    lemma c_inf_b₁:
      ce.c ⊓ ce.b₁ = ce.bot
      := by
        let a := ce.a; let b := ce.b; let c := ce.c; let b₁ := ce.b₁
        calc
          c ⊓ b₁
          _ = c ⊓ (b ⊓ (a ⊔ c)) := rfl
          _ = c ⊓ (b ⊓ (c ⊔ a)) := by congr 2; exact sup_comm
          _ = c ⊓ ((c ⊔ a) ⊓ b) := by congr 1; exact inf_comm
          _ = c ⊓ (c ⊔ a) ⊓ b   := inf_assoc.symm
          _ = c ⊓ b             := by congr 1; exact inf_sup_self

    @[simp]
    lemma b₁_inf_c:
      ce.b₁ ⊓ ce.c = ce.bot
      := calc
        ce.b₁ ⊓ ce.c  = ce.c ⊓ ce.b₁  := inf_comm
        _             = ce.bot        := ce.c_inf_b₁

    @[simp]
    lemma c_inf_a₁:
      ce.c ⊓ ce.a₁ = ce.bot
      := by
        let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        apply le_antisymm ?le ?ge
        case le => calc
          c ⊓ a₁  ≤ c ⊓ b₁  := inf_le_inf_left c a₁_le_b₁
          _       = ce.bot  := c_inf_b₁
        case ge => exact le_inf bot_le_c bot_le_a₁

    @[simp]
    lemma a₁_inf_c:
      ce.a₁ ⊓ ce.c = ce.bot
      := calc
        ce.a₁ ⊓ ce.c  = ce.c ⊓ ce.a₁  := inf_comm
        _             = ce.bot        := ce.c_inf_a₁

  end inf

  section not

    @[simp]
    lemma b₁_not_le_a₁:
      ¬ ce.b₁ ≤ ce.a₁
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        rintro h: b₁ ≤ a₁; apply ce.nonmodular
        calc
          (a ⊔ c) ⊓ b
          _ = b₁          := inf_comm
          _ ≤ a₁          := h
          _ = a ⊔ (c ⊓ b) := by rw [inf_comm]

    @[simp]
    lemma a_not_le_c:
      ¬ ce.a ≤ ce.c
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        rintro h: a ≤ c
        have: a ⊔ c = c := sup_eq_right.mpr h
        have: b₁ ≤ a₁ := calc
          b₁  = b ⊓ c := by rw [←this]
          _   ≤ a₁    := le_sup_right
        exact ce.b₁_not_le_a₁ this

    @[simp]
    lemma c_not_le_b:
      ¬ ce.c ≤ ce.b
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        rintro h: c ≤ b
        have: b ⊓ c = c := inf_eq_right.mpr h
        have: b₁ ≤ a₁ := calc
          b₁  ≤ a ⊔ c := inf_le_right
          _   = a₁    := by rw [←this]
        exact ce.b₁_not_le_a₁ this

    @[simp]
    lemma a₁_ne_b₁:
      ce.a₁ ≠ ce.b₁
      := by
        let a₁ := ce.a₁; let b₁ := ce.b₁
        rintro h: a₁ = b₁
        apply ce.b₁_not_le_a₁; show b₁ ≤ a₁
        rw [h]

    @[simp]
    lemma top_ne_bot:
      ce.top ≠ ce.bot
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        rintro h: c ⊔ a = c ⊓ b
        have: a₁ = b₁ := calc
          a₁
          _ = a ⊔ c ⊓ b   := by rw [inf_comm]
          _ = a ⊔ (c ⊔ a) := by congr 1; exact h.symm
          _ = c ⊔ a ⊔ a   := sup_comm
          _ = c ⊔ a       := by rw [sup_assoc, sup_idem]
          _ = c ⊓ b       := h
          _ = c ⊓ (b ⊓ b) := by congr 1; exact inf_idem.symm
          _ = b ⊓ c ⊓ b   := by rw [← inf_assoc]; congr 1; exact inf_comm
          _ = b ⊓ (a ⊔ c) := by rw [inf_assoc, h.symm, sup_comm]
          _ = b₁          := rfl
        exact ce.a₁_ne_b₁ this

    @[simp]
    lemma b₁_ne_top:
      ce.b₁ ≠ ce.top
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        let b₁ := ce.b₁
        rintro h: b₁ = c ⊔ a
        have: b ⊓ (a ⊔ c) = a ⊔ c := Eq.trans h sup_comm
        have: a ⊔ c ≤ b := inf_eq_right.mp this
        have: c ≤ b := le_trans le_sup_right this
        exact ce.c_not_le_b this

    @[simp]
    lemma a₁_ne_bot:
      ce.a₁ ≠ ce.bot
      := by
        let a := ce.a; let b := ce.b; let c := ce.c
        let a₁ := ce.a₁
        rintro h: a₁ = c ⊓ b
        have: a ⊔ b ⊓ c = b ⊓ c := Eq.trans h inf_comm
        have: a ≤ b ⊓ c := sup_eq_right.mp this
        have: a ≤ c := le_trans this inf_le_right
        exact ce.a_not_le_c this

    @[simp]
    lemma b₁_ne_bot:
      ce.b₁ ≠ ce.bot
      := by
        let b := ce.b; let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        rintro h: b₁ = c ⊓ b
        have: b₁ ≤ a₁ := calc
          b₁  = c ⊓ b := h
          _   = b ⊓ c := inf_comm
          _   ≤ a₁    := le_sup_right
        exact ce.b₁_not_le_a₁ this

    @[simp]
    lemma a₁_ne_top:
      ce.a₁ ≠ ce.top
      := by
        let a := ce.a; let c := ce.c
        let a₁ := ce.a₁; let b₁ := ce.b₁
        rintro h: a₁ = c ⊔ a
        have: b₁ ≤ a₁ := calc
          b₁  ≤ a ⊔ c := inf_le_right
          _   = c ⊔ a := sup_comm
          _   = a₁    := h.symm
        exact ce.b₁_not_le_a₁ this

    @[simp]
    lemma a₁_not_le_c:
      ¬ ce.a₁ ≤ ce.c
      := by
        let a := ce.a; let c := ce.c
        let a₁ := ce.a₁
        rintro h: a₁ ≤ c
        have: a ≤ c := by
          apply sup_eq_left.mp; show ce.top = c
          rw [← ce.c_sup_a₁]; exact sup_eq_left.mpr h
        exact ce.a_not_le_c this

    @[simp]
    lemma c_not_le_a₁:
      ¬ ce.c ≤ ce.a₁
      := by
        let c := ce.c
        let a₁ := ce.a₁
        rintro h: c ≤ a₁
        have: a₁ = ce.top := calc
          a₁  = c ⊔ a₁  := sup_eq_right.mpr h |>.symm
          _   = ce.top  := ce.c_sup_a₁
        exact ce.a₁_ne_top this

    @[simp]
    lemma a₁_ne_c:
      ce.a₁ ≠ ce.c
      := by
        let c := ce.c
        let a₁ := ce.a₁
        rintro h: a₁ = c
        have: a₁ ≤ c := by rw [h]
        exact ce.a₁_not_le_c this

    @[simp]
    lemma c_not_le_b₁:
      ¬ ce.c ≤ ce.b₁
      := by
        let b := ce.b; let c := ce.c
        let b₁ := ce.b₁
        rintro h: c ≤ b₁
        have: c ≤ b := by
          apply inf_eq_left.mp; show ce.bot = c
          rw [← ce.c_inf_b₁]; exact inf_eq_left.mpr h
        exact ce.c_not_le_b this

    @[simp]
    lemma b₁_not_le_c:
      ¬ ce.b₁ ≤ ce.c
      := by
        let c := ce.c
        let b₁ := ce.b₁
        rintro h: b₁ ≤ c
        have: b₁ = ce.bot := calc
          b₁  = c ⊓ b₁  := inf_eq_right.mpr h |>.symm
          _   = ce.bot  := ce.c_inf_b₁
        exact ce.b₁_ne_bot this

    @[simp]
    lemma b₁_ne_c:
      ce.b₁ ≠ ce.c
      := by
        let c := ce.c
        let b₁ := ce.b₁
        rintro h: b₁ = c
        have: c ≤ b₁ := by rw [h]
        exact ce.c_not_le_b₁ this

  end not

  @[simp]
  def N₅embedding (ce: NonmodularCE α):
    N₅ ↪ α := {
      toFun := λ
        | N₅.top => ce.top
        | N₅.bot => ce.bot
        | N₅.a   => ce.a₁
        | N₅.b   => ce.b₁
        | N₅.c   => ce.c
      inj' := by
        have := ce.a₁_ne_b₁
        have := ce.top_ne_bot
        have := ce.b₁_ne_top
        have := ce.a₁_ne_bot
        have := ce.b₁_ne_bot
        have := ce.a₁_ne_top
        have := ce.a₁_ne_c
        have := ce.b₁_ne_c
        intro x y h
        cases x; all_goals cases y
        all_goals try decide
        all_goals simp at h
        all_goals have := h.symm
        all_goals contradiction
    }

  @[simp]
  def N₅latticeEmbedding (ce: NonmodularCE α):
    N₅ ↪ℒ α := {
      N₅embedding ce with
      map_sup' := by
        intro x y
        cases x; all_goals cases y
        case top.top | bot.bot | a.a | b.b | c.c => exact sup_idem.symm
        case bot.top => exact bot_sup_top.symm
        case bot.a => exact bot_sup_a₁.symm
        case bot.b => exact bot_sup_b₁.symm
        case bot.c => exact bot_sup_c.symm
        case top.bot => exact top_sup_bot.symm
        case top.a => exact top_sup_a₁.symm
        case top.b => exact top_sup_b₁.symm
        case top.c => exact top_sup_c.symm
        case a.bot => exact a₁_sup_bot.symm
        case a.top => exact a₁_sup_top.symm
        case a.b => exact a₁_sup_b₁.symm
        case a.c => exact a₁_sup_c.symm
        case b.bot => exact b₁_sup_bot.symm
        case b.top => exact b₁_sup_top.symm
        case b.a => exact b₁_sup_a₁.symm
        case b.c => exact b₁_sup_c.symm
        case c.bot => exact c_sup_bot.symm
        case c.top => exact c_sup_top.symm
        case c.a => exact c_sup_a₁.symm
        case c.b => exact c_sup_b₁.symm
      map_inf' := by
        intro x y
        cases x; all_goals cases y
        case top.top | bot.bot | a.a | b.b | c.c => exact inf_idem.symm
        case bot.top => exact bot_inf_top.symm
        case bot.a => exact bot_inf_a₁.symm
        case bot.b => exact bot_inf_b₁.symm
        case bot.c => exact bot_inf_c.symm
        case top.bot => exact top_inf_bot.symm
        case top.a => exact top_inf_a₁.symm
        case top.b => exact top_inf_b₁.symm
        case top.c => exact top_inf_c.symm
        case a.bot => exact a₁_inf_bot.symm
        case a.top => exact a₁_inf_top.symm
        case a.b => exact a₁_inf_b₁.symm
        case a.c => exact a₁_inf_c.symm
        case b.bot => exact b₁_inf_bot.symm
        case b.top => exact b₁_inf_top.symm
        case b.a => exact b₁_inf_a₁.symm
        case b.c => exact b₁_inf_c.symm
        case c.bot => exact c_inf_bot.symm
        case c.top => exact c_inf_top.symm
        case c.a => exact c_inf_a₁.symm
        case c.b => exact c_inf_b₁.symm
    }

  end Lattice.NonmodularCE

  lemma Lattice.nonmodular_has_counter_example {α} [Lattice α]:
    ¬ IsModularLattice α → Nonempty (NonmodularCE α)
    := by
      rintro h: ¬ IsModularLattice α
      have: ¬ ∀ x y z: α, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z := by
        intro modular
        have := IsModularLattice.mk (λ y ↦ modular _ y _)
        contradiction
      have ⟨a, this⟩ := Classical.exists_not_of_not_forall this
      have ⟨c, this⟩ := Classical.exists_not_of_not_forall this
      have ⟨b, this⟩ := Classical.exists_not_of_not_forall this
      have ⟨(hab: a ≤ b), (habc: ¬ (a ⊔ c) ⊓ b ≤ a ⊔ c ⊓ b)⟩ := not_imp.mp this
      exact ⟨⟨a, b, c, hab, habc⟩⟩

  -- Theorem 3.5

  theorem Lattice.nonmodular_iff_has_N₅ {α} [Lattice α]:
    ¬ IsModularLattice α ↔ Nonempty (N₅ ↪ℒ α)
    := by
      apply Iff.intro ?mp ?mpr
      case mp =>
        rintro h: ¬ IsModularLattice α
        let ⟨ce⟩ := nonmodular_has_counter_example h
        exact ⟨ce.N₅latticeEmbedding⟩
      case mpr =>
        rintro ⟨f: N₅ ↪ℒ α⟩
        intro modular
        let a := f N₅.a; let b := f N₅.b; let c := f N₅.c
        have: a ≤ b := f.monotone (by decide)
        have h: (a ⊔ c) ⊓ b ≤ a ⊔ c ⊓ b :=
          modular.sup_inf_le_assoc_of_le _ this
        have: f ((N₅.a ⊔ N₅.c) ⊓ N₅.b) = (a ⊔ c) ⊓ b := calc
          f ((N₅.a ⊔ N₅.c) ⊓ N₅.b)
          _ = f (N₅.a ⊔ N₅.c) ⊓ f N₅.b    := map_inf f _ _
          _ = (f N₅.a ⊔ f N₅.c) ⊓ f N₅.b  := by congr 1; exact map_sup f _ _
          _ = (a ⊔ c) ⊓ b                 := rfl
        rw [← this] at h
        have: f (N₅.a ⊔ (N₅.c ⊓ N₅.b)) = a ⊔ c ⊓ b := calc
          f (N₅.a ⊔ (N₅.c ⊓ N₅.b))
          _ = f N₅.a ⊔ f (N₅.c ⊓ N₅.b)    := map_sup f _ _
          _ = f N₅.a ⊔ (f N₅.c ⊓ f N₅.b)  := by congr 1; exact map_inf f _ _
          _ = a ⊔ c ⊓ b                 := rfl
        rw [← this] at h
        have: f N₅.b ≤ f N₅.a := h
        have: N₅.b ≤ N₅.a := f.le_iff_le.mp this
        contradiction

end «Nonmodular lattices have N₅»
