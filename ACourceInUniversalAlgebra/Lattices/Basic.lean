import Paperproof

import «ACourceInUniversalAlgebra».Preliminaries.Notation

import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.ModularLattice
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Lattice
import Mathlib.Data.Set.Finite

section «Lattices»

  section «Definitions of Lattices»

    -- Definition 1.1
    -- Definition 1.2
    -- Definition 1.3
    -- skipped
    #check Lattice

    -- Examples.

    -- (1)
    abbrev Su α := Set α

    instance: Lattice (Su α) where
      sup := Set.union
      inf := Set.inter
      le_refl _ _ h := h
      le_antisymm _ _ hs₁s₂ hs₂s₁ := by
        funext; ext; apply Iff.intro ?mp ?mpr
        case mp => intro hx; exact hs₁s₂ hx
        case mpr => intro hx; exact hs₂s₁ hx
      le_trans _ _ _ hs₁s₂ hs₂s₃ _ hx := hs₂s₃ (hs₁s₂ hx)
      le_sup_left _ _ _ hx := Or.inl hx
      le_sup_right _ _ _ hx := Or.inr hx
      sup_le _ _ _ hs₁ hs₂ _ hx := Or.elim hx (λ hx ↦ hs₁ hx) (λ hx ↦ hs₂ hx)
      inf_le_left _ _ _ hx := hx.1
      inf_le_right _ _ _ hx := hx.2
      le_inf _ _ _ hs₁ hs₂ _ hx := ⟨hs₁ hx, hs₂ hx⟩

    -- (2)

    structure NatDvd where n: ℕ

    notation "ℕ_dvd" => NatDvd

    def NatDvd.ext {d₁ d₂: ℕ_dvd} (h: d₁.n = d₂.n): d₁ = d₂ := by
      cases d₁; cases d₂; congr

    instance: Lattice ℕ_dvd where
      le n m := n.n ∣ m.n
      le_refl _ := Nat.dvd_refl _
      le_antisymm _ _ h₁ h₂ := NatDvd.ext (Nat.dvd_antisymm h₁ h₂)
      le_trans _ _ _ := Nat.dvd_trans
      sup n m := ⟨n.n.lcm m.n⟩
      inf n m := ⟨n.n.gcd m.n⟩
      le_sup_left _ _ := Nat.dvd_lcm_left _ _
      le_sup_right _ _ := Nat.dvd_lcm_right _ _
      sup_le _ _ _ := Nat.lcm_dvd
      inf_le_left _ _ := Nat.gcd_dvd_left _ _
      inf_le_right _ _ := Nat.gcd_dvd_right _ _
      le_inf _ _ _ := Nat.dvd_gcd

    -- (3)
    -- Omitted.

  end «Definitions of Lattices»

  section «Isomorphic Lattices, and Sublattices»

    -- Definition 2.1
    -- skipped

    #check OrderIso

    -- Definition 2.2
    -- skipped

    #check Monotone

    --

    def OrderIso.of_monotone_with_inv_monotone {α} {β} [Lattice α] [Lattice β]
      (f: α →o β) (g: β →o α)
      (hgf: g ∘ f = id) (hfg: f ∘ g = id):
      α ≃o β
      := by
        let toEquiv: α ≃ β := {
          toFun := f
          invFun := g
          left_inv := by intro a; calc
            g (f a) = (g ∘ f) a := rfl
            _       = a         := hgf ▸ rfl
          right_inv := by intro a; calc
            f (g a) = (f ∘ g) a := rfl
            _       = a         := hfg ▸ rfl
        }
        constructor
        case toEquiv => exact toEquiv
        case map_rel_iff' =>
          intro a b; show f a ≤ f b ↔ a ≤ b
          apply Iff.intro ?mp ?mpr
          case mp => rintro h: f a ≤ f b; calc
            a = id a      := rfl
            _ = (g ∘ f) a := by rw [hgf]
            _ = g (f a)   := rfl
            _ ≤ g (f b)   := g.monotone h
            _ = (g ∘ f) b := rfl
            _ = id b      := by rw [hgf]
            _ = b         := rfl
          case mpr => intro h; exact f.monotone h

    def OrderIso.monotone_with_inv_monotone {α} {β} [Lattice α] [Lattice β] (iso: α ≃o β):
      let f := iso.toFun
      let g := iso.invFun
      g ∘ f = id ∧ f ∘ g = id ∧ Monotone f ∧ Monotone g
      := by
        intro f g
        let hgf: g ∘ f = id := by funext; exact iso.left_inv _
        let hfg: f ∘ g = id := by funext; exact iso.right_inv _
        let hf: Monotone f := by intro _ _; exact iso.map_rel_iff'.mpr
        let hg: Monotone g := by
          intro a b; rintro h: a ≤ b
          have: f (g a) ≤ f (g b) := calc
            f (g a)
            _ = (f ∘ g) a := rfl
            _ = id a      := by rw [hfg]
            _ = a         := rfl
            _ ≤ b         := h
            _ = id b      := rfl
            _ = (f ∘ g) b := by rw [hfg]
            _ = f (g b)   := rfl
          exact iso.map_rel_iff'.mp this
        exact ⟨hgf, hfg, hf, hg⟩

    -- Theorem 2.3

    theorem OrderIso.iff_monotone_with_inv_monotone {α} {β} [Lattice α] [Lattice β]:
      Nonempty (α ≃o β) ↔ ∃ (f: α → β) (g: β → α), g ∘ f = id ∧ f ∘ g = id ∧ Monotone f ∧ Monotone g
      := by
        apply Iff.intro ?mp ?mpr
        case mp =>
          intro ⟨iso⟩
          exists iso.toFun, iso.invFun
          exact iso.monotone_with_inv_monotone
        case mpr =>
          intro ⟨f, g, hgf, hfg, hf, hg⟩
          let fo := OrderHom.mk f hf
          let go := OrderHom.mk g hg
          exact ⟨OrderIso.of_monotone_with_inv_monotone fo go hgf hfg⟩

    -- Definition 2.4

    structure Lattice.Embedding (α) (β) [Lattice α] [Lattice β] extends α ↪ β, LatticeHom α β

    infixr:25 " ↪ℒ " => Lattice.Embedding

    instance Lattice.Embedding.instLatticeHomClass {α} {β} [Lattice α] [Lattice β]:
      LatticeHomClass (α ↪ℒ β) α β where
      coe f := f.toFun
      coe_injective' := by
        intro f g h; cases f; cases g; simp at h; congr
      map_sup f := f.map_sup'
      map_inf f := f.map_inf'

    lemma Lattice.Embedding.monotone {α} {β} [Lattice α] [Lattice β] (f: α ↪ℒ β):
      Monotone f
      := by
        intro a b
        rintro h: a ≤ b; show f a ≤ f b
        apply sup_eq_right.mp _; show f a ⊔ f b = f b
        calc
          f a ⊔ f b
          _ = f (a ⊔ b) := map_sup f a b |>.symm
          _ = f b       := by congr; exact sup_eq_right.mpr h

    lemma Lattice.Embedding.le_iff_le {α} {β} [Lattice α] [Lattice β] (f: α ↪ℒ β) {a b: α}:
      f a ≤ f b ↔ a ≤ b
      := by
        apply Iff.intro ?mp ?mpr
        case mpr => intro h; exact f.monotone h
        case mp =>
          rintro h: f a ≤ f b; show a ≤ b
          apply sup_eq_right.mp _; show a ⊔ b = b
          apply f.injective; show f (a ⊔ b) = f b
          calc
            f (a ⊔ b) = f a ⊔ f b := map_sup f a b
            _         = f b       := sup_eq_right.mpr h

    -- Definition 2.5

    def Lattice.Embedded α β [Lattice α] [Lattice β] :=
      Nonempty (α ↪ℒ β)

  end «Isomorphic Lattices, and Sublattices»

  section «Distributive and Modular Lattices»

    -- Definition 3.1

    #check DistribLattice

    structure Lattice.IsDistribLattice (α) [Lattice α]: Prop where
      inf_sup_left: ∀ {x y z: α}, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)

    instance Lattice.IsDistribLattice.toDistribLattice {α} [Lattice α] (h: IsDistribLattice α):
      DistribLattice α :=
        DistribLattice.ofInfSupLe (λ _ _ _ ↦ le_of_eq h.inf_sup_left)

    -- Theorem 3.2

    theorem Lattice.IsDistribLattice.iff_inf_sup_left {α} [Lattice α]:
      IsDistribLattice α ↔
      (∀ {x y z: α}, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
      := by
        apply Iff.intro ?mp ?mpr
        case mp => intro h x y z; calc
          x ⊔ (y ⊓ z)
          _ = (x ⊔ (x ⊓ z)) ⊔ (y ⊓ z) := by congr 1; exact sup_inf_self.symm
          _ = x ⊔ ((x ⊓ z) ⊔ (y ⊓ z)) := sup_assoc
          _ = x ⊔ ((z ⊓ x) ⊔ (z ⊓ y)) := by congr 2; repeat exact inf_comm
          _ = x ⊔ (z ⊓ (x ⊔ y))       := by congr 1; exact h.inf_sup_left.symm
          _ = x ⊔ ((x ⊔ y) ⊓ z)       := by congr 1; exact inf_comm
          _ = (x ⊓ (x ⊔ y)) ⊔ ((x ⊔ y) ⊓ z) := by congr 1; exact inf_sup_self.symm
          _ = ((x ⊔ y) ⊓ x) ⊔ ((x ⊔ y) ⊓ z) := by congr 1; exact inf_comm
          _ = (x ⊔ y) ⊓ (x ⊔ z)       := h.inf_sup_left.symm
        case mpr => intro h; constructor; intro x y z; calc
          x ⊓ (y ⊔ z)
          _ = (x ⊓ (x ⊔ z)) ⊓ (y ⊔ z) := by congr 1; exact inf_sup_self.symm
          _ = x ⊓ ((x ⊔ z) ⊓ (y ⊔ z)) := inf_assoc
          _ = x ⊓ ((z ⊔ x) ⊓ (z ⊔ y)) := by congr 2; repeat exact sup_comm
          _ = x ⊓ (z ⊔ (x ⊓ y))       := by congr 1; exact h.symm
          _ = x ⊓ ((x ⊓ y) ⊔ z)       := by congr 1; exact sup_comm
          _ = (x ⊔ (x ⊓ y)) ⊓ ((x ⊓ y) ⊔ z) := by congr 1; exact sup_inf_self.symm
          _ = ((x ⊓ y) ⊔ x) ⊓ ((x ⊓ y) ⊔ z) := by congr 1; exact sup_comm
          _ = (x ⊓ y) ⊔ (x ⊓ z)       := h.symm


    -- Definition 3.3
    -- skipped

    #check IsModularLattice

    -- Theorem 3.4

    lemma Lattice.IsDistribLattice.modular {α} [Lattice α]:
      IsDistribLattice α → IsModularLattice α
      := by
        intro distrib
        apply IsModularLattice.mk
        intro x y z; rintro h: x ≤ z
        show (x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)
        apply le_of_eq
        calc
          (x ⊔ y) ⊓ z
          _ = z ⊓ (x ⊔ y)       := inf_comm
          _ = (z ⊓ x) ⊔ (z ⊓ y) := distrib.inf_sup_left
          _ = x ⊔ (z ⊓ y)       := by congr 1; exact inf_eq_right.mpr h
          _ = x ⊔ (y ⊓ z)       := by congr 1; exact inf_comm

    --

    inductive Lattice.M₃
      | top | bot | a | b | c
      deriving DecidableEq, Repr

    @[simp]
    instance Lattice.M₃.instSup: Sup M₃ where
      sup := λ
      | bot, z | z, bot => z
      | x, y => if x = y then x else top

    @[simp]
    instance Lattice.M₃.instInf: Inf M₃ where
      inf := λ
      | top, z | z, top => z
      | x, y => if x = y then x else bot

    instance Lattice.M₃.instLattice: Lattice M₃ := by
      apply mk'
      case sup_comm | inf_comm | sup_inf_self | inf_sup_self =>
        intro x y; cases x; all_goals cases y
        all_goals decide
      case sup_assoc | inf_assoc =>
        intro x y z; cases x; all_goals cases y; all_goals cases z
        all_goals decide

    instance Lattice.M₃.instDecidableLE {x y: M₃}: Decidable (x ≤ y) := by
      have: (x ≤ y) = (x ⊔ y = y) := by
        ext; apply Iff.intro ?mp ?mpr
        case mp => intro h; exact h
        case mpr => intro h; exact h
      rw [this]; exact inferInstance

    instance Lattice.M₃.instModularLattice: IsModularLattice M₃ := by
      constructor
      intro x y z; show x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z
      cases x; all_goals cases y; all_goals cases z
      all_goals decide

    lemma Lattice.M₃.nondistrib:
      ¬ ∀ x y z : M₃, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
      := by intro distrib; specialize distrib a b c; contradiction

    inductive Lattice.N₅
      | top | bot | a | b | c
      deriving DecidableEq, Repr

    @[simp]
    instance Lattice.N₅.instSup: Sup N₅ where
      sup := λ
      | bot, z | z, bot => z
      | a, b | b, a => b
      | x, y => if x = y then x else top

    @[simp]
    instance Lattice.N₅.instInf: Inf N₅ where
      inf := λ
      | top, z | z, top => z
      | a, b | b, a => a
      | x, y => if x = y then x else bot

    instance Lattice.N₅.instLattice: Lattice N₅ := by
      apply mk'
      case sup_comm | inf_comm | sup_inf_self | inf_sup_self =>
        intro x y; cases x; all_goals cases y
        all_goals decide
      case sup_assoc | inf_assoc =>
        intro x y z; cases x; all_goals cases y; all_goals cases z
        all_goals decide

    instance Lattice.N₅.instDecidableLE {x y: N₅}: Decidable (x ≤ y) := by
      have: (x ≤ y) = (x ⊔ y = y) := by
        ext; apply Iff.intro ?mp ?mpr
        case mp => intro h; exact h
        case mpr => intro h; exact h
      rw [this]; exact inferInstance

    lemma Lattice.N₅.nonmodular:
      ¬ IsModularLattice N₅
      := by
        intro modular
        have := modular.sup_inf_le_assoc_of_le (x := a) c (z := b) (by decide)
        contradiction

    -- Theorem 3.5
    -- placed in «ACourceInUniversalAlgebra».N₅Embedding

    -- Theorem 3.6
    -- placed in «ACourceInUniversalAlgebra».M₃Embedding

  end «Distributive and Modular Lattices»

  section «Complete Lattices, Equivalence Relations, and Algebraic Lattices»

    -- Definition 4.1
    -- skipped

    #check CompleteLattice

    -- Theorem 4.2
    -- TODO: prove on precise statement

    lemma sup_complete_iff_inf_complete {α} [PartialOrder α]:
      (∀ S: Set α, ∃ x: α, IsLUB S x) ↔ (∀ S: Set α, ∃ x: α, IsGLB S x)
      := by
        apply Iff.intro ?mp ?mpr
        case mp =>
          rintro h: ∀ S, ∃ x, IsLUB S x
          intro S
          show ∃ x, IsGLB S x
          let S' := lowerBounds S
          have ⟨x, hx⟩: ∃ x, IsLUB S' x := h S'
          exists x
          constructor
          case left =>
            intro y (hy: y ∈ S)
            apply hx.right
            intro z (hz: z ∈ S')
            exact hz hy
          case right =>
            intro y (hy: y ∈ S')
            exact hx.left hy
        case mpr =>
          rintro h: ∀ S, ∃ x, IsGLB S x
          intro S
          show ∃ x, IsLUB S x
          let S' := upperBounds S
          have ⟨x, hx⟩: ∃ x, IsGLB S' x := h S'
          exists x
          constructor
          case left =>
            intro y (hy: y ∈ S)
            apply hx.right
            intro z (hz: z ∈ S')
            exact hz hy
          case right =>
            intro y (hy: y ∈ S')
            exact hx.left hy

    -- Examples
    -- TODO

    -- Definition 4.3
    -- TODO

  end «Complete Lattices, Equivalence Relations, and Algebraic Lattices»

  section «Closure Operators»

    -- Definition 5.1

    structure ClosureOperator (α) where
      cl: Su α → Su α
      cl_extensive {S}: S ⊆ cl S
      cl_idem' {S}: cl (cl S) ⊆ cl S
      cl_isotone {S T}: S ⊆ T → cl S ⊆ cl T

    instance ClosureOperator.toFun {α}: CoeFun (ClosureOperator α) (λ _ ↦ Su α → Su α) where
      coe c := c.cl

    def ClosureOperator.IsClosed {α} (C: ClosureOperator α) (S: Su α): Prop :=
      C S = S

    def ClosureOperator.Closed {α} (C: ClosureOperator α) :=
      {S // C S = S}

    @[simp]
    instance ClosureOperator.Closed.instMembership {α} (C: ClosureOperator α):
      Membership α (ClosureOperator.Closed C) where
      mem x S := x ∈ S.val

    @[simp]
    instance ClosureOperator.Closed.instHasSubset {α} (C: ClosureOperator α):
      HasSubset (ClosureOperator.Closed C) where
      Subset S T := S.val ⊆ T.val

    @[simp]
    instance ClosureOperator.Closed.instPartialOrder {α} (C: ClosureOperator α):
      PartialOrder (ClosureOperator.Closed C) where
      le S T := S ⊆ T
      le_refl S := subset_refl S.val
      le_antisymm S T hST hTS := by
        cases S; cases T; congr; simp at hST hTS; exact subset_antisymm hST hTS
      le_trans S T U hST hTU := by
        show S.val ⊆ U.val; apply subset_trans; exact hST; exact hTU

    lemma ClosureOperator.cl_idem {α} (C: ClosureOperator α) {S: Su α}:
      C (C S) = C S
      := by
        apply subset_antisymm ?le ?ge
        case le =>
          exact C.cl_idem'
        case ge =>
          apply C.cl_isotone
          exact C.cl_extensive

    -- Theorem 5.2

    instance ClosureOperator.Closed.instInfSet {α} (C: ClosureOperator α):
      InfSet (ClosureOperator.Closed C)
      where
        sInf Ss := {
          val := ⋂ S ∈ Ss, S.val
          property := by
            apply subset_antisymm ?le ?ge
            case le =>
              show C (⋂ S ∈ Ss, S.val) ⊆ ⋂ S ∈ Ss, S.val
              apply Set.subset_iInter _; simp
              intro S (hS: S ∈ Ss); show C (⋂ S' ∈ Ss, S'.val) ⊆ S.val
              have: S.val = C S.val := S.property.symm
              rw [this]; show C (⋂ S' ∈ Ss, S'.val) ⊆ C S.val
              apply C.cl_isotone _; show ⋂ S' ∈ Ss, S'.val ⊆ S.val
              apply Set.iInter_subset_of_subset S _
              exact Set.iInter_subset_of_subset hS (subset_refl _)
            case ge => exact C.cl_extensive
        }

    instance ClosureOperator.Closed.instCompleteLattice {α} (C: ClosureOperator α):
      CompleteLattice (ClosureOperator.Closed C) := by
        apply completeLatticeOfInf _
        intro Ss; show IsGLB Ss (sInf Ss)
        constructor
        case left =>
          intro S hS
          show sInf Ss ≤ S
          exact Set.iInter₂_subset_of_subset S hS (subset_refl _)
        case right =>
          intro S (hS: ∀ T ∈ Ss, S ≤ T)
          show S ≤ sInf Ss
          apply Set.subset_iInter₂ _; intro T (hT: T ∈ Ss)
          exact hS T hT

    @[simp]
    def ClosureOperator.Closed.sSup' {α} {C: ClosureOperator α} (Ss: Set C.Closed):
      C.Closed
      where
        val := C (⋃ S ∈ Ss, S.val)
        property := C.cl_idem

    theorem ClosureOperator.Closed.sSup_eq {α} (C: ClosureOperator α) (Ss: Set C.Closed):
      sSup Ss = sSup' Ss
      := by
        apply le_antisymm ?le ?ge
        case le =>
          apply sSup_le _
          intro S (hS: S ∈ Ss)
          apply le_trans (b := ⋃ S ∈ Ss, S.val) ?left ?right
          case left => exact Set.subset_iUnion₂_of_subset S hS (subset_refl _)
          case right => exact C.cl_extensive
        case ge =>
          have: ⋃ S ∈ Ss, S.val ⊆ (sSup Ss).val := by
            apply Set.iUnion₂_subset
            intro S (hS: S ∈ Ss); show S ⊆ sSup Ss
            exact le_sSup hS
          show (sSup' Ss).val ⊆ (sSup Ss).val
          calc
            (sSup' Ss).val
            _ = C (⋃ S ∈ Ss, S.val) := rfl
            _ ⊆ C (sSup Ss).val     := C.cl_isotone this
            _ = (sSup Ss).val       := (sSup Ss).property

    --

    @[simp]
    def CompleteLattice.SupLower α [CompleteLattice α]: ClosureOperator α where
      cl S := {x | x ≤ sSup S}
      cl_extensive := by
        intro S; show S ⊆ {x | x ≤ sSup S}
        intro x (hx: x ∈ S); show x ≤ sSup S
        exact le_sSup _ _ hx
      cl_idem' := by
        intro S
        show {x | x ≤ sSup {y | y ≤ sSup S}} ⊆ {x | x ≤ sSup S}
        suffices sSup {y | y ≤ sSup S} ≤ sSup S by
          intro x hx; exact le_trans hx this
        apply sSup_le _
        intro y (hy: y ≤ sSup S); exact hy
      cl_isotone := by
        intro S T (hST: S ⊆ T)
        show ∀ x, x ≤ sSup S → x ≤ sSup T
        suffices sSup S ≤ sSup T by intro x hx; exact le_trans hx this
        exact sSup_le_sSup hST

    lemma CompleteLattice.SupLower.sup_lower' {α} [CompleteLattice α] (x: α):
      sSup {z | z ≤ x} = x
      := by
        apply le_antisymm ?le ?ge
        case le =>
          apply sSup_le _
          intro z (hz: z ≤ x); exact hz
        case ge =>
          apply le_sSup; show x ≤ x; trivial

    def CompleteLattice.SupLower.lower {α} [CompleteLattice α] (x: α):
      (SupLower α).Closed
      where
        val := {y | y ≤ x}
        property := by
          show {y | y ≤ sSup {z | z ≤ x}} = {y | y ≤ x}
          rw [sup_lower']

    def CompleteLattice.SupLower.isom (α) [CompleteLattice α]:
      α ≃o (SupLower α).Closed
      where
        toFun x := lower x
        invFun S := sSup S.val
        left_inv x := by
          show sSup {z | z ≤ x} = x
          apply le_antisymm ?le ?ge
          case le =>
            apply sSup_le _
            intro z (hz: z ≤ x); exact hz
          case ge =>
            apply le_sSup; show x ≤ x; trivial
        right_inv S := by
          show lower (sSup S.val) = S
          apply le_antisymm ?le ?ge
          case le =>
            intro x (hx: x ≤ sSup S.val); show x ∈ S.val
            rw [S.property.symm]; show x ≤ sSup S.val
            exact hx
          case ge =>
            intro x (hx: x ∈ S); show x ≤ sSup S.val
            exact le_sSup _ _ hx
        map_rel_iff' := by
          intro x y
          show lower x ≤ lower y ↔ x ≤ y
          apply Iff.intro ?mp ?mpr
          case mp =>
            rintro h: lower x ≤ lower y
            show x ≤ y
            rw [←sup_lower' x, ←sup_lower' y]
            show sSup (lower x).val ≤ sSup (lower y).val
            exact sSup_le_sSup h
          case mpr =>
            rintro h: x ≤ y
            intro z (hz: z ≤ x); show z ≤ y
            exact le_trans hz h

    -- Theorem 5.3

    theorem CompleteLattice.iso_closed_subsets {α} [CompleteLattice α]:
      ∃ C: ClosureOperator α, Nonempty (α ≃o C.Closed)
      := by
        exists SupLower α; exact ⟨SupLower.isom α⟩

    -- Definition 5.4

    structure AlgebraicClosureOperator (α) [CompleteLattice α] extends ClosureOperator α where
      algebraic {S}: cl S = ⋃ T ∈ {T | T ≤ S ∧ T.Finite}, cl T

    def AlgebraicClosureOperator.mk' {α} [CompleteLattice α]
      (cl: Su α → Su α)
      (cl_extensive: ∀ {S}, S ⊆ cl S)
      (cl_idem': ∀ {S}, cl (cl S) ⊆ cl S)
      (algebraic: ∀ {S}, cl S = ⋃ T ∈ {T | T ≤ S ∧ T.Finite}, cl T):
      AlgebraicClosureOperator α
      where
        cl := cl
        cl_extensive S := cl_extensive S
        cl_idem' S := cl_idem' S
        algebraic := algebraic
        cl_isotone := by
          intro S T (hST: S ⊆ T)
          rw [algebraic, algebraic]
          show ⋃ U ∈ {U | U ≤ S ∧ U.Finite}, cl U ⊆ ⋃ U ∈ {U | U ≤ T ∧ U.Finite}, cl U
          apply Set.iUnion₂_subset
          intro U (hU: U ≤ S ∧ U.Finite)
          show cl U ⊆ ⋃ U ∈ {U | U ≤ T ∧ U.Finite}, cl U
          apply subset_trans _ (Set.subset_iUnion₂ U _)
          exact subset_refl _
          have hSU: U ⊆ T := subset_trans hU.left hST
          exact ⟨hSU, hU.right⟩

    -- TODO
  end «Closure Operators»

end «Lattices»
