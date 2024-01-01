import Paperproof

import Mathlib.Data.Vector.Basic

import «ACourceInUniversalAlgebra».Lattices.Basic

section «The Elements of Universal Algebra»
  section «Definitions and Examples of Algebras»

    @[simp]
    instance {α} {n}: Membership (α) (Vector α n) where
      mem a v := a ∈ v.toList

    infixr:90 " $ᵥ " => Vector.map

    -- Definition 1.1

    def NAry (α: Type u) (n: ℕ): Type u := Vector α n → α

    structure Finitary (α) where
      arity: ℕ
      eval: NAry α arity

    abbrev Nullary α := NAry α 0
    abbrev Unary α := NAry α 1
    abbrev Binary α := NAry α 2
    abbrev Ternary α := NAry α 3

    -- Definition 1.2

    structure Language where
      sym: Type u
      arity: sym → ℕ

    def Language.nArySym (L: Language) (n: ℕ): Type u :=
      { f: L.sym // L.arity f = n }

    -- Definition 1.3

    structure Alg (L: Language) where
      univ: Type u
      [nonempty: Nonempty univ]
      eval (f: L.sym): NAry univ (L.arity f)

    macro:max f:term noWs "⟦" alg:term "⟧": term =>
      `(Alg.eval $alg $f)

    -- TODO: Examples.

  end «Definitions and Examples of Algebras»

  section «Isomorphic Algebras, and Subalgebras»
    -- REMARK: We firstly define the notion of homomorphism, which is
    --  in a later section.

    -- Definition 6.1

    structure Hom {L: Language} (A: Alg L) (B: Alg L) where
      map: A.univ → B.univ
      preserve {f: L.sym}: ∀ {arg},
        map (A.eval f arg) = B.eval f (map $ᵥ arg)

    infixr:25 " →𝒜 " => Hom

    instance {L: Language} (A: Alg L) (B: Alg L): CoeFun (A →𝒜 B) (λ _ ↦ A.univ → B.univ) where
      coe h := h.map

    structure Epi {L: Language} (A: Alg L) (B: Alg L) extends A →𝒜 B where
      surjective: Function.Surjective map

    infixr:25 " ↠𝒜 " => Epi

    instance {L: Language} (A: Alg L) (B: Alg L): CoeFun (A ↠𝒜 B) (λ _ ↦ A.univ → B.univ) where
      coe h := h.map

    structure Mono {L: Language} (A: Alg L) (B: Alg L) extends A →𝒜 B where
      injective: Function.Injective map

    infixr:25 " ↪𝒜 " => Mono

    instance {L: Language} (A: Alg L) (B: Alg L): CoeFun (A ↪𝒜 B) (λ _ ↦ A.univ → B.univ) where
      coe h := h.map

    abbrev End {L: Language} (A: Alg L) := A →𝒜 A

    -- Definition 2.1

    structure Isom {L: Language} (A: Alg L) (B: Alg L) extends A →𝒜 B where
      inv': B.univ → A.univ
      inverse: Function.LeftInverse inv' map

    infixr:25 " ⭇𝒜 " => Isom

    abbrev Aut {L: Language} (A: Alg L) := A ⭇𝒜 A

    def Isomorphic {L: Language} (A: Alg L) (B: Alg L): Prop :=
      Nonempty (A ⭇𝒜 B)

    infixr:50 " ≅𝒜 " => Isomorphic

    class UpToIsom {L: Language} (p: Alg L → Prop): Prop where
      upToIsom: ∀ {A B: Alg L}, (A ⭇𝒜 B) → p A → p B

    def upToIsom {L: Language} {p: Alg L → Prop} [UpToIsom p]:
      ∀ {A B: Alg L}, (A ⭇𝒜 B) → p A → p B
      := UpToIsom.upToIsom

    -- Definition 2.2

    structure SubAlg {L: Language} (A: Alg L) where
      alg: Alg L
      embed: alg ↪𝒜 A

    structure SubUniv {L: Language} (A: Alg L) where
      set: Set A.univ
      closed: ∀ {f: L.sym} {arg},
        (∀ a ∈ arg, a ∈ set) → A.eval f arg ∈ set

    instance (A: Alg L): Membership A.univ (SubUniv A) where
      mem a S := a ∈ S.set



    def SubUniv.toSubAlg {L: Language} {A: Alg L} (S: SubUniv A) (nonempty: ∃ a, a ∈ S.set):
      SubAlg A
      where
        alg := {
          univ := { a // a ∈ S }
          nonempty := let ⟨a, haS⟩ := nonempty; ⟨⟨a, haS⟩⟩
          eval := λ f arg ↦ {
            val := f⟦A⟧ (Subtype.val $ᵥ arg)
            property := by
              show f⟦A⟧ (Subtype.val $ᵥ arg) ∈ S
              apply S.closed
              suffices ∀ n (arg: Vector {a // a ∈ S} n), ∀ a ∈ Subtype.val $ᵥ arg, a ∈ S
                from this _ _
              intro n arg a
              rintro ha: a ∈ Subtype.val $ᵥ arg
              induction arg using Vector.inductionOn
              case h_nil => simp at ha
              case h_cons a' arg' ih =>
                cases ha
                case head => exact a'.property
                case tail h => exact ih h
          }
        }
        embed := {
          map := Subtype.val
          preserve := by intro f arg; rfl
          injective := by intro x y h; ext; exact h
        }

    -- Definition 2.3

    abbrev Embedding {L: Language} (A: Alg L) (B: Alg L) := A ↪𝒜 B

    -- Theorem 2.4

    def Hom.image {L: Language} {A: Alg L} {B: Alg L} (ι: A →𝒜 B):
      SubUniv B
      where
        set := ι '' Set.univ
        closed := by
          have:
            ∀ {α} {β} {n} {xs: Vector β n} {f: α → β},
            (∀ x ∈ xs, ∃ y, f y = x) →
            ∃ ys: Vector α n, f $ᵥ ys = xs
            := by
              intro α β n xs f
              induction xs using Vector.inductionOn
              case h_nil =>
                intro; exists Vector.nil
              case h_cons x₀ xs ih =>
                rintro h: ∀ x ∈ x₀ ::ᵥ xs, ∃ y, f y = x
                show ∃ ys', f $ᵥ ys' = x₀ ::ᵥ xs
                have ⟨y₀, hy₀⟩: ∃ y₀, f y₀ = x₀ := by apply h; simp
                have ⟨ys, hys⟩: ∃ ys, f $ᵥ ys = xs := by
                  apply ih; intro x hx; apply h; simp; exact Or.inr hx
                exists y₀ ::ᵥ ys
                simp; congr
          --
          intro f arg h
          replace h: ∀ a ∈ arg, ∃ a', ι a' = a := by
            simpa [Set.image_eq_range, Set.mem_range] using h
          show f⟦B⟧ arg ∈ ι '' Set.univ
          have ⟨arg', h_arg'⟩: ∃ arg', ι $ᵥ arg' = arg := this h
          rw [← h_arg']
          show f⟦B⟧ (ι $ᵥ arg') ∈ ι '' Set.univ
          have: f⟦B⟧ (ι $ᵥ arg') = ι (f⟦A⟧ arg') := ι.preserve.symm
          rw [this]
          show ι (f⟦A⟧ arg') ∈ ι '' Set.univ
          show ∃ x ∈ Set.univ, ι x = ι (f⟦A⟧ arg')
          exists f⟦A⟧ arg'

    -- Definition 2.5
    -- TODO
  end «Isomorphic Algebras, and Subalgebras»

  section «Algebraic Lattices and Subuniverses»
    -- Definition 3.1

    def Sg {L: Language} {A: Alg L} (X: Set A.univ): SubUniv A where
      set := { a | ∀ B: SubUniv A, X ⊆ B.set → a ∈ B }
      closed := by
        intro f arg
        rintro h: ∀ a ∈ arg, ∀ B: SubUniv A, X ⊆ B.set → a ∈ B
        intro B (hB: X ⊆ B.set); show f⟦A⟧ arg ∈ B
        apply B.closed
        intro a (ha: a ∈ arg); show a ∈ B
        exact h _ ha _ hB

    -- Theorem 3.2
    -- TODO: Define algebraic closure operators first.
  end «Algebraic Lattices and Subuniverses»
end «The Elements of Universal Algebra»
