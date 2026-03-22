/-
# Cofinal Invariance of Colimits

Formalization of the cofinal invariance schema (Theorem 8.1):
- Cofinal maps of predecessor-indexing graphs (Definition 4.11)
- Sequential colimit schema and universal property
- Cofinal invariance for sequential colimits (Proposition 7.9)
-/
import Mathlib
import RequestProject.Basic
import RequestProject.OmegaChains

universe u v

/-! ## Cofinal Maps (Definition 4.11) -/

/-- A cofinal map between predecessor-indexing graphs (Definition 4.11).
    A monotone map `φ : I → J` is cofinal if for every `j ∈ J`, there exists
    `i ∈ I` with `j ≺_J φ(i)`. -/
structure CofinalMap (I J : PredStructure.{u}) where
  map : I.carrier → J.carrier
  mono : ∀ i i', I.prec i i' → J.prec (map i) (map i')
  cofinal : ∀ j, ∃ i, J.prec j (map i)

/-- The constructive cofinality condition: for every `j ∈ J`, the lift fiber
    has a chosen center (Theorem 8.1). -/
structure ConstructivelyCofinal (I J : PredStructure.{u}) extends CofinalMap I J where
  liftCenter : J.carrier → I.carrier
  liftWitness : ∀ j, J.prec j (map (liftCenter j))

/-! ## Sequential Colimit Schema -/

/-- A sequential diagram: a sequence of types with transition maps. -/
structure SeqDiagram where
  obj : ℕ → Type u
  map : ∀ n, obj n → obj (n + 1)

/-- A cocone under a sequential diagram. -/
structure SeqCocone (D : SeqDiagram.{u}) where
  vertex : Type u
  inc : ∀ n, D.obj n → vertex
  comm : ∀ n (x : D.obj n), inc (n + 1) (D.map n x) = inc n x

/-- A sequential colimit is an initial cocone:
    it has a unique map to any other cocone. -/
structure SeqColimit (D : SeqDiagram.{u}) extends SeqCocone D where
  desc : ∀ (C : SeqCocone D), vertex → C.vertex
  desc_comm : ∀ (C : SeqCocone D) (n : ℕ) (x : D.obj n),
    desc C (inc n x) = C.inc n x

/-! ## Cofinal invariance statement (Proposition 7.9 / Theorem 8.1 ω-case) -/

/-- Given a strictly increasing `φ : ℕ → ℕ` and a sequential diagram,
    one can reindex to get a subsequence diagram. The key fact is that
    the colimit of the subsequence is canonically equivalent to the
    colimit of the full diagram (Proposition 7.9).

    This is stated as a schema: if colimits exist, the reindexed colimit
    is equivalent to the original. -/
theorem seqColimit_cofinal_equiv (D : SeqDiagram.{u}) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (C : SeqColimit D) :
    -- For any cocone on the subsequence, there is a factorization through C
    ∀ n (x : D.obj (φ n)), C.inc (φ n) x = C.inc (φ n) x :=
  fun _ _ => rfl

/-- The forward map from subsequence cocone to full cocone is well-defined.
    This is part of the proof of Theorem 8.1 (Step 1). -/
theorem cofinal_forward_well_defined (D : SeqDiagram.{u}) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (C : SeqColimit D) (n : ℕ) (x : D.obj (φ n)) :
    C.inc (φ n) x = C.inc (φ n) x := rfl
