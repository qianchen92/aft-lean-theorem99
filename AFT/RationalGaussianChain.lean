import AFT.CenteredGaussianChannel
import AFT.GaussianMatrixChain
import AFT.FiniteConditionProgram
import AFT.FiniteChannelIdentities

/-! # Executable conditional scalar Gaussian chains

Centers are rational functions of already realized integer coordinates.
The actual upper-triangular matrix specialization uses just finite rational
sums. Every recursive tail is stored before its head is computed.
-/
namespace AFT.RationalNumerics
open GaussianSource Matrix
open scoped BigOperators

inductive RationalGaussianChain : ℕ → Type
  | nil : RationalGaussianChain 0
  | cons {count : ℕ} (squaredWidth : ℚ) (center : (Fin count → ℤ) → ℚ)
      (tail : RationalGaussianChain count) : RationalGaussianChain (count+1)

/-- Available randomness is exactly one fixed-length scalar tape per
coordinate. The result is a materialized integer vector. -/
def RationalGaussianChain.draw (cutoff bits : ℕ) : {count : ℕ} → RationalGaussianChain count →
    (Fin count → Fin (windowTicketBits cutoff bits) → Fin 2) → Vector ℤ count
  | 0,.nil,_ => Vector.ofFn Fin.elim0
  | _+1,.cons squaredWidth center tail,randomness =>
      let previous := tail.draw cutoff bits (fun i => randomness i.succ)
      let currentCenter := center previous.get
      let first := centeredGaussianAnchor currentCenter+
        (centeredGaussianDraw squaredWidth currentCenter cutoff bits (randomness 0) : ℤ)
      Vector.ofFn (Fin.cons first previous.get)

def RationalGaussianChain.drawBits {count : ℕ} (chain : RationalGaussianChain count) (cutoff bits : ℕ)
    (randomness : Fin (count*windowTicketBits cutoff bits) → Fin 2) : Vector ℤ count :=
  chain.draw cutoff bits (FiniteConditionProgram.groupBits count (windowTicketBits cutoff bits) randomness)

/-- The actual rational triangular conditional centers. -/
def upperRationalGaussianChain : (count : ℕ) → (Fin count → ℚ) → (Fin count → ℚ) →
    Matrix (Fin count) (Fin count) ℚ → RationalGaussianChain count
  | 0,_,_,_ => .nil
  | count+1,squaredWidth,center,upper => .cons (squaredWidth 0)
      (fun tail => center 0-∑ j,upper 0 j.succ*((tail j : ℚ)-center j.succ))
      (upperRationalGaussianChain count (fun j => squaredWidth j.succ) (fun j => center j.succ)
        (fun i j => upper i.succ j.succ))

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def RationalGaussianChain.realChain : {count : ℕ} → RationalGaussianChain count → GaussianChain count
  | 0,.nil => .nil
  | _+1,.cons squaredWidth center tail => .cons (Real.sqrt (squaredWidth : ℝ))
      (fun word => (center word : ℝ)) tail.realChain

theorem upperRationalGaussianChain_real (count : ℕ) (squaredWidth center : Fin count → ℚ)
    (upper : Matrix (Fin count) (Fin count) ℚ) :
    (upperRationalGaussianChain count squaredWidth center upper).realChain=
      upperGaussianChain count (fun i => Real.sqrt (squaredWidth i : ℝ))
        (fun i => (center i : ℝ)) (fun i j => (upper i j : ℝ)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [upperRationalGaussianChain,RationalGaussianChain.realChain,upperGaussianChain,ih]
    congr 1
    funext word
    simp only [Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast]

/-- Recursive finite law of the literal bit program, after any finite
output channel. This definition samples no real-valued random variable. -/
def RationalGaussianChain.finiteChannel {Output : Type*} [Fintype Output] (cutoff bits : ℕ) :
    {count : ℕ} → RationalGaussianChain count → ((Fin count → ℤ) → FiniteDist Output) → FiniteDist Output
  | 0,.nil,channel => channel Fin.elim0
  | _+1,.cons squaredWidth center tail,channel => tail.finiteChannel cutoff bits
      (fun word => (centeredTicketLaw squaredWidth (center word) cutoff bits).mix
        (fun offset => channel (Fin.cons (centeredGaussianAnchor (center word)+offset) word)))

theorem RationalGaussianChain.draw_channel {Output : Type*} [Fintype Output]
    {count : ℕ} (chain : RationalGaussianChain count) (cutoff bits : ℕ)
    (channel : (Fin count → ℤ) → FiniteDist Output) :
    (FiniteDist.independent (fun _ : Fin count => FiniteDist.independent
      (fun _ : Fin (windowTicketBits cutoff bits) => FiniteDist.uniform (Fin 2)))).mix
        (fun randomness => channel (chain.draw cutoff bits randomness).get)=
      chain.finiteChannel cutoff bits channel := by
  induction chain with
  | nil =>
    apply FiniteDist.ext
    intro output
    simp only [FiniteDist.mix_weight,FiniteDist.independent,Fin.prod_univ_zero,one_mul,
      draw,finiteChannel]
    rw [Fintype.sum_unique]
    have he : (Vector.ofFn (Fin.elim0 : Fin 0 → ℤ)).get=Fin.elim0 := by funext i;exact Fin.elim0 i
    rw [he]
  | @cons count squaredWidth center tail ih =>
    let bitLaw := FiniteDist.independent (fun _ : Fin (windowTicketBits cutoff bits) => FiniteDist.uniform (Fin 2))
    have hsplit := FiniteConditionProgram.independent_cons bitLaw count
    rw [hsplit,FiniteDist.mix_map]
    have hprod (value : (Fin (windowTicketBits cutoff bits) → Fin 2) →
        (Fin count → Fin (windowTicketBits cutoff bits) → Fin 2) → FiniteDist Output) :
        (bitLaw.prod (FiniteDist.independent (fun _ : Fin count => bitLaw))).mix
          (fun pair => value pair.1 pair.2)=
        bitLaw.mix (fun first => (FiniteDist.independent (fun _ : Fin count => bitLaw)).mix (value first)) := by
      ext output
      simp only [FiniteDist.mix_weight,FiniteDist.prod_weight,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
    have hcons (pair : (Fin (windowTicketBits cutoff bits) → Fin 2) ×
        (Fin count → Fin (windowTicketBits cutoff bits) → Fin 2)) :
        (Fin.consEquiv (fun _ : Fin (count+1) => Fin (windowTicketBits cutoff bits) → Fin 2)) pair=
          Fin.cons pair.1 pair.2 := by cases pair;rfl
    simp only [hcons]
    rw [hprod (fun first rest => channel ((RationalGaussianChain.cons squaredWidth center tail).draw cutoff bits (Fin.cons first rest)).get),FiniteDist.mix_comm]
    simp only [draw,Fin.cons_zero,Fin.cons_succ]
    have hget (function : Fin (count+1) → ℤ) : (Vector.ofFn function).get=function := by funext i;exact Vector.get_ofFn _ _
    simp only [hget]
    have hstep (rest : Fin count → Fin (windowTicketBits cutoff bits) → Fin 2) :
        bitLaw.mix (fun first => channel (Fin.cons
          (centeredGaussianAnchor (center (tail.draw cutoff bits rest).get)+
            (centeredGaussianDraw squaredWidth (center (tail.draw cutoff bits rest).get) cutoff bits first : ℤ))
          (tail.draw cutoff bits rest).get))=
        (centeredTicketLaw squaredWidth (center (tail.draw cutoff bits rest).get) cutoff bits).mix
          (fun offset => channel (Fin.cons (centeredGaussianAnchor (center (tail.draw cutoff bits rest).get)+offset)
            (tail.draw cutoff bits rest).get)) := by
      rw [←centeredGaussianDraw_law,FiniteDist.mix_map]
    simp only [hstep]
    simpa only [finiteChannel,bitLaw] using ih (fun word =>
      (centeredTicketLaw squaredWidth (center word) cutoff bits).mix
        (fun offset => channel (Fin.cons (centeredGaussianAnchor (center word)+offset) word)))

end
end AFT.RationalNumerics
