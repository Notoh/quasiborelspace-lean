import Mathlib

open Set Function Encodable Equiv MeasureTheory Classical Measure

instance : MeasurableSpace ℝ := Real.measurableSpace
instance : MeasurableSpace ℕ := Nat.instMeasurableSpace

universe u v
variable {X Y Z : Type*}

def disjoint_function {X : Type*} (P : ℝ → ℕ) (i: ℕ → (ℝ → X)) : ℝ → X :=
  (fun (r : ℝ) => (i ∘ P) r r)

class qbs (X : Type*) where 
  /-- predicate asking if a function ℝ → X is ``measurable'', use in_mx below instead-/
  in_mx' : (ℝ → X) → Prop
  /- Postcomposition of something in MX with a measurable function is in MX -/
  comp_meas : ∀ (f : ℝ → ℝ) (g : ℝ → X), in_mx' g → (Measurable f) → (in_mx' (g ∘ f))
  /- constant functions are in MX -/
  const : ∀ c : X, in_mx' (Function.const ℝ c)
  /- disjoint union, if α_i is a sequence of functions in MX, given any measurable partition function P of ℝ, the function that acts as α_i on each piece 
  delineated by P is in MX. -/
  disjoint_union : ∀ (i : ℕ → (ℝ → X)) (P : ℝ → ℕ), (∀ n : ℕ, in_mx' (i n)) → (Measurable P) → (in_mx' (disjoint_function P i))

@[fun_prop]
def in_mx [qbs X] (f : ℝ → X) : Prop :=
  ‹qbs X›.in_mx' f

/- when you need to specify the qbs you are working over -/
notation "in_mx[" f "]" => @in_mx _ f

def discrete_qbs (X : Type*) : qbs X where
  in_mx' := (fun _ => True)
  comp_meas := by simp
  const := by simp
  disjoint_union := by simp

instance : qbs Empty := discrete_qbs Empty

/-  
def bool_set : Set ℝ := { x : ℝ | x = 0 ∨ x = 1 }
instance : Zero bool_set := ⟨⟨0, Or.inl rfl⟩⟩
instance : qbs bool_set := discrete_qbs bool_set
-/ 
noncomputable def ind (S : Set X) : X → ℝ := Set.indicator S (fun _ => 1) 

@[fun_prop]
def qbs_morphism [qbs X] [qbs Y] (g : X → Y) : Prop :=
  forall {f : ℝ → X}, in_mx f → in_mx (g ∘ f) 

lemma id_qbs_morphism {_ : qbs X} : qbs_morphism (@id X) := by simp [qbs_morphism]

@[fun_prop]
lemma id_qbs_morphism' {_ : qbs X} : qbs_morphism fun a : X => a := id_qbs_morphism

theorem qbs_morphism_comp {_ : qbs X} {_ : qbs Y} {_ : qbs Z} {g : Y → Z} {f : X → Y} (hg : qbs_morphism g) (hf : qbs_morphism f) : qbs_morphism (g ∘ f)
:= by exact fun {f_1} a => hg (hf a)

@[fun_prop]
theorem qbs_morphism_comp' {_ : qbs X} {_ : qbs Y} {_ : qbs Z} (g : Y → Z) (f : X → Y) (hg : qbs_morphism g) (hf : qbs_morphism f) :
    qbs_morphism (fun x => g (f x)) := qbs_morphism_comp hg hf

lemma const_qbs_morphism {_ : qbs X} {_ : qbs Y} (y : Y) : qbs_morphism (Function.const X y) := by {
    simp [qbs_morphism]
    intros
    apply qbs.const
}

@[fun_prop]
lemma in_mx_const [qbs X] (c : X) : in_mx (Function.const ℝ c) := by apply qbs.const

@[fun_prop]
lemma in_mx_comp_meas [qbs X] (f : ℝ → ℝ) (g : ℝ → X) : in_mx g → (Measurable f) → in_mx (g ∘ f) := by {
    intros
    apply qbs.comp_meas <;> assumption 
} 

@[fun_prop]
lemma in_mx_disjoint_union [qbs X] (i : ℕ → (ℝ → X)) (P : ℝ → ℕ) : (∀ n : ℕ, in_mx (i n)) → (Measurable P) → (in_mx (disjoint_function P i)) := by {
    intros
    apply qbs.disjoint_union <;> assumption
}

/- generate a minimal qbs from a given set of functions -/
inductive generate_qbs (mX : Set (ℝ → X)) : (ℝ → X) → Prop
  | basic : ∀ f ∈ mX, generate_qbs mX f
  | comp : ∀ f : ℝ → ℝ, ∀ g : ℝ → X, (generate_qbs mX g) → (Measurable f) → generate_qbs mX (g ∘ f)
  | const : ∀ c : X, generate_qbs mX (Function.const ℝ c)
  | disjoint_union : ∀ (i : ℕ → (ℝ → X)) (P : ℝ → ℕ), (∀ n : ℕ, generate_qbs mX (i n)) →  (Measurable P) → generate_qbs mX (disjoint_function P i)

def generate_qbs_from (mX : Set (ℝ → X)) : qbs X where
  in_mx' := generate_qbs mX
  comp_meas := .comp
  const := .const
  disjoint_union := .disjoint_union

lemma in_mx_generate_from {mX : Set (ℝ → X)} {g : ℝ → X} (hg : g ∈ mX) : in_mx[generate_qbs_from mX] g := .basic g hg

lemma disjoint_function_preimage (P : ℝ → ℕ) (Fi : ℕ → (ℝ → X)) (A : Set X) : 
    (disjoint_function P Fi)⁻¹' A = (⋃ i : ℕ, ((Fi i)⁻¹' A) ∩ (P⁻¹' {i})) := by {
    ext; unfold disjoint_function Set.preimage;
    rename_i x; constructor
    intros hx; rw [Set.mem_iUnion]
    use (P x); simp[*]; exact hx
    intros hx;    
    rw [Set.mem_iUnion] at hx; 
    obtain ⟨i, hi⟩ := hx
    rcases hi with ⟨h1, h2⟩
    simp[*]; rw [h2]; exact h1
}

def measurable_to_qbs [MeasurableSpace X] : qbs X where
  in_mx' := Measurable
  comp_meas := by { intros f g hg hf; apply Measurable.comp hg hf }
  const := by { intros c; apply measurable_const }
  disjoint_union := by { 
  intros i P hi hP; unfold Measurable;
  intros t ht; rw [disjoint_function_preimage]
  measurability
}

instance : qbs ℝ := measurable_to_qbs

/-@[elab_as_elim]
theorem generate_qbs_from_induction (mX : Set (ℝ → X)) (p: ∀ f : ℝ → X, in_mx[generate_qbs_from mX] g → Prop)
(hbasic : ∀ f ∈ mX, ∀ hf, p f hf) ()-/

def qbs_measurable_set [qbs X] : Set X → Prop := 
  (fun s => qbs_morphism (ind s))

lemma ind_function_emptyset0 [qbs X] : ind (∅ : Set X)  = (fun _ => 0) := by { simp[ind] }

def zero_set : Set ℝ := {0}
def one_set : Set ℝ := {1}

noncomputable def ind_flip (x : ℝ) : ℝ := 
  haveI := Classical.decPred (· ∈ zero_set)
  haveI := Classical.decPred (· ∈ one_set)
  zero_set.piecewise (fun x => x + 1) (one_set.piecewise (fun x => x - 1) (id)) x  

lemma ind_flip_meas : Measurable ind_flip := by {
   unfold ind_flip
   apply Measurable.piecewise
   { unfold zero_set; measurability }
   { measurability }
   { apply Measurable.piecewise <;> try measurability
     unfold one_set; measurability }
}

lemma ind_compl_flip [qbs X] (S : Set X) : ind (Sᶜ) = (ind_flip ∘ (ind S))  := by {
  funext x
  unfold ind ind_flip indicator zero_set one_set piecewise
  simp; 
  split_ifs <;> try aesop
  /- all the cases are either trivial arithmetic or have contradictory hypotheses like 0 = 1-/
}

lemma qbs_measurable_set_compl [qbs X] (s : Set X) : qbs_measurable_set s → qbs_measurable_set sᶜ := by
{
  intros hs
  unfold qbs_measurable_set
  unfold qbs_morphism
  intros f hf
  rw [ind_compl_flip]
  unfold qbs_measurable_set at hs
  apply in_mx_comp_meas; apply ind_flip_meas
  apply hs; exact hf
}

/- below is a set-theoretic characterization of all of this stuff expressed above in type theory, helpful for some arguments (though the proof is annoying since preimages in lean aren't very nice) -/
theorem qbs_measurable_set' [qbs X] (S : Set X) : qbs_measurable_set S ↔ (∀ α : ℝ → X, in_mx α → MeasurableSet (α ⁻¹' S)) := by
{
  have h_preim : ∀ (α : ℝ → X), α ⁻¹' S = (ind S ∘ α) ⁻¹' {1}; unfold ind Set.indicator; aesop;
  constructor;
  intros hS α hα; unfold qbs_measurable_set qbs_morphism at hS; apply hS at hα; have h_meas : Measurable (ind S ∘ α); exact hα;
  rw [h_preim]; apply measurableSet_preimage h_meas; measurability;
  intros h_meas α hα; apply h_meas at hα; suffices hSα : Measurable (ind S ∘ α);
  exact hSα; unfold Measurable; intros t ht;
  by_cases h0 : (0 ∈ t)
  {
    by_cases h1 : (1 ∈ t)
    {
      have hS : (ind S ∘ α) ⁻¹' t = Set.univ;
      have h_preim_ind : (ind S) ∘ α ⁻¹' {0, 1} = Set.univ;
      unfold Set.preimage ind Set.indicator; simp; ext x; constructor; simp; intros _; simp; rw [Or.comm]; apply Classical.em (α x ∈ S);
      have ht_01 : {0, 1} ⊆ t; rw [Set.subset_def]; aesop;
      have ht_sub : (ind S ∘ α) ⁻¹' {0, 1} ⊆ (ind S ∘ α)⁻¹' t;
      intros x hx; have h_in : (ind S ∘ α) x ∈ ({0, 1} : Set ℝ); exact hx; exact ht_01 h_in;
      ext x; constructor; simp; intros _; have hx' : x ∈ univ; simp; rw [<- h_preim_ind] at hx'; exact ht_sub hx';
      rw [hS]; simp; 
    }
    {
      have hS : (ind S ∘ α) ⁻¹' t = α ⁻¹' (Sᶜ);
      unfold Set.preimage ind Set.indicator; aesop;
      measurability; 
    }
  }
  {
    by_cases h1 : (1 ∈ t)
    {
      have hS : (ind S ∘ α) ⁻¹' t = α ⁻¹' S;
      unfold Set.preimage ind Set.indicator; aesop;
      rw [hS]; exact hα;
    }
    {
      have hS : (ind S ∘ α) ⁻¹' t = ∅ ;
      unfold Set.preimage ind Set.indicator; aesop; 
      measurability;
    }
  }
}

def qbs_to_measurable [qbs X] : MeasurableSpace X where
  MeasurableSet' := qbs_measurable_set
  measurableSet_empty := by { simp [qbs_measurable_set]; simp[ind_function_emptyset0]; apply const_qbs_morphism } 
  measurableSet_compl := by { intros s hs; apply qbs_measurable_set_compl; exact hs }
  measurableSet_iUnion := by { 
  intros f hf; rw [qbs_measurable_set']; intros α hα; 
  have h : (α ⁻¹' ⋃ i, f i) = (⋃ i, α ⁻¹' f i); aesop;
  rw [h]; apply MeasurableSet.iUnion; intros b; 
  suffices h : qbs_measurable_set (f b);
  have  qbs_meas' : (∀ β : ℝ → X, in_mx β → MeasurableSet (β ⁻¹' (f b)))
  rw [<- qbs_measurable_set' (f b)]; exact h;
  exact qbs_meas' α hα; 
  exact hf b;
}

/- inside def of qbs, make to_measurable that uses this proof -/

/- this construction recovers the borel sets -/
@[simp]
lemma qbs_to_measurable_real (S : Set ℝ) : qbs_measurable_set S ↔ MeasurableSet S := by {
    constructor; intros hS; rw [qbs_measurable_set'] at hS; specialize hS id;
    simp at hS; suffices h : in_mx id; exact hS h; apply measurable_id;
    intros hS; unfold qbs_measurable_set; unfold qbs_morphism; intros f hf;
    have h_meas : Measurable f := hf; apply Measurable.comp;
    apply Measurable.indicator; simp; exact hS; exact h_meas;  
}

@[simp]
theorem qbs_ℝ_coincide : @qbs_to_measurable ℝ (@measurable_to_qbs ℝ (borel ℝ)) = borel ℝ := by {
    ext; apply qbs_to_measurable_real;
}

lemma real_qbs_morphism [qbs X] (f : ℝ → X) : in_mx f ↔ qbs_morphism f := by
{
    constructor;
    intros hf; unfold qbs_morphism; intros g hg; apply in_mx_comp_meas;
    exact hf; exact hg;
    intros hf; unfold qbs_morphism at *; let g : ℝ → ℝ := id;
    exact hf measurable_id;
}

instance [qbs X] : MeasurableSpace X := qbs_to_measurable

/-- WARNING: There is a really tricky type coercion here that I can't figure out how to get Lean to play nicely with. It's because 
    there are two MeasurableSpace ℝ's lying around, namely the borel sets and the qbs_to_measurable ℝ sets from the above instance. if something
    isn't typechecking nicely surrounding measurable things on ℝ, it's almost certainly due to this problem, where a combination of rewriting with 
    qbs.MeasurableSet_def and qbs_to_measurable_real should save you.
--/

lemma qbs.MeasurableSet_def [qbs X] (S : Set X) : MeasurableSet S ↔ qbs_measurable_set S := Iff.rfl

instance [MeasurableSpace X] : qbs X := measurable_to_qbs


lemma qbs_morphism_measurable [qbs X] [qbs Y] (f: X → Y) : qbs_morphism f → Measurable f := by
{
  intros hf t ht;
  rw [qbs.MeasurableSet_def] at *; rw [qbs_measurable_set'];
  intros α hα; unfold qbs_morphism at *;
  specialize hf hα;
  have h :(α ⁻¹' (f ⁻¹' t)) = (f ∘ α) ⁻¹' t; aesop;
  rw [h]; rw [qbs_measurable_set'] at ht;
  apply ht; exact hf;
}

lemma in_mx_measurable [qbs X] (f : ℝ → X) : in_mx f → Measurable f := by {
  intros hf; rw [real_qbs_morphism] at hf; intros t ht; rw [<- qbs_to_measurable_real] at *; rw [<- qbs.MeasurableSet_def] at *;
  apply MeasurableSet.preimage; /- type checker is an idiot here -/ rw [qbs.MeasurableSet_def] at *; exact ht;
  apply qbs_morphism_measurable; exact hf;
}

lemma qbs_to_measurable_set [MeasurableSpace X] (S : Set X) : MeasurableSet S → qbs_measurable_set S := by {
    intros hS; unfold qbs_measurable_set; unfold qbs_morphism; intros f hf;
    have h_meas : Measurable f := hf; apply Measurable.comp;
    apply Measurable.indicator; simp; exact hS; exact h_meas;  
}

theorem qbs_to_measurable_morphism [qbs X] [MeasurableSpace Y] (f: X → Y) : qbs_morphism f ↔ Measurable f := by
{
  constructor;
  {
    intros hf t ht; apply qbs_to_measurable_set at ht; rw [qbs_measurable_set'] at ht;
    rw [qbs.MeasurableSet_def]; rw [qbs_measurable_set']; intros α hα; let β : ℝ → Y := f ∘ α;
    have h : in_mx β; apply hf; exact hα;
    apply ht; exact h;
  }
  {
    intros hf; intros α hα; intros t ht; have h : qbs_measurable_set (f ⁻¹' t); apply hf; exact ht;
    have h1 : MeasurableSet (α ⁻¹' (f ⁻¹' t)); have hα' : Measurable α; apply in_mx_measurable; exact hα;
    apply MeasurableSet.preimage; rw [qbs.MeasurableSet_def]; exact h; exact hα'; 
    aesop;
  }
}

variable {I : Type}

@[simp]
def proj_i {P : I → Type*} (f : X → (Π i : I, P i)) (i : I) : X → P i :=
  fun x => (f x) i

@[simp]
lemma proj_i_comp {P : I → Type*} (f: X → (Π i : I, P i)) (i : I) (g : ℝ → X) : proj_i (f ∘ g) i = (proj_i f i) ∘ g := by {
  ext x; simp;
}

def qbs_product (P: I → Type*) [Π i : I, qbs (P i)] : qbs (Π i : I, P i) where
  in_mx' f := ∀ i : I, in_mx (proj_i f i)
  comp_meas := by { simp; intros f g hg hf i; apply in_mx_comp_meas; apply hg; exact hf; }
  const := by { simp; intros c i; apply in_mx_const; }
  disjoint_union := by { simp; intros Fi π hFi hπ i;  unfold disjoint_function; sorry /- todo-/  }

def two_element : Set ℕ := { 0, 1 }
def binary {X Y : Type} : two_element → Type := (fun x => if x = ⟨1, by { simp [two_element]}⟩ then Y else X) 

def qbs_binary_product (X Y : Type*) [qbs X] [qbs Y] : qbs (X × Y) where
  in_mx' f := in_mx (Prod.fst ∘ f) ∧ in_mx (Prod.snd ∘ f)
  comp_meas := sorry
  const := sorry
  disjoint_union := sorry

def qbs_rv (X : Type*) [qbs X] := { f : ℝ → X // in_mx f }

def qbs_morph (X Y : Type*) [qbs X] [qbs Y] := { f : X → Y // qbs_morphism f}

@[coe]
def qbs_morph.coe [qbs X] [qbs Y] : qbs_morph X Y → (X → Y) := Subtype.val

@[coe]
def qbs_rv.coe [qbs X] : qbs_rv X → (ℝ → X) := Subtype.val

def uncurry {X Y : Type*} [qbs X] [qbs Y] (f : ℝ → qbs_morph X Y) : ((ℝ × X) → Y) :=
  fun p => (f (Prod.fst p)).coe (Prod.snd p)

instance [qbs X] : qbs (ℝ × X) := qbs_binary_product ℝ X

def uncurry_morph {X Y : Type*} [qbs X] [qbs Y] (f : ℝ → qbs_morph X Y) : Prop :=
  qbs_morphism (uncurry f)

def qbs_function_space (X Y : Type) [qbs X] [qbs Y] : qbs (qbs_morph X Y) where
  in_mx' α := uncurry_morph α
  comp_meas := sorry
  const := sorry
  disjoint_union := sorry

instance [qbs X] : Coe (qbs_morph X ℝ) (X → ℝ) := {coe := qbs_morph.coe}
instance [qbs X] : Coe (qbs_rv X) (ℝ → X) := {coe := qbs_rv.coe}

structure qbs_ProbMeasure (X : Type*) [qbs X] where
  meas : ProbabilityMeasure ℝ
  rv : qbs_rv X

def qbs_ProbMeasure.of (X : Type*) [qbs X] (f : qbs_rv X) (α : ProbabilityMeasure ℝ) : qbs_ProbMeasure X := { meas := α, rv := f}

noncomputable def integrate [qbs X] (μ : qbs_ProbMeasure X) (f : qbs_morph X ℝ) : ℝ := ∫ x, (f.coe (μ.rv.coe x)) ∂ μ.meas 

def measures_equiv [qbs X] (μ σ : qbs_ProbMeasure X) : Prop := 
  ∀ f : qbs_morph X ℝ, integrate μ f = integrate σ f

lemma measures_equiv_Equivalence [qbs X] : Equivalence (fun (μ σ : qbs_ProbMeasure X) => measures_equiv μ σ) := { 
  refl := by { simp [measures_equiv]; }, symm := by { intros x y h; simp [measures_equiv] at *; intros f; symm; exact h f;}, 
  trans := by { intros x y z h1 h2; simp [measures_equiv] at *; intros f; specialize h2 f; specialize h1 f; rw [<- h2]; exact h1 }
}

def qbs_measures.setoid (X : Type*) [qbs X] : Setoid (qbs_ProbMeasure X) := Setoid.mk measures_equiv measures_equiv_Equivalence 

def qbs_measures (X : Type*) [qbs X] := Quotient.mk (qbs_measures.setoid X)

abbrev qspace (X : Type*) [qbs X] := Quotient (qbs_measures.setoid X)

def qbs_measures_qbs (X : Type*) [qbs X] : qbs (qspace X) where
  in_mx' β := ∃ α : qbs_rv X, ∃ g : ℝ → ProbabilityMeasure ℝ, ∀ r : ℝ, β r = Quotient.mk'' (qbs_ProbMeasure.of X α (g r)) 
  comp_meas := sorry
  const := sorry
  disjoint_union := sorry

noncomputable def pick_rv {X : Type*} [qbs X] (f : ℝ → qspace X) (H :  (qbs_measures_qbs X).in_mx' f) := (Classical.choose H)
noncomputable def pick_prob {X : Type*} [qbs X] (f : ℝ → qspace X) (H : (qbs_measures_qbs X).in_mx' f) : ℝ → ProbabilityMeasure ℝ := (Classical.choose (Classical.choose_spec H))

instance [qbs X] : qbs (qspace X) := qbs_measures_qbs X

noncomputable def dirac {X : Type*} (x : X) [qbs X] : qbs_ProbMeasure X := {
  meas := diracProba 0
  rv := ⟨(fun (r : ℝ) => x), by { apply in_mx_const }⟩ 
}

noncomputable def giry_bind [MeasurableSpace X] [MeasurableSpace Y] (f: X → ProbabilityMeasure Y) (μ : ProbabilityMeasure X) : ProbabilityMeasure Y :=
  ⟨Measure.bind μ (ProbabilityMeasure.toMeasure ∘ f), by { 
  rw [isProbabilityMeasure_iff]; rw [bind_apply]; have H : ∀ a : X, ((ProbabilityMeasure.toMeasure ∘ f) a) univ = 1;
  intros a; rw [<- isProbabilityMeasure_iff]; have H2 : IsProbabilityMeasure (f a).toMeasure := (f a).prop;
  apply H2; aesop; measurability; sorry}⟩ /- This is a stupid implementation detail in the implementation of the Giry monad in Mathlib, and not actually axiomatizing anything-/

noncomputable def qbs_giry_unit (X : Type*) [qbs X] : qbs_morph X (qspace X) :=
  ⟨fun x => Quotient.mk'' (dirac x), by { sorry }⟩ 

lemma dumb_coercion {X Y : Type*} [qbs X] [qbs Y] (f : qbs_morph X (qspace Y)) (α : qbs_rv X) : (qbs_measures_qbs Y).in_mx' (f.coe ∘ α.coe) := by {
    unfold qbs_rv qbs_morph at *; aesop;
}

noncomputable def qbs_giry_bind {X Y : Type*} [qbs X] [qbs Y] (f : qbs_morph X (qspace Y)) (μ : qbs_ProbMeasure X) : qspace Y :=
  Quotient.mk'' (qbs_ProbMeasure.of Y (pick_rv (f.coe ∘ (μ.rv).coe) (dumb_coercion f μ.rv)) 
  (giry_bind (pick_prob (f.coe ∘ (μ.rv).coe) (dumb_coercion f μ.rv)) μ.meas)) 
/- TODO I think something is subtly wrong above since we are making two different choices to instantiate pick_rv and pick_prob whereas they should be the same pair-/

notation μ " >>= " f => qbs_giry_bind f μ

theorem giry_monad_unit {X : Type*} [qbs X] : ∀ μ : qbs_ProbMeasure X, (μ >>= qbs_giry_unit X) = Quotient.mk'' μ := sorry

theorem giry_monad_unit_bind {X : Type*} [qbs X] : ∀ x : X, ∀ f : qbs_morph X (qspace X), ((dirac x) >>= f) = f.coe x := sorry

open CategoryTheory

@[to_additive existing qbs_category]
def qbs_category : Type (u + 1) := Bundled qbs 

namespace qbs_category

/- a default coercion between a category of qbs's and a collection of objects and morphisms-/
instance : CoeSort qbs_category Type* := Bundled.coeSort

/- recover a qbs from an object in a category -/
instance (X : qbs_category) : qbs X := X.str

/- turn a qbs into an object in the category -/
def of (X : Type u) [qb : qbs X] : qbs_category := ⟨X, qb⟩ 

/- coercion version of the above -/
@[simp]
theorem coe_of (X : Type u) [qbs X] : (of X : Type u) = X := rfl 

/- the morphisms of our category -/
instance unbundledHom : UnbundledHom @qbs_morphism :=
  ⟨@id_qbs_morphism, @qbs_morphism_comp⟩

/- a proof this forms a large (concrete) category-/
deriving instance LargeCategory for qbs_category

instance : ConcreteCategory qbs_category := by
  unfold qbs_category
  infer_instance

instance : Inhabited qbs_category := ⟨qbs_category.of Empty⟩
attribute [local instance] ConcreteCategory.instFunLike

/- TODO ADJUNCTION -/
end qbs_category



