Require Import HoTT.
Require Import polynomial.
Require Import polynomial_lemma.

Structure it_signature :=
  {
    point_index : Type ;
    point : point_index -> polynomial
  }.

Structure it_algebra (Σ : it_signature) :=
  {
    carrier :> Type ;
    it_point : forall (i : point_index Σ), poly_act (point Σ i) carrier -> carrier
  }.

Arguments carrier {_}.
Arguments it_point {Σ} i _.

Section it_morphism.
  Variable (Σ : it_signature).

  Class it_morph {A₁ A₂ : it_algebra Σ} (f : A₁ -> A₂) :=
    point_commute : forall (i : point_index Σ) (x : poly_act (point Σ i) A₁),
      f(it_point A₁ i x) = it_point A₂ i (poly_map (point Σ i) f x).

  Global Instance id_it_morph (A : it_algebra Σ) : it_morph (idmap : A -> A)
    := fun i x => ap (it_point A i) (poly_map_id (point Σ i) x)^.

  Global Instance comp_it_morph
             {A₁ A₂ A₃ : it_algebra Σ}
             (g : A₂ -> A₃) `{it_morph _ _ g}
             (f : A₁ -> A₂) `{it_morph _ _ f}
    : it_morph (g o f)
    := fun i x =>
         (ap g (point_commute i x))
           @ (point_commute i (poly_map (point Σ i) f x))
           @ ap (it_point A₃ i) (poly_map_compose g f x)^.
End it_morphism.

Arguments it_morph {Σ} {A₁ A₂} f.
Arguments point_commute {Σ A₁ A₂} f {_} i.
Arguments id_it_morph {Σ} A.
Arguments comp_it_morph {Σ A₁ A₂ A₃} g {_} f {_}.

Section initial_it_algebra.
  Variable (Σ : it_signature).

  Definition weak_initial (A : it_algebra Σ) : Type
    := forall (B : it_algebra Σ), {f : A -> B & it_morph f}.

  Definition unique_initial (A : it_algebra Σ) : Type
    := forall (B : it_algebra Σ) (f g : A -> B),
      it_morph f -> it_morph g -> forall (x : A), f x = g x.

  Definition initial (A : it_algebra Σ) : Type
    := weak_initial A * unique_initial A.
End initial_it_algebra.

Arguments weak_initial {Σ} A.
Arguments unique_initial {Σ} A.
Arguments initial {Σ} A.

Section inductive_type.
  Variable (Σ : it_signature).

  Definition point_over
             {T : Type}
             (F : T -> Type)
             (c : forall i, poly_act (point Σ i) T -> T)
    := forall (i : point_index Σ) (u : poly_act (point Σ i) T),
      poly_fam (point Σ i) F u -> F (c i u).

  Structure IT :=
    {
      it_alg :> it_algebra Σ ;
      it_ind : forall (F : carrier it_alg -> Type)
                      (c : point_over F (it_point it_alg))
                      (x : carrier it_alg),
          F x ;
      it_ind_beta : forall (F : carrier it_alg -> Type)
                           (c : point_over F (it_point it_alg))
                           (i : point_index Σ)
                           (t : poly_act (point Σ i) (carrier it_alg)),
          it_ind F c (it_point it_alg i t) =
          c i t (poly_dmap (point Σ i) (it_ind F c) t)
    }.

  Definition it_rec_map (T : IT) (A : it_algebra Σ) : T -> A
    := it_ind T (fun _ => A) (fun i x p => (it_point A i (fam_const _ p))).

  Global Instance it_rec_map_is_morph (T : IT) (A : it_algebra Σ)
    : it_morph (it_rec_map T A)
    := fun i x => it_ind_beta _ _ _ _ _ @ ap (it_point A i) (fam_const_map _ x).

  Definition it_rec (T : IT) (A : it_algebra Σ) : {f : T -> A & it_morph f}
    := (it_rec_map T A;it_rec_map_is_morph T A).

  Definition it_rec_beta
             (T : IT) (A : it_algebra Σ)
             (i : point_index Σ) (x : poly_act (point Σ i) T)
    : (it_rec T A).1 (it_point T i x)
      =
      it_point A i (poly_map (point Σ i) (it_rec T A).1 x)
    := it_ind_beta _ _ _ i x @ ap (it_point A i) (const_dmap (it_rec T A).1 x).
End inductive_type.

Arguments it_ind {Σ _} F c.
Arguments it_ind_beta {Σ _} F c _ _.
Arguments it_rec {Σ T} A.
Arguments it_rec_beta {Σ T} A i x.

Section uniqueness_inductive_types.
  Variable (Σ : it_signature).

  Definition it_to_it (T₁ T₂ : IT Σ) : {f : T₁ -> T₂ & it_morph f}
    := it_rec T₂.

  Definition it_to_it_eq (T₁ T₂ : IT Σ)
    : forall (x : T₂), (it_to_it T₁ T₂).1 ((it_to_it T₂ T₁).1 x) = x
    := it_ind
         _
         (fun i x y =>
            (ap _ (it_rec_beta T₁ i x))
              @ (it_rec_beta T₂ i (poly_map (point Σ i) (it_to_it T₂ T₁).1 x))
              @ (ap (it_point T₂ i)
                    (((poly_map_compose _ _ x)^)
                       @ (fam_eq _ _ x y)
                       @ (poly_map_id (point Σ i) x))
                )).

  Global Instance is_equiv_it_to_it (T₁ T₂ : IT Σ)
    : IsEquiv (it_to_it T₁ T₂).1
    := isequiv_adjointify _
                          (it_to_it T₂ T₁).1
                          (it_to_it_eq T₁ T₂)
                          (it_to_it_eq T₂ T₁).
End uniqueness_inductive_types.

Section inductive_type_is_fixpoint.
  Variable (Σ : it_signature) (T : IT Σ).

  Definition T_to_FT : T -> {i : point_index Σ & poly_act (point Σ i) T}
    := it_ind _ (fun i x _ => (i;x)).

  Definition FT_to_T : {i : point_index Σ & poly_act (point Σ i) T} -> T
    := fun x => it_point T x.1 x.2.

  Global Instance is_equiv_T_to_FT : IsEquiv T_to_FT
    := isequiv_adjointify
         _
         FT_to_T
         (fun x => it_ind_beta _ _ x.1 x.2)
         (it_ind (fun z => FT_to_T(T_to_FT z) = z)
                 (fun i y _ => ap FT_to_T (it_ind_beta _ _ i y))).
End inductive_type_is_fixpoint.

Section inductive_type_is_initial.
  Variable (Σ : it_signature) (T : IT Σ).

  Definition inductive_to_initial : initial T
    := ((fun A => it_rec A),
        fun A f g Hf Hg =>
          it_ind (fun z => f z = g z)
                 (fun i y z =>
                    (point_commute f i y)
                      @ (ap (it_point A i) (fam_eq f g y z))
                      @ (point_commute g i y)^)).
End inductive_type_is_initial.

Section initial_is_inductive.
  Variable (Σ : it_signature) (T : it_algebra Σ) (HT : initial T).

  Definition dependent_algebra
             (F : T -> Type)
             (c : point_over Σ F (it_point T))
    : it_algebra Σ
    := {|carrier := {x : T & F x} ;
         it_point :=
           fun i x =>
             let u := poly_map (point Σ i) pr1 x in
             (it_point T i u;
                c i
                  u
                  (fam_sum _ (@poly_dmap (point Σ i) {x : T & F x} (fun z => F z.1) pr2 x))
             )
       |}.

  Global Instance pr_dependent_algebra
             (F : T -> Type)
             (c : point_over Σ F (it_point T))
    : it_morph (pr1 : dependent_algebra F c -> T)
    := fun i x => idpath.

  Definition initial_to_inductive : IT Σ.
  Proof.
    destruct HT as [T_rec T_unique].
    simple refine {|it_alg := T|}.
    - intros F c x.
      destruct (T_rec (dependent_algebra F c)) as [f Hf].
      exact (transport F (T_unique T (pr1 o f) idmap _ _ x) (f x).2).
    - intros F c i x ; cbn.
      destruct (T_rec (dependent_algebra F c)) as [f Hf].
      rewrite (transport_pr2 _ _ (Hf i x)) ; simpl.
(*      Check (ap pr1 (Hf i x)^ @
     T_unique T (fun x0 : T => (f x0).1) idmap (comp_it_morph _ f) 
     (id_it_morph T) (it_point T i x)).
      assert ((poly_map (point Σ i) pr1 (poly_map (point Σ i) f x)) = x).
      {
        induction (point Σ i) ; cbn.
        - refine (T_unique T (fun x0 : T => (f x0).1) idmap (comp_it_morph _ f) 
                          (id_it_morph T) _).
        - reflexivity.
        - exact (path_prod' (IHp1 (fst x)) (IHp2 (snd x))).
        - destruct x as [x | x].
          + apply (ap inl (IHp1 x)).
          + apply (ap inr (IHp2 x)).
      }
      Check (fam_sum (poly_map (point Σ i) f x) (poly_dmap (point Σ i) _ (poly_map (point Σ i) f x))).
      Definition test
                 (F : T -> Type)
                 (c : point_over Σ F (it_point T))
                 (i : point_index Σ)
                 (x : poly_act (point Σ i) T)
                 (f : T -> dependent_algebra F c)
                 (p : it_point T i (poly_map (point Σ i) pr1 (poly_map (point Σ i) f x))
                      = it_point T i x)
                 g z
        : transport F p (c i (poly_map (point Σ i) pr1 (poly_map (point Σ i) f x)) z)
          =
          c i x (g z).
      Proof.
 *)
  Admitted.
End initial_is_inductive. 