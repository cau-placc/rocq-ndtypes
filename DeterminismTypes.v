From Equations Require Import Equations.
From Stdlib    Require Import
  Bool
  EqNat
  FunctionalExtensionality
  PeanoNat
  Program.Equality
  Program.Wf
  Lia
  Lists.List
  Lists.ListSet
  Strings.String.
Import ListNotations.

(**
NOTE: Formalization is now completely updated.

You can check that this formalization corresponds to the paper.
Just search in this document for the following important theorems and
definitions:
- "typeOf" corresponds to the simplified Curry type system
- compatibility is as defined in the paper
- "Exp" is the type of expressions
- "DType" is the type of deterministic types
- "TType" is the type of Curry types
- "more_specific" is the subtyping relation
- "Gamma '|-' e ':?' delta" is the Deterministic typing relation
- "step" (or "==>") is the small-step semantics
- "subst" is the substitution function
- "notOr" is the definition for a deterministic result
- Important Theorems are: "completeness", "preservation",
  "soundness" and "functional_is_deterministic"

Also, I am a rocq novice, so this is probably not the most elegant
formalization. If you have suggestions for improvements, please let me know.
*)

(* Section Types:
   Defines the fundamental type systems used in the formalization.
   This includes both traditional "Curry" types (TType) and determinism types (DType),
   as well as expressions, patterns and type equality operations. *)
Section Types.

  Definition total_map (K V : Type) := K -> V.

  Definition update {K V : Type} (beq : K -> K -> bool)
                                 (m : total_map K V) (k : K) (v : V) :=
    fun k' => if beq k k' then v else m k'.

  Lemma double_update_indep :
    forall {V : Type} (Delta : nat -> V) n1 t1 n2 t2,
    n1 <> n2 ->
    update Nat.eqb (update Nat.eqb Delta n1 t1) n2 t2 =
    update Nat.eqb (update Nat.eqb Delta n2 t2) n1 t1.
  Proof.
    intros. apply functional_extensionality.
    intro x. unfold update.
    destruct (n1 =? x) eqn:Heq1;
    destruct (n2 =? x) eqn:Heq2; try reflexivity;
    rewrite Nat.eqb_eq in *; subst; contradiction.
  Qed.

  Lemma double_update :
    forall {V : Type} (Delta : nat -> V) n t1 t2,
    update Nat.eqb (update Nat.eqb Delta n t1) n t2 =
    update Nat.eqb Delta n t2.
  Proof.
    intros. apply functional_extensionality.
    intro x. unfold update.
    destruct (n =? x); try reflexivity.
  Qed.

  Definition Arity := nat.

  Inductive TType : Type :=
    | TBool : TType
    | TList : TType -> TType
    | TArrow : TType -> TType -> TType.

  Fixpoint first_order (t : TType) : Prop :=
    match t with
    | TBool => True
    | TList t' => first_order t'
    | TArrow _ _ => False
    end.

  Inductive Pattern : Type :=
    | Pat : forall (n1 : nat) (t1 : TType) (n2 : nat)
          , n1 <> n2 -> Pattern.

  Inductive TType_FO : Type :=
    | FO : forall (t : TType), first_order t -> TType_FO.

  Inductive Exp : Type :=
    | Var    : nat -> Exp
    | BTrue  : Exp
    | BFalse : Exp
    | Nil    : TType -> Exp
    | Cons   : Exp -> Exp -> Exp
    | App    : Exp -> Exp -> Exp
    | Abs    : nat -> TType -> Exp -> Exp
    | Or     : Exp -> Exp -> Exp
    | Free   : nat -> TType_FO -> Exp -> Exp
    | CaseB  : Exp -> Exp -> Exp -> Exp
    | CaseL  : Exp -> Exp -> Pattern -> Exp -> Exp.

  Definition notOr (e : Exp) : Prop :=
    match e with
    | Or _ _ => False
    | _ => True
    end.

  Fixpoint functional (e : Exp) : Prop :=
    match e with
    | Or _ _ => False
    | Free _ _ _ => False
    | Cons e1 e2 => functional e1 /\ functional e2
    | App e1 e2 => functional e1 /\ functional e2
    | Abs _ _ e1 => functional e1
    | CaseB e1 e2 e3 => functional e1 /\ functional e2 /\ functional e3
    | CaseL e1 e2 (Pat _ _ _ _) e3 =>
        functional e1 /\ functional e2 /\
        functional e3
    | Var _ => True
    | BTrue => True
    | BFalse => True
    | Nil _ => True
    end.

  Fixpoint eqType (t1 t2 : TType) : bool :=
    match t1, t2 with
    | TBool, TBool => true
    | TList t1, TList t2 => eqType t1 t2
    | TArrow t11 t12, TArrow t21 t22 =>
        andb (eqType t11 t21) (eqType t12 t22)
    | _, _ => false
    end.

  Lemma eqType_refl : forall t,
    eqType t t = true.
  Proof.
    induction t; simpl; auto with *.
  Qed.

  Lemma eqType_eq : forall t1 t2,
    eqType t1 t2 = true <-> t1 = t2.
  Proof.
    intros. split.
    - intros. generalize dependent t2. induction t1;
      intros; destruct t2; eauto with *.
      + apply IHt1 in H. subst. reflexivity.
      + simpl in H. apply Bool.andb_true_iff in H. destruct H.
        apply IHt1_1 in H. apply IHt1_2 in H0.
        subst. reflexivity.
    - intros. subst. apply eqType_refl.
  Qed.

  Definition eqTypeS (t1 t2 : option TType) : bool :=
    match t1, t2 with
    | Some t1', Some t2' => eqType t1' t2'
    | None, None => true
    | _, _ => false
    end.

  Lemma eqTypeS_refl : forall t,
    eqTypeS t t = true.
  Proof.
    intros. destruct t; simpl; try reflexivity.
    apply eqType_refl.
  Qed.

  Fixpoint typeOf (c : nat -> TType) (e : Exp) : option TType :=
    match e with
    | Var n => Some (c n)
    | BTrue => Some TBool
    | BFalse => Some TBool
    | Nil t => Some (TList t)
    | Cons e1 e2 => match (typeOf c e2) with
                    | Some t2 => match t2 with
                      | TList t2' =>
                        if eqTypeS (typeOf c e1) (Some t2')
                        then Some (TList t2')
                        else None
                      | _ => None
                      end
                    | _ => None
                    end
    | App e1 e2 => match typeOf c e1, typeOf c e2 with
                   | Some (TArrow t1 t2), Some t1' =>
                        if eqType t1 t1'
                          then Some t2 else None
                   | _, _ => None
                   end
    | Abs n t e => match typeOf (update Nat.eqb c n t) e with
                  | Some t' => Some (TArrow t t')
                  | None => None
                  end
    | Or e1 e2 => let t1 := typeOf c e1 in if eqTypeS t1 (typeOf c e2)
                                          then t1 else None
    | Free n (FO t _) e => typeOf (update Nat.eqb c n t) e
    | CaseB e1 e2 e3 => match typeOf c e1 with
                  | Some TBool => match typeOf c e2, typeOf c e3 with
                    | Some t1, Some t2 =>
                      if eqType t1 t2 then Some t1 else None
                    | _, _ => None
                    end
                  | _ => None
                  end
    | CaseL e1 e2 (Pat n1 t1' n2 _) e3 =>
      if eqTypeS (typeOf c e1) (Some (TList t1'))
        then if eqTypeS (typeOf c e2)
                     (typeOf (update Nat.eqb
                             (update Nat.eqb c n2 (TList t1'))
                                n1 t1') e3)
                then typeOf c e2
                else None
      else None
    end.

  Definition well_typed (c : nat -> TType) (e : Exp) : Prop :=
    match typeOf c e with
    | Some _ => True
    | None => False
    end.

  Inductive DType : Type :=
    | Det : DType
    | Any : DType
    | Arrow : DType -> DType -> DType.

  Fixpoint nonAny (d : DType) : Prop :=
    match d with
    | Det => True
    | Any => False
    | Arrow d1 d2 => nonAny d1 /\ nonAny d2
    end.

  Fixpoint compatible (d : DType) (t : TType) : Prop :=
    match d, t with
    | Det, _ => True
    | Any, _ => True
    | Arrow d1 d2, TArrow t1 t2 =>
        compatible d1 t1 /\ compatible d2 t2
    | _, _ => False
    end.

  Fixpoint mkCompatible (t : TType) : DType :=
    match t with
    | TBool => Det
    | TList _ => Det
    | TArrow t1 t2 => Arrow (mkCompatible t1) (mkCompatible t2)
    end.

  Lemma mkCompatible_compatible : forall t,
    compatible (mkCompatible t) t.
  Proof.
    induction t.
    - reflexivity.
    - reflexivity.
    - simpl. split; [apply IHt1 | apply IHt2].
  Qed.

  Lemma compatible_Any : forall t,
    compatible Any t.
  Proof. reflexivity. Qed.

  Lemma compatible_bool_list : forall d t,
    compatible d (TList t) -> compatible d TBool.
  Proof.
    intros. destruct d; simpl in *; auto.
  Qed.

End Types.

  (* some tactics to destruct
     typeOf occurrences in hypotheses *)

  Ltac invert_if_convenient H :=
  match type of H with
  | False => inversion H
  | Some _ = Some _ => inversion H
  | _ => idtac
  end.

  Ltac destruct_typeOf_in H :=
    match type of H with
    | context[typeOf ?R ?E] =>
        let Heq := fresh "Heq" "1" in
        destruct (typeOf R E) eqn:Heq; simpl in H;
        try discriminate; invert_if_convenient H
    end.

  Ltac destruct_t H :=
  match type of H with
    | context[match ?v with _ => _ end] =>
        match v with
        | ?x => is_var x;
          let Heq := fresh "Heq" "1" in
          destruct x eqn:Heq; simpl in H;
          try discriminate; invert_if_convenient H
        end
  end.

  Ltac destruct_eqTypeS H :=
    simpl in H;
    match type of H with
    | context[eqType ?t ?t'] =>
        let Heq := fresh "Heq" "1" in
        destruct (eqType t t') eqn:Heq; try discriminate; invert_if_convenient H;
        try (
          pose Heq as HT;
          apply eqType_eq in HT;
          try subst t'; try subst t)
    end.

  Ltac destruct_typeOf_chain H :=
    unfold well_typed in *; simpl in *;
    repeat (
      destruct_typeOf_in H;
      try destruct_t H;
      try destruct_eqTypeS H
    );
    subst.

  Lemma well_typed_subterms :
    forall Delta e,
    well_typed Delta e ->
    match e with
    | Cons e1 e2 => well_typed Delta e1 /\ well_typed Delta e2
    | App e1 e2 => well_typed Delta e1 /\ well_typed Delta e2
    | Abs x t e1 => well_typed (update Nat.eqb Delta x t) e1
    | Or e1 e2 => well_typed Delta e1 /\ well_typed Delta e2
    | Free x (FO t _) e1 => well_typed (update Nat.eqb Delta x t) e1
    | CaseB e1 e2 e3 => well_typed Delta e1 /\ well_typed Delta e2 /\ well_typed Delta e3
    | CaseL e1 e2 (Pat n1 t1 n2 _) e3 =>
        well_typed Delta e1 /\
        well_typed Delta e2 /\
        well_typed (update Nat.eqb (update Nat.eqb Delta n1 t1) n2 (TList t1)) e3
    | _ => True
    end.
  Proof.
    intros. destruct e; try destruct p; try destruct t;
    try rewrite double_update_indep;
    destruct_typeOf_chain H; auto.
  Qed.

(* Section Context:
   Defines typing contexts and compatibility between traditional and
   determinism type contexts. Includes operations to create compatible contexts
   and lemmas about context updates. *)
Section Context.

  Definition context := total_map nat DType.
  Definition contextT := total_map nat TType.

  Definition compatibleCtx (c : context) (cT : contextT) : Prop :=
    forall n, compatible (c n) (cT n).

  Definition mkCompatibleCtx (cT : contextT) : context :=
    fun n => mkCompatible (cT n).

  Lemma update_compatible :
    forall Gamma Delta n t d,
    compatibleCtx Gamma Delta ->
    compatible d t ->
    compatibleCtx (update Nat.eqb Gamma n d)
                  (update Nat.eqb Delta n t).
  Proof.
    intros. unfold compatibleCtx. intro n0.
    unfold update. destruct (n =? n0) eqn:Heq; eauto.
  Qed.

  Lemma update_update_compatible :
    forall Gamma Delta n1 n2 t1 d1 t2 d2,
    compatibleCtx Gamma Delta ->
    compatible d1 t1 ->
    compatible d2 t2 ->
    let Gamma' := update Nat.eqb Gamma n1 d1 in
    compatibleCtx (update Nat.eqb Gamma' n2 d2)
                  (update Nat.eqb (update Nat.eqb Delta n1 t1) n2 t2).
  Proof.
    intros. unfold compatibleCtx in *. intro n0.
    subst Gamma'. unfold update in *.
    destruct (n1 =? n0) eqn:Heq1;
    destruct (n2 =? n0) eqn:Heq2; eauto.
  Qed.

End Context.

(* Section Subtyping:
   Defines the subtyping relations for determinism types.
   - more_specific: checks if one determinism type is more specific than another
   - less_specific: the opposite of more_specific
   - decide: determines the result type of function application based on specificity *)
Section Subtyping.

  Fixpoint sizeD (d : DType) : nat :=
    match d with
    | Det => 1
    | Any => 1
    | Arrow d1 d2 => 1 + sizeD d1 + sizeD d2
    end.

  Obligation Tactic := simpl; lia.

  Equations more_specific (d1 d2 : DType) : bool
    by wf (sizeD d1 + sizeD d2) lt :=
  more_specific _ Any := true;
  more_specific Det Det := true;
  more_specific (Arrow d1 d2) Det :=
    andb (more_specific Det d1) (more_specific d2 Det);
  more_specific Det (Arrow d1' d2') :=
    andb (more_specific d1' Det) (more_specific Det d2');
  more_specific (Arrow d1 d2) (Arrow d1' d2') :=
    andb (more_specific d1' d1) (more_specific d2 d2');
  more_specific _ _ := false.

  Lemma unfold_more_specific : forall d1 d2,
    more_specific d1 d2 = match d1, d2 with
    | _, Any => true
    | Det, Det => true
    | Arrow d1 d2, Det =>
        andb (more_specific Det d1) (more_specific d2 Det)
    | Det, Arrow d1' d2' =>
        andb (more_specific d1' Det) (more_specific Det d2')
    | Arrow d1 d2, Arrow d1' d2' =>
        andb (more_specific d1' d1) (more_specific d2 d2')
    | _, _ => false
    end.
  Proof.
    intros. destruct d1, d2; simpl; try reflexivity.
    - rewrite more_specific_equation_5. reflexivity.
    - rewrite more_specific_equation_3. reflexivity.
    - rewrite more_specific_equation_7. reflexivity.
  Qed.

  Lemma Det_is_like_Det_to_Det : forall d,
    (more_specific d Det =
    more_specific d (Arrow Det Det)) /\
    (more_specific Det d =
    more_specific (Arrow Det Det) d).
  Proof.
    destruct d; auto; split.
    - rewrite (unfold_more_specific (Arrow d1 d2) (Arrow Det Det)).
      rewrite unfold_more_specific. reflexivity.
    - rewrite (unfold_more_specific (Arrow Det Det) (Arrow d1 d2)).
      rewrite unfold_more_specific. reflexivity.
  Qed.

  Definition less_specific (d1 d2 : DType) : bool :=
    more_specific d2 d1.

  Definition decide (d1 d3 d2 : DType) : DType :=
    if more_specific d3 d1 then d2 else Any.

  Example more_specific_ex1 :
    more_specific (Arrow Any Det) (Arrow Det Det) = true.
  Proof. trivial. Qed.

  Example more_specific_ex2 :
    more_specific (Arrow Det Det) (Arrow Any Det) = false.
  Proof. trivial. Qed.

  Example more_specific_ex3 :
    more_specific (Arrow (Arrow Det Det) Det) (Arrow (Arrow Any Det) Det) = true.
  Proof. trivial. Qed.

  (* map :# (Det -> Det) -> (Det -> Det)
  map :# (Any -> Det) -> (Any -> Any)  -- spine *)
  Example more_specific_ex4 :
    more_specific (Arrow (Arrow Det Det) (Arrow Det Det))
                  (Arrow (Arrow Any Det) (Arrow Any Any)) = false /\
    less_specific (Arrow (Arrow Det Det) (Arrow Det Det))
                  (Arrow (Arrow Any Det) (Arrow Any Any)) = false.
  Proof. intuition. Qed.

  Lemma specificity_not_inverses : exists d1 d2,
    more_specific d1 d2 = false /\ less_specific d1 d2 = false.
  Proof.
    exists (Arrow Det Det), (Arrow Any Any). intuition.
  Qed.

  Lemma more_specific_refl : forall d, more_specific d d = true.
  Proof.
    - induction d; simpl; trivial.
      rewrite more_specific_equation_7.
      rewrite IHd1. rewrite IHd2. reflexivity.
  Qed.

  Lemma more_specific_Det_l : forall d1 d2,
    more_specific d1 Det = true ->
    more_specific Det d2 = true ->
    more_specific d1 d2 = true
    with more_specific_Det_r : forall d1 d2,
      more_specific Det d1 = true ->
      more_specific d2 Det = true ->
      more_specific d2 d1 = true.
  Proof.
    --
    induction d1; intros; simpl in *; try reflexivity.
    - apply H0.
    - inversion H.
    - rewrite unfold_more_specific in H.
      rewrite andb_true_iff in H. destruct H.
      destruct d2.
      + rewrite unfold_more_specific.
        rewrite H, H1. reflexivity.
      + reflexivity.
      + rewrite unfold_more_specific.
        rewrite unfold_more_specific in H0.
        rewrite andb_true_iff in H0. destruct H0.
        rewrite IHd1_2; try assumption.
        rewrite more_specific_Det_r; try assumption.
        reflexivity.
    --
    induction d1; intros; simpl in *; try reflexivity.
    - apply H0.
    - rewrite unfold_more_specific in H.
      rewrite andb_true_iff in H. destruct H.
      destruct d2.
      + rewrite unfold_more_specific.
        rewrite H, H1. reflexivity.
      + inversion H0.
      + rewrite unfold_more_specific.
        rewrite unfold_more_specific in H0.
        rewrite andb_true_iff in H0. destruct H0.
        rewrite IHd1_2; try assumption.
        rewrite more_specific_Det_l; try assumption.
        reflexivity.
  Qed.

  Lemma more_specific_transitive : forall d1 d2 d3,
    more_specific d1 d2 = true ->
    more_specific d2 d3 = true ->
    more_specific d1 d3 = true.
  Proof.
    intros d1 d2. generalize dependent d1.
    induction d2; intros.
    - destruct d1.
      + assumption.
      + inversion H.
      + destruct d3; simpl in *.
        * assumption.
        * reflexivity.
        * rewrite unfold_more_specific in *.
          rewrite andb_true_iff in H0. destruct H0.
          rewrite andb_true_iff in H. destruct H.
          rewrite more_specific_Det_l; try assumption.
          rewrite more_specific_Det_r; try assumption.
          reflexivity.
    - destruct d3; simpl in *.
      + inversion H0.
      + assumption.
      + inversion H0.
    - destruct d1, d3; simpl in *; trivial.
      + rewrite unfold_more_specific in *.
        rewrite andb_true_iff in H. destruct H.
        rewrite andb_true_iff in H0. destruct H0.
        erewrite IHd2_1; try assumption.
        erewrite IHd2_2; try assumption.
        reflexivity.
      + rewrite unfold_more_specific in *.
        rewrite andb_true_iff in H. destruct H.
        rewrite andb_true_iff in H0. destruct H0.
        erewrite IHd2_1; try assumption.
        erewrite IHd2_2; try assumption.
        reflexivity.
      + rewrite unfold_more_specific in *.
        rewrite andb_true_iff in H. destruct H.
        rewrite andb_true_iff in H0. destruct H0.
        erewrite IHd2_1; try assumption.
        erewrite IHd2_2; try assumption.
        reflexivity.
  Qed.

  Lemma more_specific_Any : forall d, more_specific d Any = true.
  Proof.
    - induction d; simpl; trivial.
  Qed.

  Lemma nonAny_more_specific_det : forall d1,
    nonAny d1 ->
      more_specific d1 Det = true /\
        more_specific Det d1 = true.
  Proof.
    induction d1; simpl; intros; try reflexivity; try inversion H.
    - split; reflexivity.
    - split; rewrite unfold_more_specific.
      + destruct (IHd1_1 H0). destruct (IHd1_2 H1).
        rewrite H3, H4. reflexivity.
      + destruct (IHd1_1 H0). destruct (IHd1_2 H1).
        rewrite H2, H5. reflexivity.
  Qed.

  Lemma nonAny_more_specific : forall d1 d2,
    nonAny d1 -> nonAny d2 ->
      more_specific d2 d1 = true /\
      more_specific d1 d2 = true.
  Proof.
    induction d1; intros.
    - apply nonAny_more_specific_det. assumption.
    - inversion H.
    - rewrite unfold_more_specific. destruct H.
      destruct d2.
      + apply nonAny_more_specific_det in H.
        destruct H. rewrite H.
        apply nonAny_more_specific_det in H1.
        destruct H1. rewrite H3. split. reflexivity.
        rewrite unfold_more_specific. rewrite H2, H1. reflexivity.
      + inversion H0.
      + split.
        * destruct H0.
          destruct (IHd1_1 d2_1 H H0). destruct (IHd1_2 d2_2 H1 H2).
          rewrite H4, H5. reflexivity.
        * rewrite unfold_more_specific. destruct H0.
          destruct (IHd1_1 d2_1 H H0). destruct (IHd1_2 d2_2 H1 H2).
          rewrite H3, H6. reflexivity.
  Qed.

End Subtyping.

Section LeastUpperBound.

  Obligation Tactic := simpl; lia.

  Equations lub_helper (b : bool) (d1 d2 : DType) : DType
    by wf (sizeD d1 + sizeD d2) lt :=
  lub_helper true Det Det := Det;
  lub_helper true (Arrow d1_1 d1_2) Det :=
    Arrow (lub_helper false d1_1 Det) (lub_helper true d1_2 Det);
  lub_helper true (Arrow d1_1 d1_2) (Arrow d2_1 d2_2) :=
    Arrow (lub_helper false d1_1 d2_1) (lub_helper true d1_2 d2_2);
  lub_helper true Det (Arrow d2_1 d2_2) :=
    Arrow (lub_helper false Det d2_1) (lub_helper true Det d2_2);
  lub_helper true _ _ := Any;
  lub_helper false Any Any := Any;
  lub_helper false (Arrow d1_1 d1_2) Det :=
    Arrow (lub_helper true d1_1 Det) (lub_helper false d1_2 Det);
  lub_helper false (Arrow d1_1 d1_2) (Arrow d2_1 d2_2) :=
    Arrow (lub_helper true d1_1 d2_1) (lub_helper false d1_2 d2_2);
  lub_helper false Det (Arrow d2_1 d2_2) :=
    Arrow (lub_helper true Det d2_1) (lub_helper false Det d2_2);
  lub_helper false d1 Any := d1;
  lub_helper false Any d2 := d2;
  lub_helper false Det Det := Det.

  Definition lub2 (d1 d2 : DType) : DType :=
    lub_helper true d1 d2.

  Definition glb2 (d1 d2 : DType) : DType :=
    lub_helper false d1 d2.

  Lemma unfold_lub2 : forall d1 d2,
    lub2 d1 d2 = match d1, d2 with
    | Det, Det => Det
    | Arrow d1_1 d1_2, Det =>
        Arrow (glb2 d1_1 Det) (lub2 d1_2 Det)
    | Arrow d1_1 d1_2, Arrow d2_1 d2_2 =>
        Arrow (glb2 d1_1 d2_1) (lub2 d1_2 d2_2)
    | Det, Arrow d2_1 d2_2 =>
        Arrow (glb2 Det d2_1) (lub2 Det d2_2)
    | Any, Any => Any
    | Det, Any => Any
    | Arrow _ _, Any => Any
    | Any, Det => Any
    | Any, Arrow _ _ => Any
    end.
  Proof.
    intros. destruct d1, d2; simpl; try reflexivity.
    - rewrite lub_helper_equation_3. reflexivity.
    - rewrite lub_helper_equation_5. reflexivity.
    - rewrite lub_helper_equation_7. reflexivity.
  Qed.

  Lemma unfold_glb2 : forall d1 d2,
    glb2 d1 d2 = match d1, d2 with
    | Det, Det => Det
    | Arrow d1_1 d1_2, Det =>
        Arrow (lub2 d1_1 Det) (glb2 d1_2 Det)
    | Arrow d1_1 d1_2, Arrow d2_1 d2_2 =>
        Arrow (lub2 d1_1 d2_1) (glb2 d1_2 d2_2)
    | Det, Arrow d2_1 d2_2 =>
        Arrow (lub2 Det d2_1) (glb2 Det d2_2)
    | Any, Any => Any
    | Det, Any => Det
    | Arrow d1_1 d1_2, Any =>
        Arrow d1_1 d1_2
    | Any, Det => Det
    | Any, Arrow d2_1 d2_2 =>
        Arrow d2_1 d2_2
    end.
  Proof.
    intros. destruct d1, d2; simpl; try reflexivity.
    - rewrite lub_helper_equation_10. reflexivity.
    - rewrite lub_helper_equation_14. reflexivity.
    - rewrite lub_helper_equation_16. reflexivity.
  Qed.

  Definition lub (d1 d2 d3 : DType) : DType :=
    match d1 with
    | Det => lub2 d2 d3
    | _ => Any
    end.

  Ltac simpl_more_specific H :=
    rewrite unfold_more_specific in H; simpl in H.

  Ltac simpl_lub H :=
    try rewrite unfold_lub2 in H; simpl in H;
    try rewrite unfold_glb2 in H; simpl in H.

  Ltac destruct_h H :=
  match type of H with
  | context[_ /\ _] =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      destruct H as [H1 H2]
  end.

  Ltac simpl_all H :=
    try simpl_lub H;
    try simpl_more_specific H;
    try rewrite andb_true_iff in H; simpl in H;
    try destruct_h H.

  Lemma compatible_lub2 : forall t d1 d2,
    compatible d1 t ->
    compatible d2 t ->
    compatible (lub2 d1 d2) t
    with compatible_glb2 : forall t d1 d2,
    compatible d1 t ->
    compatible d2 t ->
    compatible (glb2 d1 d2) t.
  Proof.
    --
    induction t; intros.
    - destruct d1, d2; try reflexivity; try assumption.
    - destruct d1, d2; try reflexivity; try assumption.
    - destruct d1, d2; try reflexivity; try assumption;
      simpl in *.
      + destruct H0.
        rewrite unfold_lub2. simpl. split.
        apply compatible_glb2; try assumption.
        apply compatible_lub2; try assumption.
      + destruct H.
        rewrite unfold_lub2. simpl. split.
        apply compatible_glb2; try assumption.
        apply compatible_lub2; try assumption.
      + destruct H0, H.
        rewrite unfold_lub2. simpl. split.
        apply compatible_glb2; try assumption.
        apply compatible_lub2; try assumption.
    --
    induction t; intros.
    - destruct d1, d2; try reflexivity; try assumption.
    - destruct d1, d2; try reflexivity; try assumption.
    - destruct d1, d2; try reflexivity; try assumption.
      simpl in *.
      + destruct H0.
        rewrite unfold_glb2. simpl. split.
        apply compatible_lub2; try assumption.
        apply compatible_glb2; try assumption.
      + destruct H.
        rewrite unfold_glb2. simpl. split.
        apply compatible_lub2; try assumption.
        apply compatible_glb2; try assumption.
      + destruct H0, H.
        rewrite unfold_glb2. simpl. split.
        apply compatible_lub2; try assumption.
        apply compatible_glb2; try assumption.
  Qed.

  Lemma compatible_lub : forall d1 d2 d3 t,
    compatible d1 TBool ->
    compatible d2 t ->
    compatible d3 t ->
    compatible (lub d1 d2 d3) t.
  Proof.
    intros d1 d2 d3 t Hc1 Hc2 Hc3.
    unfold lub.
    destruct d1 eqn:H1.
    - apply compatible_lub2; assumption.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma more_specific_lub_glb_pair : forall d1 d2,
    more_specific d1 (lub2 d1 d2) = true /\
    more_specific d2 (lub2 d1 d2) = true /\
    more_specific (glb2 d1 d2) d1 = true /\
    more_specific (glb2 d1 d2) d2 = true.
  Proof.
    intros d1 d2.
    refine (
    well_founded_induction
      lt_wf
      (fun n =>
       forall d1 d2,
         sizeD d1 + sizeD d2 = n ->
         more_specific d1 (lub2 d1 d2) = true /\
         more_specific d2 (lub2 d1 d2) = true /\
         more_specific (glb2 d1 d2) d1 = true /\
         more_specific (glb2 d1 d2) d2 = true)
      _
      (sizeD d1 + sizeD d2) d1 d2 eq_refl
    ).
    intros n IH d_1 d_2 Hsz. subst n.
    destruct d_1 as [| | a b]; destruct d_2 as [| | c d]; simpl;
    try (repeat split; reflexivity).

    - (* d1 = Det, d2 = Arrow c d *)
      pose proof (IH (sizeD Det + sizeD c) ltac:(simpl; lia)
                    Det c eq_refl) as Hc.
      pose proof (IH (sizeD Det + sizeD d) ltac:(simpl; lia)
                    Det d eq_refl) as Hd.
      destruct Hc as [Hc1 [Hc2 [Hc3 Hc4]]].
      destruct Hd as [Hd1 [Hd2 [Hd3 Hd4]]].
      repeat split.
      + rewrite unfold_lub2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_lub2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.

    - (* d1 = Any, d2 = Arrow c d *)
      pose proof (IH (sizeD Any + sizeD c) ltac:(simpl; lia)
                    Any c eq_refl) as Hc.
      pose proof (IH (sizeD Any + sizeD d) ltac:(simpl; lia)
                    Any d eq_refl) as Hd.
      destruct Hc as [Hc1 [Hc2 [Hc3 Hc4]]].
      destruct Hd as [Hd1 [Hd2 [Hd3 Hd4]]].
      repeat split.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; apply more_specific_refl.

    - (* d1 = Arrow a b, d2 = Det *)
      pose proof (IH (sizeD a + sizeD Det) ltac:(simpl; lia)
                    a Det eq_refl) as Ha.
      pose proof (IH (sizeD b + sizeD Det) ltac:(simpl; lia)
                    b Det eq_refl) as Hb.
      destruct Ha as [Ha1 [Ha2 [Ha3 Ha4]]].
      destruct Hb as [Hb1 [Hb2 [Hb3 Hb4]]].
      repeat split.
      + rewrite unfold_lub2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_lub2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.

    - (* d1 = Arrow a b, d2 = Any *)
      repeat split.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; apply more_specific_refl.

    - (* d1 = Arrow a b, d2 = Arrow c d *)
      pose proof (IH (sizeD a + sizeD c) ltac:(simpl; lia)
                    a c eq_refl) as Ha.
      pose proof (IH (sizeD b + sizeD d) ltac:(simpl; lia)
                    b d eq_refl) as Hb.
      destruct Ha as [Ha1 [Ha2 [Ha3 Ha4]]].
      destruct Hb as [Hb1 [Hb2 [Hb3 Hb4]]].
      repeat split.
      + rewrite unfold_lub2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_lub2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
      + rewrite unfold_glb2, unfold_more_specific. simpl.
        apply andb_true_iff. split; assumption.
  Qed.

  Lemma more_specific_lub2_l : forall d1 d2,
    more_specific d1 (lub2 d1 d2) = true.
  Proof.
    intros d1 d2.
    destruct (more_specific_lub_glb_pair d1 d2) as [H1 [H2 [H3 H4]]].
    assumption.
  Qed.

  Lemma more_specific_lub2_r : forall d1 d2,
    more_specific d2 (lub2 d1 d2) = true.
  Proof.
    intros d1 d2.
    destruct (more_specific_lub_glb_pair d1 d2) as [H1 [H2 [H3 H4]]].
    assumption.
  Qed.

  Lemma more_specific_glb2_l : forall d1 d2,
    more_specific (glb2 d1 d2) d1 = true.
  Proof.
    intros d1 d2.
    destruct (more_specific_lub_glb_pair d1 d2) as [H1 [H2 [H3 H4]]].
    assumption.
  Qed.

  Lemma more_specific_glb2_r : forall d1 d2,
    more_specific (glb2 d1 d2) d2 = true.
  Proof.
    intros d1 d2.
    destruct (more_specific_lub_glb_pair d1 d2) as [H1 [H2 [H3 H4]]].
    assumption.
  Qed.

  Lemma more_specific_lub_l : forall d1 d2 d3,
    more_specific d2 (lub d1 d2 d3) = true.
  Proof.
    intros. unfold lub.
    destruct d1 eqn:H1; try apply more_specific_Any.
    apply more_specific_lub2_l.
  Qed.

  Lemma more_specific_lub_r : forall d1 d2 d3,
    more_specific d3 (lub d1 d2 d3) = true.
  Proof.
    intros. unfold lub.
    destruct d1 eqn:H1; try apply more_specific_Any.
    apply more_specific_lub2_r.
  Qed.

  Lemma more_specific_lub2_general : forall u d1 d2,
    ( more_specific d1 u = true ->
      more_specific d2 u = true ->
      more_specific (lub2 d1 d2) u = true) /\
    ( more_specific u d1 = true ->
      more_specific u d2 = true ->
      more_specific u (glb2 d1 d2) = true).
  Proof.
    intros u d1 d2.
    refine (
    well_founded_induction
      lt_wf
      (fun n =>
        forall u d1 d2,
          sizeD d1 + sizeD d2 = n ->
            ( more_specific d1 u = true ->
              more_specific d2 u = true ->
              more_specific (lub2 d1 d2) u = true) /\
            ( more_specific u d1 = true ->
              more_specific u d2 = true ->
              more_specific u (glb2 d1 d2) = true))
      _
      (sizeD d1 + sizeD d2) u d1 d2 eq_refl
    ).
    intros n IH o d_1 d_2 Hsz. subst n.
    destruct d_1 as [| | a b]; destruct d_2 as [| | c d]; simpl;
    try (repeat split; reflexivity).

    - (* d1 = Det, d2 = Det *)
      repeat split; intros H1 H2;
      try rewrite unfold_lub2; try rewrite glb; assumption.

    - (* d1 = Det, d2 = Any *)
      repeat split; intros H1 H2;
      try rewrite unfold_lub2; try rewrite glb; assumption.

    - (* d1 = Det, d2 = Arrow c d *)
      pose proof (IH (sizeD Det + sizeD c) ltac:(simpl; lia)
                    o Det c eq_refl) as Hc.
      pose proof (IH (sizeD Det + sizeD d) ltac:(simpl; lia)
                    o Det d eq_refl) as Hd.
      destruct Hc as [Hc_l Hc_r].
      destruct Hd as [Hd_l Hd_r].
      repeat split; intros H1 H2.
      + destruct o.
        * simpl_all H2.
          rewrite unfold_lub2, unfold_more_specific.
          apply andb_true_iff. split.
          -- apply Hc_r; try assumption.
          -- apply Hd_l; try assumption.
        * apply more_specific_Any.
        * rewrite unfold_more_specific in H2.
          rewrite andb_true_iff in H2. destruct H2.
          rewrite unfold_more_specific in H1.
          rewrite andb_true_iff in H1. destruct H1.
          pose proof (IH (sizeD Det + sizeD c) ltac:(simpl; lia)
                        o1 Det c eq_refl) as Hc'.
          pose proof (IH (sizeD Det + sizeD d) ltac:(simpl; lia)
                        o2 Det d eq_refl) as Hd'.
          destruct Hc' as [Hc_l' Hc_r'].
          destruct Hd' as [Hd_l' Hd_r'].
          rewrite unfold_lub2, unfold_more_specific.
          apply andb_true_iff. split.
          -- apply Hc_r'; try assumption.
          -- apply Hd_l'; try assumption.
      + destruct o.
        * simpl_all H2.
          rewrite unfold_glb2, unfold_more_specific.
          apply andb_true_iff. split.
          -- apply Hc_l; try assumption.
          -- apply Hd_r; try assumption.
        * inversion H1.
        * simpl_all H1.
          simpl_all H2.
          pose proof (IH (sizeD Det + sizeD c) ltac:(simpl; lia)
                        o1 Det c eq_refl) as Hc'.
          pose proof (IH (sizeD Det + sizeD d) ltac:(simpl; lia)
                        o2 Det d eq_refl) as Hd'.
          destruct Hc' as [Hc_l' Hc_r'].
          destruct Hd' as [Hd_l' Hd_r'].
          rewrite unfold_glb2, unfold_more_specific.
          apply andb_true_iff. split.
            -- apply Hc_l'; assumption.
            -- apply Hd_r'; assumption.

    - (* d1 = Any, d2 = Det *)
      repeat split; intros H1 H2;
      try rewrite unfold_lub2; try rewrite unfold_glb2; assumption.

    - (* d1 = Any, d2 = Any *)
      repeat split; intros H1 H2;
      try rewrite unfold_lub2; try rewrite unfold_glb2; assumption.

    - (* d1 = Any, d2 = Arrow c d *)
      pose proof (IH (sizeD Any + sizeD c) ltac:(simpl; lia)
                    o Any c eq_refl) as Hc.
      pose proof (IH (sizeD Any + sizeD d) ltac:(simpl; lia)
                    o Any d eq_refl) as Hd.
      destruct Hc as [Hc_l Hc_r].
      destruct Hd as [Hd_l Hd_r].
      repeat split; intros H1 H2.
      + destruct o.
        * inversion H1.
        * apply more_specific_Any.
        * inversion H1.
      + destruct o.
        * simpl_all H2.
          rewrite unfold_glb2, unfold_more_specific.
          apply andb_true_iff. split; assumption.
        * inversion H2.
        * simpl_all H2.
          rewrite unfold_glb2, unfold_more_specific.
          apply andb_true_iff. split; assumption.

    - (* d1 = Arrow a b, d2 = Det *)
      pose proof (IH (sizeD a + sizeD Det) ltac:(simpl; lia)
                    o a Det eq_refl) as Hc.
      pose proof (IH (sizeD b + sizeD Det) ltac:(simpl; lia)
                    o b Det eq_refl) as Hd.
      destruct Hc as [Hc_l Hc_r].
      destruct Hd as [Hd_l Hd_r].
      repeat split; intros H1 H2.
      + destruct o.
        * simpl_all H1.
          rewrite unfold_lub2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_r; assumption.
          -- apply Hd_l; assumption.
        * apply more_specific_Any.
        * simpl_all H1.
          simpl_all H2.
          pose proof (IH (sizeD a + sizeD Det) ltac:(simpl; lia)
                        o1 a Det eq_refl) as Hc'.
          pose proof (IH (sizeD b + sizeD Det) ltac:(simpl; lia)
                        o2 b Det eq_refl) as Hd'.
          destruct Hc' as [Hc_l' Hc_r'].
          destruct Hd' as [Hd_l' Hd_r'].
          rewrite unfold_lub2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_r'; assumption.
          -- apply Hd_l'; assumption.
      + destruct o.
        * simpl_all H1.
          rewrite unfold_glb2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_l; assumption.
          -- apply Hd_r; assumption.
        * inversion H2.
        * simpl_all H1.
          simpl_all H2.
          pose proof (IH (sizeD a + sizeD Det) ltac:(simpl; lia)
                        o1 a Det eq_refl) as Hc'.
          pose proof (IH (sizeD b + sizeD Det) ltac:(simpl; lia)
                        o2 b Det eq_refl) as Hd'.
          destruct Hc' as [Hc_l' Hc_r'].
          destruct Hd' as [Hd_l' Hd_r'].
          rewrite unfold_glb2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_l'; assumption.
          -- apply Hd_r'; assumption.

    - (* d1 = Arrow a b, d2 = Any *)
      pose proof (IH (sizeD a + sizeD Any) ltac:(simpl; lia)
                    o a Any eq_refl) as Hc.
      pose proof (IH (sizeD b + sizeD Any) ltac:(simpl; lia)
                    o b Any eq_refl) as Hd.
      destruct Hc as [Hc_l Hc_r].
      destruct Hd as [Hd_l Hd_r].
      repeat split; intros H1 H2.
      + destruct o.
        * inversion H2.
        * apply more_specific_Any.
        * inversion H2.
      + destruct o.
        * simpl_all H1.
          rewrite unfold_glb2, unfold_more_specific. simpl.
          apply andb_true_iff. split; assumption.
        * inversion H1.
        * simpl_all H1.
          rewrite unfold_glb2, unfold_more_specific. simpl.
          apply andb_true_iff. split; assumption.

    - (* d1 = Arrow a b, d2 = Arrow c d *)
      pose proof (IH (sizeD a + sizeD c) ltac:(simpl; lia)
                    o a c eq_refl) as Hc.
      pose proof (IH (sizeD b + sizeD d) ltac:(simpl; lia)
                    o b d eq_refl) as Hd.
      destruct Hc as [Hc_l Hc_r].
      destruct Hd as [Hd_l Hd_r].
      repeat split; intros H1 H2.
      + destruct o.
        * simpl_all H1.
          simpl_all H2.
          rewrite unfold_lub2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_r; assumption.
          -- apply Hd_l; assumption.
        * apply more_specific_Any.
        * rewrite unfold_more_specific in H1.
          rewrite andb_true_iff in H1. destruct H1.
          rewrite unfold_more_specific in H2.
          rewrite andb_true_iff in H2. destruct H2.
          pose proof (IH (sizeD a + sizeD c) ltac:(simpl; lia)
                        o1 a c eq_refl) as Hc'.
          pose proof (IH (sizeD b + sizeD d) ltac:(simpl; lia)
                        o2 b d eq_refl) as Hd'.
          destruct Hc' as [Hc_l' Hc_r'].
          destruct Hd' as [Hd_l' Hd_r'].
          rewrite unfold_lub2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_r'; assumption.
          -- apply Hd_l'; assumption.
      + destruct o.
        * simpl_all H1.
          simpl_all H2.
          rewrite unfold_glb2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_l; assumption.
          -- apply Hd_r; assumption.
        * inversion H2.
        * simpl_all H1.
          simpl_all H2.
          pose proof (IH (sizeD a + sizeD c) ltac:(simpl; lia)
                        o1 a c eq_refl) as Hc'.
          pose proof (IH (sizeD b + sizeD d) ltac:(simpl; lia)
                        o2 b d eq_refl) as Hd'.
          destruct Hc' as [Hc_l' Hc_r'].
          destruct Hd' as [Hd_l' Hd_r'].
          rewrite unfold_glb2, unfold_more_specific. simpl.
          apply andb_true_iff. split.
          -- apply Hc_l'; assumption.
          -- apply Hd_r'; assumption.
  Qed.

  Lemma more_specific_lub: forall x1 x2 x3 d1 d2 d3,
    compatible x1 TBool ->
    more_specific x1 d1 = true ->
    more_specific x2 d2 = true ->
    more_specific x3 d3 = true ->
    more_specific (lub x1 x2 x3) (lub d1 d2 d3) = true.
  Proof.
    assert
      (forall d1 d2 x1 x2,
      more_specific d1 x1 = true ->
      more_specific d2 x2 = true ->
      more_specific (lub2 d1 d2) (lub2 x1 x2) = true)
      as more_specific_lub_small.
    --
    intros d1 d2 x1 x2 H0 H1.
    destruct (more_specific_lub_glb_pair x1 x2)
      as [Hlub_l [Hlub_r [Hglb_l Hglb_r]]].
    specialize (more_specific_transitive d1 x1 (lub2 x1 x2) H0 Hlub_l)
      as HA.
    specialize (more_specific_transitive d2 x2 (lub2 x1 x2) H1 Hlub_r)
      as HB.
    apply more_specific_lub2_general; assumption.
    --
    intros x1 x2 x3 d1 d2 d3 C1 H1 H2 H3.
    unfold lub.
    destruct x1, d1; try reflexivity.
    - eapply more_specific_lub_small; eassumption.
    - inversion H1.
    - inversion C1.
  Qed.

  Lemma nonAny_lub2_glb2_det_left: forall d,
    nonAny d ->
    nonAny (lub2 Det d) /\
    nonAny (glb2 Det d).
  Proof.
    induction d; intros.
    - split; reflexivity.
    - inversion H.
    - destruct H.
      apply IHd1 in H. destruct H.
      apply IHd2 in H0. destruct H0.
      split.
      + rewrite unfold_lub2. simpl.
        split; assumption.
      + rewrite unfold_glb2. simpl.
        split; assumption.
  Qed.

  Lemma nonAny_lub2_glb2_det_right: forall d,
    nonAny d ->
    nonAny (lub2 d Det) /\
    nonAny (glb2 d Det).
  Proof.
    induction d; intros.
    - split; reflexivity.
    - inversion H.
    - destruct H.
      apply IHd1 in H. destruct H.
      apply IHd2 in H0. destruct H0.
      split.
      + rewrite unfold_lub2. simpl.
        split; assumption.
      + rewrite unfold_glb2. simpl.
        split; assumption.
  Qed.

  Lemma nonAny_lub2: forall d1 d2,
    nonAny d1 ->
    nonAny d2 ->
      nonAny (lub2 d1 d2) /\
      nonAny (glb2 d1 d2).
  Proof.
    induction d1; intros.
    - split.
      * rewrite unfold_lub2.
        destruct d2.
        + reflexivity.
        + inversion H0.
        + destruct H0.
          apply nonAny_lub2_glb2_det_left in H0. destruct H0.
          apply nonAny_lub2_glb2_det_left in H1. destruct H1.
          simpl. split; assumption.
      * rewrite unfold_glb2.
        destruct d2.
        + reflexivity.
        + inversion H0.
        + destruct H0.
          apply nonAny_lub2_glb2_det_left in H0. destruct H0.
          apply nonAny_lub2_glb2_det_left in H1. destruct H1.
          simpl. split; assumption.
    - inversion H.
    - split.
      * rewrite unfold_lub2.
        destruct d2.
        + destruct H.
          apply nonAny_lub2_glb2_det_right in H. destruct H.
          apply nonAny_lub2_glb2_det_right in H1. destruct H1.
          simpl. split; assumption.
        + inversion H0.
        + destruct H, H0. simpl. split.
          ** apply IHd1_1; assumption.
          ** apply IHd1_2; assumption.
      * rewrite unfold_glb2.
        destruct d2.
        + destruct H.
          apply nonAny_lub2_glb2_det_right in H. destruct H.
          apply nonAny_lub2_glb2_det_right in H1. destruct H1.
          simpl. split; assumption.
        + inversion H0.
        + destruct H, H0. simpl. split.
          ** apply IHd1_1; assumption.
          ** apply IHd1_2; assumption.
  Qed.

  Lemma nonAny_lub: forall d1 d2 d3,
    compatible d1 TBool ->
    nonAny d1 ->
    nonAny d2 ->
    nonAny d3 ->
    nonAny (lub d1 d2 d3).
  Proof.
    intros.
    unfold lub.
    destruct d1.
    - apply nonAny_lub2; assumption.
    - inversion H0.
    - inversion H.
  Qed.

End LeastUpperBound.

(* Section DetTyping:
   Defines the typing rules for determinism types.
   These rules capture when an expression has a particular determinism type,
   connecting the operational behavior with static determinism properties. *)
Section DetTyping.

  Reserved Notation "Gamma '|-' e ':?' delta" (at level 40).
  Inductive hasDType : context -> Exp -> DType -> Prop :=
    | Rule_Var : forall Gamma x d,
          (Gamma x) = d ->
          Gamma |- Var x :? d
    | Rule_BTrue : forall Gamma,
          Gamma |- BTrue :? Det
    | Rule_BFalse : forall Gamma,
          Gamma |- BFalse :? Det
    | Rule_Nil : forall Gamma t,
          Gamma |- Nil t :? Det
    | Rule_Cons : forall Gamma e1 e2 d1 d2,
          Gamma |- e1 :? d1 ->
          Gamma |- e2 :? d2 ->
          let d3 := if more_specific d1 Det && more_specific d2 Det then Det else Any in
          Gamma |- Cons e1 e2 :? d3
    | Rule_AppAny : forall Gamma e1 e2 d,
          Gamma |- e1 :? Any ->
          Gamma |- e2 :? d ->
          Gamma |- App e1 e2 :? Any
    | Rule_AppDet : forall Gamma e1 e2 d,
          Gamma |- e1 :? Det ->
          Gamma |- e2 :? d ->
          Gamma |- App e1 e2 :? decide Det d Det
    | Rule_AppFun : forall Gamma e1 e2 d1 d2 d3 d4,
          Gamma |- e1 :? Arrow d1 d2 ->
          Gamma |- e2 :? d3 ->
          d4 = decide d1 d3 d2 ->
          Gamma |- App e1 e2 :? d4
    | Rule_Abs : forall Gamma x e d1 d2 t1,
          compatible d1 t1 ->
          let Gamma' := update Nat.eqb Gamma x d1 in
          Gamma' |- e :? d2 ->
          Gamma |- Abs x t1 e :? Arrow d1 d2
    | Rule_Choice : forall Gamma e1 e2 d1 d2,
          Gamma |- e1 :? d1 ->
          Gamma |- e2 :? d2 ->
          Gamma |- Or e1 e2 :? Any
    | Rule_Free : forall Gamma x t e d,
          let Gamma' := update Nat.eqb Gamma x Any in
          Gamma' |- e :? d ->
          Gamma |- Free x t e :? d
    | Rule_CaseBool : forall Gamma e1 e2 e3 d1 d2 d3,
          Gamma |- e1 :? d1 ->
          Gamma |- e2 :? d2 ->
          Gamma |- e3 :? d3 ->
          Gamma |- CaseB e1 e2 e3 :? lub d1 d2 d3
    | Rule_CaseList :
        forall Gamma e1 e2 e3 n1 n2 d1 t1 d2 d_1 d_2 d_3 H,
          Gamma |- e1 :? d_1 ->
          compatible d1 t1 ->
          compatible d2 (TList t1) ->
          Gamma |- e2 :? d_2 ->

          let Gamma'  := update Nat.eqb Gamma  n1 d1 in
          let Gamma'' := update Nat.eqb Gamma' n2 d2 in
          Gamma'' |- e3 :? d_3 ->
          let p := Pat n1 t1 n2 H in
          more_specific d_1 d1 = true -> (* not needed for d_2, d2*)
          Gamma |- CaseL e1 e2 p e3 :? lub d_1 d_2 d_3
    where "Gamma '|-' e ':?' delta" := (hasDType Gamma e delta).

End DetTyping.

(* Section SmallStepSemantics:
   Defines the operational semantics of the language using a small-step
   reduction relation. Includes substitution functions and free/bound variable tracking. *)
Section SmallStepSemantics.

  Fixpoint subst (n : nat) (v : Exp) (e : Exp) : Exp :=
    match e with
    | Var x => if Nat.eqb x n then v else e
    | BTrue => BTrue
    | BFalse => BFalse
    | Nil t => Nil t
    | Cons e1 e2 => Cons (subst n v e1) (subst n v e2)
    | App e1 e2 => App (subst n v e1) (subst n v e2)
    | Abs x t e => if Nat.eqb x n
                    then Abs x t e
                    else Abs x t (subst n v e)
    | Or e1 e2 => Or (subst n v e1) (subst n v e2)
    | Free x t e => if Nat.eqb x n
                    then Free x t e
                    else Free x t (subst n v e)
    | CaseB e1 e2 e3 =>
        CaseB (subst n v e1) (subst n v e2) (subst n v e3)
    | CaseL e1 e2 (Pat n1 t1 n2 H) e3 =>
      if Nat.eqb n n1 || Nat.eqb n n2
        then CaseL (subst n v e1) (subst n v e2)
                   (Pat n1 t1 n2 H) e3
        else CaseL (subst n v e1) (subst n v e2)
          (Pat n1 t1 n2 H) (subst n v e3)
    end.

  Fixpoint subst_all (ns : list (nat * Exp * TType)) (e : Exp) : Exp :=
    match ns with
    | [] => e
    | (n, e', _)::ns => subst_all ns (subst n e' e)
    end.

  Fixpoint removeb {A} (beq : A -> A -> bool) (x : A) (l : list A) : list A :=
    match l with
    | [] => []
    | y :: ys => if beq x y then removeb beq x ys else y :: removeb beq x ys
    end.

  Fixpoint freeVars (e : Exp) : list nat :=
    match e with
    | Var x => [x]
    | BTrue => []
    | BFalse => []
    | Nil _ => []
    | Cons e1 e2 => freeVars e1 ++ freeVars e2
    | App e1 e2 => freeVars e1 ++ freeVars e2
    | Abs x _ e' => removeb Nat.eqb x (freeVars e')
    | Or e1 e2 => freeVars e1 ++ freeVars e2
    | Free x _ e' => removeb Nat.eqb x (freeVars e')
    | CaseB e1 e2 e3 =>
        freeVars e1 ++ freeVars e2 ++ freeVars e3
    | CaseL e1 e2 (Pat n1 _ n2 _) e3 =>
        freeVars e1 ++ freeVars e2 ++
        removeb Nat.eqb n1 (removeb Nat.eqb n2 (freeVars e3))
    end.

  Fixpoint boundVars (e : Exp) : list nat :=
    match e with
    | Var _ => []
    | BTrue => []
    | BFalse => []
    | Nil _ => []
    | Cons e1 e2 => boundVars e1 ++ boundVars e2
    | App e1 e2 => boundVars e1 ++ boundVars e2
    | Abs x _ e' => x :: boundVars e'
    | Or e1 e2 => boundVars e1 ++ boundVars e2
    | Free x _ e' => x :: boundVars e'
    | CaseB e1 e2 e3 =>
        boundVars e1 ++ boundVars e2 ++ boundVars e3
    | CaseL e1 e2 (Pat n1 _ n2 _) e3 =>
        boundVars e1 ++ boundVars e2 ++
        n1 :: n2 :: boundVars e3
    end.

  Fixpoint anyIn (xs ys : list nat) : bool :=
    match xs with
    | [] => false
    | x::xs' => if List.existsb (Nat.eqb x) ys
                  then true
                  else anyIn xs' ys
    end.

  (* Helper function to construct first-order proof *)
  Fixpoint first_order_proof (t : TType) : option (first_order t) :=
    match t with
    | TBool => Some I
    | TList t' => match first_order_proof t' with
                  | Some pf => Some pf
                  | None => None
                  end
    | TArrow _ _ => None
    end.

  Fixpoint gen (t : TType) : option Exp :=
    match t with
    | TBool => Some (Or BTrue BFalse)
    | TList t' => match gen t', first_order_proof (TList t') with
                  | Some e', Some pf => Some (Or (Nil t')
                                                 (Cons e'
                                                   (Free 0 (FO (TList t') pf)
                                                     (Var 0))))
                  | _, _ => None
                  end
    | TArrow t1 t2 => None
    end.

  Lemma typeOf_gen : forall t c e,
    gen t = Some e ->
    typeOf c e = Some t.
  Proof.
    induction t; intros; eauto.
    - simpl in *. inversion H. auto.
    - simpl in *.
      destruct (gen t) eqn:Hgen; try discriminate.
      destruct (first_order_proof t) eqn:Hpf; try discriminate.
      inversion H. subst. simpl in *.
      rewrite IHt; eauto. rewrite eqTypeS_refl, eqType_refl.
      reflexivity.
    - inversion H.
  Qed.

  Lemma freeVars_gen : forall t e,
    gen t = Some e ->
    freeVars e = [].
  Proof.
    induction t; intros; eauto.
    - simpl in *. inversion H. auto.
    - simpl in *.
      destruct (gen t) eqn:Hgen; try discriminate.
      destruct (first_order_proof t) eqn:Hpf; try discriminate.
      inversion H. subst. simpl in *.
      rewrite IHt; eauto.
    - inversion H.
  Qed.

  (* Small-step semantics *)

  Fixpoint step (e : Exp) : option Exp :=
    match e with
    | App (Abs x _ e1) e2 => if anyIn (freeVars e2) (x::boundVars e1)
            then None
            else Some (subst x e2 e1)
    | App (Or e1 e2) e3 => Some (Or (App e1 e3) (App e2 e3))
    | App e1 e2 => match step e1 with
                    | None => None
                    | Some e1' => Some (App e1' e2)
                    end
    | CaseB e e2 e3 =>
        match step e with
        | None =>
          match e with
          | (Or e4 e5) =>
              Some (Or (CaseB e4 e2 e3) (CaseB e5 e2 e3))
          | BFalse => Some e2
          | BTrue => Some e3
          | _ => None
          end
        | Some e' => Some (CaseB e' e2 e3)
        end
    | CaseL e e2 (Pat n1 t1 n2 H) e3 =>
        match step e with
        | None =>
          match e with
          | (Or e4 e5) =>
              Some (Or (CaseL e4 e2 (Pat n1 t1 n2 H) e3)
                      (CaseL e5 e2 (Pat n1 t1 n2 H) e3))
          | Nil _ => Some e2
          | Cons e4 e5 =>
            if anyIn (freeVars (Cons e4 e5)) (n1::n2::boundVars e3)
              then None
              else if anyIn (freeVars e5) (boundVars e4)
                then None
                else Some (subst_all [(n1, e4, t1);
                                      (n2, e5, TList t1)] e3)
          | _ => None
          end
        | Some e' => Some (CaseL e' e2 (Pat n1 t1 n2 H) e3)
        end
    | Or e1 e2 => match step e1 with
                  | None => match step e2 with
                            | None => None
                            | Some e2' => Some (Or e1 e2')
                            end
                  | Some e1' => Some (Or e1' e2)
                  end
    | Free n (FO t _) e => match (gen t) with
                      | Some e' => Some (subst n e' e)
                      | None => None
                      end
    | Cons e1 e2 => match step e1 with
                    | None => match step e2 with
                              | None => None
                              | Some e2' => Some (Cons e1 e2')
                              end
                    | Some e1' => Some (Cons e1' e2)
                    end
    | _ => None
    end.

  Reserved Notation "e '==>' e'" (at level 40).
  Inductive step_rel : Exp -> Exp -> Prop :=
    Single_Step : forall e e', step e = Some e' -> e ==> e'
  where "e '==>' e'" := (step_rel e e').

  Reserved Notation "e '==>*' e'" (at level 40).
  Inductive multi_step_rel : Exp -> Exp -> Prop :=
    | Multi_Step_Refl : forall e, e ==>* e
    | Multi_Step_Many : forall e1 e2 e3, e1 ==> e2 -> e2  ==>* e3 -> e1 ==>* e3
  where "e '==>*' e'" := (multi_step_rel e e').

End SmallStepSemantics.


(* redeclare notation globally *)
Notation "Gamma '|-' e ':?' delta" := (hasDType Gamma e delta)
  (at level 40).

Notation "e ==> e'" := (step_rel e e') (at level 40).

Notation "e '==>*' e'" := (multi_step_rel e e')
  (at level 40).

Section Examples.
  (* Examples of determinism types and typing rules *)

  Hint Resolve Rule_Var Rule_BTrue Rule_BFalse Rule_Nil
               Rule_Cons Rule_Choice Rule_CaseBool
               Rule_CaseList : core.

  Definition Gamma1 := update Nat.eqb (fun _ => Any) 1 Det.

  Example exVar : Gamma1 |- Var 1 :? Det.
  Proof. eauto. Qed.

  Example exFreeVar : Gamma1 |- Var 42 :? Any.
  Proof. eauto. Qed.

  Example exCons : Gamma1 |- Nil TBool :? Det.
  Proof. eauto. Qed.

  Example exApp : Gamma1 |- App (Abs 2 TBool (Var 2)) (Var 1) :? Det.
  Proof.
    eapply Rule_AppFun with (d1 := Det) (d2 := Det) (d3 := Det);
    try apply Rule_Abs; eauto; reflexivity.
  Qed.

  Example exAppEval : App (Abs 2 TBool (Var 2)) (Var 1) ==>* Var 1.
  Proof.
    eapply Multi_Step_Many. apply Single_Step.
    reflexivity. apply Multi_Step_Refl.
  Qed.

  Example exAbs : Gamma1 |- Abs 2 TBool (Var 1) :? Arrow Det Det.
  Proof.
    apply Rule_Abs; eauto; reflexivity.
  Qed.

  Definition Gamma2 := update Nat.eqb (fun _ => Any) 1 (Arrow (Arrow Det Det) (Arrow Det Det)).

  Example exPoly : Gamma2 |- App (Var 1) (Abs 2 TBool (Var 2)) :? Arrow Det Det.
  Proof.
    eapply Rule_AppFun with (d1 := Arrow Det Det)
                            (d2 := Arrow Det Det)
                            (d3 := Arrow Det Det);
    try apply Rule_Abs; eauto. reflexivity.
  Qed.

  Example exChoice : Gamma1 |- Or (Var 1) (Var 1) :? Any.
  Proof. eauto. Qed.

  Example exFree : step (Free 1 (FO TBool I) (Var 1)) = Some (Or BTrue BFalse).
  Proof. reflexivity. Qed.

  (*
  1 = allValues :? Any -> Det
  2 = \x -> id x ? not x :? Any -> Any
  result must not be of type Det
  *)
  Definition RhoAV' := update Nat.eqb (fun _ => TBool) 1 (TArrow TBool TBool).
  Definition RhoAV  := update Nat.eqb RhoAV' 2 (TArrow TBool TBool).
  Definition GammaAV := update Nat.eqb (update Nat.eqb (fun _ => Any) 1 Any) 2 (mkCompatible (RhoAV 2)).
  (* GammaAV = {1 -> Any, 2 -> Arrow Det Det} *)

  (* The following example requires the AppAny rule to type it correctly. *)
  Example exAllValues : GammaAV |- App (Var 1) (Var 2) :? Any.
  Proof.
      eapply Rule_AppAny; apply Rule_Var; reflexivity.
  Qed.

  (* (Det -> Det -> Det) <=
     (Det -> Any -> Det). *)
  Example exFlipConst :
    less_specific
      (Arrow Det (Arrow Det Det))
      (Arrow Det (Arrow Any Det)) = true.
  Proof. intuition. Qed.

End Examples.

(* Section PreservationTTypesHelper:
   Helper lemmas for the preservation theorem, primarily focused on
   variable management, substitution properties, and interaction between
   free and bound variables. *)
Section PreservationTTypesHelper.

  Lemma existsb_concat :
    forall (l1 l2 : list nat) (beq : nat -> nat -> bool) x,
    existsb (beq x) (l1 ++ l2) = false <->
      existsb (beq x) l1 = false /\ existsb (beq x) l2 = false.
  Proof.
    induction l1; intros l2 beq x.
    - intuition.
    - split; intros.
      + simpl in H. destruct (beq x a) eqn:Heq.
        * discriminate.
        * apply IHl1 in H. destruct H as [H1 H2].
          split. simpl. rewrite Heq. assumption. assumption.
      + destruct H as [H1 H2]. simpl in *.
        destruct (beq x a) eqn:Heq.
        * discriminate.
        * apply IHl1. intuition.
  Qed.

  Lemma anyIn_concat1 :
    forall e1 e2 e3,
    anyIn e1 (e2 ++ e3) = false <->
    anyIn e1 e2 = false /\ anyIn e1 e3 = false.
  Proof.
    induction e1; intros e2 e3.
    - intuition.
    - split; intros.
      + simpl in H.
        destruct (List.existsb (Nat.eqb a)
                               (e2 ++ e3)) eqn:Heq.
        * discriminate.
        * apply IHe1 in H. destruct H as [H1 H2].
          apply existsb_concat in Heq. destruct Heq.
          split; simpl; try rewrite H; try rewrite H0; assumption.
      + destruct H. simpl in *.
        destruct (existsb (Nat.eqb a) e2) eqn:Heq2.
        * discriminate.
        * destruct (existsb (Nat.eqb a) e3) eqn:Heq3.
          --  discriminate.
          --  specialize (existsb_concat e2 e3
                            Nat.eqb a) as H1.
              destruct H1. rewrite H2.
              apply IHe1. split; assumption.
              split; assumption.
  Qed.

  Lemma anyIn_concat2 :
    forall e1 e2 e3,
    anyIn (e1 ++ e2) e3 = false <->
    anyIn e1 e3 = false /\ anyIn e2 e3 = false.
  Proof.
    induction e1; intros e2 e3.
    - intuition.
    - split; intros.
      + simpl in *.
        destruct (List.existsb (Nat.eqb a) e3) eqn:Heq.
        * discriminate.
        * apply IHe1 in H. destruct H as [H1 H2]. intuition.
      + simpl in *. destruct H.
        destruct (List.existsb (Nat.eqb a) e3) eqn:Heq.
        * discriminate.
        * apply IHe1. intuition.
  Qed.

  Lemma anyIn_cons :
    forall e1 e2 a,
    anyIn e1 (a :: e2) = false <->
    anyIn e1 e2 = false /\ anyIn e1 [a] = false.
  Proof.
    induction e1; intros.
    - intuition.
    - split; intros.
      + simpl in H. destruct (a =? a0) eqn:Heq.
        * discriminate.
        * simpl in *.
          destruct (existsb (Nat.eqb a) e2) eqn:Heq2.
          --  discriminate.
          --  apply IHe1 in H. destruct H. split.
              assumption. rewrite Heq. rewrite H0. reflexivity.
      + destruct H as [H1 H2]. simpl in *.
        destruct (a =? a0) eqn:Heq.
        * discriminate.
        * destruct (existsb (Nat.eqb a) e2) eqn:Heq2.
          --  discriminate.
          --  apply IHe1. intuition.
  Qed.

  Lemma anyIn_subterm :
    forall e1 e2,
    anyIn (freeVars e2) (boundVars e1) = false ->
    match e1 with
    | Cons e1' e2' => anyIn (freeVars e2) (boundVars e1') = false /\
                      anyIn (freeVars e2) (boundVars e2') = false
    | App e1' e2'  => anyIn (freeVars e2) (boundVars e1') = false /\
                      anyIn (freeVars e2) (boundVars e2') = false
    | Abs x _ e1'  => anyIn (freeVars e2) (boundVars e1') = false /\
                      anyIn (freeVars e2) [x] = false
    | Or e1' e2'   => anyIn (freeVars e2) (boundVars e1') = false /\
                      anyIn (freeVars e2) (boundVars e2') = false
    | Free x _ e1' => anyIn (freeVars e2) (boundVars e1') = false /\
                      anyIn (freeVars e2) [x] = false
    | CaseB e1' e2' e3' =>
        anyIn (freeVars e2) (boundVars e1') = false /\
        anyIn (freeVars e2) (boundVars e2') = false /\
        anyIn (freeVars e2) (boundVars e3') = false
    | CaseL e1' e2' (Pat n1 _ n2 _) e3' =>
        anyIn (freeVars e2) (boundVars e1') = false /\
        anyIn (freeVars e2) (boundVars e2') = false /\
        anyIn (freeVars e2) (n1 :: n2 :: boundVars e3') = false
    | _ => True
    end.
  Proof.
    intros e1 e2 H. destruct e1; try destruct p; simpl in *;
    try reflexivity; try apply anyIn_concat1 in H;
    try apply anyIn_cons in H; intuition;
    try apply anyIn_concat1 in H1; intuition;
    try assumption.
  Qed.

  Lemma anyIn_removeb : forall xs n n1,
    n <> n1 ->
    anyIn (removeb Nat.eqb n xs) [n1] = false ->
    anyIn xs [n1] = false.
  Proof.
    induction xs.
    - intros n n1 H H2. reflexivity.
    - intros n n1 H H2. simpl in H2.
      destruct (n =? a) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst a. simpl.
        rewrite <- Nat.eqb_neq in H. rewrite H. simpl.
        eapply IHxs. apply Nat.eqb_neq in H.
        apply H. assumption.
      + simpl in *. destruct (a =? n1) eqn:Heq1.
        * simpl in H2. inversion H2.
        * simpl in *. eapply IHxs. eassumption. assumption.
  Qed.

  Lemma typeOf_unbound :
    forall e Delta n t t2,
    typeOf Delta e = Some t ->
    anyIn (freeVars e) [n] = false ->
    typeOf (update Nat.eqb Delta n t2) e = typeOf Delta e.
  Proof.
    induction e; intros Delta n1 t1 t2 H H1; simpl in *.
    - destruct (n =? n1) eqn:Heq; inversion H1.
      unfold update. rewrite Nat.eqb_sym in Heq. rewrite Heq.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct_typeOf_chain H.
      eapply anyIn_concat2 in H1.
      destruct H1 as [H1 H2]. erewrite IHe1. erewrite IHe2.
      rewrite Heq1. rewrite Heq2. rewrite eqTypeS_refl.
      reflexivity. eassumption.
      assumption. eassumption. assumption.
    - destruct_typeOf_chain H.
      eapply anyIn_concat2 in H1.
      destruct H1 as [H1 H2]. erewrite IHe1. erewrite IHe2.
      rewrite Heq1. rewrite Heq2. rewrite Heq3. reflexivity.
      apply Heq2. assumption. apply Heq1. assumption.
    - destruct_typeOf_chain H.
      destruct (n =? n1) eqn:Heq2.
      + apply Nat.eqb_eq in Heq2. subst n1.
        rewrite double_update. rewrite Heq1. reflexivity.
      + apply Nat.eqb_neq in Heq2.
        rewrite double_update_indep. erewrite IHe.
        rewrite Heq1. reflexivity. apply Heq1.
        eapply anyIn_removeb. apply Heq2. assumption.
        symmetry. assumption.
    - destruct_typeOf_chain H. eapply anyIn_concat2 in H1.
      destruct H1 as [H1 H2]. erewrite IHe1. erewrite IHe2.
      rewrite Heq1. rewrite Heq0. rewrite eqTypeS_refl.
      reflexivity. apply Heq0. assumption. apply Heq1. assumption.
    - destruct t, (n =? n1) eqn:Heq2.
      + apply Nat.eqb_eq in Heq2. subst n1.
        rewrite double_update. reflexivity.
      + apply Nat.eqb_neq in Heq2.
        rewrite double_update_indep; eauto.
        erewrite IHe; eauto.
        eapply anyIn_removeb; eauto.
    - destruct_typeOf_chain H. eapply anyIn_concat2 in H1.
      destruct H1 as [H3 H4]. apply anyIn_concat2 in H4.
      destruct H4 as [H5 H6]. erewrite IHe1.
      rewrite Heq1. erewrite IHe2. rewrite Heq2.
      erewrite IHe3. rewrite Heq3. rewrite eqType_refl. reflexivity.
      eassumption. eassumption. eassumption.
      eassumption. eassumption. eassumption.
    - destruct p. destruct_typeOf_chain H.
      eapply anyIn_concat2 in H1.
      destruct H1 as [H1 H2]. apply anyIn_concat2 in H2.
      destruct H2 as [H3 H4].
      erewrite IHe1; try eassumption.
      erewrite IHe2; try eassumption.
      rewrite eqTypeS_refl. rewrite Heq1.
      rewrite eqTypeS_refl. rewrite Heq2. rewrite eqTypeS_refl.
      destruct (n1 =? n2) eqn:Heq6.
      + rewrite Nat.eqb_eq in Heq6. subst n2.
        rewrite double_update. rewrite Heq3.
        rewrite eqTypeS_refl. reflexivity.
      + destruct (n1 =? n0) eqn:Heq7.
        * apply Nat.eqb_neq in Heq6. apply Nat.eqb_eq in Heq7.
          subst n0. rewrite (double_update_indep _ n1 _ n2).
          rewrite double_update. rewrite Heq3.
          rewrite eqTypeS_refl. reflexivity.
          assumption.
        * apply Nat.eqb_neq in Heq6. apply Nat.eqb_neq in Heq7.
          rewrite (double_update_indep _ n1 _ n2); eauto.
          rewrite (double_update_indep _ n1 _ n0); eauto.
          erewrite IHe3; eauto. rewrite Heq3.
          rewrite eqTypeS_refl. reflexivity.
          apply anyIn_removeb in H4; eauto.
          apply anyIn_removeb in H4; eauto.
  Qed.

  Lemma anyIn_subst :
    forall e1 e2 e3 n3,
    anyIn (freeVars e2) (boundVars e1) = false ->
    anyIn (freeVars e3) [n3] = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    anyIn (freeVars e2) (boundVars (subst n3 e3 e1)) = false.
  Proof.
    induction e1; intros e2 e3 n3 H1 H2 H3; simpl; auto.
    - destruct (n =? n3) eqn:Heq.
      * rewrite Nat.eqb_eq in Heq. subst n3.
        simpl in H1. apply H3.
      * apply H1.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      apply anyIn_concat1; intuition.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      apply anyIn_concat1; intuition.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      destruct (n =? n3) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst n3.
        simpl in *. apply anyIn_cons; intuition.
      * simpl in *. apply anyIn_cons; intuition.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      apply anyIn_concat1; intuition.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      destruct t, (n =? n3) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst n3.
        simpl in *. apply anyIn_cons; intuition.
      + simpl in *. apply anyIn_cons; intuition.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      apply anyIn_concat1; intuition.
      apply anyIn_concat1; intuition.
    - destruct p. apply anyIn_subterm in H1.
      destruct H1, H0. simpl.
      destruct (n3 =? n1) eqn:Heq1,
                (n3 =? n2) eqn:Heq2; simpl in *.
      + apply Nat.eqb_eq in Heq1. apply Nat.eqb_eq in Heq2. subst.
        apply anyIn_concat1; intuition.
      + apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. subst.
        apply anyIn_concat1; intuition.
        apply anyIn_concat1; intuition.
      + apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. subst.
        apply anyIn_concat1; intuition.
        apply anyIn_concat1; intuition.
      + apply Nat.eqb_neq in Heq1. apply Nat.eqb_neq in Heq2.
        apply anyIn_concat1; intuition.
        apply anyIn_concat1; intuition.
        apply anyIn_cons in H1. destruct H1.
        apply anyIn_cons in H1. destruct H1.
        apply anyIn_cons; intuition.
        apply anyIn_cons; intuition.
  Qed.

End PreservationTTypesHelper.

(* Section PreservationTTypes:
   Main lemmas for type preservation, showing that typing is preserved
   under substitution and reduction steps. *)
Section PreservationTTypes.

  Lemma subst_preservation :
    forall Delta e1 e2 n t t2,
    anyIn (freeVars e2) (n::boundVars e1) = false ->
    typeOf (update Nat.eqb Delta n t2) e1 = Some t ->
    typeOf Delta e2 = Some t2 ->
    typeOf Delta (subst n e2 e1) = Some t.
  Proof.
    intros Delta e1. generalize dependent Delta.
    induction e1; intros Delta e2 n0 t1 t2 HF H H1.
    - simpl in H. inversion H. subst.
      unfold subst. unfold update.
      destruct (n =? n0) eqn:Heq.
      + rewrite Nat.eqb_eq in Heq. subst n0.
        rewrite Nat.eqb_refl. assumption.
      + rewrite Nat.eqb_sym in Heq. simpl.
        rewrite Heq. reflexivity.
    - inversion H. simpl. reflexivity.
    - inversion H. simpl. reflexivity.
    - inversion H. simpl. reflexivity.
    - inversion H. simpl.
      destruct_typeOf_chain H2.
      apply anyIn_cons in HF.
      destruct HF as [HF HFA].
      apply anyIn_concat1 in HF. destruct HF as [HF1 HF2].
      erewrite IHe1_1 with (t := t3).
      erewrite (IHe1_2) with (t := TList t3).
      reflexivity. apply anyIn_cons.
      split; assumption.
      eassumption. assumption. apply anyIn_cons.
      split; assumption. eassumption. assumption.
    - simpl. simpl in H.
      destruct_typeOf_chain H.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_concat1 in HF. destruct HF as [HF1 HF2].
      eapply (IHe1_1 Delta) in Heq1. eapply (IHe1_2 Delta) in Heq2.
      rewrite Heq1. rewrite Heq2. rewrite Heq3.
      reflexivity. apply anyIn_cons. split;
      assumption. assumption. apply anyIn_cons.
      split; assumption. assumption.
    - simpl. simpl in H.
      destruct_typeOf_chain H.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_cons in HF. destruct HF as [HF1 HF2].
      inversion H. subst. destruct (n =? n0) eqn:Heq2.
      + apply Nat.eqb_eq in Heq2. subst n0.
        simpl. rewrite double_update in Heq1.
        rewrite Heq1. reflexivity.
      + simpl. erewrite IHe1. reflexivity.
        apply anyIn_cons. split; assumption.
        rewrite double_update_indep. apply Heq1.
        apply Nat.eqb_neq in Heq2. assumption.
        erewrite typeOf_unbound; try eassumption.
    - simpl. simpl in H.
      destruct_typeOf_chain H.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_concat1 in HF. destruct HF as [HF1 HF2].
      erewrite IHe1_1. erewrite IHe1_2.
      rewrite eqTypeS_refl. reflexivity.
      apply anyIn_cons. split; assumption.
      eassumption. apply H1.
      apply anyIn_cons. split; assumption.
      apply Heq1. apply H1.
    - simpl in *.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_cons in HF. destruct HF as [HF1 HF2].
      destruct t, (n =? n0) eqn:Heq2.
      + apply Nat.eqb_eq in Heq2. subst n0.
        simpl. rewrite double_update in H.
        assumption.
      + simpl. erewrite IHe1. reflexivity.
        apply anyIn_cons. split; assumption.
        rewrite double_update_indep. apply H.
        apply Nat.eqb_neq in Heq2. assumption.
        erewrite typeOf_unbound; try eassumption.
    - simpl. simpl in H.
      destruct_typeOf_chain H.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_concat1 in HF. destruct HF as [HF1 HF2].
      apply anyIn_concat1 in HF2. destruct HF2.
      erewrite IHe1_1 with (t := TBool).
      erewrite IHe1_2. erewrite IHe1_3.
      rewrite eqType_refl. reflexivity.
      apply anyIn_cons. split; assumption.
      apply Heq3. eassumption. apply anyIn_cons.
      split; assumption. apply Heq2. eassumption.  apply anyIn_cons. split; assumption. apply Heq1. eassumption.
    - destruct p. simpl. simpl in H.
      destruct_typeOf_chain H.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_concat1 in HF. destruct HF as [HF HF2].
      apply anyIn_concat1 in HF2. destruct HF2 as [HF2 HF3].
      destruct (n0 =? n1) eqn:HeqN1,
               (n0 =? n2) eqn:HeqN2.
      * apply Nat.eqb_eq in HeqN1.
        apply Nat.eqb_eq in HeqN2. subst.
        simpl. rewrite double_update in Heq3.
        rewrite double_update in Heq3.
        rewrite double_update.
        rewrite Heq3. erewrite IHe1_1.
        rewrite eqTypeS_refl.
        erewrite IHe1_2. rewrite eqTypeS_refl. reflexivity.
        apply anyIn_cons. split; assumption.
        eassumption. eassumption.
        apply anyIn_cons. split; assumption.
        eassumption. eassumption.
      * apply Nat.eqb_eq in HeqN1.
        apply Nat.eqb_neq in HeqN2. subst. simpl.
        rewrite double_update_indep in Heq3; eauto.
        rewrite double_update in Heq3; eauto.
        rewrite double_update_indep in Heq3; eauto.
        erewrite Heq3. erewrite IHe1_1; eauto.
        rewrite eqTypeS_refl.
        erewrite IHe1_2; eauto. rewrite eqTypeS_refl. reflexivity.
        apply anyIn_cons. intuition.
        apply anyIn_cons. intuition.
      * apply Nat.eqb_neq in HeqN1.
        apply Nat.eqb_eq in HeqN2. subst. simpl.
        rewrite double_update in Heq3.
        erewrite Heq3. erewrite IHe1_1; eauto.
        rewrite eqTypeS_refl.
        erewrite IHe1_2; eauto. rewrite eqTypeS_refl. reflexivity.
        apply anyIn_cons. intuition.
        apply anyIn_cons. intuition.
      * apply Nat.eqb_neq in HeqN1.
        apply Nat.eqb_neq in HeqN2.
        subst. simpl. erewrite IHe1_1. shelve.
        apply anyIn_cons. split; assumption.
        apply Heq1. eassumption. Unshelve. simpl.
        rewrite (eqType_refl).
        apply anyIn_cons in HF3. destruct HF3.
        apply anyIn_cons in H0. destruct H0.
        erewrite IHe1_2. shelve.
        apply anyIn_cons. split; assumption.
        rewrite Heq2. reflexivity. assumption. Unshelve.
        erewrite IHe1_3. rewrite eqTypeS_refl. reflexivity.
        apply anyIn_cons. split; assumption.
        erewrite (double_update_indep _ n1 _ n0); eauto.
        erewrite (double_update_indep _ n2 _ n0); eauto.
        erewrite typeOf_unbound; try eassumption.
        erewrite typeOf_unbound; try eassumption.
        erewrite typeOf_unbound; try eassumption.
  Qed.

  Lemma subst_preservation2 :
    forall Delta e1 e2 n t n3 t3 e3 t2,
    anyIn (freeVars e2) (n3::n::boundVars e1) = false ->
    anyIn (freeVars e3) (n3::n::boundVars e1) = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    n <> n3 ->
    typeOf (update Nat.eqb (update Nat.eqb Delta n3 t3) n t2) e1
      = Some t ->
    typeOf Delta e2 = Some t2 ->
    typeOf Delta e3 = Some t3 ->
    typeOf Delta (subst n e2 (subst n3 e3 e1)) = Some t.
  Proof.
    intros.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H0. destruct H0.
    apply anyIn_cons in H0. destruct H0.
    * eapply subst_preservation; eauto.
      - apply anyIn_cons; intuition.
        apply anyIn_subst; assumption.
      - eapply subst_preservation.
        + apply anyIn_cons; intuition.
        + rewrite double_update_indep; eassumption.
        + erewrite typeOf_unbound; eassumption.
  Qed.

  Lemma step_preservation :
    forall e e' Delta t,
    step e = Some e' ->
    typeOf Delta e = Some t ->
    typeOf Delta e' = Some t.
  Proof.
    induction e; intros; inversion H; subst.
    - destruct (step e1) eqn:Heq1, (step e2) eqn:Heq2;
      inversion H2; subst.
      + destruct_typeOf_chain H0.
        erewrite IHe1. rewrite eqTypeS_refl.
        apply H0. reflexivity. assumption.
      + destruct_typeOf_chain H0.
        erewrite IHe1. rewrite eqTypeS_refl.
        apply H0. reflexivity. assumption.
      + destruct_typeOf_chain H0.
        erewrite IHe2 with (t := TList t2).
        rewrite eqTypeS_refl.
        apply H0. reflexivity. assumption.
  - destruct e1; try inversion H2.
    + destruct_typeOf_chain H0.
    + destruct (step (App e1_1 e1_2)) eqn:Heq1;
      inversion H2; subst.
      destruct_typeOf_chain H0.
      erewrite IHe1 with (t := TArrow _ _).
      rewrite Heq7. reflexivity. reflexivity.
      simpl. rewrite Heq0. rewrite Heq3.
      rewrite Heq4. reflexivity.
    + destruct_typeOf_chain H0.
      destruct (anyIn (freeVars e2) (n::boundVars e1)) eqn:Heq4;
      try inversion H2; subst. eapply subst_preservation;
      eassumption.
    + destruct_typeOf_chain H0.
      rewrite eqTypeS_refl. reflexivity.
    + destruct t0. destruct_typeOf_chain H0.
      destruct (gen t0) eqn:Heq4; inversion H. subst.
      simpl. erewrite IHe1 with (t:=TArrow _ _).
      rewrite Heq2, eqType_refl. reflexivity.
      reflexivity. assumption.
    + destruct_typeOf_chain H0.
      destruct (step e1_1) eqn:Heq6; inversion H3; subst.
      * assert (typeOf Delta (CaseB e e1_2 e1_3) =
                  Some (TArrow t3_1 t)).
        eapply IHe1. reflexivity.
        rewrite Heq1, Heq2, Heq3, eqType_refl. reflexivity.
        destruct_typeOf_chain H1. rewrite Heq5.
        rewrite eqType_refl. reflexivity.
      * destruct e1_1; inversion H3; subst.
        ** simpl. rewrite Heq3, Heq5, eqType_refl.
           reflexivity.
        ** simpl. rewrite Heq2, Heq5, eqType_refl.
           reflexivity.
        ** simpl. destruct_typeOf_chain Heq1.
           rewrite Heq2, Heq3, Heq5, eqType_refl, eqTypeS_refl,
                   eqType_refl. reflexivity.
    + destruct p. destruct_typeOf_chain H0.
      destruct (step e1_1) eqn:Heq6; inversion H3; subst.
      * assert (typeOf Delta (CaseL e e1_2 (Pat n1 t1 n2 n ) e1_3) =
                  Some (TArrow t3_1 t)).
        eapply IHe1. reflexivity.
        rewrite Heq1, Heq2, Heq3, eqTypeS_refl, eqTypeS_refl.
        reflexivity. destruct_typeOf_chain H1.
        rewrite Heq5, eqTypeS_refl, eqTypeS_refl, eqType_refl.
        reflexivity.
      * destruct e1_1; inversion H3; subst.
        **  simpl. rewrite Heq2, Heq5, eqType_refl.
            reflexivity.
        **  destruct (anyIn (freeVars e1_1_1 ++ freeVars e1_1_2)
                          (n1 :: n2 :: boundVars e1_3)) eqn:Heq9;
            try discriminate.
            destruct (anyIn (freeVars e1_1_2)
                            (boundVars e1_1_1)) eqn:Heq10;
            try discriminate. inversion H3. subst.
            apply anyIn_concat2 in Heq9. destruct Heq9 as [Heq9 HFA].
            destruct_typeOf_chain Heq1.
            simpl. erewrite subst_preservation2
              with (t := TArrow _ _).
            rewrite Heq5, eqType_refl. reflexivity.
            assumption. assumption. assumption.
            symmetry. assumption.
            rewrite double_update_indep. eassumption.
            assumption. assumption. assumption.
        **  simpl. destruct_typeOf_chain Heq1.
            rewrite Heq2, Heq3, Heq5, eqTypeS_refl, eqTypeS_refl,
              eqTypeS_refl, eqType_refl. reflexivity.
  - destruct_typeOf_chain H0.
    destruct (step e1) eqn:HeqS1.
    + inversion H2. subst. simpl.
      erewrite IHe1. erewrite Heq0. rewrite eqTypeS_refl.
      reflexivity. reflexivity. assumption.
    + destruct (step e2) eqn:HeqS2.
      * inversion H2. subst. simpl.
        erewrite (IHe2 e). erewrite Heq1. rewrite eqTypeS_refl.
        reflexivity. reflexivity. assumption.
      * inversion H2.
  - destruct t. destruct_typeOf_chain H0.
    destruct (gen t) eqn:Heq2; inversion H2; subst.
    eapply subst_preservation; eauto.
    erewrite freeVars_gen; eauto.
    eapply typeOf_gen. eauto.
  - destruct_typeOf_chain H0.
    destruct (step e1) eqn:HeqS1.
    + inversion H2. subst. simpl.
      erewrite IHe1 with (t:=TBool).
      rewrite Heq2, Heq3, eqType_refl. reflexivity.
      reflexivity. assumption.
    + destruct e1; inversion H2; subst; try assumption.
      simpl. destruct_typeOf_chain Heq1.
      rewrite Heq2, Heq3, eqTypeS_refl, eqType_refl.
      reflexivity.
  - destruct p. destruct_typeOf_chain H0.
    destruct (step e1) eqn:HeqS1.
    + inversion H2. subst. simpl.
      erewrite IHe1 with (t := TList _).
      rewrite eqTypeS_refl, Heq2, Heq3, eqTypeS_refl. reflexivity.
      reflexivity. assumption.
    + destruct e1; inversion H2; subst; try assumption.
      ++  destruct (anyIn (freeVars e1_1 ++ freeVars e1_2)
                      (n1 :: n2 :: boundVars e3)) eqn:Heq5;
          try discriminate;
          destruct (anyIn (freeVars e1_2) (boundVars e1_1)) eqn:Heq6;
          try inversion H2; subst.
          apply anyIn_concat2 in Heq5. destruct Heq5 as [Heq5 HFA].
          destruct_typeOf_chain Heq1.
          rewrite double_update_indep in Heq3; eauto.
          eapply subst_preservation2; eauto.
      ++  destruct_typeOf_chain Heq1.
          rewrite eqTypeS_refl, eqTypeS_refl,
                  Heq2, Heq3, eqTypeS_refl. reflexivity.
  Qed.

  Lemma well_typed_step :
    forall Delta e e',
    well_typed Delta e ->
    e ==> e' ->
    well_typed Delta e'.
  Proof.
    intros Delta e e' Hwt Hstep.
    inversion Hstep. subst.
    destruct_typeOf_chain Hwt.
    erewrite step_preservation.
    reflexivity. apply H. apply Heq1.
  Qed.

  Theorem well_typed_multi_step :
    forall Delta e e',
    well_typed Delta e ->
    e ==>* e' ->
    well_typed Delta e'.
  Proof.
    intros Delta e e' Hwt Hstep.
    induction Hstep; auto.
    apply IHHstep. apply well_typed_step with (e := e1).
    apply Hwt. apply H.
  Qed.

End PreservationTTypes.

Section Proofs.

  Hint Resolve more_specific_Any compatible_Any Single_Step
               more_specific_refl : core.

  Lemma compatibility:
    forall e Delta Gamma t d,
    compatibleCtx Gamma Delta ->
    typeOf Delta e = Some t ->
    Gamma |- e :? d ->
    compatible d t.
  Proof.
    induction e; intros.
    - inversion H1; inversion H0; subst.
      unfold compatibleCtx in *. apply H.
    - inversion H1. inversion H0. reflexivity.
    - inversion H1. inversion H0. reflexivity.
    - inversion H1. inversion H0. reflexivity.
    - inversion H1. subst. destruct_typeOf_chain H0.
      destruct d1, d2; try reflexivity; subst d3.
      + destruct (more_specific Det Det && more_specific (Arrow d2_1 d2_2) Det); reflexivity.
      + destruct (more_specific (Arrow d1_1 d1_2) Det && more_specific Det Det); reflexivity.
      + destruct (more_specific (Arrow d1_1 d1_2) Det && more_specific Any Det); reflexivity.
      + destruct (more_specific (Arrow d1_1 d1_2) Det && more_specific (Arrow d2_1 d2_2) Det); reflexivity.
    - inversion H1; subst.
      + reflexivity.
      + unfold decide.
        destruct (more_specific d0 Det); reflexivity.
      + destruct_typeOf_chain H0.
        unfold decide in H1. unfold decide.
        destruct (more_specific d3 d1).
        * eapply IHe1 with (t:=TArrow _ _) in H4.
          destruct H4. eassumption.
          eassumption. apply Heq1.
        * reflexivity.
    - inversion H1. subst.
      destruct_typeOf_chain H0.
      split. assumption. eapply IHe.
      apply update_compatible; try eassumption.
      eassumption. eassumption.
    - inversion H1. reflexivity.
    - inversion H1; subst.
      destruct_typeOf_chain H0. destruct t.
      eapply IHe in H7; try eassumption.
      apply update_compatible; eauto.
    - inversion H1; subst.
      destruct_typeOf_chain H0.
      eapply (IHe1 _ _ _ _ H Heq1) in H6.
      eapply (IHe2 _ _ _ _ H Heq2) in H8.
      eapply (IHe3 _ _ _ _ H Heq3) in H9.
      apply compatible_lub; assumption.
    - inversion H1; subst.
      destruct_typeOf_chain H0.
      eapply (IHe1 _ _ _ _ H Heq1) in H7.
      eapply (IHe2 _ _ _ _ H Heq2) in H12.
      eapply (IHe3               ) in H13.
      apply compatible_lub; try assumption.
      destruct d_1; try assumption.
      apply H13. subst Gamma'. subst Gamma''.
      destruct (n1 =? n2) eqn:HeqN1.
      + apply Nat.eqb_eq in HeqN1. subst.
        contradiction.
      + apply Nat.eqb_neq in HeqN1.
        rewrite double_update_indep; eauto.
        apply update_compatible; eauto.
        apply update_compatible; eauto.
      + assumption.
  Qed.

  (* Theorem completeness:
    Shows that any well-typed expression in the Curry type system
    can be assigned a determinism type. This establishes that
    determinism typing covers all valid programs. *)
  Theorem completeness :
    forall e Delta Gamma t,
    compatibleCtx Gamma Delta ->
    typeOf Delta e = Some t ->
    exists d, Gamma |- e :? d /\ compatible d t.
  Proof.
    intro e.
    induction e; intros Delta Gamma t0 HG HW.
    * eapply (compatibility _ _ _ _ _ HG) in HW.
      unfold compatibleCtx in HG.
      exists (Gamma n). split. apply Rule_Var.
      reflexivity. apply HW. apply Rule_Var. reflexivity.
    * exists Det. split. apply Rule_BTrue.
      simpl in HW. inversion HW. reflexivity.
    * exists Det. split. apply Rule_BFalse.
      simpl in HW. inversion HW. reflexivity.
    * exists Det. split. apply Rule_Nil.
      simpl in HW. inversion HW. reflexivity.
    * destruct_typeOf_chain HW.
      destruct (IHe1 Delta Gamma t2 HG Heq2), H,
               (IHe2 Delta Gamma _ HG Heq1), H1.
      eexists. split.
      eapply Rule_Cons; try eassumption; try reflexivity.
      destruct (more_specific x Det && more_specific x0 Det); reflexivity.
    * destruct_typeOf_chain HW.
      destruct (IHe1 Delta Gamma (TArrow t1_1 t0) HG Heq1), H,
               (IHe2 Delta Gamma t1_1 HG Heq2), H1, x.
      - exists (decide Det x0 Det). split. apply Rule_AppDet.
        apply H. apply H1. unfold decide.
        destruct (more_specific x0 Det) eqn:Heq4; reflexivity.
      - exists Any. split. eapply Rule_AppAny.
        apply H. apply H1. reflexivity.
      - eexists. split. eapply Rule_AppFun.
        apply H. apply H1.
        reflexivity. destruct H0.
        unfold decide. destruct (more_specific x0 x1) eqn:Heq4.
        assumption. reflexivity.
    * destruct_typeOf_chain HW.
      edestruct (IHe (update Nat.eqb Delta n t)
                     (update Nat.eqb Gamma n (mkCompatible t))).
      unfold compatibleCtx in *. intros n0.
      unfold update. destruct (n =? n0) eqn:Heq2.
      apply mkCompatible_compatible. apply HG.
      apply Heq1. destruct H.
      eexists. split. apply Rule_Abs.
      apply mkCompatible_compatible. apply H.
      simpl. split.
      apply mkCompatible_compatible. apply H0.
    * destruct_typeOf_chain HW.
      destruct (IHe1 Delta Gamma t0 HG Heq1), H,
               (IHe2 Delta Gamma t0 HG Heq0), H1.
      exists Any. split. eapply Rule_Choice. apply H. apply H1.
      reflexivity.
    * destruct_typeOf_chain HW. destruct t.
      edestruct IHe.
      apply update_compatible. eassumption.
      apply compatible_Any. apply HW. destruct H.
      exists x. intuition. eapply Rule_Free. eauto.
    * destruct_typeOf_chain HW.
      destruct (IHe1 _ _ _ HG Heq1), H,
               (IHe2 _ _ _ HG Heq2), H1,
               (IHe3 _ _ _ HG Heq3), H3.
      exists (lub x x0 x1). split.
      eapply Rule_CaseBool; try eassumption.
      apply compatible_lub; try assumption.
    * destruct p. destruct_typeOf_chain HW.
      destruct (IHe1 _ _ _ HG Heq1), H,
               (IHe2 _ _ _ HG Heq2), H1.
      eapply IHe3 in Heq3. destruct Heq3, H3.
      exists (lub x x0 x1). split.
      eapply Rule_CaseList with (d1 := Any);
      try eassumption. reflexivity.
      apply more_specific_Any.
      apply compatible_lub; try assumption.
      destruct x; inversion H0; reflexivity.
      rewrite double_update_indep; trivial.
      apply update_compatible; trivial.
      apply update_compatible; trivial.
  Qed.

  Lemma hasDType_unbound : forall e Gamma d1 d2 n,
    Gamma |- e :? d1 ->
    anyIn (freeVars e) [n] = false ->
    update Nat.eqb Gamma n d2 |- e :? d1.
  Proof.
    fix hasDType_unbound 1.
    induction e; intros.
    - simpl in *. destruct (n0 =? n) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst. rewrite Nat.eqb_refl in H0.
        inversion H0.
      + subst. apply Rule_Var. unfold update. rewrite Heq.
        inversion H. assumption.
    - inversion H. subst. simpl in *.
      apply Rule_BTrue.
    - inversion H. subst. simpl in *.
      apply Rule_BFalse.
    - inversion H. subst. simpl in *.
      apply Rule_Nil.
    - inversion H. subst. simpl in *.
      apply anyIn_cons in H0. destruct H0 as [HH1 HH2].
      apply anyIn_concat2 in HH1. destruct HH1 as [HH3 HH4].
      apply anyIn_concat2 in HH2. destruct HH2 as [HH5 HH6].
      subst d4. eapply Rule_Cons;
      try apply (IHe1 Gamma _ _ n); try eassumption;
      try apply (IHe2 Gamma _ _ n); try eassumption;
      try reflexivity.
    - unfold freeVars in H0. fold freeVars in H0.
      apply anyIn_concat2 in H0. destruct H0 as [H0_1 H0_2].
      inversion H; subst; simpl in *.
      + eapply IHe1 in H3; eauto. eapply IHe2 in H5; eauto.
        eapply Rule_AppAny; eauto.
      + eapply IHe1 in H3; eauto. eapply IHe2 in H5; eauto.
        eapply Rule_AppDet; eauto.
      + eapply IHe1 in H2; eauto. eapply IHe2 in H4; eauto.
        eapply Rule_AppFun; eauto.
    - inversion H. subst. simpl in *.
      destruct (n0 =? n) eqn:Heq.
      + rewrite Nat.eqb_eq in Heq. subst.
        eapply Rule_Abs. assumption.
        rewrite double_update. eassumption.
      + apply Nat.eqb_neq in Heq. eapply IHe in H7.
        eapply Rule_Abs. assumption.
        rewrite double_update_indep; eassumption.
        apply anyIn_removeb in H0; auto.
    - inversion H. subst. simpl in *.
      apply anyIn_concat2 in H0. destruct H0 as [HH1 HH2].
      eapply IHe1 in H4. eapply IHe2 in H6.
      eapply Rule_Choice. eassumption. eassumption.
      assumption. assumption.
    - inversion H. subst. simpl in *.
      destruct (n0 =? n) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst.
        eapply Rule_Free. rewrite double_update. eassumption.
      + apply Nat.eqb_neq in Heq.
        eapply IHe in H6. eapply Rule_Free.
        rewrite double_update_indep; eassumption.
        apply anyIn_removeb in H0; auto.
    - inversion H. subst. simpl in *.
      apply anyIn_concat2 in H0.
      destruct H0 as [HH1 HH2].
      apply anyIn_concat2 in HH2.
      destruct HH2 as [HH3 HH4].
      apply Rule_CaseBool.
      apply IHe1; assumption.
      apply IHe2; assumption.
      apply IHe3; assumption.
    - inversion H. subst. simpl in *.
      apply anyIn_concat2 in H0.
      destruct H0 as [HH1 HH2].
      apply anyIn_concat2 in HH2.
      destruct HH2 as [HH3 HH4].
      eapply Rule_CaseList.
      apply IHe1; assumption. apply H7. apply H9.
      apply IHe2; assumption.
      destruct (n =? n2) eqn:HeqN2,
               (n =? n1) eqn:HeqN1.
      + apply Nat.eqb_eq in HeqN2.
        apply Nat.eqb_eq in HeqN1. subst.
        rewrite double_update.
        rewrite double_update.
        subst Gamma'. subst Gamma''.
        rewrite double_update in H12.
        assumption.
      + apply Nat.eqb_eq in HeqN2.
        apply Nat.eqb_neq in HeqN1. subst.
        rewrite double_update_indep; eauto.
        rewrite double_update; eauto.
        subst Gamma'. subst Gamma''.
        rewrite double_update_indep in H12; eauto.
      + apply Nat.eqb_neq in HeqN2.
        apply Nat.eqb_eq in HeqN1. subst.
        rewrite double_update; eauto.
      + apply Nat.eqb_neq in HeqN2.
        apply Nat.eqb_neq in HeqN1. subst.
        rewrite (double_update_indep _ n _ n1); auto.
        rewrite (double_update_indep _ n _ n2); auto.
        subst Gamma'. subst Gamma''.
        apply anyIn_removeb in HH4; auto.
        apply anyIn_removeb in HH4; auto.
      + assumption.
  Qed.

  (* Lemma subst_lemma:
   A key substitution lemma showing that if a well-typed expression e1 has a
   determinism type d2, and we substitute a well-typed expression e2 with
   compatible determinism type, then the result maintains a determinism type
   that is at least as specific as the original. *)
  Lemma subst_lemma : forall e1 e2 Delta Gamma t2 d2 d1 d3 n,
    anyIn (freeVars e2) (n::boundVars e1) = false ->
    well_typed (update Nat.eqb Delta n t2) e1 ->
    typeOf Delta e2 = Some t2 ->
    compatibleCtx Gamma Delta ->
    compatible d2 t2 ->
    update Nat.eqb Gamma n d2 |- e1 :? d1 ->
    more_specific d3 d2 = true ->
    Gamma |- e2 :? d3 ->
    exists d4,
      more_specific d4 d1 = true /\
      Gamma |- subst n e2 e1 :? d4.
  Proof.
    induction e1; intro;
    intros Delta Gamma t2 d2 d1 d3 n0 H H0 H1 H3 H4; intros.
    - inversion H2. subst. simpl.
      unfold update. destruct (n =? n0) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst.
        rewrite Nat.eqb_refl in *.
        exists d3. split. assumption. assumption.
      + rewrite Nat.eqb_sym in Heq. rewrite Heq in *.
        exists (update Nat.eqb Gamma n0 d2 n).
        unfold update. rewrite Heq. split.
        apply more_specific_refl.
        apply Rule_Var. reflexivity.
    - inversion H2. subst. simpl in *.
      exists Det. intuition. apply Rule_BTrue.
    - inversion H2. subst. simpl in *.
      exists Det. intuition. apply Rule_BFalse.
    - inversion H2. subst. simpl in *.
      exists Det. intuition. apply Rule_Nil.
    - inversion H2. subst. simpl in *.
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_concat1 in HH1. destruct HH1 as [HH3 HH4].
      apply well_typed_subterms in H0. destruct H0 as [H0_1 H0_2].
      edestruct IHe1_1 in H10; try eassumption.
      apply anyIn_cons. split; eassumption.
      edestruct IHe1_2 in H12; try eassumption.
      apply anyIn_cons. split; eassumption.
      destruct H, H0. eexists. split.
      shelve. eapply Rule_Cons; eauto.
      Unshelve. subst d5.
      destruct (more_specific x Det) eqn:Heq1, (more_specific x0 Det) eqn:Heq2,
               (more_specific d0 Det) eqn:Heq3, (more_specific d4 Det) eqn:Heq4;
      try reflexivity; try apply more_specific_Any; simpl.
      + rewrite (more_specific_transitive x0 d4 Det) in Heq2;
        try assumption. inversion Heq2.
      + rewrite (more_specific_transitive x d0 Det) in Heq1;
        try assumption. inversion Heq1.
      + rewrite (more_specific_transitive x0 d4 Det) in Heq2;
        try assumption. inversion Heq2.
    - apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_subterm in HH1. destruct HH1 as [HH3 HH4].
      destruct_typeOf_chain H0.
      inversion H2; subst.
      + edestruct IHe1_1 in H6; try apply anyIn_cons;
        try split; try eassumption.
        unfold well_typed. rewrite Heq1. reflexivity.
        edestruct IHe1_2 in H6; try apply anyIn_cons;
        try split; try eassumption.
        unfold well_typed. rewrite Heq2. reflexivity.
        destruct H, H7, x; simpl.
        * eexists. split. apply more_specific_Any.
          eapply Rule_AppDet. apply H8. apply H10.
        * eexists. split. apply more_specific_Any.
          eapply Rule_AppAny. apply H8. apply H10.
        * eexists. split. apply more_specific_Any.
          eapply Rule_AppFun. apply H8. apply H10.
          reflexivity.
      + edestruct IHe1_1 in H6; try apply anyIn_cons;
        try split; try eassumption.
        unfold well_typed. rewrite Heq1. reflexivity.
        edestruct IHe1_2 in H6; try apply anyIn_cons;
        try split; try eassumption.
        unfold well_typed. rewrite Heq2. reflexivity.
        destruct H, H7, x.
        * exists (decide Det x0 Det). split.
          unfold decide.
          destruct (more_specific d  Det) eqn:Heq4,
                   (more_specific x0 Det) eqn:Heq5.
          --  reflexivity.
          --  eapply more_specific_transitive
                with (d2:=d) (d3 := Det) in H7.
              rewrite H7 in Heq5. inversion Heq5.
              assumption.
          --  apply more_specific_Any.
          -- reflexivity.
          -- eapply Rule_AppDet; eassumption.
        * inversion H.
        * eexists (decide x1 x0 x2). split.
          unfold decide. rewrite unfold_more_specific in H.
          rewrite andb_true_iff in H. destruct H.
          destruct (more_specific x0 x1) eqn:Heq4,
                   (more_specific d Det) eqn:Heq5.
          --  assumption.
          --  reflexivity.
          --  apply (more_specific_transitive x0 d Det) in Heq5; try assumption.
              rewrite (more_specific_transitive x0 Det x1) in Heq4; try assumption.
              inversion Heq4.
          --  reflexivity.
          --  eapply Rule_AppFun. apply H8. apply H10. reflexivity.
      + edestruct IHe1_1 in H5;
        try apply anyIn_cons;
        try split; try eassumption.
        unfold well_typed. rewrite Heq1. reflexivity.
        edestruct IHe1_2 in H8; try apply anyIn_cons; try split; try eassumption.
        unfold well_typed. rewrite Heq2. reflexivity.
        destruct H, H7, x; simpl.
        * eexists. split. shelve.
          eapply Rule_AppDet; eassumption.
          Unshelve. unfold decide.
          rewrite unfold_more_specific in H.
          rewrite andb_true_iff in H. destruct H.
          destruct (more_specific x0 Det) eqn:Heq4,
                   (more_specific d5 d0) eqn:Heq5.
          --  assumption.
          --  reflexivity.
          --  apply (more_specific_transitive x0 d5 d0) in Heq5; try assumption.
              rewrite (more_specific_transitive x0 d0 Det) in Heq4; try assumption.
              inversion Heq4.
          --  reflexivity.
        * inversion H.
        * eexists. split. shelve.
          eapply Rule_AppFun. apply H9. apply H11. reflexivity.
          Unshelve. rewrite unfold_more_specific in H. apply andb_true_iff in H.
          destruct H. unfold decide.
          destruct (more_specific d5 d0) eqn:Heq4;
          try apply more_specific_Any.
          eapply (more_specific_transitive d5 d0 x1) in Heq4.
          eapply (more_specific_transitive x0 d5 x1) in Heq4.
          rewrite Heq4. assumption. assumption. assumption.
    - inversion H2. subst.
      apply well_typed_subterms in H0.
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_subterm in HH1. destruct HH1 as [HH3 HH4].
      destruct (n0 =? n) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst.
        eexists. simpl. rewrite Nat.eqb_refl.
        split. shelve. eapply Rule_Abs. apply H12.
        subst Gamma'. rewrite double_update in H13. apply H13.
        Unshelve. rewrite unfold_more_specific.
        rewrite more_specific_refl.
        rewrite more_specific_refl. reflexivity.
      + apply Nat.eqb_neq in Heq. subst Gamma'.
        rewrite double_update_indep in H0; try assumption.
        rewrite double_update_indep in H13; try assumption.
        edestruct IHe1 in H13; try eassumption.
        apply anyIn_cons. split; eassumption.
        erewrite typeOf_unbound; eassumption.
        apply update_compatible; assumption.
        apply hasDType_unbound; assumption.
        destruct H. eexists. split. shelve. simpl.
        apply Nat.eqb_neq in Heq. rewrite Nat.eqb_sym in Heq.
        rewrite Heq. eapply Rule_Abs; eassumption. Unshelve.
        rewrite unfold_more_specific.
        rewrite more_specific_refl.
        rewrite H. reflexivity.
    - inversion H2. subst.
      apply well_typed_subterms in H0. destruct H0 as [H0_1 H0_2].
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_concat1 in HH1. destruct HH1 as [HH3 HH4].
      edestruct IHe1_1 in H10; try eassumption.
      apply anyIn_cons. split; eassumption.
      edestruct IHe1_2 in H10; try eassumption.
      apply anyIn_cons. split; eassumption.
      destruct H, H0.
      exists Any. split. apply more_specific_Any.
      simpl. eapply Rule_Choice; eassumption.
    - inversion H2. destruct t. subst. simpl in *.
      apply well_typed_subterms in H0.
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_cons in HH1. destruct HH1 as [HH3 HH4].
      destruct (n =? n0) eqn:HeqN1.
      + apply Nat.eqb_eq in HeqN1. subst Gamma'. subst n0.
        rewrite double_update in H0.
        rewrite double_update in H12.
        exists d1. split. apply more_specific_refl.
        eapply Rule_Free; eassumption.
      + apply Nat.eqb_neq in HeqN1. subst Gamma'.
        rewrite double_update_indep in H0; try eauto.
        rewrite double_update_indep in H12; try eauto.
        edestruct IHe1 in H12; try eassumption.
        apply anyIn_cons. split; eassumption.
        erewrite typeOf_unbound; eassumption.
        apply update_compatible; eauto.
        apply hasDType_unbound; assumption.
        destruct H. exists x. intuition.
        simpl. eapply Rule_Free; eassumption.
    - inversion H2. subst.
      remember H0 as HC. clear HeqHC.
      apply well_typed_subterms in H0.
      destruct H0 as [H0_1 [H0_2 H0_3]].
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_subterm in HH1.
      destruct HH1 as [HH3 [HH4 HH5]].
      edestruct IHe1_1 in H0_1; try eassumption.
      apply anyIn_cons. split; eassumption.
      edestruct IHe1_2 in H0_2; try eassumption.
      apply anyIn_cons. split; eassumption.
      edestruct IHe1_3 in H0_3; try eassumption.
      apply anyIn_cons. split; eassumption.
      destruct H, H0, H7.
      exists (lub x x0 x1). split.
      * destruct_typeOf_chain HC.
        apply more_specific_lub; try assumption.
        remember Heq1 as Heq1C. clear HeqHeq1C.
        specialize (update_compatible _ _ n0 _ _ H3 H4) as Hupd.
        eapply (compatibility _ _ _ _ _ Hupd Heq1) in H11.
        eapply (subst_preservation _ e1_1 e2 n0 TBool) in H1.
        eapply compatibility with (d := x) in H1; eassumption.
        apply anyIn_cons. split; assumption. assumption.
      * simpl. apply Rule_CaseBool; assumption.
    - inversion H2. subst.
      remember H0 as HC. clear HeqHC.
      apply well_typed_subterms in H0.
      destruct H0 as [H0_1 [H0_2 H0_3]].
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_subterm in HH1.
      destruct HH1 as [HH3 [HH4 HH5]].
      apply anyIn_cons in HH5.
      destruct HH5 as [HH6 HH7].
      apply anyIn_cons in HH6.
      destruct HH6 as [HH8 HH9].
      destruct_typeOf_chain HC.
      edestruct IHe1_1 with (e2:=e2) in H0_1; eauto.
      apply anyIn_cons. intuition. rewrite Heq1. reflexivity.
      edestruct IHe1_2 with (e2:=e2) in H0_2; eauto.
      apply anyIn_cons. intuition. rewrite Heq2. reflexivity.
      destruct H, H0, (n0 =? n1) eqn:HeqN1,
                      (n0 =? n2) eqn:HeqN2.
      + rewrite Nat.eqb_eq in HeqN1. subst n1.
        rewrite Nat.eqb_eq in HeqN2. subst n2.
        contradiction.
      + rewrite Nat.eqb_eq in HeqN1. subst n1.
        rewrite Nat.eqb_neq in HeqN2.
        rewrite double_update_indep in Heq3;
        try symmetry; try assumption.
        rewrite double_update in Heq3.
        rewrite double_update_indep in Heq3;
        try assumption.
        subst Gamma'. subst Gamma''. subst Gamma'0.
        rewrite double_update in H18.
        rewrite double_update_indep in H18;
        try assumption.
        unfold well_typed in IHe1_3.
        eexists (lub x x0 d_3). split.
        --  apply more_specific_lub; try assumption.
            eapply compatibility in H8. shelve.
            eassumption.
            eapply subst_preservation.
            apply anyIn_cons. split; assumption.
            apply Heq1. apply H1.
            apply more_specific_refl.
            Unshelve. destruct x;
            try reflexivity; try inversion H8.
        --  simpl. eapply Rule_CaseList; try eassumption.
            rewrite double_update_indep; try eassumption.
            eapply more_specific_transitive; eassumption.
      + rewrite Nat.eqb_neq in HeqN1.
        rewrite Nat.eqb_eq in HeqN2. subst n2.
        subst Gamma'. subst Gamma''. subst Gamma'0.
        rewrite double_update in Heq3.
        rewrite double_update_indep in Heq3;
        try symmetry; try assumption.
        rewrite double_update_indep in H18;
        try symmetry; try assumption.
        rewrite double_update in H18.
        unfold well_typed in IHe1_3.
        eexists (lub x x0 d_3). split.
        --  apply more_specific_lub; try assumption.
            eapply compatibility in H8. shelve.
            eassumption.
            eapply subst_preservation.
            apply anyIn_cons. split; assumption.
            apply Heq1. apply H1.
            apply more_specific_refl.
            Unshelve. destruct x;
            try reflexivity; try inversion H8.
        --  eapply Rule_CaseList; try eassumption.
            rewrite double_update_indep; try eassumption.
            eapply more_specific_transitive; eassumption.
      + rewrite Nat.eqb_neq in HeqN1.
        rewrite Nat.eqb_neq in HeqN2.
        rewrite (double_update_indep _ n0 _ n2 _ HeqN2) in Heq3.
        rewrite (double_update_indep _ n0 _ n1 _ HeqN1) in Heq3.
        subst Gamma'. subst Gamma''. subst Gamma'0.
        rewrite (double_update_indep _ n0 _ n1 _ HeqN1) in H18.
        rewrite (double_update_indep _ n0 _ n2 _ HeqN2) in H18.
        edestruct IHe1_3 in H0_3.
        apply anyIn_cons. split; try eassumption.
        unfold well_typed. rewrite Heq3.
        reflexivity. erewrite typeOf_unbound; eauto.
        erewrite typeOf_unbound; eauto.
        erewrite typeOf_unbound; eauto.
        erewrite double_update_indep; eauto.
        apply update_compatible; try eassumption.
        apply update_compatible; try eassumption.
        eassumption. eassumption. eassumption.
        apply hasDType_unbound; eauto.
        apply hasDType_unbound; eauto.
        destruct H10. exists (lub x x0 x1). split.
        * apply more_specific_lub; try assumption.
          remember Heq1 as Heq1C. clear HeqHeq1C.
          eapply compatibility in Heq1; eauto.
          eapply compatibility with (t:=TList _) in H8; eauto.
          destruct x; try reflexivity; try inversion H8.
          eapply subst_preservation; eauto.
          apply anyIn_cons. split; assumption.
          apply update_compatible; eassumption.
        * simpl. eapply Rule_CaseList; try eassumption.
          eapply more_specific_transitive; eassumption.
  Qed.

  (* Lemma subst_lemma2:
   A more complex substitution lemma that handles cases
   with two nested substitutions.
   It ensures that the determinism type
   of the resulting expression is still well-typed
   and maintains the required properties.

   While it looks more complex, it essentially just requires
   the same properties as subst_lemma, but for
   two expressions and their respective types.
   Thus, most of the properties are essentially duplicated.
   *)

  Lemma subst_lemma2 :
    forall e1 e2 e3 Delta Gamma t2 t3 d1 d2 d3 n2 n3 d2' d3',
    anyIn (freeVars e2) (n3::n2::boundVars e1) = false ->
    anyIn (freeVars e3) (n3::n2::boundVars e1) = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    well_typed (update Nat.eqb (update Nat.eqb Delta n3 t3) n2 t2) e1 ->
    typeOf Delta e2 = Some t2 ->
    typeOf Delta e3 = Some t3 ->
    n2 <> n3 ->
    compatibleCtx Gamma Delta ->
    compatible d2 t2 ->
    compatible d3 t3 ->
    update Nat.eqb (update Nat.eqb Gamma n3 d3) n2 d2 |- e1 :? d1 ->
    more_specific d2' d2 = true ->
    more_specific d3' d3 = true ->
    Gamma |- e2 :? d2' ->
    Gamma |- e3 :? d3' ->
    exists d4,
      more_specific d4 d1 = true /\
      Gamma |- subst n2 e2 (subst n3 e3 e1) :? d4.
  Proof.
    intros.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H0. destruct H0.
    apply anyIn_cons in H0. destruct H0.
    destruct_typeOf_chain H2.
    edestruct subst_lemma with (e1 := e1) (e2 := e3) (n := n3).
    + apply anyIn_cons. split; assumption.
    + unfold well_typed.
      rewrite double_update_indep in Heq1; eauto.
      rewrite Heq1. reflexivity.
    + erewrite typeOf_unbound; eauto.
    + eapply (update_compatible _ Delta); eauto.
    + eassumption.
    + rewrite double_update_indep in H9; eauto.
    + eassumption.
    + apply hasDType_unbound; assumption.
    + destruct H18.
      edestruct subst_lemma with (e2 := e2) (n := n2); eauto.
      - apply anyIn_cons; intuition. apply anyIn_subst; eauto.
      - unfold well_typed.
        erewrite subst_preservation; eauto.
        apply anyIn_cons; intuition.
        rewrite double_update_indep; eauto.
        erewrite typeOf_unbound; eassumption.
      - destruct H20. exists x0. intuition.
        eapply more_specific_transitive; eassumption.
  Qed.

  (* Theorem preservation:
   Shows that if an expression e reduces to e', then the determinism type
   of e' is at least as specific as the determinism type of e.
   This is the core type safety property for the determinism type system. *)
  Theorem preservation : forall e e' Delta Gamma t d,
    compatibleCtx Gamma Delta ->
    e ==> e' ->
    typeOf Delta e = Some t ->
    compatible d t ->
    Gamma |- e :? d ->
    exists d', more_specific d' d = true /\ compatible d' t
      /\ Gamma |- e' :? d'.
  Proof.
    induction e; intros e' Delta Gamma t0 d0 HX H HW HC H0;
    inversion H; inversion H1; subst.
    * inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct (step e1) eqn:Heq.
      + inversion H5. subst.
        edestruct IHe1; try eassumption.
        apply Single_Step. apply Heq.
        eapply compatibility; eassumption.
        destruct H2, H3.
        eexists. split. shelve. split. shelve.
        eapply Rule_Cons; eauto. Unshelve. subst d3.
        - destruct (more_specific x  Det) eqn:Heq4,
                   (more_specific d2 Det) eqn:Heq5,
                   (more_specific d1 Det) eqn:Heq6;
          try reflexivity; try apply more_specific_Any; simpl.
          rewrite (more_specific_transitive x d1 Det) in Heq4; try assumption.
          inversion Heq4.
        - destruct (more_specific x  Det) eqn:Heq4,
                   (more_specific d2 Det) eqn:Heq5;
          reflexivity.
      + destruct (step e2) eqn:Heq4; inversion H5.
        subst. edestruct IHe2. try eassumption.
        apply Single_Step. apply Heq4. eassumption.
        eapply compatibility; eassumption.
        assumption. destruct H2, H3.
        eexists. split. shelve. split. shelve.
        eapply Rule_Cons; eauto. Unshelve. subst d3.
        - destruct (more_specific x  Det) eqn:Heq5,
                   (more_specific d2 Det) eqn:Heq6,
                   (more_specific d1 Det) eqn:Heq7;
          try reflexivity; try apply more_specific_Any; simpl.
          rewrite (more_specific_transitive x d2 Det) in Heq5; try assumption.
          inversion Heq5.
        - destruct (more_specific x  Det) eqn:Heq5,
                   (more_specific d1 Det) eqn:Heq6;
          reflexivity.
    * remember H1 as H1C. clear HeqH1C.
      destruct_typeOf_chain HW.
      destruct e1 eqn:Heq5; inversion H5; subst.
      + destruct_typeOf_chain Heq1.
      (* App App *)
      + destruct (step (App e3 e4)) eqn:Heq;
        inversion H5.
        inversion H0; subst.
        - edestruct IHe1 with (d := Any).
          eassumption.
          apply Single_Step. apply Heq. eassumption.
          reflexivity. assumption. destruct H2, H4, x.
          --  exists (decide Det d Det). split. apply more_specific_Any.
              split. unfold decide.
              destruct (more_specific d Det); reflexivity.
              apply Rule_AppDet; assumption.
          --  exists Any; intuition.
              eapply Rule_AppAny; eassumption.
          --  eexists (decide x1 d x2); intuition.
              unfold decide. destruct (more_specific d x1).
              destruct H4. assumption. reflexivity.
              eapply Rule_AppFun; eauto.
        - edestruct IHe1 with (d := Det); eauto.
          reflexivity. destruct H2, H4, x.
          --  exists (decide Det d Det). split. apply more_specific_refl.
              split. unfold decide. destruct (more_specific d Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  exists Any; auto with *.
          --  rewrite unfold_more_specific in H2.
              apply andb_true_iff in H2. destruct H2.
              destruct H4.
              eexists (decide x1 d x2). split. shelve. split. shelve.
              eapply Rule_AppFun. apply H6. apply H10.
              reflexivity. Unshelve. unfold decide in *.
              destruct (more_specific d x1) eqn:Heq4,
                       (more_specific d Det) eqn:Heq5.
              ++  assumption.
              ++  apply more_specific_Any.
              ++  rewrite (more_specific_transitive d Det x1) in Heq4;
                  try assumption. inversion Heq4.
              ++  reflexivity.
              ++  unfold decide.
                  destruct (more_specific d x1) eqn:Heq4.
                  assumption. reflexivity.
        - edestruct IHe1 with (d := (Arrow d1 d2)); eauto.
          eapply (compatibility (App e3 e4)); eauto.
          destruct H2, H4, x.
          --  rewrite unfold_more_specific in H2.
              apply andb_true_iff in H2. destruct H2.
              eexists (decide Det d3 Det). split.
              unfold decide.
              destruct (more_specific d3 Det) eqn:Heq4,
                       (more_specific d3 d1) eqn:Heq5;
              try reflexivity; try apply more_specific_Any.
              assumption.
              rewrite (more_specific_transitive d3 d1 Det) in Heq4;
              try assumption. inversion Heq4.
              split. unfold decide.
              destruct (more_specific d3 Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  inversion H2.
          --  rewrite unfold_more_specific in H2.
              apply (andb_true_iff) in H2.
              destruct H2, H4.
              eexists (decide x1 d3 x2). split.
              unfold decide.
              destruct (more_specific d3 x1) eqn:Heq4,
                       (more_specific d3 d1) eqn:Heq5;
              try apply more_specific_Any; try assumption.
              rewrite (more_specific_transitive d3 d1 x1) in Heq4; try assumption.
              inversion Heq4. split. unfold decide.
              destruct (more_specific d3 x1). assumption. reflexivity.
              eapply Rule_AppFun; eauto.
      (* App Abs *)
      + destruct_typeOf_chain Heq1.
        destruct (anyIn (freeVars e2) (n :: boundVars e)) eqn:Heq7;
        try discriminate. inversion H5. subst.
        inversion H0.
        - inversion H7.
        - inversion H7.
        - inversion H6; subst. unfold decide in *.
          destruct (more_specific d3 d1) eqn:Heq5.
          --  edestruct subst_lemma; eauto.
              unfold well_typed. rewrite Heq0. reflexivity.
              destruct H2. eexists. split. apply H2.
              split. eapply compatibility; eauto.
              eapply subst_preservation; eassumption.
              eassumption.
          --  edestruct completeness. eassumption.
              eapply subst_preservation; eassumption.
              destruct H2. eexists. split.
              apply more_specific_Any. split; eassumption.
      (* App Or *)
      + destruct d0.
        - inversion H0; inversion H4.
          rewrite H6 in H7. inversion H7.
        - inversion H0.
          --  exists Any. split. apply more_specific_Any.
              split. reflexivity. inversion H5. subst.
              destruct_typeOf_chain Heq1.
              eapply (step_preservation (App (Or e3 e4) e2)
                                        (Or (App e3 e2) (App e4 e2))) in H1C.
              edestruct (completeness (App e3 e2)). eassumption.
              simpl. rewrite Heq0, Heq2, eqType_refl. reflexivity.
              edestruct (completeness (App e4 e2)). eassumption.
              simpl. rewrite Heq4, Heq2, eqType_refl. reflexivity.
              destruct H2, H3.
              eapply Rule_Choice; eassumption.
              simpl. rewrite Heq0, Heq2, Heq4, eqTypeS_refl, eqType_refl.
              reflexivity.
          -- inversion H7.
          -- inversion H4.
        - inversion H0; inversion H4. inversion H7.
      (* App Free *)
      + destruct t, (step (Free n (FO t f) e)) eqn:Heq;
        inversion H5; subst. inversion H0; subst.
        - edestruct IHe1. eassumption. apply Single_Step.
          apply Heq. rewrite Heq1. reflexivity.
          eapply compatibility; eassumption. apply H7.
          destruct H2, H4, x.
          --  exists (decide Det d Det). split.
              apply more_specific_Any. split. unfold decide.
              destruct (more_specific d Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  exists Any; intuition.
              eapply Rule_AppAny; eassumption.
          --  exists (decide x1 d x2). split.
              apply more_specific_Any. split.
              unfold decide. destruct (more_specific d x1).
              destruct H4. assumption. reflexivity.
              eapply Rule_AppFun; eauto.
        - edestruct IHe1. eassumption. apply Single_Step. apply Heq.
          rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H4, x.
          --  exists (decide Det d Det). split.
              apply more_specific_refl. split.
              unfold decide. destruct (more_specific d Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  inversion H2.
          --  rewrite unfold_more_specific in H2.
              apply (andb_true_iff) in H2.
              destruct H2, H4.
              eexists (decide x1 d x2). split. unfold decide.
              destruct (more_specific d x1) eqn:M1,
                       (more_specific d Det) eqn:M2;
              try assumption; try apply more_specific_Any.
              rewrite (more_specific_transitive d Det x1) in M1;
              try assumption. inversion M1.
              split. unfold decide. destruct (more_specific d x1).
              assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
        - edestruct IHe1. eassumption. apply Single_Step. apply Heq.
          rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H4, x.
          --  rewrite unfold_more_specific in H2.
              apply andb_true_iff in H2. destruct H2.
              eexists (decide Det d3 Det). split.
              unfold decide.
              destruct (more_specific d3 Det) eqn:Heq4,
                       (more_specific d3 d1)  eqn:Heq5;
              try reflexivity; try apply more_specific_Any.
              assumption.
              rewrite (more_specific_transitive d3 d1 Det) in Heq4;
              try assumption. inversion Heq4. split. unfold decide.
              destruct (more_specific d3 Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  inversion H2.
          --  rewrite unfold_more_specific in H2.
              apply (andb_true_iff) in H2.
              destruct H2, H4.
              eexists (decide x1 d3 x2). split. unfold decide.
              destruct (more_specific d3 d1) eqn:M1,
                       (more_specific d3 x1) eqn:M2;
              try assumption; try apply more_specific_Any.
              rewrite (more_specific_transitive d3 d1 x1) in M2;
              try assumption. inversion M2.
              split. unfold decide. destruct (more_specific d3 x1).
              assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
      (* App Case *)
      + destruct (step (CaseB e3 e4 e5)) eqn:Heq;
        inversion H5; subst; inversion H0; subst.
        - edestruct IHe1. eassumption. apply Single_Step. apply Heq.
          rewrite Heq1. reflexivity. eapply compatibility; eauto.
          eassumption. destruct H2, H2, H4, x.
          --  exists (decide Det d Det).
              rewrite more_specific_Any, more_specific_Any.
              split. reflexivity. split. unfold decide.
              destruct (more_specific d Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  exists Any; intuition.
              eapply Rule_AppAny; eassumption.
          --  exists (decide x1 d x2). split.
              apply more_specific_Any. split.
              unfold decide. destruct (more_specific d x1).
              destruct H2. assumption. reflexivity.
              eapply Rule_AppFun; eauto.
        - edestruct IHe1. eassumption. apply Single_Step.
          apply Heq. rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H4, x.
          --  exists (decide Det d Det). split. apply more_specific_refl.
              split. unfold decide. destruct (more_specific d Det);
              reflexivity. eapply Rule_AppDet; eassumption.
          --  inversion H2.
          --  rewrite unfold_more_specific in H2.
              apply (andb_true_iff) in H2.
              destruct H2, H4.
              exists (decide x1 d x2). split. unfold decide.
              destruct (more_specific d x1) eqn:M1,
                       (more_specific d Det) eqn:M2;
              try assumption; try apply more_specific_Any.
              rewrite (more_specific_transitive d Det x1) in M1;
              try assumption. inversion M1. split.
              unfold decide. destruct (more_specific d x1); trivial.
              eapply Rule_AppFun; try eassumption. reflexivity.
        - edestruct IHe1. eassumption. apply Single_Step.
          apply Heq. rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H4, x.
          --  rewrite unfold_more_specific in H2.
              apply andb_true_iff in H2. destruct H2.
              exists (decide Det d3 Det).
              split. unfold decide.
              destruct (more_specific d3 Det) eqn:Heq4,
                       (more_specific d3 d1)  eqn:Heq5;
              try reflexivity. assumption.
              rewrite (more_specific_transitive d3 d1 Det) in Heq4;
              try assumption. inversion Heq4. split. unfold decide.
              destruct (more_specific d3 Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  inversion H2.
          --  rewrite unfold_more_specific in H2.
              apply (andb_true_iff) in H2.
              destruct H2, H4.
              exists (decide x1 d3 x2). split. unfold decide.
              destruct (more_specific d3 d1) eqn:M1,
                       (more_specific d3 x1) eqn:M2;
              try assumption; try apply more_specific_Any.
              rewrite (more_specific_transitive d3 d1 x1) in M2;
              try assumption. inversion M2. split.
              unfold decide. destruct (more_specific d3 x1); trivial.
              eapply Rule_AppFun; try eassumption. reflexivity.
      + destruct (step (CaseL e3 e4 p e5)) eqn:Heq;
        inversion H5; subst; inversion H0; subst.
        - edestruct IHe1. eassumption. apply Single_Step. apply Heq.
          rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H4, x.
          --  exists (decide Det d Det). split. apply more_specific_Any.
              split. unfold decide. destruct (more_specific d Det);
              reflexivity. eapply Rule_AppDet; eassumption.
          --  exists Any. split. apply more_specific_Any.
              split. reflexivity.
              eapply Rule_AppAny; eassumption.
          --  exists (decide x1 d x2). split. apply more_specific_Any.
              split. unfold decide. destruct (more_specific d x1).
              destruct H4. assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
        - edestruct IHe1. eassumption. apply Single_Step.
          apply Heq. rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H4, x.
          --  exists (decide Det d Det). split. apply more_specific_refl.
              split. unfold decide. destruct (more_specific d Det);
              reflexivity. eapply Rule_AppDet; eassumption.
          --  inversion H2.
          --  rewrite unfold_more_specific in H2.
              apply (andb_true_iff) in H2.
              destruct H2, H4.
              exists (decide x1 d x2). split. unfold decide.
              destruct (more_specific d x1) eqn:M1,
                       (more_specific d Det) eqn:M2;
              try assumption; try apply more_specific_Any.
              rewrite more_specific_transitive
                with (d1:=d) (d2:=Det) (d3:=x1) in M1;
              try assumption. inversion M1. split. unfold decide.
              destruct (more_specific d x1). assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
        - edestruct IHe1. eassumption. apply Single_Step.
          apply Heq. rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H4, x.
          --  rewrite unfold_more_specific in H2.
              apply andb_true_iff in H2. destruct H2.
              exists (decide Det d3 Det).
              split. unfold decide.
              destruct (more_specific d3 Det) eqn:Heq4,
                       (more_specific d3 d1)  eqn:Heq5;
              try reflexivity. assumption.
              rewrite (more_specific_transitive d3 d1 Det) in Heq4;
              try assumption. inversion Heq4. split. unfold decide.
              destruct (more_specific d3 Det); reflexivity.
              eapply Rule_AppDet; eassumption.
          --  inversion H2.
          --  rewrite unfold_more_specific in H2.
              apply (andb_true_iff) in H2.
              destruct H2, H4.
              exists (decide x1 d3 x2). split. unfold decide.
              destruct (more_specific d3 d1) eqn:M1,
                       (more_specific d3 x1) eqn:M2;
              try assumption; try apply more_specific_Any.
              rewrite (more_specific_transitive d3 d1 x1) in M2;
              try assumption. inversion M2. split. unfold decide.
              destruct (more_specific d3 x1); trivial.
              eapply Rule_AppFun; try eassumption. reflexivity.
    (* Or *)
    * inversion H1. inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct (step e1) eqn:Heq3.
      + inversion H5. subst.
        edestruct IHe1. eassumption. apply Single_Step. eassumption.
        eassumption. eapply (compatibility e1); eassumption.
        eassumption. destruct H2, H4. exists Any; intuition.
        eapply Rule_Choice; eassumption.
      + destruct (step e2) eqn:Heq4; inversion H5. subst.
        edestruct IHe2. eassumption. apply Single_Step. eassumption.
        eassumption. eapply (compatibility e2); eassumption.
        eassumption. destruct H2, H4. exists Any; intuition.
        eapply Rule_Choice; eassumption.
    (* Free *)
    * destruct_typeOf_chain HW.
      destruct t, (gen t) eqn:Heq1; try discriminate.
      specialize (freeVars_gen t e0 Heq1) as HF.
      inversion H5; inversion H0; subst. eapply typeOf_gen in Heq1.
      edestruct (completeness e0); eauto. destruct H2.
      edestruct subst_lemma with (d2:=Any).
      rewrite HF. reflexivity. unfold well_typed.
      rewrite HW. reflexivity. apply Heq1. eassumption. reflexivity.
      eassumption. apply more_specific_Any. eassumption. destruct H4.
      exists x0. intuition.
      eapply subst_preservation with (e2:=e0) in HW; eauto.
      eapply compatibility in HW; eauto.
      rewrite HF. reflexivity.
    (* Case *)
    * inversion H1. inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct (step e1) eqn:Heq5.
      + edestruct IHe1. eassumption. apply Single_Step. eassumption.
        eassumption. eapply (compatibility e1); eassumption.
        eassumption. destruct H2, H4. inversion H1. subst.
        remember H10 as H10C. clear HeqH10C.
        remember H11 as H11C. clear HeqH11C.
        eapply (compatibility e2) in H10C; try eassumption.
        eapply (compatibility e3) in H11C; try eassumption.
        eexists. split. apply more_specific_lub; eauto.
        split. apply compatible_lub; eauto.
        eapply Rule_CaseBool; eassumption.
      + destruct e1; inversion H5; subst.
        ++  eexists. split. apply more_specific_lub_r. split.
            eapply compatibility. apply HX. apply Heq3. eassumption.
            eassumption.
        ++  eexists. split. apply more_specific_lub_l. split.
            eapply compatibility. apply HX. apply Heq2. eassumption.
            eassumption.
        ++  inversion H8. subst. exists Any. split.
            destruct d2, d3; reflexivity.
            split. reflexivity.
            destruct_typeOf_chain Heq1.
            edestruct (completeness (CaseB e1_2 e2 e3)).
            eassumption. simpl.
            rewrite Heq2, Heq3, Heq6, eqType_refl. reflexivity.
            destruct H2. edestruct (completeness (CaseB e1_1 e2 e3)).
            eassumption. simpl.
            rewrite Heq0, Heq2, Heq3, eqType_refl. reflexivity.
            destruct H6. eapply Rule_Choice;
            eapply Rule_CaseBool; eassumption.
    * destruct p. inversion H1. inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct (step e1) eqn:Heq5.
      + edestruct IHe1. eassumption. apply Single_Step. eassumption.
        eassumption. eapply (compatibility e1); eassumption.
        eassumption. destruct H4, H6. inversion H1. subst.
        remember H18 as H18C. clear HeqH18C.
        remember H19 as H19C. clear HeqH19C.
        subst Gamma'. subst Gamma''.
        eapply (compatibility e2) in H18C; try eassumption.
        eapply (compatibility e3) in H19C; try eassumption.
        assert (compatible x TBool).
        destruct x; try reflexivity; try inversion H6.
        eexists. split. apply more_specific_lub with (x1:=x); eauto.
        split. apply compatible_lub; eauto.
        eapply Rule_CaseList with (d1:=d1) (d2:=d2); try eassumption.
        eapply more_specific_transitive; eassumption.
        rewrite double_update_indep; try eassumption.
        apply update_compatible; eauto.
        apply update_compatible; eauto.
      + destruct e1; inversion H5; subst.
        ++  eexists. split. apply more_specific_lub_l. split.
            eapply compatibility. apply HX. apply Heq2. eassumption.
            assumption.
        ++  destruct (anyIn (freeVars e1_1 ++ freeVars e1_2)
                        (n1 :: n2 :: boundVars e3)) eqn:Heq6;
            try discriminate.
            destruct (anyIn (freeVars e1_2)
                        (boundVars e1_1)) eqn:Heq7;
            try discriminate. inversion H3. subst.
            apply anyIn_concat2 in Heq6. destruct Heq6.
            destruct_typeOf_chain Heq1.
            inversion H15. subst. subst Gamma'. subst Gamma''.
            specialize (compatibility _ _ _ _ _ HX Heq9 H12) as H22.
            specialize (compatibility _ _ _ _ _ HX Heq6 H21) as H23.
            specialize (compatibility _ _ _ _ _ HX Heq2 H18) as H24.
            rewrite double_update_indep in Heq3; intuition.
            specialize update_compatible as HX'.
            eapply (compatibility _ _ _ _ _) in H19 as H25; eauto.
            subst d4. subst.
            destruct d3; try inversion H23.
            **  unfold lub. rewrite (unfold_more_specific Det Det).
                rewrite andb_true_r.
                destruct (more_specific d0 Det) eqn:Heq11.
                --- destruct (subst_lemma2 _ _ _ Delta Gamma (TList t1)
                            t1 d_3 d2 d1 _ _ Det d0 H7 H4); eauto.
                    unfold well_typed. rewrite Heq3. reflexivity.
                    destruct d2; try inversion H17.
                    reflexivity. reflexivity.
                    rewrite (unfold_more_specific Det Det) in H20.
                    simpl in H20.
                    eapply more_specific_transitive; eauto.
                    destruct H11. exists x. split.
                    specialize (more_specific_lub2_r d_2 d_3) as HL.
                    apply (more_specific_transitive x d_3 _ H11 HL).
                    split. eapply compatibility. apply HX.
                    eapply subst_preservation2.
                    apply H7. apply H4. assumption. symmetry. assumption.
                    rewrite Heq3. reflexivity. assumption. assumption.
                    assumption. assumption.
                --- edestruct completeness. apply HX.
                    eapply subst_preservation2.
                    apply H7. apply H4. assumption. symmetry. assumption.
                    rewrite Heq3. reflexivity. assumption. assumption.
                    destruct H11. exists x. split.
                    apply more_specific_Any. split. assumption.
                    assumption.
            **  unfold lub. rewrite (unfold_more_specific Any Det).
                rewrite andb_false_r.
                edestruct completeness. apply HX.
                eapply subst_preservation2.
                apply H7. apply H4. assumption. symmetry. assumption.
                rewrite Heq3. reflexivity. assumption. assumption.
                destruct H11. exists x. split.
                apply more_specific_Any. split. assumption.
                assumption.
        ++  inversion H15. subst. exists Any. split.
            destruct d_2, d_3; reflexivity.
            split. reflexivity.
            destruct_typeOf_chain Heq1.
            edestruct (completeness (CaseL e1_2 e2
                        (Pat n1 t1 n2 n) e3)).
            eassumption. simpl.
            rewrite Heq3, Heq7, Heq2, eqTypeS_refl, eqTypeS_refl.
            reflexivity. destruct H4.
            edestruct (completeness (CaseL e1_1 e2
                        (Pat n1 t1 n2 n) e3)).
            eassumption. simpl.
            rewrite Heq2, Heq3, Heq6, eqTypeS_refl, eqTypeS_refl.
            reflexivity. destruct H7.
            eapply Rule_Choice; eapply Rule_CaseList; try eassumption;
            destruct d1; try inversion H20;
            try apply more_specific_Any.
  Qed.

  Theorem preservation_multi : forall e e' t,
    e ==>* e' ->
    forall Delta Gamma d,
    compatibleCtx Gamma Delta ->
    typeOf Delta e = Some t ->
    compatible d t ->
    Gamma |- e :? d ->
    exists d', more_specific d' d = true
      /\ compatible d' t
      /\ Gamma |- e' :? d'.
  Proof.
    intros e e' t H. induction H; intros; eauto.
    remember H as HC. clear HeqHC. inversion HC.
    remember H2 as H2C. clear HeqH2C.
    eapply (step_preservation _ _ _ _ H5) in H2.
    apply (preservation e1 e2 Delta Gamma t d) in H; try assumption.
    destruct H, H, H5, H8.
    destruct (IHmulti_step_rel Delta Gamma x); eauto.
    destruct H9, H10. exists x0. split.
    eapply more_specific_transitive; eauto.
    split; assumption.
  Qed.

  (* Theorem soundness:
   The main theorem showing that if an expression e has deterministic type Det,
   then any expression e' that e reduces to will not be a non-deterministic choice.
   This validates that the determinism type system correctly tracks non-determinism. *)
  Theorem soundness : forall Delta Gamma e e' t,
    compatibleCtx Gamma Delta ->
    typeOf Delta e = Some t ->
    Gamma |- e :? Det ->
    e ==>* e' ->
    notOr e'.
  Proof.
    intros Delta Gamma e e' t H1 H2 H3 H4.
    assert (compatible Det t) as H5 by
      (destruct t; auto with *; reflexivity).
    destruct (preservation_multi e e' t H4
                Delta Gamma Det H1 H2 H5 H3)
      as [d' [H6 [_ H7]]].
    destruct e'; try reflexivity.
    inversion H7. subst. inversion H6.
  Qed.

Theorem functional_is_deterministic : forall e t Delta Gamma,
    compatibleCtx Gamma Delta ->
    (forall x, nonAny (Gamma x)) ->
    typeOf Delta e = Some t ->
    functional e ->
    exists d, Gamma |- e :? d
      /\ nonAny d.
  Proof.
    induction e; intros; try inversion H2.
    - exists (Gamma n). split. apply Rule_Var. reflexivity.
      apply H0.
    - exists Det. split. apply Rule_BTrue. reflexivity.
    - exists Det. split. apply Rule_BFalse. reflexivity.
    - exists Det. split. apply Rule_Nil. reflexivity.
    - destruct_typeOf_chain H1.
      destruct (IHe1 _ _ _ H H0 Heq2 H3). destruct H5.
      destruct (IHe2 _ _ _ H H0 Heq1 H4). destruct H7.
      eexists. split. apply Rule_Cons; eassumption.
      apply nonAny_more_specific_det in H6. destruct H6.
      apply nonAny_more_specific_det in H8. destruct H8.
      rewrite H6, H8. reflexivity.
    - destruct_typeOf_chain H1.
      destruct (IHe1 _ _ _ H H0 Heq1 H3). destruct H5.
      destruct (IHe2 _ _ _ H H0 Heq2 H4). destruct H7.
      destruct x.
      + eexists. split. apply Rule_AppDet; eassumption.
        unfold decide.
        apply nonAny_more_specific_det in H8. destruct H8.
        rewrite H8. reflexivity.
      + inversion H6.
      + exists (decide x1 x0 x2). split. eapply Rule_AppFun.
        eassumption. eassumption. reflexivity.
        unfold decide. destruct H6.
        apply (nonAny_more_specific _ _ H8) in H6. destruct H6.
        rewrite H10. assumption.
    - destruct_typeOf_chain H1.
      edestruct (IHe t1 (update Nat.eqb Delta n t)).
      eapply (update_compatible _ _ _ _ Det). eassumption.
      reflexivity.
      + intros. unfold update. destruct (Nat.eqb n x) eqn:Heq; auto.
        reflexivity.
      + assumption.
      + assumption.
      + destruct H3. exists (Arrow Det x). split. apply Rule_Abs.
        reflexivity. assumption. simpl. eauto.
    - destruct_typeOf_chain H1. destruct H4.
      destruct (IHe1 _ _ _ H H0 Heq1 H3). destruct H6.
      destruct (IHe2 _ _ _ H H0 Heq2 H4). destruct H8.
      destruct (IHe3 _ _ _ H H0 Heq3 H5). destruct H10.
      eexists. split. apply Rule_CaseBool. eassumption.
      eassumption. eassumption.
      apply nonAny_lub. eapply compatibility. eassumption. eassumption. assumption. assumption. assumption. assumption.
    - destruct_typeOf_chain H1. destruct H2, H3.
      destruct (IHe1 _ _ _ H H0 Heq1 H2). destruct H5.
      destruct (IHe2 _ _ _ H H0 Heq3 H3). destruct H7.
      edestruct (IHe3 t
        (update Nat.eqb (update Nat.eqb Delta n2 (TList t1)) n1 t1)
        (update Nat.eqb (update Nat.eqb
                        Gamma n2 Det) n1 Det)).
      eapply (update_compatible _ _ _ _ Det).
      eapply (update_compatible _ _ _ _ Det). assumption.
      reflexivity. reflexivity.
      + intros. unfold update.
        destruct (Nat.eqb n1 x1) eqn:Heq6, (Nat.eqb n2 x1) eqn:Heq7.
        reflexivity. reflexivity. reflexivity. apply H0.
      + assumption.
      + assumption.
      + destruct H9. eexists. split.
        eapply Rule_CaseList with (d1 := Det) (d2 := Det).
        eassumption. reflexivity. reflexivity. eassumption.
        rewrite double_update_indep. eassumption. assumption.
        apply nonAny_more_specific_det. assumption.
        apply nonAny_lub; try assumption.
        eapply compatible_bool_list.
        eapply compatibility. eassumption. eassumption. assumption.
  Qed.

End Proofs.
