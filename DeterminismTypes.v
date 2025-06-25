Require Import Strings.String Lists.List Lists.ListSet PeanoNat EqNat Bool FunctionalExtensionality Coq.Program.Equality.
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
- "Gamma '|-' e ':::' delta" is the Deterministic typing relation
- "step" (or "==>") is the small-step semantics
- "subst" is the substitution function
- "notOr" is the definition for a deterministic result
- Important Theorems are: "completeness", "preservation" and "soundness"

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
    forall {V : Type} (Rho : nat -> V) n1 t1 n2 t2,
    n1 <> n2 ->
    update Nat.eqb (update Nat.eqb Rho n1 t1) n2 t2 =
    update Nat.eqb (update Nat.eqb Rho n2 t2) n1 t1.
  Proof.
    intros. apply functional_extensionality.
    intro x. unfold update.
    destruct (n1 =? x) eqn:Heq1;
    destruct (n2 =? x) eqn:Heq2; try reflexivity;
    rewrite Nat.eqb_eq in *; subst; contradiction.
  Qed.

  Lemma double_update :
    forall {V : Type} (Rho : nat -> V) n t1 t2,
    update Nat.eqb (update Nat.eqb Rho n t1) n t2 =
    update Nat.eqb Rho n t2.
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

  Inductive Pattern : Type :=
    | Pat : forall (n1 : nat) (t1 : TType) (n2 : nat)
          , n1 <> n2 -> Pattern.

  Inductive Exp : Type :=
    | Var    : nat -> Exp
    | BTrue  : Exp
    | BFalse : Exp
    | Nil    : TType -> Exp
    | Cons   : Exp -> Exp -> Exp
    | App    : Exp -> Exp -> Exp
    | Abs    : nat -> TType -> Exp -> Exp
    | Or     : Exp -> Exp -> Exp
    | CaseB  : Exp -> Exp -> Exp -> Exp
    | CaseL  : Exp -> Exp -> Pattern -> Exp -> Exp.

  Definition notOr (e : Exp) : Prop :=
    match e with
    | Or _ _ => False
    | _ => True
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
    - intros. generalize dependent t2. induction t1; intros.
      + destruct t2; try discriminate. reflexivity.
      + destruct t2; try discriminate. simpl in H.
        apply IHt1 in H. subst. reflexivity.
      + destruct t2; try discriminate. simpl in H.
        apply Bool.andb_true_iff in H. destruct H.
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
    | D : DType
    | ND : DType
    | Arrow : DType -> DType -> DType.

  Fixpoint compatible (d : DType) (t : TType) : Prop :=
    match d, t with
    | D, TBool => True
    | D, TList _ => True
    | ND, _ => True
    | Arrow d1 d2, TArrow t1 t2 =>
        compatible d1 t1 /\ compatible d2 t2
    | _, _ => False
    end.

  Fixpoint mkCompatible (t : TType) : DType :=
    match t with
    | TBool => D
    | TList _ => D
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

  Lemma compatible_ND : forall t,
    compatible ND t.
  Proof. reflexivity. Qed.

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
    forall Rho e,
    well_typed Rho e ->
    match e with
    | Cons e1 e2 => well_typed Rho e1 /\ well_typed Rho e2
    | App e1 e2 => well_typed Rho e1 /\ well_typed Rho e2
    | Abs x t e1 => well_typed (update Nat.eqb Rho x t) e1
    | Or e1 e2 => well_typed Rho e1 /\ well_typed Rho e2
    | CaseB e1 e2 e3 => well_typed Rho e1 /\ well_typed Rho e2 /\ well_typed Rho e3
    | CaseL e1 e2 (Pat n1 t1 n2 _) e3 =>
        well_typed Rho e1 /\
        well_typed Rho e2 /\
        well_typed (update Nat.eqb (update Nat.eqb Rho n1 t1) n2 (TList t1)) e3
    | _ => True
    end.
  Proof.
    intros. destruct e; try destruct p;
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
    forall Gamma Rho n t d,
    compatibleCtx Gamma Rho ->
    compatible d t ->
    compatibleCtx (update Nat.eqb Gamma n d)
                  (update Nat.eqb Rho n t).
  Proof.
    intros. unfold compatibleCtx. intro n0.
    unfold update. destruct (n =? n0) eqn:Heq; eauto.
  Qed.

  Lemma update_update_compatible :
    forall Gamma Rho n1 n2 t1 d1 t2 d2,
    compatibleCtx Gamma Rho ->
    compatible d1 t1 ->
    compatible d2 t2 ->
    let Gamma' := update Nat.eqb Gamma n1 d1 in
    compatibleCtx (update Nat.eqb Gamma' n2 d2)
                  (update Nat.eqb (update Nat.eqb Rho n1 t1) n2 t2).
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

  Fixpoint more_specific (d1 d2 : DType) : bool :=
    match d1, d2 with
    | _, ND => true
    | D, D => true
    | Arrow d1 d2, Arrow d1' d2' =>
        andb (less_specific d1 d1') (more_specific d2 d2')
    | _, _ => false
    end
    with less_specific (d1 d2 : DType) : bool :=
      match d1, d2 with
      | ND, _ => true
      | D, D => true
      | Arrow d1 d2, Arrow d1' d2' =>
          andb (more_specific d1 d1') (less_specific d2 d2')
      | _, _ => false
      end.

  Definition decide (d1 d3 d2 : DType) : DType :=
    if more_specific d3 d1 then d2 else ND.

  Example more_specific_ex1 :
    more_specific (Arrow ND D) (Arrow D D) = true.
  Proof. trivial. Qed.

  Example more_specific_ex2 :
    more_specific (Arrow D D) (Arrow ND D) = false.
  Proof. trivial. Qed.

  Example more_specific_ex3 :
    more_specific (Arrow (Arrow D D) D) (Arrow (Arrow ND D) D) = true.
  Proof. trivial. Qed.

  (* map :# (D -> D) -> (D -> D)
  map :# (ND -> D) -> (ND -> ND)  -- spine *)
  Example more_specific_ex4 :
    more_specific (Arrow (Arrow D D) (Arrow D D))
                  (Arrow (Arrow ND D) (Arrow ND ND)) = false /\
    less_specific (Arrow (Arrow D D) (Arrow D D))
                  (Arrow (Arrow ND D) (Arrow ND ND)) = false.
  Proof. split; trivial. Qed.

  Lemma specificity_not_inverses : exists d1 d2,
    more_specific d1 d2 = false /\ less_specific d1 d2 = false.
  Proof.
    exists (Arrow D D), (Arrow ND ND).
    split; reflexivity.
  Qed.

  Lemma more_specific_refl : forall d, more_specific d d = true
    with less_specific_refl : forall d, less_specific d d = true.
  Proof.
    - induction d; simpl; trivial.
      rewrite IHd2. rewrite less_specific_refl. reflexivity.
    - induction d; simpl; trivial.
      rewrite IHd2. rewrite more_specific_refl. reflexivity.
  Qed.

  Lemma more_specific_less_specific : forall d1 d2,
    more_specific d1 d2 = less_specific d2 d1
    with less_specific_more_specific : forall d1 d2,
    less_specific d1 d2 = more_specific d2 d1.
  Proof.
    --
    induction d1; intro d2; induction d2; simpl; trivial.
    - rewrite <- IHd1_2.
      rewrite less_specific_more_specific.
      reflexivity.
    --
    induction d1; intro d2; induction d2; simpl; trivial.
    - rewrite <- IHd1_2.
      rewrite more_specific_less_specific.
      reflexivity.
  Qed.

  Lemma more_specific_transitive : forall d1 d2 d3,
    more_specific d1 d2 = true ->
    more_specific d2 d3 = true ->
    more_specific d1 d3 = true
    with less_specific_transitive : forall d1 d2 d3,
    less_specific d1 d2 = true ->
    less_specific d2 d3 = true ->
    less_specific d1 d3 = true.
  Proof.
    --
    intros. induction d1, d2, d3; simpl; trivial.
    - inversion H.
    - inversion H0.
    - simpl in H. simpl in H0.
      apply Bool.andb_true_iff in H. destruct H.
      apply Bool.andb_true_iff in H0. destruct H0.
      erewrite less_specific_transitive.
      erewrite more_specific_transitive.
      reflexivity.
      apply H1.
      apply H2.
      apply H.
      apply H0.

    --
    intros. induction d1, d2, d3; simpl; trivial.
    - inversion H0.
    - inversion H.
    - simpl in H. simpl in H0.
      apply Bool.andb_true_iff in H. destruct H.
      apply Bool.andb_true_iff in H0. destruct H0.
      erewrite less_specific_transitive; eauto.
      erewrite more_specific_transitive; eauto.
  Qed.

  Lemma more_specific_ND : forall d, more_specific d ND = true.
  Proof.
    - induction d; simpl; trivial.
  Qed.

  Lemma more_specific_D : forall d,
    more_specific d D = true -> d = D.
  Proof.
    - induction d; intros; inversion H; simpl; trivial.
  Qed.

End Subtyping.

Section LeastUpperBound.

  Definition lub2 (d1 d2 : DType) : DType :=
    if more_specific d1 d2 then d2
    else if more_specific d2 d1 then d1
    else ND.

  Definition lub (d1 d2 d3 : DType) : DType :=
    lub2 (lub2 d1 d2) d3.

  Lemma compatible_lub : forall d1 d2 d3 t,
    compatible d1 TBool ->
    compatible d2 t ->
    compatible d3 t ->
    compatible (lub d1 d2 d3) t.
  Proof.
    intros d1 d2 d3 t Hc1 Hc2 Hc3.
    unfold lub. unfold lub2.
    destruct (more_specific d1 d2) eqn:H1.
    - destruct (more_specific d2 d3) eqn:H2.
      + assumption.
      + destruct (more_specific d3 d2) eqn:H3.
        * assumption.
        * reflexivity.
    - destruct (more_specific d2 d1) eqn:H4.
      + destruct (more_specific d1 d3) eqn:H5.
        * assumption.
        * destruct (more_specific d3 d1) eqn:H6.
          -- destruct d1; inversion Hc1.
             ++  destruct t; try reflexivity.
                 destruct d2; inversion Hc2;
                 inversion H4.
             ++ reflexivity.
          -- reflexivity.
      + simpl. destruct d3; auto; reflexivity.
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
      compatible d1 TBool ->
      more_specific d1 x1 = true ->
      more_specific d2 x2 = true ->
      more_specific (lub2 d1 d2) (lub2 x1 x2) = true)
      as more_specific_lub2.
    --
    intros d1 d2 x1 x2 C1 H1 H2.
    unfold lub2. destruct (more_specific d1 d2) eqn:H3.
    - destruct (more_specific x1 x2) eqn:H4.
      + assumption.
      + destruct (more_specific x2 x1) eqn:H5.
        * eapply more_specific_transitive.
          apply H2. apply H5.
        * apply more_specific_ND.
    - destruct (more_specific d2 d1) eqn:H5.
      + destruct (more_specific x1 x2) eqn:H6.
        * eapply more_specific_transitive.
          apply H1. apply H6.
        * destruct (more_specific x2 x1) eqn:H7.
          ++ assumption.
          ++ apply more_specific_ND.
      + destruct (more_specific x1 x2) eqn:H6.
        * destruct d1, d2, x1, x2;
          try discriminate;
          try reflexivity.
          inversion C1.
        * destruct (more_specific x2 x1) eqn:H7.
          ++  destruct d1, d2, x1, x2;
              try discriminate;
              try reflexivity.
              inversion C1.
          ++ reflexivity.
    --
    intros x1 x2 x3 d1 d2 d3 C1 H1 H2 H3.
    unfold lub.
    apply more_specific_lub2; try assumption.
    - destruct x1, x2; try discriminate;
      try reflexivity.
      inversion C1.
    - apply more_specific_lub2; try assumption.
  Qed.

  Lemma more_specific_lub2 : forall d1 d2 d3,
    more_specific d2 (lub d1 d2 d3) = true.
  Proof.
    intros. unfold lub, lub2.
    destruct (more_specific d1 d2) eqn:H1.
    - destruct (more_specific d2 d3) eqn:H2.
      + assumption.
      + destruct (more_specific d3 d2) eqn:H3.
        * apply more_specific_refl.
        * apply more_specific_ND.
    - destruct (more_specific d2 d1) eqn:H4.
      + destruct (more_specific d1 d3) eqn:H5.
        * eapply more_specific_transitive; eassumption.
        * destruct (more_specific d3 d1) eqn:H6.
          -- assumption.
          -- apply more_specific_ND.
      + simpl. destruct d3; simpl; apply more_specific_ND.
  Qed.

  Lemma more_specific_lub3 : forall d1 d2 d3,
    more_specific d3 (lub d1 d2 d3) = true.
  Proof.
    intros. unfold lub, lub2.
    destruct (more_specific d1 d2) eqn:H1.
    - destruct (more_specific d2 d3) eqn:H2.
      + apply more_specific_refl.
      + destruct (more_specific d3 d2) eqn:H3.
        * assumption.
        * apply more_specific_ND.
    - destruct (more_specific d2 d1) eqn:H4.
      + destruct (more_specific d1 d3) eqn:H5.
        * apply more_specific_refl.
        * destruct (more_specific d3 d1) eqn:H6.
          -- assumption.
          -- apply more_specific_ND.
      + simpl. destruct d3; reflexivity.
  Qed.

End LeastUpperBound.

(* Section DetTyping:
   Defines the typing rules for determinism types.
   These rules capture when an expression has a particular determinism type,
   connecting the operational behavior with static determinism properties. *)
Section DetTyping.

  Reserved Notation "Gamma '|-' e ':::' delta" (at level 40).
  Inductive hasDType : context -> Exp -> DType -> Prop :=
    | Rule_Var : forall Gamma x d,
          (Gamma x) = d ->
          Gamma |- Var x ::: d
    | Rule_BTrue : forall Gamma,
          Gamma |- BTrue ::: D
    | Rule_BFalse : forall Gamma,
          Gamma |- BFalse ::: D
    | Rule_Nil : forall Gamma t,
          Gamma |- Nil t ::: D
    | Rule_Cons : forall Gamma e1 e2 d1 d2 d3,
          Gamma |- e1 ::: d1 ->
          Gamma |- e2 ::: d2 ->
          d3 = match d1, d2 with
              | D, D => D
              | _, _ => ND
              end ->
          Gamma |- Cons e1 e2 ::: d3
    | Rule_AppND : forall Gamma e1 e2 d,
          Gamma |- e1 ::: ND ->
          Gamma |- e2 ::: d ->
          Gamma |- App e1 e2 ::: ND
    | Rule_AppFun : forall Gamma e1 e2 d1 d2 d3 d4,
          Gamma |- e1 ::: Arrow d1 d2 ->
          Gamma |- e2 ::: d3 ->
          d4 = decide d1 d3 d2 ->
          Gamma |- App e1 e2 ::: d4
    | Rule_Abs : forall Gamma x e d1 d2 t1,
          compatible d1 t1 ->
          let Gamma' := update Nat.eqb Gamma x d1 in
          Gamma' |- e ::: d2 ->
          Gamma |- Abs x t1 e ::: Arrow d1 d2
    | Rule_Choice : forall Gamma e1 e2 d1 d2,
          Gamma |- e1 ::: d1 ->
          Gamma |- e2 ::: d2 ->
          Gamma |- Or e1 e2 ::: ND
    | Rule_CaseBool : forall Gamma e1 e2 e3 d1 d2 d3,
          Gamma |- e1 ::: d1 ->
          Gamma |- e2 ::: d2 ->
          Gamma |- e3 ::: d3 ->
          Gamma |- CaseB e1 e2 e3 ::: lub d1 d2 d3
    | Rule_CaseList :
        forall Gamma e1 e2 e3 n1 n2 d1 t1 d2 d_1 d_2 d_3 H,
          Gamma |- e1 ::: d_1 ->
          compatible d1 t1 ->
          compatible d2 (TList t1) ->
          Gamma |- e2 ::: d_2 ->
          let Gamma'  := update Nat.eqb Gamma  n1 d1 in
          let Gamma'' := update Nat.eqb Gamma' n2 d2 in
          Gamma'' |- e3 ::: d_3 ->
          let p := Pat n1 t1 n2 H in
          Gamma |- CaseL e1 e2 p e3 ::: lub d_1 d_2 d_3
    where "Gamma '|-' e ':::' delta" := (hasDType Gamma e delta).

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
    | CaseB (Or e1 e2) e3 e4 =>
        Some (Or (CaseB e1 e3 e4) (CaseB e2 e3 e4))
    | CaseL (Or e1 e2) e3 (Pat n1 t1 n2 H) e4 =>
        Some (Or (CaseL e1 e3 (Pat n1 t1 n2 H) e4)
                 (CaseL e2 e3 (Pat n1 t1 n2 H) e4))
    | CaseB BFalse e2 e3 => Some e2
    | CaseB BTrue e2 e3 => Some e3
    | CaseL (Nil _) e2 _ e3 => Some e2
    | CaseL (Cons e1 e2) e3 (Pat n1 t1 n2 H) e4 =>
          if anyIn (freeVars (Cons e1 e2)) (n1::n2::boundVars e4)
            then None
            else if anyIn (freeVars e2) (boundVars e1)
              then None
              else Some (subst_all [(n1, e1, t1);
                                    (n2, e2, TList t1)] e4)
    | Or e1 e2 => match step e1 with
                  | None => match step e2 with
                            | None => None
                            | Some e2' => Some (Or e1 e2')
                            end
                  | Some e1' => Some (Or e1' e2)
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
Notation "Gamma '|-' e ':::' delta" := (hasDType Gamma e delta)
  (at level 40).

Notation "e ==> e'" := (step_rel e e') (at level 40).

Notation "e '==>*' e'" := (multi_step_rel e e')
  (at level 40).

Section Examples.
  (* Examples of determinism types and typing rules *)

  Hint Resolve Rule_Var Rule_BTrue Rule_BFalse Rule_Nil
               Rule_Cons Rule_Choice Rule_CaseBool
               Rule_CaseList : core.

  Definition Gamma1 := update Nat.eqb (fun _ => ND) 1 D.

  Example exVar : Gamma1 |- Var 1 ::: D.
  Proof. eauto. Qed.

  Example eFreeVar : Gamma1 |- Var 42 ::: ND.
  Proof. eauto. Qed.

  Example exCons : Gamma1 |- Nil TBool ::: D.
  Proof. eauto. Qed.

  Example exApp : Gamma1 |- App (Abs 2 TBool (Var 2)) (Var 1) ::: D.
  Proof.
    eapply Rule_AppFun with (d1 := D) (d2 := D) (d3 := D);
    try apply Rule_Abs; eauto; reflexivity.
  Qed.

  Example exAppEval : App (Abs 2 TBool (Var 2)) (Var 1) ==>* Var 1.
  Proof.
    eapply Multi_Step_Many. apply Single_Step.
    reflexivity. apply Multi_Step_Refl.
  Qed.

  Example exAbs : Gamma1 |- Abs 2 TBool (Var 1) ::: Arrow D D.
  Proof.
    apply Rule_Abs; eauto; reflexivity.
  Qed.

  Definition Gamma2 := update Nat.eqb (fun _ => ND) 1 (Arrow (Arrow D D) (Arrow D D)).

  Example exPoly : Gamma2 |- App (Var 1) (Abs 2 TBool (Var 2)) ::: Arrow D D.
  Proof.
    eapply Rule_AppFun with (d1 := Arrow D D)
                            (d2 := Arrow D D)
                            (d3 := Arrow D D);
    try apply Rule_Abs; eauto. reflexivity.
  Qed.

  Example exChoice : Gamma1 |- Or (Var 1) (Var 1) ::: ND.
  Proof. eauto. Qed.

  (*
  1 = allValues :? Any -> Det
  2 = \x -> id x ? not x :? Any -> Any
  result must not be of type D
  *)
  Definition RhoAV' := update Nat.eqb (fun _ => TBool) 1 (TArrow TBool TBool).
  Definition RhoAV  := update Nat.eqb RhoAV' 2 (TArrow TBool TBool).
  Definition GammaAV := update Nat.eqb (update Nat.eqb (fun _ => ND) 1 ND) 2 (mkCompatible (RhoAV 2)).
  (* GammaAV = {1 -> D, 2 -> Arrow TBool TBool} *)

  (* The following example requires the AppND rule to type it correctly. *)
  Example exAllValues : GammaAV |- App (Var 1) (Var 2) ::: ND.
  Proof.
      eapply Rule_AppND; apply Rule_Var; reflexivity.
  Qed.

  Example exAllValuesNotD : not (GammaAV |- App (Var 1) (Var 2) ::: D).
  Proof.
      unfold not. intros.
      inversion H. inversion H2. inversion H4. subst.
      unfold GammaAV in *. unfold mkCompatibleCtx in *.
      unfold RhoAV in *. unfold RhoAV' in *. simpl in *.
      inversion H9.
  Qed.

  (*
  The AppND rule is required to type the following example.
  1 -> not :? Det -> Det
  2 -> id :? Det -> Det
  (not ? id) :? Any
  (not ? id) True :? Any
  *)
  Definition RhoC' := update Nat.eqb (fun _ => TBool) 1 (TArrow TBool TBool).
  Definition RhoC  := update Nat.eqb RhoC' 2 (TArrow TBool TBool).
  Definition GammaC := mkCompatibleCtx RhoC.
  Example exChoice2 : GammaC |- App (Or (Var 1) (Var 2)) BFalse ::: ND.
  Proof. eapply Rule_AppND; eauto. Qed.

  Lemma exChoice2_must_use_AppND :
  forall b d,
    GammaC |- App (Or (Var 1) (Var 2)) b ::: d ->
    d = ND /\
    (forall d1 d2,
      ~ (GammaC |- Or (Var 1) (Var 2) ::: d1 /\ GammaC |- b ::: d2 /\
         exists d3 d4 d5,
           GammaC |- Or (Var 1) (Var 2) ::: Arrow d3 d4 /\
           GammaC |- b ::: d5 /\
           d = decide d3 d5 d4)).
  Proof.
    intros b d H.
    inversion H; subst.
    - split; auto.
      intros d3 d4 [H1 [H2 [d5 [d6 [d7 [H4 [H6 H7]]]]]]].
      inversion H4.
    - inversion H2.
  Qed.

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
    forall e Rho n t t2,
    typeOf Rho e = Some t ->
    anyIn (freeVars e) [n] = false ->
    typeOf (update Nat.eqb Rho n t2) e = typeOf Rho e.
  Proof.
    induction e; intros Rho n1 t1 t2 H H1; simpl in *.
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
          rewrite (double_update_indep _ n1 _ n2).
          rewrite (double_update_indep _ n1 _ n0).
          erewrite IHe3. rewrite Heq3.
          rewrite eqTypeS_refl. reflexivity.
          eassumption. apply anyIn_removeb in H4.
          apply anyIn_removeb in H4. assumption.
          symmetry. assumption. symmetry. assumption.
          assumption. assumption.
  Qed.

  Lemma anyIn_subst :
    forall e1 e2 e3 n3,
    anyIn (freeVars e2) (boundVars e1) = false ->
    anyIn (freeVars e3) [n3] = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    anyIn (freeVars e2) (boundVars (subst n3 e3 e1)) = false.
  Proof.
    induction e1; intros e2 e3 n3 H1 H2 H3.
    - simpl. destruct (n =? n3) eqn:Heq.
      * rewrite Nat.eqb_eq in Heq. subst n3.
        simpl in H1. apply H3.
      * apply H1.
    - simpl. apply H1.
    - simpl. apply H1.
    - simpl. apply H1.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      apply anyIn_concat1. split.
      apply IHe1_1; assumption.
      apply IHe1_2; assumption.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      apply anyIn_concat1. split.
      apply IHe1_1; assumption.
      apply IHe1_2; assumption.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      destruct (n =? n3) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst n3.
        simpl in *. apply anyIn_cons.
        split; assumption.
      * simpl in *. apply anyIn_cons. split;
        try eapply IHe1; try eassumption.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      apply anyIn_concat1. split.
      apply IHe1_1; assumption.
      apply IHe1_2; assumption.
    - simpl. apply anyIn_subterm in H1. destruct H1.
      destruct H0.
      apply anyIn_concat1. split.
      apply IHe1_1; assumption.
      apply anyIn_concat1. split.
      apply IHe1_2; assumption.
      apply IHe1_3; assumption.
    - destruct p. apply anyIn_subterm in H1. destruct H1.
      destruct H0. simpl.
      destruct (n3 =? n1) eqn:Heq1,
                (n3 =? n2) eqn:Heq2; simpl in *.
      + apply Nat.eqb_eq in Heq1. apply Nat.eqb_eq in Heq2. subst.
        apply anyIn_concat1. split.
        apply IHe1_1; assumption.
        apply anyIn_concat1. split.
        apply IHe1_2; assumption.
        assumption.
      + apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. subst.
        apply anyIn_concat1. split.
        apply IHe1_1; assumption.
        apply anyIn_concat1. split.
        apply IHe1_2; assumption.
        assumption.
      + apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. subst.
        apply anyIn_concat1. split.
        apply IHe1_1; assumption.
        apply anyIn_concat1. split.
        apply IHe1_2; assumption.
        assumption.
      + apply Nat.eqb_neq in Heq1. apply Nat.eqb_neq in Heq2.
        apply anyIn_concat1. split.
        eapply IHe1_1; assumption.
        apply anyIn_concat1. split.
        eapply IHe1_2; assumption.
        apply anyIn_cons in H1. destruct H1.
        apply anyIn_cons in H1. destruct H1.
        apply anyIn_cons. split. apply anyIn_cons.
        split. eapply IHe1_3; try eassumption. assumption. assumption.
  Qed.

End PreservationTTypesHelper.

(* Section PreservationTTypes:
   Main lemmas for type preservation, showing that typing is preserved
   under substitution and reduction steps. *)
Section PreservationTTypes.

  Lemma subst_preservation :
    forall Rho e1 e2 n t t2,
    anyIn (freeVars e2) (n::boundVars e1) = false ->
    typeOf (update Nat.eqb Rho n t2) e1 = Some t ->
    typeOf Rho e2 = Some t2 ->
    typeOf Rho (subst n e2 e1) = Some t.
  Proof.
    intros Rho e1. generalize dependent Rho.
    induction e1; intros Rho e2 n0 t1 t2 HF H H1.
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
      eapply (IHe1_1 Rho) in Heq1. eapply (IHe1_2 Rho) in Heq2.
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
        rewrite double_update_indep in Heq3.
        rewrite double_update in Heq3.
        rewrite double_update_indep in Heq3.
        erewrite Heq3. erewrite IHe1_1.
        rewrite eqTypeS_refl.
        erewrite IHe1_2. rewrite eqTypeS_refl. reflexivity.
        apply anyIn_cons. split; assumption.
        eassumption. eassumption.
        apply anyIn_cons. split; assumption.
        eassumption. eassumption. eassumption. symmetry. assumption.
      * apply Nat.eqb_neq in HeqN1.
        apply Nat.eqb_eq in HeqN2. subst. simpl.
        rewrite double_update in Heq3.
        erewrite Heq3. erewrite IHe1_1.
        rewrite eqTypeS_refl.
        erewrite IHe1_2. rewrite eqTypeS_refl. reflexivity.
        apply anyIn_cons. split; assumption.
        eassumption. eassumption.
        apply anyIn_cons. split; assumption.
        eassumption. eassumption.
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
        erewrite IHe1_3. rewrite eqTypeS_refl.
        reflexivity.
        apply anyIn_cons. split; assumption.
        erewrite (double_update_indep _ n1 _ n0).
        erewrite (double_update_indep _ n2 _ n0).
        rewrite Heq3. reflexivity. symmetry. assumption.
        symmetry. assumption.
        erewrite typeOf_unbound; try eassumption.
        erewrite typeOf_unbound; try eassumption.
        erewrite typeOf_unbound; try eassumption.
  Qed.

  Lemma subst_preservation2 :
    forall Rho e1 e2 n t n3 t3 e3 t2,
    anyIn (freeVars e2) (n3::n::boundVars e1) = false ->
    anyIn (freeVars e3) (n3::n::boundVars e1) = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    n <> n3 ->
    typeOf (update Nat.eqb (update Nat.eqb Rho n3 t3) n t2) e1
      = Some t ->
    typeOf Rho e2 = Some t2 ->
    typeOf Rho e3 = Some t3 ->
    typeOf Rho (subst n e2 (subst n3 e3 e1)) = Some t.
  Proof.
    intros.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H0. destruct H0.
    apply anyIn_cons in H0. destruct H0.
    * eapply subst_preservation.
      - apply anyIn_cons. split.
        apply anyIn_subst; try assumption.
        apply H7.
      - eapply subst_preservation.
        + apply anyIn_cons. split; assumption.
        + rewrite double_update_indep. eassumption. assumption.
        + erewrite typeOf_unbound. apply H5. apply H5. apply H9.
      - apply H4.
  Qed.

  Lemma step_preservation :
    forall e e' Rho t,
    step e = Some e' ->
    typeOf Rho e = Some t ->
    typeOf Rho e' = Some t.
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
    + destruct e1_1; try inversion H3; subst.
      * destruct_typeOf_chain H0. reflexivity.
      * destruct_typeOf_chain H0. reflexivity.
      * destruct_typeOf_chain H0.
        rewrite eqTypeS_refl. rewrite eqType_refl. reflexivity.
    + destruct p, e1_1; inversion H3; subst.
      * destruct_typeOf_chain H0. reflexivity.
      * destruct (anyIn (freeVars e1_1_1 ++ freeVars e1_1_2)
                        (n1 :: n2 :: boundVars e1_3)) eqn:Heq1;
        try discriminate.
        destruct (anyIn (freeVars e1_1_2)
                        (boundVars e1_1_1)) eqn:Heq2;
        try discriminate. inversion H3. subst.
        apply anyIn_concat2 in Heq1. destruct Heq1 as [Heq1 HFA].
        destruct_typeOf_chain H0.
        erewrite subst_preservation2
          with (t := TArrow _ _).
        rewrite eqType_refl. reflexivity.
        assumption. assumption. assumption.
        symmetry. assumption.
        rewrite double_update_indep. eassumption.
        assumption. assumption. assumption.
      * destruct_typeOf_chain H0.
        rewrite eqTypeS_refl. rewrite eqTypeS_refl.
        rewrite eqTypeS_refl. rewrite Heq9. reflexivity.
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
  - destruct e1; inversion H2; subst.
    + destruct_typeOf_chain H0. reflexivity.
    + destruct_typeOf_chain H0. reflexivity.
    + destruct_typeOf_chain H0.
      rewrite eqTypeS_refl. reflexivity.
  - destruct p, e1; inversion H2; subst.
    + destruct_typeOf_chain H0. reflexivity.
    + destruct (anyIn (freeVars e1_1 ++ freeVars e1_2)
                      (n1 :: n2 :: boundVars e3)) eqn:Heq1;
      try discriminate;
      destruct (anyIn (freeVars e1_2) (boundVars e1_1)) eqn:Heq2;
      try inversion H2; subst.
      apply anyIn_concat2 in Heq1. destruct Heq1 as [Heq1 HFA].
      destruct_typeOf_chain H0.
      eapply subst_preservation2; try assumption.
      symmetry. assumption.
      rewrite double_update_indep. eassumption.
      assumption. assumption. assumption.
    + destruct_typeOf_chain H0.
      rewrite eqTypeS_refl. rewrite eqTypeS_refl.
      rewrite eqTypeS_refl. reflexivity.
  Qed.

  Lemma well_typed_step :
    forall Rho e e',
    well_typed Rho e ->
    e ==> e' ->
    well_typed Rho e'.
  Proof.
    intros Rho e e' Hwt Hstep.
    inversion Hstep. subst.
    destruct_typeOf_chain Hwt.
    erewrite step_preservation.
    reflexivity. apply H. apply Heq1.
  Qed.

  Theorem well_typed_multi_step :
    forall Rho e e',
    well_typed Rho e ->
    e ==>* e' ->
    well_typed Rho e'.
  Proof.
    intros Rho e e' Hwt Hstep.
    induction Hstep; auto.
    apply IHHstep. apply well_typed_step with (e := e1).
    apply Hwt. apply H.
  Qed.

End PreservationTTypes.

Section Proofs.

  Hint Resolve more_specific_ND compatible_ND : core.

  Lemma compatibility:
    forall e Rho Gamma t d,
    compatibleCtx Gamma Rho ->
    typeOf Rho e = Some t ->
    Gamma |- e ::: d ->
    compatible d t.
  Proof.
    induction e; intros.
    - inversion H1; subst.
      simpl in H0. inversion H0.
      unfold compatibleCtx in *.
      destruct (Rho n) eqn:HeqR; rewrite <- HeqR; apply H.
    - inversion H1; subst. simpl in H1. simpl in H0. inversion H0.
      reflexivity.
    - inversion H1; subst. simpl in H1. simpl in H0. inversion H0.
      reflexivity.
    - inversion H1; subst. simpl in H1. simpl in H0. inversion H0.
      reflexivity.
    - inversion H1. subst. simpl.
      destruct_typeOf_chain H0.
      destruct d1, d2; auto; reflexivity.
    - inversion H1; subst.
      + reflexivity.
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
        rewrite double_update_indep.
        apply update_compatible.
        apply update_compatible.
        apply H. apply H11. apply H9.
        apply HeqN1.
      + assumption.
  Qed.

  (* Theorem completeness:
    Shows that any well-typed expression in the Curry type system
    can be assigned a determinism type. This establishes that
    determinism typing covers all valid programs. *)
  Theorem completeness :
    forall e Rho Gamma t,
    compatibleCtx Gamma Rho ->
    typeOf Rho e = Some t ->
    exists d, Gamma |- e ::: d /\ compatible d t.
  Proof.
    intro e.
    induction e; intros Rho Gamma t0 HG HW.
    * destruct (Gamma n) eqn:Heq.
        - exists D. split. apply Rule_Var.
          rewrite Heq. reflexivity.
          eapply compatibility in HW. apply HW.
          eassumption. eapply Rule_Var. assumption.
        - exists ND. split. apply Rule_Var.
          rewrite Heq. reflexivity. reflexivity.
        - exists (Arrow d1 d2). split. apply Rule_Var.
          rewrite Heq. reflexivity.
          eapply compatibility in HW. apply HW.
          eassumption. eapply Rule_Var. assumption.
    * exists D. split. apply Rule_BTrue.
      simpl in HW. inversion HW. reflexivity.
    * exists D. split. apply Rule_BFalse.
      simpl in HW. inversion HW. reflexivity.
    * exists D. split. apply Rule_Nil.
      simpl in HW. inversion HW. reflexivity.
    * destruct_typeOf_chain HW.
      destruct (IHe1 Rho Gamma t2 HG Heq2), H,
               (IHe2 Rho Gamma _ HG Heq1), H1.
      eexists. split.
      eapply Rule_Cons; try eassumption; try reflexivity.
      destruct x, x0; reflexivity.
    * destruct_typeOf_chain HW.
      destruct (IHe1 Rho Gamma (TArrow t1_1 t0) HG Heq1), H,
               (IHe2 Rho Gamma t1_1 HG Heq2), H1, x.
      - eapply compatibility with (t:= TArrow _ _) in H.
        inversion H. eassumption. apply Heq1.
      - exists ND. split. eapply Rule_AppND.
        apply H. apply H1. reflexivity.
      - eexists. split. eapply Rule_AppFun.
        apply H. apply H1.
        reflexivity. destruct H0.
        unfold decide. destruct (more_specific x0 x1) eqn:Heq4.
        assumption. reflexivity.
    * destruct_typeOf_chain HW.
      edestruct (IHe (update Nat.eqb Rho n t)
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
      destruct (IHe1 Rho Gamma t0 HG Heq1), H,
               (IHe2 Rho Gamma t0 HG Heq0), H1.
      exists ND. split. eapply Rule_Choice. apply H. apply H1.
      reflexivity.
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
      eapply Rule_CaseList with (d1 := ND);
      try eassumption. reflexivity.
      apply compatible_lub; try assumption.
      destruct x; inversion H0; reflexivity.
      rewrite double_update_indep; trivial.
      apply update_compatible; trivial.
      apply update_compatible; trivial.
  Qed.

  Lemma hasDType_unbound : forall e Gamma d1 d2 n,
    Gamma |- e ::: d1 ->
    anyIn (freeVars e) [n] = false ->
    update Nat.eqb Gamma n d2 |- e ::: d1.
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
      destruct d0 eqn:HeqD0, d3 eqn:HeqD3;
      eapply Rule_Cons with (d1 := d0) (d2 := d3); subst;
      try apply (IHe1 Gamma _ _ n); try eassumption;
      try apply (IHe2 Gamma _ _ n); try eassumption;
      try reflexivity.
    - unfold freeVars in H0. fold freeVars in H0.
      apply anyIn_concat2 in H0. destruct H0 as [H0_1 H0_2].
      inversion H; subst; simpl in *.
      + eapply IHe1 in H3; eauto. eapply IHe2 in H5; eauto.
        eapply Rule_AppND; eauto.
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
      apply IHe1; assumption. apply H8. apply H10.
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
  Qed.

  (* Lemma subst_lemma:
   A key substitution lemma showing that if a well-typed expression e1 has a
   determinism type d2, and we substitute a well-typed expression e2 with
   compatible determinism type, then the result maintains a determinism type
   that is at least as specific as the original. *)
  Lemma subst_lemma : forall e1 e2 Rho Gamma t2 d2 d1 d3 n,
    anyIn (freeVars e2) (n::boundVars e1) = false ->
    well_typed (update Nat.eqb Rho n t2) e1 ->
    typeOf Rho e2 = Some t2 ->
    compatibleCtx Gamma Rho ->
    compatible d2 t2 ->
    update Nat.eqb Gamma n d2 |- e1 ::: d1 ->
    more_specific d3 d2 = true ->
    Gamma |- e2 ::: d3 ->
    exists d4,
      more_specific d4 d1 = true /\
      Gamma |- subst n e2 e1 ::: d4.
  Proof.
    induction e1; intro;
    intros Rho Gamma t2 d2 d1 d3 n0 H H0 H1 H3 H4; intros.
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
      exists D. split. apply more_specific_refl.
      apply Rule_BTrue.
    - inversion H2. subst. simpl in *.
      exists D. split. apply more_specific_refl.
      apply Rule_BFalse.
    - inversion H2. subst. simpl in *.
      exists D. split. apply more_specific_refl.
      apply Rule_Nil.
    - inversion H2. subst. simpl in *.
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_concat1 in HH1. destruct HH1 as [HH3 HH4].
      apply well_typed_subterms in H0. destruct H0 as [H0_1 H0_2].
      edestruct IHe1_1 in H9; try eassumption.
      apply anyIn_cons. split; eassumption.
      edestruct IHe1_2 in H11; try eassumption.
      apply anyIn_cons. split; eassumption.
      destruct H, H0. eexists. split.
      shelve. eapply Rule_Cons; eauto. Unshelve.
      destruct x, x0, d0, d4; try inversion H;
      try inversion H0; try rewrite H12; try reflexivity.
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
        * eapply (subst_preservation Rho) in Heq1.
          eapply (compatibility _ _ _ _ _ H3 Heq1) in H8. inversion H8.
          apply anyIn_cons. split; assumption.
          assumption.
        * eexists. split. apply more_specific_ND.
          eapply Rule_AppND. apply H8. apply H10.
        * eexists. split. apply more_specific_ND.
          eapply Rule_AppFun. apply H8. apply H10.
          reflexivity.
      + edestruct IHe1_1 in H5;
        try apply anyIn_cons;
        try split; try eassumption.
        unfold well_typed. rewrite Heq1. reflexivity.
        edestruct IHe1_2 in H8; try apply anyIn_cons; try split; try eassumption.
        unfold well_typed. rewrite Heq2. reflexivity.
        destruct H, H7, x; simpl.
        * inversion H.
        * inversion H.
        * eexists. split. shelve.
          eapply Rule_AppFun. apply H9. apply H11. reflexivity.
          Unshelve. simpl in H. apply andb_true_iff in H.
          destruct H. unfold decide.
          destruct (more_specific d5 d0) eqn:Heq4;
          try apply more_specific_ND.
          rewrite less_specific_more_specific in H.
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
        Unshelve. simpl. rewrite less_specific_refl. rewrite more_specific_refl. reflexivity.
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
        simpl. rewrite less_specific_refl.
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
      exists ND. split. apply more_specific_ND.
      simpl. eapply Rule_Choice; eassumption.
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
      * apply more_specific_lub; try assumption.
        destruct_typeOf_chain HC.
        remember Heq1 as Heq1C. clear HeqHeq1C.
        eapply compatibility in Heq1. shelve.
        shelve. apply H11. Unshelve.
        -- eapply subst_preservation in H1; try eassumption.
           eapply compatibility in H1; eassumption.
           apply anyIn_cons. split; assumption.
        -- apply update_compatible; assumption.
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
      edestruct IHe1_1 in H0_1.
      apply anyIn_cons. split; try eassumption.
      rewrite Heq1. reflexivity. eassumption. eassumption.
      eassumption. eassumption. eassumption. eassumption.
      destruct H. edestruct IHe1_2 in H0_2.
      apply anyIn_cons. split; try eassumption.
      rewrite Heq2. reflexivity. eassumption. eassumption.
      eassumption. eassumption. eassumption. eassumption.
      destruct H8, (n0 =? n1) eqn:HeqN1,
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
            eapply compatibility in H0. shelve.
            eassumption.
            eapply subst_preservation.
            apply anyIn_cons. split; assumption.
            apply Heq1. apply H1.
            apply more_specific_refl.
            Unshelve. destruct x;
            try reflexivity; try inversion H0.
        --  simpl. eapply Rule_CaseList; try eassumption.
            rewrite double_update_indep; try eassumption.
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
            eapply compatibility in H0. shelve.
            eassumption.
            eapply subst_preservation.
            apply anyIn_cons. split; assumption.
            apply Heq1. apply H1.
            apply more_specific_refl.
            Unshelve. destruct x;
            try reflexivity; try inversion H0.
        --  eapply Rule_CaseList; try eassumption.
            rewrite double_update_indep; try eassumption.
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
          eapply compatibility with (t:=TList _) in H0; eauto.
          destruct x; try reflexivity; try inversion H0.
          eapply subst_preservation; eauto.
          apply anyIn_cons. split; assumption.
          apply update_compatible; eassumption.
        * simpl. eapply Rule_CaseList; eassumption.
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
    forall e1 e2 e3 Rho Gamma t2 t3 d1 d2 d3 n2 n3 d2' d3',
    anyIn (freeVars e2) (n3::n2::boundVars e1) = false ->
    anyIn (freeVars e3) (n3::n2::boundVars e1) = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    well_typed (update Nat.eqb (update Nat.eqb Rho n3 t3) n2 t2) e1 ->
    typeOf Rho e2 = Some t2 ->
    typeOf Rho e3 = Some t3 ->
    n2 <> n3 ->
    compatibleCtx Gamma Rho ->
    compatible d2 t2 ->
    compatible d3 t3 ->
    update Nat.eqb (update Nat.eqb Gamma n3 d3) n2 d2 |- e1 ::: d1 ->
    more_specific d2' d2 = true ->
    more_specific d3' d3 = true ->
    Gamma |- e2 ::: d2' ->
    Gamma |- e3 ::: d3' ->
    exists d4,
      more_specific d4 d1 = true /\
      Gamma |- subst n2 e2 (subst n3 e3 e1) ::: d4.
  Proof.
    intros.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H0. destruct H0.
    apply anyIn_cons in H0. destruct H0.
    destruct_typeOf_chain H2.
    edestruct subst_lemma with (e1 := e1) (n := n3).
    + apply anyIn_cons. split. apply H0. apply H16.
    + unfold well_typed.
      rewrite double_update_indep in Heq1.
      rewrite Heq1. reflexivity. symmetry. assumption.
    + erewrite typeOf_unbound. apply H4. apply H4. assumption.
    + eapply (update_compatible _ (Rho)). eassumption.
      eassumption.
    + apply H8.
    + rewrite double_update_indep in H9.
      apply H9. symmetry. assumption.
    + eassumption.
    + apply hasDType_unbound; assumption.
    + destruct H18.
      edestruct subst_lemma with (e1 := subst n3 e3 e1) (n := n2).
      - apply anyIn_cons. split. apply anyIn_subst. apply H.
        apply H16. apply H1. apply H15.
      - unfold well_typed.
        erewrite subst_preservation. reflexivity.
        apply anyIn_cons. split; assumption.
        rewrite double_update_indep.
        rewrite Heq1. reflexivity. assumption.
        erewrite typeOf_unbound; eassumption.
      - assumption.
      - apply H6.
      - apply H7.
      - apply H19.
      - eassumption.
      - eassumption.
      - destruct H20. exists x0. split.
        eapply more_specific_transitive; eassumption.
        apply H21.
  Qed.

  (* Theorem preservation:
   Shows that if an expression e reduces to e', then the determinism type
   of e' is at least as specific as the determinism type of e.
   This is the core type safety property for the determinism type system. *)
  Theorem preservation : forall e e' Rho Gamma t d,
    compatibleCtx Gamma Rho ->
    e ==> e' ->
    typeOf Rho e = Some t ->
    compatible d t ->
    Gamma |- e ::: d ->
    exists d', more_specific d' d = true /\ compatible d' t
      /\ Gamma |- e' ::: d'.
  Proof.
    induction e; intros e' Rho Gamma t0 d0 HX H HW HC H0; inversion H.
    * inversion H1.
    * inversion H1.
    * inversion H1.
    * inversion H1.
    * inversion H1. inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct (step e1) eqn:Heq.
      + inversion H5. subst.
        edestruct IHe1. eassumption.
        apply Single_Step. apply Heq. eassumption.
        eapply compatibility; eassumption.
        apply H7. destruct H2, H3.
        eexists. split. shelve. split. shelve.
        eapply Rule_Cons. eassumption. eassumption.
        reflexivity. Unshelve.
        destruct d1, d2, x; try reflexivity;
        try inversion H8; try inversion H2.
        destruct x, d2; reflexivity.
      + destruct (step e2) eqn:Heq4; inversion H5.
        subst.
        edestruct IHe2. eassumption.
        apply Single_Step. apply Heq4. eassumption.
        eapply compatibility. eassumption.
        apply Heq1. eassumption.
        apply H9. destruct H2, H3.
        eexists. split. shelve. split. shelve.
        eapply Rule_Cons. apply H7. apply H4.
        reflexivity. Unshelve.
        destruct d1, d2, x; try reflexivity;
        try inversion H8; try inversion H2.
        destruct x, d1; reflexivity.
    * inversion H1. subst.
      remember H1 as H1C. clear HeqH1C.
      destruct_typeOf_chain HW.
      destruct e1 eqn:Heq5.
      + simpl in H5. inversion H5.
      + inversion H5.
      + inversion H5.
      + inversion H5.
      (* App Cons *)
      + destruct_typeOf_chain Heq1.
      (* App App *)
      + destruct (step (App e3 e4)) eqn:Heq;
        inversion H5.
        inversion H0; subst.
        - edestruct IHe1 with (d := ND).
          eassumption.
          apply Single_Step. apply Heq. eassumption.
          eapply (compatibility (App e3 e4)).
          eassumption. assumption.
          assumption. assumption.
          destruct H2, H3, x.
          --  inversion H3.
          --  exists ND. split. apply more_specific_ND.
              split. reflexivity.
              eapply Rule_AppND; eassumption.
          --  eexists (decide x1 d x2). split.
              apply more_specific_ND. split.
              unfold decide. destruct (more_specific d x1).
              destruct H3. assumption. reflexivity.
              eapply Rule_AppFun. apply H4 . apply H9. reflexivity.
        - edestruct IHe1 with (d := (Arrow d1 d2)).
          eassumption.
          apply Single_Step. apply Heq. eassumption.
          eapply (compatibility (App e3 e4)).
          eassumption. assumption.
          assumption. assumption.
          destruct H2, H3, x.
          --  inversion H3.
          --  inversion H2.
          --  simpl in H2. apply (andb_true_iff) in H2.
              destruct H2, H3.
              unfold decide. destruct (more_specific d3 d1) eqn:Heq4.
              ++  exists x2. split. assumption. split.
                  assumption. eapply Rule_AppFun.
                  eassumption. eassumption. unfold decide.
                  erewrite more_specific_transitive.
                  reflexivity. eassumption.
                  rewrite more_specific_less_specific.
                  assumption.
              ++  exists (decide x1 d3 x2). split.
                  apply more_specific_ND. split.
                  unfold decide. destruct (more_specific d3 x1).
                  assumption. reflexivity.
                  eapply Rule_AppFun; try eassumption.
                  reflexivity.
      (* App Abs *)
      + inversion H5. subst.
        destruct_typeOf_chain Heq1.
        destruct (anyIn (freeVars e2) (n :: boundVars e)) eqn:Heq7;
        try discriminate. inversion H5. subst.
        inversion H0.
        - inversion H7.
        - inversion H6; subst. unfold decide in *.
          destruct (more_specific d3 d1) eqn:Heq5.
          --  edestruct subst_lemma. eassumption.
              unfold well_typed. rewrite Heq0. reflexivity.
              assumption. eassumption. eassumption.
              eassumption. apply Heq5. assumption.
              destruct H2. eexists. split. apply H2.
              split. eapply compatibility. eassumption.
              eapply subst_preservation. eassumption.
              eassumption. assumption. assumption. assumption.
          --  edestruct completeness. eassumption.
              eapply subst_preservation; eassumption.
              destruct H2. eexists. split.
              apply more_specific_ND. split. apply H4. apply H2.
      (* App Or *)
      + destruct d0.
        - inversion H0; inversion H4.
        - inversion H0; try inversion H4.
          exists ND. split. apply more_specific_ND.
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
        - inversion H0; inversion H4.
      (* App Case *)
      + destruct (step (CaseB e3 e4 e5)) eqn:Heq;
        inversion H5; subst; inversion H0; subst.
        - edestruct IHe1. eassumption. apply Single_Step. apply Heq.
          rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H3.
          destruct x.
          --  inversion H3.
          --  exists ND. split. apply more_specific_ND.
              split. reflexivity.
              eapply Rule_AppND; eassumption.
          --  exists (decide x1 d x2). split.
              apply more_specific_ND. split.
              unfold decide. destruct (more_specific d x1).
              destruct H3. assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
        - edestruct IHe1. eassumption. apply Single_Step.
          apply Heq. rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H3, x.
          --  inversion H3.
          --  inversion H2.
          --  simpl in H2. apply (andb_true_iff) in H2.
              destruct H2, H3.
              rewrite <- more_specific_less_specific in H2.
              exists (decide x1 d3 x2). split. unfold decide.
              destruct (more_specific d3 x1) eqn:M1,
                       (more_specific d3 d1) eqn:M2;
              try assumption; try apply more_specific_ND.
              apply more_specific_transitive
                with (d1:=d3) (d2:=d1) (d3:=x1) in M2.
              rewrite M1 in M2. inversion M2. assumption.
              split. unfold decide. destruct (more_specific d3 x1).
              assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
      + destruct (step (CaseL e3 e4 p e5)) eqn:Heq;
        inversion H5; subst; inversion H0; subst.
        - edestruct IHe1. eassumption. apply Single_Step. apply Heq.
          rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H3, x.
          --  inversion H3.
          --  exists ND. split. apply more_specific_ND.
              split. reflexivity.
              eapply Rule_AppND; eassumption.
          --  exists (decide x1 d x2). split. apply more_specific_ND.
              split. unfold decide. destruct (more_specific d x1).
              destruct H3. assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
        - edestruct IHe1. eassumption. apply Single_Step.
          apply Heq. rewrite Heq1. reflexivity. eapply compatibility.
          eassumption. apply Heq1. eassumption. assumption.
          destruct H2, H3, x.
          --  inversion H3.
          --  inversion H2.
          --  simpl in H2. apply (andb_true_iff) in H2.
              destruct H2, H3.
              rewrite <- more_specific_less_specific in H2.
              exists (decide x1 d3 x2). split. unfold decide.
              destruct (more_specific d3 x1) eqn:M1,
                       (more_specific d3 d1) eqn:M2;
              try assumption; try apply more_specific_ND.
              apply more_specific_transitive
                with (d1:=d3) (d2:=d1) (d3:=x1) in M2.
              rewrite M1 in M2. inversion M2. assumption.
              split. unfold decide. destruct (more_specific d3 x1).
              assumption. reflexivity.
              eapply Rule_AppFun; try eassumption. reflexivity.
    * inversion H1.
    (* Or *)
    * inversion H1. inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct (step e1) eqn:Heq3.
      + inversion H5. subst.
        edestruct IHe1. eassumption. apply Single_Step. eassumption.
        eassumption. shelve. eassumption.
        destruct H2, H3. exists ND. split. apply more_specific_refl.
        split. reflexivity. eapply Rule_Choice; eassumption.
        Unshelve. eapply (compatibility e1). eassumption.
        apply Heq1. eassumption.
      + destruct (step e2) eqn:Heq4; inversion H5. subst.
        edestruct IHe2. eassumption. apply Single_Step. eassumption.
        eassumption. shelve. eassumption.
        destruct H2, H3. exists ND. split. apply more_specific_refl.
        split. reflexivity. eapply Rule_Choice; eassumption.
        Unshelve. eapply (compatibility e2). eassumption.
        assumption. eassumption.
    (* Case *)
    * inversion H1. inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct e1; inversion H5; subst.
      + eexists. split. apply more_specific_lub3. split.
        eapply compatibility. apply HX. apply Heq3. eassumption.
        eassumption.
      + eexists. split. apply more_specific_lub2. split.
        eapply compatibility. apply HX. apply Heq2. eassumption.
        eassumption.
      + inversion H9. subst. exists ND. split.
        destruct d2, d3; reflexivity.
        split. reflexivity.
        destruct_typeOf_chain Heq1.
        edestruct (completeness (CaseB e1_2 e2 e3)).
        eassumption. unfold well_typed. simpl.
        rewrite Heq5, Heq2, Heq3, eqType_refl. reflexivity.
        destruct H2. edestruct (completeness (CaseB e1_1 e2 e3)).
        eassumption. unfold well_typed. simpl.
        rewrite Heq0, Heq2, Heq3. rewrite eqType_refl. reflexivity.
        destruct H4. eapply Rule_Choice; eapply Rule_CaseBool; eassumption.
    * destruct p. inversion H1. inversion H0. subst.
      destruct_typeOf_chain HW.
      destruct e1; inversion H5; subst.
      + eexists. split. apply more_specific_lub2. split.
        eapply compatibility. apply HX. apply Heq2. eassumption.
        apply H19.
      + destruct (anyIn (freeVars e1_1 ++ freeVars e1_2)
                    (n1 :: n2 :: boundVars e3)) eqn:Heq6;
        try discriminate.
        destruct (anyIn (freeVars e1_2) (boundVars e1_1)) eqn:Heq7;
        try discriminate. inversion H3. subst.
        apply anyIn_concat2 in Heq6. destruct Heq6.
        destruct_typeOf_chain Heq1.
        inversion H16. subst. subst Gamma'. subst Gamma''.
        specialize (compatibility _ _ _ _ _ HX Heq8 H10) as H22.
        specialize (compatibility _ _ _ _ _ HX Heq5 H12) as H23.
        specialize (compatibility _ _ _ _ _ HX Heq2 H19) as H24.
        rewrite double_update_indep in Heq3; try symmetry; try assumption.
        specialize (update_update_compatible _ _ n1 n2 _ _ _ _ HX H17 H18) as HXC.
        specialize (compatibility _ _ _ _ _ HXC Heq3 H20)  as H25.
        destruct (more_specific d3 d2) eqn:Heq11,
                 (more_specific d0 d1) eqn:Heq12.
        --- edestruct subst_lemma2. apply H6. apply H2.
            apply Heq7. unfold well_typed.
            rewrite Heq3. reflexivity.
            assumption. assumption. symmetry. assumption.
            eassumption. apply H18. apply H17.
            apply H20. apply Heq11. apply Heq12. apply H12.
            apply H10. destruct H7. exists x. split.
            **  destruct d0.
                --  destruct d3.
                    ++  destruct d_2, d_3; unfold lub, lub2; simpl;
                        try apply more_specific_ND. apply H7.
                    ++  destruct d_2, d_3; simpl;
                        apply more_specific_ND.
                    ++  destruct d_2, d_3; simpl;
                        apply more_specific_ND.
                --  destruct d_2, d_3; simpl; apply more_specific_ND.
                --  destruct d_2, d_3; simpl; apply more_specific_ND.
            **  split. eapply compatibility. apply HX.
                eapply subst_preservation2. apply H6. apply H2.
                apply Heq7. symmetry. assumption. rewrite Heq3.
                reflexivity. assumption. assumption. assumption.
                assumption.
        --- destruct t1, d0, d1; try inversion Heq12;
            try inversion H17; try inversion H22.
            +++ edestruct completeness. apply HX.
                eapply subst_preservation2.
                apply H6. apply H2. assumption. symmetry. assumption.
                rewrite Heq3. reflexivity. assumption. assumption.
                destruct H7. exists x.
                split. destruct d_2, d_3; apply more_specific_ND.
                split. assumption. assumption.
            +++ edestruct completeness. apply HX.
                eapply subst_preservation2.
                apply H6. apply H2. assumption. symmetry. assumption.
                rewrite Heq3. reflexivity. assumption. assumption.
                destruct H7. exists x.
                split. destruct d_2, d_3; apply more_specific_ND.
                split. assumption. assumption.
            +++ edestruct completeness. apply HX.
                eapply subst_preservation2.
                apply H6. apply H2. assumption. symmetry. assumption.
                rewrite Heq3. reflexivity. assumption. assumption.
                destruct H11. exists x.
                split. destruct d_2, d_3; apply more_specific_ND.
                split. assumption. assumption.
            +++ edestruct completeness. apply HX.
                eapply subst_preservation2.
                apply H6. apply H2. assumption. symmetry. assumption.
                rewrite Heq3. reflexivity. assumption. assumption.
                destruct H21. exists x.
                split. destruct d_2, d_3; apply more_specific_ND.
                split. assumption. assumption.
        --- destruct d3, d2; try inversion Heq11;
            try inversion H23; try inversion H18.
            edestruct completeness. apply HX.
            eapply subst_preservation2.
            apply H6. apply H2. assumption. symmetry. assumption.
            rewrite Heq3. reflexivity. assumption. assumption.
            destruct H7. exists x.
            split. destruct d0, d_2, d_3; apply more_specific_ND.
            split. assumption. assumption.
        --- destruct d3, d2; try inversion Heq11;
            try inversion H23; try inversion H18.
            edestruct completeness. apply HX.
            eapply subst_preservation2.
            apply H6. apply H2. assumption. symmetry. assumption.
            rewrite Heq3. reflexivity. assumption. assumption.
            destruct H7. exists x.
            split. destruct d0, d_2, d_3; apply more_specific_ND.
            split. assumption. assumption.
      + inversion H16. subst. exists ND. split.
        destruct d_2, d_3; reflexivity.
        split. reflexivity.
        destruct_typeOf_chain Heq1.
        edestruct (completeness (CaseL e1_2 e2 (Pat n1 t1 n2 n) e3)).
        eassumption. unfold well_typed. simpl.
        rewrite Heq6, Heq3, Heq2, eqTypeS_refl, eqTypeS_refl.
        reflexivity. destruct H2.
        edestruct (completeness (CaseL e1_1 e2 (Pat n1 t1 n2 n) e3)).
        eassumption. unfold well_typed. simpl.
        rewrite Heq5, Heq3, Heq2, eqTypeS_refl, eqTypeS_refl.
        reflexivity. destruct H6.
        eapply Rule_Choice; eapply Rule_CaseList; eassumption.
  Qed.

  Theorem preservation_multi : forall e e' t,
    e ==>* e' ->
    forall Rho Gamma d,
    compatibleCtx Gamma Rho ->
    typeOf Rho e = Some t ->
    compatible d t ->
    Gamma |- e ::: d ->
    exists d', more_specific d' d = true
      /\ compatible d t
      /\ Gamma |- e' ::: d'.
  Proof.
    intros e e' t H. induction H; intros.
    * exists d. split. apply more_specific_refl.
      split; assumption.
    * remember H as HC. clear HeqHC. inversion HC.
      remember H2 as H2C. clear HeqH2C.
      eapply (step_preservation _ _ _ _ H5) in H2.
      apply (preservation e1 e2 Rho Gamma t d) in H; try assumption.
      destruct H, H, H5, H8.
      destruct (IHmulti_step_rel Rho Gamma x); eauto.
      destruct H9, H10. exists x0. split.
      eapply more_specific_transitive; eauto.
      split; assumption.
  Qed.

  (* Theorem soundness:
   The main theorem showing that if an expression e has deterministic type D,
   then any expression e' that e reduces to will not be a non-deterministic choice.
   This validates that the determinism type system correctly tracks non-determinism. *)
  Theorem soundness : forall Rho Gamma e e' t,
    compatibleCtx Gamma Rho ->
    typeOf Rho e = Some t ->
    Gamma |- e ::: D ->
    compatible D t ->
    e ==>* e' ->
    notOr e'.
  Proof.
    intros. destruct (preservation_multi e e' t H3
                          Rho Gamma D H H0 H2 H1).
    destruct H4, H5. apply more_specific_D in H4.
    subst. destruct e'; try reflexivity; try inversion H6.
  Qed.

End Proofs.
