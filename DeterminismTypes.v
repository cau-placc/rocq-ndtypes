Require Import Strings.String Lists.List Lists.ListSet PeanoNat EqNat Bool FunctionalExtensionality Coq.Program.Equality.
Import ListNotations.

(**
NOTE: due to time constraints, the formalization is not yet fully updated
to the paper. Should be updated by mid June. Differences are:
- A different simplified Curry type system with only types Unit and Pairs.
  Consequently, our expressions have different data constructors as well.
- Compatibility is used differently, in the sense that we constructively
  build compatible types and contexts, rather than using a
  compatibility relation.

For the reason that we still have to update the formalization,
there are currently two small sections where this formalization
is not yet completely machine-checked. We will address this in the near future.
These points are the application of the substitution lemma on determinsm
types in the preservation theorem for case and function application.
At the moment, there is a consistency problem between the way compatibility
is used in the preservation theorem statement and the way it is used in the
substitution lemma.

Other than these differences, you can check that this corresponds to the paper.
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

  Definition Arity := nat.

  Inductive TType : Type :=
    | TUnit : TType
    | TPair : TType -> TType -> TType
    | TArrow : TType -> TType -> TType.

  Inductive Pattern : Type :=
    | Pat : forall (n1 : nat) (t1 : TType) (n2 : nat) (t2 : TType)
          , n1 <> n2 -> Pattern.

  Inductive Exp : Type :=
    | Var : nat -> Exp
    | Unit : Exp
    | Pair : Exp -> Exp -> Exp
    | App : Exp -> Exp -> Exp
    | Abs : nat -> TType -> Exp -> Exp
    | Or  : Exp -> Exp -> Exp
    | Case: Exp -> Branch -> Exp
   with Branch : Type :=
     | BranchUnit :            Exp -> Branch
     | BranchPair : Pattern -> Exp -> Branch.

  Scheme Exp_Branch_mut := Induction for Exp Sort Prop
    with   Branch_Exp_mut := Induction for Branch Sort Prop.

  Combined Scheme ExpBranch_mutind from Exp_Branch_mut, Branch_Exp_mut.

  Definition notOr (e : Exp) : Prop :=
    match e with
    | Or _ _ => False
    | _ => True
    end.

  Fixpoint eqType (t1 t2 : TType) : bool :=
    match t1, t2 with
    | TUnit, TUnit => true
    | TPair t11 t12, TPair t21 t22 =>
        andb (eqType t11 t21) (eqType t12 t22)
    | TArrow t11 t12, TArrow t21 t22 =>
        andb (eqType t11 t21) (eqType t12 t22)
    | _, _ => false
    end.

  Lemma eqType_refl : forall t,
    eqType t t = true.
  Proof.
    induction t; simpl; try reflexivity.
    - rewrite IHt1. rewrite IHt2. reflexivity.
    - rewrite IHt1. rewrite IHt2. reflexivity.
  Qed.

  Lemma eq_Type_eq : forall t1 t2,
    eqType t1 t2 = true <-> t1 = t2.
  Proof.
    intros. split.
    - intros. generalize dependent t2. induction t1; intros.
      + destruct t2; try discriminate. reflexivity.
      + destruct t2; try discriminate. simpl in H.
        apply Bool.andb_true_iff in H. destruct H.
        apply IHt1_1 in H. apply IHt1_2 in H0.
        subst. reflexivity.
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
    | Unit => Some TUnit
    | Pair e1 e2 => match (typeOf c e1), (typeOf c e2) with
                    | Some t1, Some t2 => Some (TPair t1 t2)
                    | _, _ => None
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
    | Case e1 brs => match brs, typeOf c e1 with
                    | BranchUnit e2, Some TUnit => typeOf c e2
                    | BranchPair (Pat n1 t1 n2 t2 H) e2,
                      Some (TPair t1' t2') =>
                        let c'  := update Nat.eqb c  n1 t1 in
                        let c'' := update Nat.eqb c' n2 t2 in
                        if eqType t1 t1' && eqType t2 t2'
                          then typeOf c'' e2
                          else None
                    | _, _ => None
                    end
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
    | D, TUnit => True
    | D, TPair t1 t2 => True
    | ND, _ => True
    | Arrow d1 d2, TArrow t1 t2 =>
        compatible d1 t1 /\ compatible d2 t2
    | _, _ => False
    end.

  Fixpoint mkCompatible (t : TType) : DType :=
    match t with
    | TUnit => D
    | TPair t1 t2 => D
    | TArrow t1 t2 => Arrow (mkCompatible t1) (mkCompatible t2)
    end.

  Lemma mkCompatible_compatible : forall t,
    compatible (mkCompatible t) t.
  Proof.
    induction t; simpl; try constructor; auto.
  Qed.

  Fixpoint beq_DType (d1 d2 : DType) : bool :=
    match d1, d2 with
    | D, D => true
    | ND, ND => true
    | Arrow d1 d2, Arrow d1' d2' => andb (beq_DType d1 d1') (beq_DType d2 d2')
    | _, _ => false
    end.

End Types.

(* Section Context:
   Defines typing contexts and compatibility between traditional and
   determinism type contexts. Includes operations to create compatible contexts
   and lemmas about context updates. *)
Section Context.

  Definition context := total_map nat DType.
  Definition contextT := total_map nat TType.

  Definition compatibleCtx (c : context) (cT : contextT) : Prop :=
    forall n, compatible (c n) (cT n).

  Definition mkCompatibleCtx : contextT -> context :=
    fun c => fun n =>  mkCompatible (c n).

  Lemma update_compatible :
    forall Gamma Rho n t,
    Gamma = mkCompatibleCtx Rho ->
    update Nat.eqb Gamma n (mkCompatible t) =
    mkCompatibleCtx (update Nat.eqb Rho n t).
  Proof.
    intros. apply functional_extensionality. intro x.
    unfold mkCompatibleCtx. unfold update.
    destruct (Nat.eqb n x) eqn:Heq.
    - reflexivity.
    - unfold mkCompatibleCtx in H. rewrite H. reflexivity.
  Qed.

  Lemma update_update_compatible :
    forall Gamma Rho n1 n2 t1 t2,
    Gamma = mkCompatibleCtx Rho ->
    let Gamma' := update Nat.eqb Gamma n1 (mkCompatible t1) in
    update Nat.eqb Gamma' n2 (mkCompatible t2) =
    mkCompatibleCtx (update Nat.eqb (update Nat.eqb Rho n1 t1) n2 t2).
  Proof.
    intros. apply functional_extensionality. intro x.
    unfold mkCompatibleCtx. unfold update.
    destruct (Nat.eqb n1 x) eqn:Heq1;
    destruct (Nat.eqb n2 x) eqn:Heq2; try reflexivity.
    - subst Gamma'. unfold update.
      rewrite Heq1. reflexivity.
    - subst Gamma'. unfold update.
      rewrite Heq1. unfold mkCompatibleCtx in H.
      rewrite H. reflexivity.
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
      erewrite less_specific_transitive.
      erewrite more_specific_transitive.
      reflexivity.
      apply H.
      apply H0.
      apply H1.
      apply H2.
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

(* Section DetTyping:
   Defines the typing rules for determinism types.
   These rules capture when an expression has a particular determinism type,
   connecting the operational behavior with static determinism properties. *)
Section DetTyping.

  Fixpoint d_fun (n : Arity) : DType :=
    match n with
    | 0 => D
    | S m => Arrow D (d_fun m)
    end.

  Reserved Notation "Gamma '|-' e ':::' delta" (at level 40).
  Inductive hasDType : context -> Exp -> DType -> Prop :=
    | Rule_Var : forall Gamma x d,
          (Gamma x) = d ->
          Gamma |- Var x ::: d
    | Rule_Unit : forall Gamma d,
          d = d_fun 0 ->
          Gamma |- Unit ::: d
    | Rule_Pair : forall Gamma e1 e2 d1 d2 d3,
          Gamma |- e1 ::: d1 ->
          Gamma |- e2 ::: d2 ->
          d3 = match d1, d2 with
              | D, D => D
              | _, _ => ND
              end ->
          Gamma |- Pair e1 e2 ::: d3
    | Rule_AppND : forall Gamma e1 e2 d1 d2,
          Gamma |- e1 ::: d1 ->
          Gamma |- e2 ::: d2 ->
          Gamma |- App e1 e2 ::: ND
    | Rule_AppFun : forall Gamma e1 e2 d1 d2 d3 d4,
          Gamma |- e1 ::: Arrow d1 d2 ->
          Gamma |- e2 ::: d3 ->
          d4 = decide d1 d3 d2 ->
          Gamma |- App e1 e2 ::: d4
    | Rule_Abs : forall Gamma x e d1 d2 t,
          d1 = mkCompatible t ->
          let Gamma' := update Nat.eqb Gamma x d1 in
          Gamma' |- e ::: d2 ->
          Gamma |- Abs x t e ::: Arrow d1 d2
    | Rule_Choice : forall Gamma e1 e2 d1 d2,
          Gamma |- e1 ::: d1 ->
          Gamma |- e2 ::: d2 ->
          Gamma |- Or e1 e2 ::: ND
    | Rule_CaseNDUnit : forall Gamma e1 e2 d,
          Gamma |- e1 ::: ND ->
          Gamma |- e2 ::: d ->
          Gamma |- Case e1 (BranchUnit e2) ::: ND
    | Rule_CaseNDPair : forall Gamma e1 e2 n1 n2 t1 t2 d H,
          Gamma |- e1 ::: ND ->
          let Gamma'  := update Nat.eqb Gamma  n1 (mkCompatible t1) in
          let Gamma'' := update Nat.eqb Gamma' n2 (mkCompatible t2) in
          Gamma'' |- e2 ::: d ->
          let p := Pat n1 t1 n2 t2 H in
          Gamma |- Case e1 (BranchPair p e2) ::: ND
    | Rule_CaseDUnit : forall Gamma e1 e2 d,
          Gamma |- e1 ::: D ->
          Gamma |- e2 ::: d ->
          Gamma |- Case e1 (BranchUnit e2) ::: d
    | Rule_CaseDPair : forall Gamma e1 e2 n1 n2 t1 t2 d H,
          Gamma |- e1 ::: D ->
          let Gamma'  := update Nat.eqb Gamma  n1 (mkCompatible t1) in
          let Gamma'' := update Nat.eqb Gamma' n2 (mkCompatible t2) in
          Gamma'' |- e2 ::: d ->
          let p := Pat n1 t1 n2 t2 H in
          Gamma |- Case e1 (BranchPair p e2) ::: d
    where "Gamma '|-' e ':::' delta" := (hasDType Gamma e delta).

End DetTyping.

(* Section SmallStepSemantics:
   Defines the operational semantics of the language using a small-step
   reduction relation. Includes substitution functions and free/bound variable tracking. *)
Section SmallStepSemantics.

  Fixpoint subst (n : nat) (v : Exp) (e : Exp) : Exp :=
    match e with
    | Var x => if Nat.eqb x n then v else e
    | Unit => Unit
    | Pair e1 e2 => Pair (subst n v e1) (subst n v e2)
    | App e1 e2 => App (subst n v e1) (subst n v e2)
    | Abs x t e => if Nat.eqb x n
                    then Abs x t e
                    else Abs x t (subst n v e)
    | Or e1 e2 => Or (subst n v e1) (subst n v e2)
    | Case e br => Case (subst n v e)
      (match br with
        | BranchUnit e2 =>
            BranchUnit (subst n v e2)
        | BranchPair (Pat n1 t1 n2 t2 H) e2 =>
            if Nat.eqb n n1 || Nat.eqb n n2
              then BranchPair (Pat n1 t1 n2 t2 H) e2
              else BranchPair (Pat n1 t1 n2 t2 H) (subst n v e2)
        end)
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
    | Unit => []
    | Pair e1 e2 => freeVars e1 ++ freeVars e2
    | App e1 e2 => freeVars e1 ++ freeVars e2
    | Abs x _ e' => removeb Nat.eqb x (freeVars e')
    | Or e1 e2 => freeVars e1 ++ freeVars e2
    | Case e' br =>
        let vars := freeVars e' in
        match br with
        | BranchUnit e'' => vars ++ freeVars e''
        | BranchPair (Pat n1 _ n2 _ _) e'' =>
            vars ++ removeb Nat.eqb n1
                    (removeb Nat.eqb n2 (freeVars e''))
        end
    end.

  Fixpoint boundVars (e : Exp) : list nat :=
    match e with
    | Var _ => []
    | Unit => []
    | Pair e1 e2 => boundVars e1 ++ boundVars e2
    | App e1 e2 => boundVars e1 ++ boundVars e2
    | Abs x _ e' => x :: boundVars e'
    | Or e1 e2 => boundVars e1 ++ boundVars e2
    | Case e' br =>
        let vars := boundVars e' in
        match br with
        | BranchUnit e'' => vars ++ boundVars e''
        | BranchPair (Pat n1 _ n2 _ _) e'' => vars ++
            n1 :: n2 :: boundVars e''
        end
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
    | Case (Or e1 e2) br =>
        Some (Or (Case e1 br) (Case e2 br))
    | Case Unit (BranchUnit e) => Some e
    | Case (Pair e1 e2)
        (BranchPair (Pat n1 t1 n2 t2 _) e3) =>
          if anyIn (freeVars (Pair e1 e2)) (n1::n2::boundVars e3)
            then None
            else if anyIn (freeVars e2) (boundVars e1)
              then None
              else Some (subst_all [(n1, e1, t1); (n2, e2, t2)] e3)
    | Or e1 e2 => match step e1 with
                  | None => match step e2 with
                            | None => None
                            | Some e2' => Some (Or e1 e2')
                            end
                  | Some e1' => Some (Or e1' e2)
                  end
    | Pair e1 e2 => match step e1 with
                    | None => match step e2 with
                              | None => None
                              | Some e2' => Some (Pair e1 e2')
                              end
                    | Some e1' => Some (Pair e1' e2)
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

  Definition Gamma1 := update Nat.eqb (fun _ => ND) 1 D.

  Example exVar : Gamma1 |- Var 1 ::: D.
  Proof.
      eapply Rule_Var.
      reflexivity.
  Qed.

  Example eFreeVar : Gamma1 |- Var 42 ::: ND.
  Proof.
      apply Rule_Var.
      reflexivity.
  Qed.

  Example exCons : Gamma1 |- Unit ::: D.
  Proof.
      apply Rule_Unit; trivial.
  Qed.

  Example exApp : Gamma1 |- App (Abs 2 TUnit (Var 2)) (Var 1) ::: D.
  Proof.
      eapply Rule_AppFun with (d1 := D) (d2 := D) (d3 := D).
      + apply Rule_Abs. reflexivity.
        apply Rule_Var.
        reflexivity.
      + apply Rule_Var. reflexivity.
      + reflexivity.
  Qed.

  Example exAppEval : App (Abs 2 TUnit (Var 2)) (Var 1) ==>* Var 1.
  Proof.
      eapply Multi_Step_Many. apply Single_Step. reflexivity. apply Multi_Step_Refl.
  Qed.

  Example exAbs : Gamma1 |- Abs 2 TUnit (Var 1) ::: Arrow D D.
  Proof.
      apply Rule_Abs. reflexivity.
      apply Rule_Var. reflexivity.
  Qed.

  Definition Gamma2 := update Nat.eqb (fun _ => ND) 1 (Arrow (Arrow D D) (Arrow D D)).

  Example exPoly : Gamma2 |- App (Var 1) (Abs 2 TUnit (Var 2)) ::: Arrow D D.
  Proof.
      eapply Rule_AppFun with (d1 := Arrow D D) (d2 := Arrow D D) (d3 := Arrow D D).
      + apply Rule_Var. reflexivity.
      + apply Rule_Abs. reflexivity.
        apply Rule_Var. reflexivity.
      + reflexivity.
  Qed.

  Example exChoice : Gamma1 |- Or (Var 1) (Var 1) ::: ND.
  Proof.
      eapply Rule_Choice.
      - apply Rule_Var. reflexivity.
      - apply Rule_Var. reflexivity.
  Qed.

  Example exCase : Gamma1 |- Case (Var 42) (BranchUnit (Var 1)) ::: ND.
  Proof.
      eapply Rule_CaseNDUnit.
      apply Rule_Var. reflexivity.
      apply Rule_Var. reflexivity.
  Qed.

  (*
  1 = allValues :? Any -> Det
  2 = \x -> id x ? not x :? Any -> Any
  result must not be of type D
  *)
  Definition RhoAV' := update Nat.eqb (fun _ => TUnit) 1 (TArrow TUnit TUnit).
  Definition RhoAV  := update Nat.eqb RhoAV' 2 (TArrow TUnit TUnit).
  Definition GammaAV := mkCompatibleCtx RhoAV.
  Example exAllValues : GammaAV |- App (Var 1) (Var 2) ::: ND.
  Proof.
      eapply Rule_AppND.
      - apply Rule_Var. reflexivity.
      - apply Rule_Var. reflexivity.
  Qed.
  Example exAllValuesNotD : not (GammaAV |- App (Var 1) (Var 2) ::: D).
  Proof.
      unfold not. intros.
      inversion H. inversion H2. inversion H4. subst.
      unfold GammaAV in *. unfold mkCompatibleCtx in *.
      unfold RhoAV in *. unfold RhoAV' in *. simpl in *.
      inversion H9. subst. unfold decide in H6. simpl in H6.
      inversion H6.
  Qed.

  (*
  The AppND rule is required to type the following example.
  1 -> not :? Det -> Det
  2 -> id :? Det -> Det
  (not ? id) :? Any
  (not ? id) True :? Any
  *)
  Definition RhoC' := update Nat.eqb (fun _ => TUnit) 1 (TArrow TUnit TUnit).
  Definition RhoC  := update Nat.eqb RhoC' 2 (TArrow TUnit TUnit).
  Definition GammaC := mkCompatibleCtx RhoC.
  Example exChoice2 : GammaC |- App (Or (Var 1) (Var 2)) Unit ::: ND.
  Proof.
      eapply Rule_AppND.
      - eapply Rule_Choice.
        + apply Rule_Var. reflexivity.
        + apply Rule_Var. reflexivity.
      - apply Rule_Unit. reflexivity.
  Qed.
  Lemma exChoice2_must_use_AppND :
  forall d,
    GammaC |- App (Or (Var 1) (Var 2)) Unit ::: d ->
    d = ND /\
    (forall d1 d2,
      ~ (GammaC |- Or (Var 1) (Var 2) ::: d1 /\ GammaC |- Unit ::: d2 /\
         exists d3 d4 d5,
           GammaC |- Or (Var 1) (Var 2) ::: Arrow d3 d4 /\
           GammaC |- Unit ::: d5 /\
           d = decide d3 d5 d4)).
  Proof.
    intros d H.
    inversion H; subst.
    - split; auto.
      intros d3 d4 [H1 [H2 [d5 [d6 [d7 [H4 [H6 H7]]]]]]].
      inversion H4.
    - inversion H2.
  Qed.

End Examples.

(* Section WellTypedness:
   Contains lemmas about well-typed terms, focusing on the
   relationship between expression structure and type safety. *)
Section WellTypedness.

  Lemma well_typed_Pair :
    forall Rho e1 e2,
    well_typed Rho (Pair e1 e2) ->
    well_typed Rho e1 /\ well_typed Rho e2.
  Proof.
    intros. unfold well_typed in *.
    unfold typeOf in H. fold typeOf in H.
    destruct (typeOf Rho e1) eqn:Heq1;
    destruct (typeOf Rho e2) eqn:Heq2;
    auto.
  Qed.

  Lemma well_typed_App :
    forall Rho e1 e2,
    well_typed Rho (App e1 e2) ->
    well_typed Rho e1 /\ well_typed Rho e2.
  Proof.
    intros. unfold well_typed in *.
    unfold typeOf in H. fold typeOf in H.
    destruct (typeOf Rho e1) eqn:Heq1;
    destruct (typeOf Rho e2) eqn:Heq2; auto.
    destruct t; auto.
  Qed.

  Lemma well_typed_Abs :
    forall Rho x e t,
    well_typed Rho (Abs x t e) ->
    well_typed (update Nat.eqb Rho x t) e.
  Proof.
    intros. unfold well_typed in *.
    unfold typeOf in H. fold typeOf in H.
    destruct (typeOf (update Nat.eqb Rho x t) e) eqn:Heq; auto.
  Qed.

  Lemma well_typed_Choice :
    forall Rho e1 e2,
    well_typed Rho (Or e1 e2) ->
    well_typed Rho e1 /\ well_typed Rho e2.
  Proof.
    intros. unfold well_typed in *.
    unfold typeOf in H. fold typeOf in H.
    destruct (typeOf Rho e1) eqn:Heq1;
    destruct (typeOf Rho e2) eqn:Heq2; auto.
  Qed.

  Lemma well_typed_Case_Unit :
    forall Rho e brs,
    well_typed Rho (Case e (BranchUnit brs)) ->
    well_typed Rho e /\ well_typed Rho brs.
  Proof.
    intros. unfold well_typed in *.
    unfold typeOf in H. fold typeOf in H.
    destruct (typeOf Rho e) eqn:Heq1;
    destruct (typeOf Rho brs) eqn:Heq2; auto.
    destruct t; auto.
  Qed.

  Lemma well_typed_Case_Pair :
    forall Rho e n1 n2 t1 t2 brs HU,
    well_typed Rho (Case e (BranchPair (Pat n1 t1 n2 t2 HU) brs)) ->
    let Rho'  := update Nat.eqb Rho  n1 t1 in
    let Rho'' := update Nat.eqb Rho' n2 t2 in
    well_typed Rho e /\ well_typed Rho'' brs.
  Proof.
    intros. unfold well_typed in *.
    unfold typeOf in H. fold typeOf in H.
    destruct (typeOf Rho e) eqn:Heq1;
    destruct (typeOf Rho'' brs) eqn:Heq2; auto.
    destruct t; auto.
    subst Rho''. subst Rho'.
    destruct (eqType t1 t3 && eqType t2 t4).
    rewrite Heq2 in H. auto. auto.
  Qed.

  Lemma well_typed_Case :
    forall Rho e b,
    well_typed Rho (Case e b) ->
    well_typed Rho e.
  Proof.
    intros. unfold well_typed in *.
    unfold typeOf in H. fold typeOf in H.
    destruct (typeOf Rho e) eqn:Heq1; auto.
    destruct b; auto; destruct p; auto.
  Qed.

End WellTypedness.

(* Section PreservationTTypesHelper:
   Helper lemmas for the preservation theorem, primarily focused on
   variable management, substitution properties, and interaction between
   free and bound variables. *)
Section PreservationTTypesHelper.

  Lemma double_update_indep :
    forall {V : Type} (Rho : nat -> V) n1 t1 n2 t2,
    n1 <> n2 ->
    update Nat.eqb (update Nat.eqb Rho n1 t1) n2 t2 =
    update Nat.eqb (update Nat.eqb Rho n2 t2) n1 t1.
  Proof.
    intros V Rho n1 t1 n2 t2 H.
    apply functional_extensionality. intro x.
    unfold update.
    destruct (Nat.eqb n1 x) eqn:Heq1;
    destruct (Nat.eqb n2 x) eqn:Heq2; try reflexivity;
    rewrite Nat.eqb_eq in *; subst; contradiction.
  Qed.

  Lemma double_update :
    forall {V : Type} (Rho : nat -> V) n t1 t2,
    update Nat.eqb (update Nat.eqb Rho n t1) n t2 =
    update Nat.eqb Rho n t2.
  Proof.
    intros V Rho n1 t1 t2.
    apply functional_extensionality. intro x.
    unfold update.
    destruct (Nat.eqb n1 x); try reflexivity.
  Qed.

  Lemma existsb_concat :
    forall (l1 l2 : list nat) (beq : nat -> nat -> bool) x,
    existsb (beq x) (l1 ++ l2) = false ->
      existsb (beq x) l1 = false /\ existsb (beq x) l2 = false.
  Proof.
    induction l1; intros l2 beq x H.
    - split. reflexivity. simpl in H. assumption.
    - simpl in H. destruct (beq x a) eqn:Heq.
      + discriminate.
      + apply IHl1 in H. destruct H as [H1 H2].
        split. simpl. rewrite Heq. assumption. assumption.
  Qed.

  Lemma existsb_concat_r :
    forall (l1 l2 : list nat) (beq : nat -> nat -> bool) x,
    existsb (beq x) l1 = false ->
    existsb (beq x) l2 = false ->
    existsb (beq x) (l1 ++ l2) = false.
  Proof.
    induction l1; intros l2 beq x H H1.
    - simpl. assumption.
    - simpl in *. destruct (beq x a) eqn:Heq.
      + discriminate.
      + apply IHl1 in H1. assumption. assumption.
  Qed.

  Lemma anyIn_concat1 :
    forall e1 e2 e3,
    anyIn e1 (e2 ++ e3) = false ->
    anyIn e1 e2 = false /\ anyIn e1 e3 = false.
  Proof.
    induction e1; intros e2 e3 H.
    - split; reflexivity.
    - simpl in H.
      destruct (List.existsb (Nat.eqb a) (e2 ++ e3)) eqn:Heq.
      + discriminate.
      + apply IHe1 in H. destruct H as [H1 H2].
        apply existsb_concat in Heq. destruct Heq.
        split; simpl; try rewrite H; try rewrite H0; assumption.
  Qed.

  Lemma anyIn_concat1_r :
    forall e1 e2 e3,
    anyIn e1 e2 = false ->
    anyIn e1 e3 = false ->
    anyIn e1 (e2 ++ e3) = false.
  Proof.
    induction e1; intros e2 e3 H H1.
    - simpl. reflexivity.
    - simpl in *. destruct (existsb (Nat.eqb a) e2) eqn:Heq.
      + discriminate.
      + destruct (existsb (Nat.eqb a) e3) eqn:Heq2.
        * discriminate.
        * rewrite existsb_concat_r. apply IHe1; assumption.
          assumption. assumption.
  Qed.

  Lemma anyIn_concat2 :
    forall e1 e2 e3,
    anyIn (e1 ++ e2) e3 = false ->
    anyIn e1 e3 = false /\ anyIn e2 e3 = false.
  Proof.
    induction e1.
    - intros e2 e3 H. split. reflexivity. simpl in H. assumption.
    - intros e2 e3 H.
      simpl in H. destruct (List.existsb (Nat.eqb a) e3) eqn:Heq.
      + discriminate.
      + apply IHe1 in H. destruct H as [H1 H2].
        split. simpl. rewrite Heq. assumption. assumption.
  Qed.

  Lemma anyIn_concat2_r :
    forall e1 e2 e3,
    anyIn e1 e3 = false ->
    anyIn e2 e3 = false ->
    anyIn (e1 ++ e2) e3 = false.
  Proof.
    induction e1.
    - intros e2 e3 H H1. simpl in *. assumption.
    - intros e2 e3 H H1.
      simpl in *. destruct (List.existsb (Nat.eqb a) e3) eqn:Heq.
      + discriminate.
      + apply IHe1 in H1. assumption. assumption.
  Qed.

  Lemma anyIn_cons :
    forall e1 e2 a,
    anyIn e1 (a :: e2) = false ->
    anyIn e1 e2 = false /\ anyIn e1 [a] = false.
  Proof.
    induction e1.
    - intros e2 a H. split; reflexivity.
    - intros e2 a2 H.
      simpl in H. destruct (Nat.eqb a a2) eqn:Heq.
      + discriminate.
      + simpl in *. destruct (existsb (Nat.eqb a) e2) eqn:Heq2.
        * discriminate.
        * apply IHe1 in H. destruct H. split. assumption.
          rewrite Heq. rewrite H0. reflexivity.
  Qed.

  Lemma anyIn_cons_r :
    forall e1 e2 a,
    anyIn e1 e2 = false ->
    anyIn e1 [a] = false ->
    anyIn e1 (a :: e2) = false.
  Proof.
    induction e1.
    - intros e2 a H1 H2. reflexivity.
    - intros e2 a2 H1 H2.
      simpl in *. destruct (Nat.eqb a a2) eqn:Heq.
      + discriminate.
      + simpl in *. destruct (existsb (Nat.eqb a) e2) eqn:Heq2.
        * discriminate.
        * apply IHe1; assumption.
  Qed.

  Lemma anyIn_Pair :
    forall e1_1 e1_2 e2,
    anyIn (freeVars e2) (boundVars (Pair e1_1 e1_2)) = false ->
    anyIn (freeVars e2) (boundVars e1_1) = false /\
    anyIn (freeVars e2) (boundVars e1_2) = false.
  Proof.
    intros e1_1 e1_2 e2 H.
    unfold boundVars in H. fold boundVars in H.
    apply anyIn_concat1 in H. assumption.
  Qed.

  Lemma anyIn_Pair2 :
    forall e1_1 e1_2 e2,
    anyIn (freeVars (Pair e1_1 e1_2)) (boundVars e2) = false ->
    anyIn (freeVars e1_1) (boundVars e2) = false /\
    anyIn (freeVars e1_2) (boundVars e2) = false.
  Proof.
    intros e1_1 e1_2 e2 H.
    unfold boundVars in H. fold boundVars in H.
    apply anyIn_concat2 in H. assumption.
  Qed.

  Lemma anyIn_App :
    forall e1 e2 e3,
    anyIn (freeVars e1) (boundVars (App e2 e3)) = false ->
    anyIn (freeVars e1) (boundVars e2) = false /\
    anyIn (freeVars e1) (boundVars e3) = false.
  Proof.
    intros e1 e2 e3 H.
    unfold freeVars in H. fold freeVars in H.
    apply anyIn_concat1 in H. assumption.
  Qed.

  Lemma anyIn_Abs :
    forall e x t e2,
    anyIn (freeVars e) (boundVars (Abs x t e2)) = false ->
    anyIn (freeVars e) (boundVars e2) = false /\
    anyIn (freeVars e) [x] = false.
  Proof.
    intros e x t e2 H.
    unfold boundVars in H. fold boundVars in H.
    apply anyIn_cons in H. assumption.
  Qed.

  Lemma anyIn_Or :
    forall e1 e2 e3,
    anyIn (freeVars e1) (boundVars (Or e2 e3)) = false ->
    anyIn (freeVars e1) (boundVars e2) = false /\
    anyIn (freeVars e1) (boundVars e3) = false.
  Proof.
    intros e1 e2 e3 H.
    unfold freeVars in H. fold freeVars in H.
    apply anyIn_concat1 in H. assumption.
  Qed.

  Lemma anyIn_Case_Unit :
    forall e e1 e2,
    anyIn (freeVars e) (boundVars (Case e1 (BranchUnit e2))) = false ->
    anyIn (freeVars e) (boundVars e1) = false /\
    anyIn (freeVars e) (boundVars e2) = false.
  Proof.
    intros e e1 e2 H.
    unfold boundVars in H. fold boundVars in H.
    apply anyIn_concat1 in H. assumption.
  Qed.

  Lemma anyIn_Case_Pair :
    forall e e1 n1 t1 n2 t2 e2 HU,
    anyIn (freeVars e) (boundVars (Case e1
      (BranchPair (Pat n1 t1 n2 t2 HU) e2))) = false ->
    anyIn (freeVars e) (boundVars e1) = false /\
    anyIn (freeVars e) (n1 :: n2 :: boundVars e2) = false.
  Proof.
    intros e e1 n1 t1 n2 t2 e2 HU H.
    unfold boundVars in H. fold boundVars in H.
    apply anyIn_concat1 in H. assumption.
  Qed.

  Lemma anyIn_removeb : forall xs n n1,
    n <> n1 ->
    anyIn (removeb Nat.eqb n xs) [n1] = false ->
    anyIn xs [n1] = false.
  Proof.
    induction xs.
    - intros n n1 H H2. reflexivity.
    - intros n n1 H H2. simpl in H2.
      destruct (Nat.eqb n a) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst a. simpl.
        rewrite <- Nat.eqb_neq in H. rewrite H. simpl.
        eapply IHxs. apply Nat.eqb_neq in H.
        apply H. assumption.
      + simpl in *. destruct (Nat.eqb a n1) eqn:Heq1.
        * simpl in H2. inversion H2.
        * simpl in *. eapply IHxs. eassumption. assumption.
  Qed.

  Lemma typeOf_unbound :
    forall e Rho n t t2,
    typeOf Rho e = Some t ->
    anyIn (freeVars e) [n] = false ->
    typeOf (update Nat.eqb Rho n t2) e = typeOf Rho e.
  Proof.
    fix typeOf_unbound 1.
    --
    induction e; intros Rho n1 t1 t2 H H1; simpl in *.
    - destruct (Nat.eqb n n1) eqn:Heq; inversion H1.
      unfold update. rewrite Nat.eqb_sym in Heq. rewrite Heq.
      reflexivity.
    - reflexivity.
    - destruct (typeOf Rho e1) eqn:Heq1,
               (typeOf Rho e2) eqn:Heq2; try discriminate.
      inversion H. subst. eapply anyIn_concat2 in H1.
      destruct H1 as [H1 H2]. erewrite IHe1. erewrite IHe2.
      rewrite Heq1. rewrite Heq2. reflexivity. apply Heq2.
      assumption. apply Heq1. assumption.
    - destruct (typeOf Rho e1) eqn:Heq1,
               (typeOf Rho e2) eqn:Heq2; try discriminate;
      destruct t; try discriminate.
      destruct (eqType t3 t0) eqn:Heq3; try discriminate.
      inversion H. subst. eapply anyIn_concat2 in H1.
      destruct H1 as [H1 H2]. erewrite IHe1. erewrite IHe2.
      rewrite Heq1. rewrite Heq2. rewrite Heq3. reflexivity.
      apply Heq2. assumption. apply Heq1. assumption.
    - destruct (typeOf (update Nat.eqb Rho n t) e) eqn:Heq1;
      try discriminate. inversion H. subst.
      destruct (Nat.eqb n n1) eqn:Heq2.
      + apply Nat.eqb_eq in Heq2. subst n1.
        rewrite double_update. rewrite Heq1. reflexivity.
      + apply Nat.eqb_neq in Heq2.
        rewrite double_update_indep. erewrite IHe.
        rewrite Heq1. reflexivity. apply Heq1.
        eapply anyIn_removeb. apply Heq2. assumption.
        symmetry. assumption.
    - destruct (typeOf Rho e1) eqn:Heq1,
               (typeOf Rho e2) eqn:Heq2; try discriminate.
      simpl in H. destruct (eqType t t0) eqn:Heq3; try discriminate.
      apply eq_Type_eq in Heq3. inversion H. subst.
      inversion H. subst. eapply anyIn_concat2 in H1.
      destruct H1 as [H1 H2]. erewrite IHe1. erewrite IHe2.
      rewrite Heq1. rewrite Heq2. rewrite eqTypeS_refl.
      reflexivity. apply Heq2. assumption. apply Heq1. assumption.
    - destruct b.
      + destruct (typeOf Rho e) eqn:Heq1; try discriminate.
        destruct t; try discriminate.
        inversion H. subst. eapply anyIn_concat2 in H1.
        destruct H1 as [H3 H4]. erewrite IHe.
        rewrite Heq1. erewrite typeOf_unbound. reflexivity.
        apply H2. assumption. apply Heq1. assumption.
      + destruct p. destruct (typeOf Rho e) eqn:Heq1; try discriminate.
        destruct t; try discriminate.
        destruct (eqType t0 t4 && eqType t3 t5) eqn:Heq2;
        try discriminate. eapply anyIn_concat2 in H1.
        destruct H1 as [H1 H2]. erewrite IHe.
        rewrite Heq1. rewrite Heq2. shelve. apply Heq1.
        apply H1. Unshelve.
        apply andb_true_iff in Heq2. destruct Heq2 as [Heq2 Heq3].
        apply eq_Type_eq in Heq2. apply eq_Type_eq in Heq3. subst.
        destruct (Nat.eqb n1 n0) eqn:Heq3,
                 (Nat.eqb n2 n1) eqn:Heq4.
        * apply Nat.eqb_eq in Heq3. apply Nat.eqb_eq in Heq4. subst.
          contradiction.
        * apply Nat.eqb_eq in Heq3. apply Nat.eqb_neq in Heq4. subst.
          rewrite double_update. reflexivity.
        * apply Nat.eqb_neq in Heq3. apply Nat.eqb_eq in Heq4. subst.
          rewrite double_update_indep. rewrite double_update.
          rewrite double_update_indep. reflexivity.
          assumption. symmetry. assumption.
        * apply Nat.eqb_neq in Heq3. apply Nat.eqb_neq in Heq4.
          erewrite (double_update_indep _ n1 _ n0).
          erewrite (double_update_indep _ n1 _ n2).
          erewrite typeOf_unbound. reflexivity.
          apply H. apply anyIn_removeb in H2. apply anyIn_removeb in H2.
          apply H2. assumption. symmetry. assumption.
          symmetry. assumption. assumption.
  Qed.

  Lemma any_in_subst :
    forall e1 e2 e3 n3,
    anyIn (freeVars e2) (boundVars e1) = false ->
    anyIn (freeVars e3) [n3] = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    anyIn (freeVars e2) (boundVars (subst n3 e3 e1)) = false.
  Proof.
    fix any_in_subst 1.
    --
    induction e1; intros e2 e3 n3 H1 H2 H3.
    - simpl. destruct (Nat.eqb n n3) eqn:Heq.
      * rewrite Nat.eqb_eq in Heq. subst n3.
        simpl in H1. apply H3.
      * apply H1.
    - simpl. apply H1.
    - simpl. apply anyIn_Pair in H1. destruct H1.
      eapply anyIn_concat1_r. apply IHe1_1; assumption.
      apply IHe1_2; assumption.
    - simpl. apply anyIn_App in H1. destruct H1.
      eapply anyIn_concat1_r. apply IHe1_1; assumption.
      apply IHe1_2; assumption.
    - simpl. apply anyIn_Abs in H1. destruct H1.
      destruct (Nat.eqb n n3) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst n3.
        simpl in *. apply anyIn_cons_r; assumption.
      * simpl in *. apply anyIn_cons_r.
        eapply IHe1; try eassumption. assumption.
    - simpl. apply anyIn_Or in H1. destruct H1.
      eapply anyIn_concat1_r. apply IHe1_1; assumption.
      apply IHe1_2; assumption.
    - destruct b.
      * simpl. apply anyIn_Case_Unit in H1. destruct H1.
        eapply anyIn_concat1_r. apply IHe1; assumption.
        apply any_in_subst; assumption.
      * destruct p. simpl.
        apply anyIn_Case_Pair in H1. destruct H1.
        destruct (Nat.eqb n3 n1) eqn:Heq1,
                 (Nat.eqb n3 n2) eqn:Heq2; simpl in *.
        + apply Nat.eqb_eq in Heq1. apply Nat.eqb_eq in Heq2. subst.
          eapply anyIn_concat1_r. apply IHe1; assumption. assumption.
        + apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. subst.
          eapply anyIn_concat1_r. apply IHe1; assumption. assumption.
        + apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. subst.
          eapply anyIn_concat1_r. apply IHe1; assumption. assumption.
        + apply Nat.eqb_neq in Heq1. apply Nat.eqb_neq in Heq2.
          eapply anyIn_concat1_r. apply IHe1; assumption.
          apply anyIn_cons in H0. destruct H0.
          apply anyIn_cons in H0. destruct H0.
          apply anyIn_cons_r. apply anyIn_cons_r.
          apply any_in_subst; assumption. assumption. assumption.
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
    fix subst_preservation 2.
    --
    intros Rho e1. generalize dependent Rho.
    induction e1; intros Rho e2 n0 t1 t2 HF H H1.
    - unfold typeOf in H. inversion H. subst. clear H.
      unfold subst. unfold update.
      destruct (Nat.eqb n n0) eqn:Heq.
      + rewrite Nat.eqb_eq in Heq. subst n0.
        rewrite Nat.eqb_refl. assumption.
      + rewrite Nat.eqb_sym in Heq. simpl.
        rewrite Heq. reflexivity.
    - inversion H. simpl. reflexivity.
    - inversion H. simpl.
      remember (update Nat.eqb Rho n0 t2) as Rho'.
      destruct (typeOf Rho' e1_1) eqn:Heq1,
               (typeOf Rho' e1_2) eqn:Heq2; try discriminate.
      subst Rho'. apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_Pair in HF. destruct HF as [HF1 HF2].
      erewrite IHe1_1. erewrite IHe1_2.
      reflexivity. apply anyIn_cons_r; assumption. eassumption.
      assumption. apply anyIn_cons_r; assumption. eassumption.
      assumption.
    - simpl. simpl in H.
      remember (update Nat.eqb Rho n0 t2) as Rho'.
      destruct (typeOf Rho' e1_1) eqn:Heq1,
               (typeOf Rho' e1_2) eqn:Heq2; try discriminate;
      destruct t; try discriminate.
      destruct (eqType t3 t0) eqn:Heq3; try discriminate.
      inversion H. subst.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_App in HF. destruct HF as [HF1 HF2].
      eapply (IHe1_1 Rho) in Heq1. eapply (IHe1_2 Rho) in Heq2.
      rewrite Heq1. rewrite Heq2. rewrite Heq3.
      reflexivity. apply anyIn_cons_r; assumption. assumption.
      apply anyIn_cons_r; assumption. assumption.
    - simpl. simpl in H.
      remember (update Nat.eqb Rho n0 t2) as Rho'.
      remember (update Nat.eqb Rho' n t) as Rho''.
      destruct (typeOf Rho'' e1) eqn:Heq1; try discriminate.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_Abs in HF. destruct HF as [HF1 HF2].
      inversion H. subst. destruct (Nat.eqb n n0) eqn:Heq2.
      + apply Nat.eqb_eq in Heq2. subst n0.
        simpl. rewrite double_update in Heq1.
        rewrite Heq1. reflexivity.
      + simpl. erewrite IHe1. reflexivity.
        apply anyIn_cons_r; assumption.
        rewrite double_update_indep. apply Heq1.
        apply Nat.eqb_neq in Heq2. assumption.
        erewrite typeOf_unbound; try eassumption.
    - simpl. simpl in H.
      remember (update Nat.eqb Rho n0 t2) as Rho'.
      destruct (typeOf Rho' e1_1) eqn:Heq1;
      destruct (typeOf Rho' e1_2) eqn:Heq2; try discriminate.
      simpl in H. destruct (eqType t t0) eqn:Heq3; try discriminate.
      apply eq_Type_eq in Heq3. inversion H. subst.
      apply anyIn_cons in HF. destruct HF as [HF HFA].
      apply anyIn_Or in HF. destruct HF as [HF1 HF2].
      erewrite IHe1_1. shelve. apply anyIn_cons_r; assumption.
      apply Heq1. apply H1. Unshelve.
      erewrite IHe1_2. shelve. apply anyIn_cons_r; assumption.
      apply Heq2. apply H1. Unshelve.
      rewrite eqTypeS_refl. reflexivity.
    - simpl. simpl in H.
      destruct b.
      + remember (update Nat.eqb Rho n0 t2) as Rho'.
        destruct (typeOf Rho' e1) eqn:Heq1; try discriminate.
        destruct t; try discriminate.
        apply anyIn_cons in HF. destruct HF as [HF HFA].
        apply anyIn_Case_Unit in HF. destruct HF as [HF1 HF2].
        erewrite IHe1. shelve. apply anyIn_cons_r; assumption.
        subst. apply Heq1. eassumption. Unshelve. simpl.
        eapply subst_preservation. apply anyIn_cons_r; assumption.
        subst. apply H. apply H1.
      + destruct p. remember (update Nat.eqb Rho n0 t2) as Rho'.
        destruct (typeOf Rho' e1) eqn:Heq1; try discriminate.
        destruct t; try discriminate.
        destruct (eqType t0 t4 && eqType t3 t5) eqn:Heq2;
        try discriminate. apply anyIn_cons in HF.
        destruct HF as [HF HFA]. apply anyIn_Case_Pair in HF.
        destruct HF as [HF1 HF2].
        destruct (Nat.eqb n0 n1) eqn:HeqN1, (Nat.eqb n0 n2) eqn:HeqN2.
        * apply Nat.eqb_eq in HeqN1. apply Nat.eqb_eq in HeqN2. subst.
          simpl. erewrite IHe1. shelve.
          apply anyIn_cons_r; assumption. apply Heq1.
          eassumption. Unshelve. simpl.
          rewrite Heq2. erewrite double_update.
          erewrite double_update in H.
          erewrite double_update in H.
          assumption.
        * apply Nat.eqb_eq in HeqN1. apply Nat.eqb_neq in HeqN2. subst.
          simpl. erewrite IHe1. shelve.
          apply anyIn_cons_r; assumption. apply Heq1.
          eassumption. Unshelve. simpl.
          rewrite Heq2. erewrite double_update in H. assumption.
        * apply Nat.eqb_neq in HeqN1. apply Nat.eqb_eq in HeqN2. subst.
          simpl. erewrite IHe1. shelve.
          apply anyIn_cons_r; assumption. apply Heq1.
          eassumption. Unshelve. simpl.
          rewrite Heq2. erewrite double_update_indep in H.
          rewrite double_update in H.
          erewrite double_update_indep in H.
          assumption. apply HeqN1. symmetry. apply HeqN1.
        * apply Nat.eqb_neq in HeqN1. apply Nat.eqb_neq in HeqN2.
          subst. simpl. erewrite IHe1. shelve.
          apply anyIn_cons_r; assumption. apply Heq1.
          eassumption. Unshelve. simpl.
          apply anyIn_cons in HF2. destruct HF2.
          apply anyIn_cons in H0. destruct H0.
          rewrite Heq2. eapply subst_preservation.
          apply anyIn_cons_r; assumption.
          erewrite (double_update_indep _ n2 _ n0).
          erewrite (double_update_indep _ n1 _ n0).
          eassumption. symmetry. assumption. symmetry. assumption.
          erewrite typeOf_unbound; try eassumption;
          erewrite typeOf_unbound; eassumption.
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
      - apply anyIn_cons_r. shelve. assumption. Unshelve.
        apply t2. apply any_in_subst; try assumption.
      - eapply subst_preservation.
        + apply anyIn_cons_r; assumption.
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
    induction e using Exp_Branch_mut
      with (P := fun e => forall e' Rho t,
        step e = Some e' ->
        typeOf Rho e = Some t ->
        typeOf Rho e' = Some t)
           (P0 := fun brs => forall e e' Rho t,
        step (Case e brs) = Some e' ->
        typeOf Rho (Case e brs) = Some t ->
        typeOf Rho e' = Some t); intros; inversion H; subst.
    - destruct (step e1) eqn:Heq1, (step e2) eqn:Heq2;
      inversion H2; subst.
      + unfold typeOf. fold typeOf.
        unfold typeOf in H0. fold typeOf in H0.
        destruct (typeOf Rho e1) eqn:Heq3,
                 (typeOf Rho e2) eqn:Heq4;
        try inversion H0; subst.
        erewrite IHe1. apply H0. reflexivity. apply Heq3.
      + unfold typeOf. fold typeOf.
        unfold typeOf in H0. fold typeOf in H0.
        destruct (typeOf Rho e1) eqn:Heq3,
                 (typeOf Rho e2) eqn:Heq4;
        try inversion H0; subst.
        erewrite IHe1. apply H0. reflexivity. apply Heq3.
      + unfold typeOf. fold typeOf.
        unfold typeOf in H0. fold typeOf in H0.
        destruct (typeOf Rho e1) eqn:Heq3,
                 (typeOf Rho e2) eqn:Heq4;
        try inversion H0; subst.
        erewrite IHe2. apply H0. reflexivity. apply Heq4.
  - destruct e1; try inversion H2.
    + destruct (step (Pair e1_1 e1_2)) eqn:Heq1;
      inversion H2; subst.
      unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf Rho e1_1) eqn:Heq2,
               (typeOf Rho e1_2) eqn:Heq3;
      try inversion H0; subst.
    + destruct (step (App e1_1 e1_2)) eqn:Heq1;
      inversion H2; subst.
      unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf Rho e1_1) eqn:Heq2,
               (typeOf Rho e1_2) eqn:Heq3;
      try inversion H0; subst;
      destruct t0; inversion H0.
      destruct (eqType t0_1 t1) eqn:Heq4; try inversion H0; subst.
      destruct t0_2; inversion H0; subst.
      destruct (typeOf Rho e2) eqn:Heq5; try inversion H0; subst.
      destruct (eqType t0_2_1 t0) eqn:Heq6; try inversion H0; subst.
      erewrite IHe1. shelve. reflexivity.
      unfold typeOf. fold typeOf. rewrite Heq2. rewrite Heq3.
      rewrite Heq4. reflexivity. Unshelve.
      simpl. rewrite Heq6. reflexivity.
    + subst. unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf (update Nat.eqb Rho n t0) e1) eqn:Heq1;
      try inversion H0; subst. destruct (typeOf Rho e2) eqn:Heq2;
      try inversion H0; subst. destruct (eqType t0 t2) eqn:Heq3;
      try inversion H0; subst.
      destruct (anyIn (freeVars e2) (n::boundVars e1)) eqn:Heq4;
      try inversion H2; subst. eapply subst_preservation.
      eassumption. apply eq_Type_eq in Heq3. subst. eassumption.
      eassumption.
    + subst. clear H2.
      unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf Rho e1_1) eqn:Heq2,
               (typeOf Rho e1_2) eqn:Heq3;
      try inversion H0; subst. simpl in H0. simpl.
      destruct (eqType t0 t1) eqn:Heq4; try inversion H0; subst.
      destruct (t0) eqn:Heq5; try inversion H0; subst.
      destruct (typeOf Rho e2) eqn:Heq6; try inversion H0; subst.
      destruct (eqType t2_1 t0) eqn:Heq7; try inversion H0; subst.
      rewrite eq_Type_eq in Heq4. subst. rewrite Heq7.
      rewrite eqTypeS_refl. reflexivity.
    + destruct e1; try inversion H3; subst.
      * destruct b; try inversion H3; subst.
        unfold typeOf. fold typeOf.
        unfold typeOf in H0. fold typeOf in H0.
        apply H0.
      * destruct b; try inversion H3; subst.
        destruct p. simpl in *. inversion H2.
        unfold typeOf. fold typeOf.
        destruct (typeOf Rho e1_1) eqn:Heq1,
                 (typeOf Rho e1_2) eqn:Heq2; try inversion H0; subst.
        destruct (eqType t1 t0 && eqType t2 t3) eqn:Heq3;
        try inversion H0; subst.
        apply andb_true_iff in Heq3. destruct Heq3 as [Heq3_1 Heq3_2].
        apply eq_Type_eq in Heq3_1. apply eq_Type_eq in Heq3_2. subst.
        destruct (typeOf (update Nat.eqb
                         (update Nat.eqb Rho n1 t0) n2 t3) e) eqn:Heq4;
        try inversion H0; subst.
        destruct t1; inversion H0; subst.
        destruct (typeOf Rho e2) eqn:Heq5; try inversion H0; subst.
        destruct (eqType t1_1 t1) eqn:Heq6; try inversion H0; subst.
        destruct (anyIn (freeVars e1_1 ++ freeVars e1_2)
                        (n1::n2:: boundVars e)) eqn:Heq7;
        try inversion H2; subst.
        destruct (anyIn (freeVars e1_2)(boundVars e1_1)) eqn:Heq8;
        try inversion H2; subst. unfold typeOf. fold typeOf.
        apply anyIn_concat2 in Heq7. destruct Heq7 as [Heq7_1 Heq7_2].
        erewrite subst_preservation2. shelve.
        assumption. assumption. assumption. symmetry. assumption.
        apply Heq4. apply  Heq2. apply Heq1. Unshelve.
        simpl. rewrite Heq5. rewrite Heq6. reflexivity.
      * unfold typeOf. fold typeOf.
        unfold typeOf in H0. fold typeOf in H0.
        destruct b.
        --  destruct (eqTypeS (typeOf Rho e1_1)
                              (typeOf Rho e1_2)) eqn:Heq1;
            try inversion H0; subst.
            destruct (typeOf Rho e1_1) eqn:Heq2;
            destruct (typeOf Rho e1_2) eqn:Heq3;
            try inversion H0; try inversion Heq1.
            destruct t0; inversion H0; subst.
            destruct t1; inversion Heq1; subst.
            rewrite eqTypeS_refl. reflexivity.
        --  destruct p.
            destruct (eqTypeS (typeOf Rho e1_1) (typeOf Rho e1_2)) eqn:Heq1;
            try inversion H0; subst.
            destruct (typeOf Rho e1_1) eqn:Heq2;
            destruct (typeOf Rho e1_2) eqn:Heq3;
            try inversion H0; try inversion Heq1.
            apply eq_Type_eq in Heq1. subst.
            destruct t3; inversion H0; subst.
            destruct (eqType t1 t3_1 && eqType t2 t3_2) eqn:Heq4;
            try inversion H0; subst.
            apply andb_true_iff in Heq4.
            destruct Heq4 as [Heq4_1 Heq4_2].
            apply eq_Type_eq in Heq4_1. apply eq_Type_eq in Heq4_2.
            rewrite eqTypeS_refl. reflexivity.
  - destruct (step e1) eqn:Heq1, (step e2) eqn:Heq2;
    inversion H2; subst.
    + unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf Rho e1) eqn:Heq3,
               (typeOf Rho e2) eqn:Heq4;
      try inversion H0; subst.
      destruct (eqType t0 t1) eqn:Heq5; try inversion H3; subst.
      apply eq_Type_eq in Heq5. subst.
      erewrite IHe1. shelve. reflexivity. apply Heq3.
      Unshelve. rewrite eqTypeS_refl. reflexivity.
    + unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf Rho e1) eqn:Heq3,
               (typeOf Rho e2) eqn:Heq4;
      try inversion H0; subst.
      destruct (eqType t0 t1) eqn:Heq5; try inversion H3; subst.
      apply eq_Type_eq in Heq5. subst.
      erewrite IHe1. shelve. reflexivity. apply Heq3.
      Unshelve. rewrite eqTypeS_refl. reflexivity.
    + unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf Rho e1) eqn:Heq3,
               (typeOf Rho e2) eqn:Heq4;
      try inversion H0; subst.
      destruct (eqType t0 t1) eqn:Heq5; try inversion H3; subst.
      apply eq_Type_eq in Heq5. subst.
      erewrite IHe2. shelve. reflexivity. apply Heq4.
      Unshelve. rewrite eqTypeS_refl. reflexivity.
  - destruct e; inversion H2; subst.
    + destruct b; inversion H3; subst.
      unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      assumption.
    + destruct b; inversion H3; subst. destruct p.
      unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct (typeOf Rho e1) eqn:Heq1;
      destruct (typeOf Rho e2) eqn:Heq2; try inversion H0; subst.
      destruct (eqType t1 t0 && eqType t2 t3) eqn:Heq3;
      try inversion H0; subst.
      erewrite IHe0. rewrite H5. reflexivity.
      apply H. unfold typeOf. fold typeOf.
      rewrite Heq1. rewrite Heq2. rewrite Heq3.
      apply H5.
    + unfold typeOf. fold typeOf.
      unfold typeOf in H0. fold typeOf in H0.
      destruct b.
      * destruct (eqTypeS (typeOf Rho e1) (typeOf Rho e2)) eqn:Heq1;
        try inversion H0; subst.
        destruct (typeOf Rho e1) eqn:Heq2;
        destruct (typeOf Rho e2) eqn:Heq3;
        try inversion H0; try inversion Heq1.
        destruct t0; inversion H0; subst.
        destruct t1; inversion Heq1; subst.
        rewrite eqTypeS_refl. reflexivity.
      * destruct p.
        destruct (eqTypeS (typeOf Rho e1) (typeOf Rho e2)) eqn:Heq1;
        try inversion H0; subst.
        destruct (typeOf Rho e1) eqn:Heq2;
        destruct (typeOf Rho e2) eqn:Heq3;
        try inversion H0; try inversion Heq1.
        destruct t0; inversion H0; subst.
        destruct (eqType t1 t0_1 && eqType t2 t0_2) eqn:Heq4;
        try inversion H0; subst. rewrite H6.
        apply eq_Type_eq in H5. subst. rewrite Heq4.
        rewrite eqTypeS_refl. reflexivity.
  - destruct e0; inversion H2.
    + unfold typeOf in H0. fold typeOf in H0.
      subst. assumption.
    + unfold typeOf in H0. fold typeOf in H0.
      unfold typeOf. fold typeOf.
      destruct (typeOf Rho e0_1) eqn:Heq1;
      destruct (typeOf Rho e0_2) eqn:Heq2; try inversion H0; subst.
      simpl in *.
      destruct (eqType t0 t1) eqn:Heq3; try inversion H0; subst.
      apply eq_Type_eq in Heq3. subst.
      destruct t1; inversion H0; subst.
      rewrite eqTypeS_refl. reflexivity.
  - destruct p. destruct e0; inversion H2; subst.
    + unfold typeOf in H0. fold typeOf in H0.
      unfold typeOf. fold typeOf.
      destruct (typeOf Rho e0_1) eqn:Heq1;
      destruct (typeOf Rho e0_2) eqn:Heq2; try inversion H0; subst.
      simpl in *.
      destruct (eqType t1 t0 && eqType t2 t3) eqn:Heq3; try inversion H0; subst.
      apply andb_true_iff in Heq3. destruct Heq3 as [Heq4 Heq5].
      apply eq_Type_eq in Heq4. apply eq_Type_eq in Heq5. subst.
      destruct (anyIn (freeVars e0_1 ++ freeVars e0_2)
                      (n1::n2::boundVars e)) eqn:Heq6;
      try inversion H2; subst.
      destruct (anyIn (freeVars e0_2) (boundVars e0_1)) eqn:Heq7;
      try inversion H2; subst.
      apply anyIn_concat2 in Heq6. destruct Heq6 as [Heq6_1 Heq6_2].
      erewrite subst_preservation2. rewrite H0. reflexivity.
      assumption. assumption. assumption. symmetry. assumption.
      apply H0. apply Heq2. apply Heq1.
    + unfold typeOf in H0. fold typeOf in H0.
      unfold typeOf. fold typeOf.
      destruct (typeOf Rho e0_1) eqn:Heq1;
      destruct (typeOf Rho e0_2) eqn:Heq2; try inversion H0; subst.
      simpl in *.
      destruct (eqType t0 t3) eqn:Heq3; try inversion H0; subst.
      apply eq_Type_eq in Heq3. subst.
      destruct t3; inversion H0; subst.
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
    unfold well_typed in *.
    destruct (typeOf Rho e) eqn:Heq; try inversion Hwt.
    erewrite step_preservation.
    reflexivity. apply H. apply Heq.
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

  Lemma compatibility:
    forall e Rho Gamma x,
    Gamma = mkCompatibleCtx Rho ->
    well_typed Rho e ->
    Gamma |- e ::: x ->
    exists t,
    typeOf Rho e = Some t /\
    compatible x t.
  Proof.
    induction e using Exp_Branch_mut
      with (P :=  fun e => forall Rho Gamma x,
                    Gamma = mkCompatibleCtx Rho ->
                    well_typed Rho e ->
                    Gamma |- e ::: x -> exists t,
                    typeOf Rho e = Some t /\
                    compatible x t)
           (P0 := fun brs => forall e Rho Gamma x,
                    Gamma = mkCompatibleCtx Rho ->
                    well_typed Rho (Case e brs) ->
                    Gamma |- Case e brs ::: x -> exists t,
                    typeOf Rho (Case e brs) = Some t /\
                    compatible x t); intros.
    - inversion H1; subst.
      unfold typeOf. fold typeOf.
      unfold mkCompatibleCtx in *.
      destruct (Rho n).
        * eexists. split. reflexivity. reflexivity.
        * eexists. split. reflexivity. apply mkCompatible_compatible.
        * eexists. split. reflexivity. apply mkCompatible_compatible.
    - inversion H1; subst. simpl in H1. exists TUnit.
      split. reflexivity. reflexivity.
    - inversion H1. subst. simpl.
      apply well_typed_Pair in H0.
      destruct H0.
      unfold well_typed in H0.
      unfold well_typed in H.
      destruct (typeOf Rho e1) eqn:Heq1;
      destruct (typeOf Rho e2) eqn:Heq2;
      try inversion H0; try inversion H.
      exists (TPair t t0).
      split. reflexivity. destruct d1; destruct d2; auto.
    - remember H0 as H0C. clear HeqH0C.
      unfold well_typed in H0.
      unfold typeOf in *. fold typeOf in *.
      destruct (typeOf Rho e1) eqn:Heq1.
      shelve. inversion H0. Unshelve.
      destruct t. inversion H0. inversion H0.
      destruct (typeOf Rho e2).
      shelve. inversion H0. Unshelve.
      destruct (eqType t1 t).
      shelve. inversion H0. Unshelve.
      exists t2. inversion H1; subst.
      + split. reflexivity. reflexivity.
      + unfold decide in H1. unfold decide.
        destruct (more_specific d3 d1) eqn:Heq2.
        * split. reflexivity.
          apply well_typed_App in H0C. destruct H0C.
          edestruct IHe1. reflexivity. apply H.
          apply H4. destruct H3. rewrite Heq1 in H3.
          inversion H3. subst. simpl in H5.
          destruct H5. assumption.
        * split. reflexivity. reflexivity.
    - inversion H1. subst.
      remember H0 as H0C. clear HeqH0C.
      unfold well_typed in H0.
      destruct (typeOf Rho (Abs n t e)) eqn:Heq1.
      + unfold typeOf in Heq1. fold typeOf in Heq1.
        destruct (typeOf (update Nat.eqb Rho n t) e) eqn:Heq2.
        * exists t0. split. reflexivity. simpl.
          inversion Heq1. subst.
          apply well_typed_Abs in H0C.
          edestruct IHe. reflexivity.
          apply H0C. inversion H1.
          subst Gamma'0. subst. erewrite <- update_compatible.
          apply H9. reflexivity.
          destruct H. rewrite Heq2 in H. inversion H. subst.
          split. apply mkCompatible_compatible. assumption.
        * inversion Heq1.
      + inversion H0.
    - inversion H1. unfold well_typed in H0.
      destruct (typeOf Rho (Or e1 e2)). exists t.
      split. reflexivity. reflexivity. inversion H0.
    - inversion H1.
      + unfold well_typed in H0.
        destruct b; inversion H3. subst.
        destruct (typeOf Rho (Case e (BranchUnit e0))).
        exists t. split; reflexivity. inversion H0.
      + unfold well_typed in H0.
        destruct b; inversion H4. subst.
        destruct (typeOf Rho (Case e (BranchPair p e0))).
        exists t. split; reflexivity.
        inversion H0.
      + subst. remember H0 as H0C. clear HeqH0C.
        apply well_typed_Case_Unit in H0.
        destruct H0 as [H0A H0B].
        edestruct (IHe0 e Rho (mkCompatibleCtx Rho) x).
        reflexivity. assumption. assumption.
        destruct H. unfold well_typed in *.
        unfold typeOf. fold typeOf.
        unfold typeOf in H0C. fold typeOf in H0C.
        destruct (typeOf Rho e) eqn:Heq1;
        destruct (typeOf Rho e2) eqn:Heq2;
        try inversion H0A; try inversion H0B.
        destruct t; try inversion H0C.
        inversion H. subst.
        exists x0. split. rewrite Heq2 in H3. rewrite Heq1 in H3.
        assumption. assumption.
      + subst. remember H0 as H0C. clear HeqH0C.
        remember H0 as H0D. clear HeqH0D.
        unfold well_typed in H0.
        unfold typeOf in H0. fold typeOf in H0.
        unfold typeOf. fold typeOf.
        destruct (typeOf Rho e) eqn:Heq1.
        shelve. inversion H0. Unshelve. subst.
        destruct p. destruct t; try inversion H0.
        remember (update Nat.eqb Rho n0 t0) as Rho'.
        destruct (eqType t0 t4 && eqType t3 t5) eqn:Heq3.
        shelve. inversion H0. Unshelve.
        destruct (typeOf (update Nat.eqb Rho' n3 t3) e2) eqn:Heq2.
        shelve. inversion H0. Unshelve.
        eapply well_typed_Case_Pair in H0C.
        destruct H0C.
        edestruct (IHe0 e). reflexivity. apply H0D.
        apply H1. destruct H4. exists t. split. reflexivity.
        unfold typeOf in H4. fold typeOf in H4.
        rewrite Heq1 in H4. rewrite Heq3 in H4.
        subst Rho'. rewrite Heq2 in H4.
        inversion H4. subst. assumption.
    - inversion H1; subst.
      + unfold well_typed in H0.
        destruct (typeOf Rho (Case e0 (BranchUnit e))) eqn:Heq1.
        exists t. split; reflexivity.
        inversion H0.
      + remember H0 as H0C. clear HeqH0C.
        unfold well_typed in H0.
        apply well_typed_Case_Unit in H0C.
        destruct H0C as [H0A H0B].
        destruct (typeOf Rho (Case e0 (BranchUnit e))) eqn:Heq1.
        shelve. inversion H0. Unshelve.
        exists t. edestruct (IHe Rho). reflexivity.
        apply H0B. apply H7. destruct H.
        unfold typeOf in Heq1. fold typeOf in Heq1.
        rewrite H in Heq1. destruct (typeOf Rho e0) eqn:Heq2.
        shelve. inversion Heq1. Unshelve.
        destruct t0; inversion Heq1. subst.
        split. reflexivity. assumption.
    - inversion H1; subst.
      + unfold well_typed in H0.
        destruct (typeOf Rho (Case e0 (BranchPair p0 e))) eqn:Heq1.
        exists t. split; reflexivity. inversion H0.
      + subst p0. remember H0 as H0C. clear HeqH0C.
        unfold well_typed in H0.
        apply well_typed_Case_Pair in H0C.
        destruct H0C as [H0A H0B].
        remember (BranchPair (Pat n1 t1 n2 t2 H2) e) as b.
        destruct (typeOf Rho (Case e0 b)) eqn:Heq1.
        shelve. inversion H0. Unshelve.
        exists t. edestruct (IHe). reflexivity.
        apply H0B. subst Gamma''. subst Gamma'.
        erewrite <- update_update_compatible.
        apply H9. reflexivity. destruct H. subst b.
        unfold typeOf in Heq1. fold typeOf in Heq1.
        rewrite H in Heq1. destruct (typeOf Rho e0) eqn:Heq2.
        shelve. inversion Heq1. Unshelve.
        destruct t0; inversion Heq1.
        destruct (eqType t1 t0_1 && eqType t2 t0_2) eqn:Heq3.
        shelve. inversion Heq1. Unshelve.
        split. reflexivity. inversion H5. subst. assumption.
  Qed.

  (* Theorem completeness:
    Shows that any well-typed expression in the Curry type system
    can be assigned a determinism type. This establishes that
    determinism typing covers all valid programs. *)
  Theorem completeness :
    forall e Rho Gamma,
    Gamma = mkCompatibleCtx Rho ->
    well_typed Rho e ->
    exists d, Gamma |- e ::: d.
  Proof.
    fix completeness 1.
    intro e.
    induction e; intros Rho Gamma HG HW.
    * destruct (Gamma n) eqn:Heq.
        - exists D. apply Rule_Var.
          rewrite Heq. reflexivity.
        - exists ND. apply Rule_Var.
          rewrite Heq. reflexivity.
        - exists (Arrow d1 d2). apply Rule_Var.
          rewrite Heq. reflexivity.
    * exists D. apply Rule_Unit. reflexivity.
    * apply well_typed_Pair in HW. destruct HW as [HW1 HW2].
      destruct (IHe1 Rho Gamma HG HW1).
      destruct (IHe2 Rho Gamma HG HW2).
      destruct x; destruct x0; eexists; eapply Rule_Pair;
      try eassumption; try reflexivity.
    * remember HW as HWC. clear HeqHWC.
      apply well_typed_App in HW. destruct HW as [HW1 HW2].
      destruct (IHe1 Rho Gamma HG HW1).
      destruct (IHe2 Rho Gamma HG HW2).
      destruct x.
      - edestruct compatibility. eassumption. apply HW1.
        apply H. destruct H1.
        unfold well_typed in HWC.
        unfold typeOf in HWC. fold typeOf in HWC.
        rewrite H1 in HWC. destruct x; inversion H2; inversion HWC.
      - exists ND. eapply Rule_AppND. apply H. apply H0.
      - eexists. eapply Rule_AppND. apply H. apply H0.
    * apply well_typed_Abs in HW.
      edestruct (IHe (update Nat.eqb Rho n t) (update Nat.eqb Gamma n (mkCompatible t))). shelve. apply HW.
      eexists. apply (Rule_Abs). reflexivity. apply H.
      Unshelve. apply update_compatible. assumption.
    * apply well_typed_Choice in HW. destruct HW as [HW1 HW2].
      destruct (IHe1 Rho Gamma HG HW1).
      destruct (IHe2 Rho Gamma HG HW2).
      exists ND. eapply Rule_Choice. apply H. apply H0.
    * destruct b.
      - remember HW as HWC. clear HeqHWC.
        apply well_typed_Case_Unit in HW. destruct HW as [HW1 HW2].
        destruct (IHe Rho Gamma HG HW1).
        destruct (completeness e0 Rho Gamma HG HW2).
        destruct x.
        + exists x0. eapply Rule_CaseDUnit. apply H. apply H0.
        + exists ND. eapply Rule_CaseNDUnit. apply H. apply H0.
        + destruct (compatibility e Rho Gamma (Arrow x1 x2) HG HW1 H).
          destruct H1.
          unfold well_typed in HWC.
          unfold typeOf in HWC. fold typeOf in HWC.
          rewrite H1 in HWC.
          destruct x; inversion H2. inversion HWC.
      - destruct p.
        remember HW as HWC. clear HeqHWC.
        apply well_typed_Case_Pair in HW. destruct HW as [HW1 HW2].
        destruct (IHe Rho Gamma HG HW1).
        edestruct (completeness e0).
        reflexivity. apply HW2.
        destruct x.
        + exists x0. eapply Rule_CaseDPair.
          apply H. erewrite update_update_compatible.
          apply H0. apply HG.
        + exists ND. eapply Rule_CaseNDPair. apply H.
          erewrite update_update_compatible.
          apply H0. apply HG.
        + destruct (compatibility e Rho Gamma (Arrow x1 x2) HG HW1 H).
          destruct H1.
          unfold well_typed in HWC.
          unfold typeOf in HWC. fold typeOf in HWC.
          rewrite H1 in HWC.
          destruct x; inversion H2. inversion HWC.
  Qed.

  Lemma hasDType_unbound : forall e Gamma d t n,
    Gamma |- e ::: d ->
    anyIn (freeVars e) [n] = false ->
    update Nat.eqb Gamma n (mkCompatible t) |- e ::: d.
  Proof.
    fix hasDType_unbound 1.
    induction e; intros.
    - simpl in *. destruct (Nat.eqb n0 n) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst. rewrite Nat.eqb_refl in H0.
        inversion H0.
      + subst. apply Rule_Var. unfold update. rewrite Heq.
        inversion H. assumption.
    - inversion H. subst. simpl in *.
      apply Rule_Unit. reflexivity.
    - inversion H. subst. simpl in *.
      apply anyIn_cons in H0. destruct H0 as [HH1 HH2].
      apply anyIn_concat2 in HH1. destruct HH1 as [HH3 HH4].
      apply anyIn_concat2 in HH2. destruct HH2 as [HH5 HH6].
      eapply IHe1 in H3. eapply IHe2 in H5.
      eapply Rule_Pair. eassumption. eassumption. reflexivity.
      eassumption. eassumption.
    - unfold freeVars in H0. fold freeVars in H0.
      apply anyIn_concat2 in H0. destruct H0 as [H0_1 H0_2].
      inversion H; subst; simpl in *.
      + eapply IHe1 in H3. eapply IHe2 in H5.
        eapply Rule_AppND. eassumption. eassumption.
        eassumption. eassumption.
      + eapply IHe1 in H2. eapply IHe2 in H4.
        eapply Rule_AppFun. eassumption. eassumption.
        reflexivity. eassumption. eassumption.
    - inversion H. subst. simpl in *.
      destruct (n0 =? n) eqn:Heq.
      + rewrite Nat.eqb_eq in Heq. subst.
        eapply Rule_Abs. reflexivity.
        rewrite double_update. eassumption.
      + apply Nat.eqb_neq in Heq. eapply IHe in H7.
        eapply Rule_Abs. reflexivity. rewrite double_update_indep.
        apply H7. assumption. apply anyIn_removeb in H0. assumption.
        symmetry. assumption.
    - inversion H. subst. simpl in *.
      apply anyIn_concat2 in H0. destruct H0 as [HH1 HH2].
      eapply IHe1 in H4. eapply IHe2 in H6.
      eapply Rule_Choice. eassumption. eassumption.
      assumption. assumption.
    - destruct b eqn:HeqB; inversion H; subst; simpl in *.
      + apply anyIn_concat2 in H0. destruct H0 as [H0_1 H0_2].
        eapply IHe in H0_1.
        apply (hasDType_unbound e0 Gamma d0 t) in H0_2.
        eapply Rule_CaseNDUnit. eassumption. eassumption.
        eassumption. eassumption.
      + apply anyIn_concat2 in H0. destruct H0 as [H0_1 H0_2].
        eapply IHe in H0_1.
        apply (hasDType_unbound e0 Gamma d t) in H0_2.
        eapply Rule_CaseDUnit. eassumption. eassumption.
        eassumption. eassumption.
      + subst p0. apply anyIn_concat2 in H0. destruct H0 as [H0_1 H0_2].
        subst Gamma''. subst Gamma'.
        destruct (n1 =? n) eqn:Heq1, (n2 =? n) eqn:Heq2.
        * apply Nat.eqb_eq in Heq1. subst.
          eapply IHe in H0_1. eapply Rule_CaseNDPair.
          eassumption. rewrite double_update. apply H8.
          apply H7.
        * apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. subst.
          eapply IHe in H0_1. eapply Rule_CaseNDPair.
          eassumption. rewrite double_update. apply H8.
          apply H7.
        * apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. subst.
          eapply IHe in H0_1. eapply Rule_CaseNDPair.
          eassumption. rewrite double_update_indep.
          rewrite double_update. rewrite double_update_indep.
          apply H8. symmetry. assumption. assumption. assumption.
        * apply Nat.eqb_neq in Heq1. apply Nat.eqb_neq in Heq2.
          eapply IHe in H0_1. eapply anyIn_removeb in H0_2.
          eapply anyIn_removeb in H0_2.
          apply (hasDType_unbound e0
                   (update Nat.eqb (update Nat.eqb Gamma n1
                           (mkCompatible t1))n2 (mkCompatible t2)) d0 t)
                     in H0_2.
          eapply Rule_CaseNDPair.
          eassumption.
          rewrite (double_update_indep _ n _ n1).
          rewrite (double_update_indep _ n _ n2).
          apply H0_2. symmetry. eassumption. symmetry. eassumption.
          apply H8. eassumption. eassumption. eassumption.
      + subst p0. apply anyIn_concat2 in H0. destruct H0 as [H0_1 H0_2].
        subst Gamma''. subst Gamma'.
        destruct (n1 =? n) eqn:Heq1, (n2 =? n) eqn:Heq2.
        * apply Nat.eqb_eq in Heq1. subst.
          eapply IHe in H0_1. eapply Rule_CaseDPair.
          eassumption. rewrite double_update. apply H8.
          apply H7.
        * apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. subst.
          eapply IHe in H0_1. eapply Rule_CaseDPair.
          eassumption. rewrite double_update. apply H8.
          apply H7.
        * apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. subst.
          eapply IHe in H0_1. eapply Rule_CaseDPair.
          eassumption. rewrite double_update_indep.
          rewrite double_update. rewrite double_update_indep.
          apply H8. symmetry. assumption. assumption. assumption.
        * apply Nat.eqb_neq in Heq1. apply Nat.eqb_neq in Heq2.
          eapply IHe in H0_1. eapply anyIn_removeb in H0_2.
          eapply anyIn_removeb in H0_2.
          apply (hasDType_unbound e0
                   (update Nat.eqb (update Nat.eqb Gamma n1
                           (mkCompatible t1))n2 (mkCompatible t2)) d t)
                     in H0_2.
          eapply Rule_CaseDPair.
          eassumption.
          rewrite (double_update_indep _ n _ n1).
          rewrite (double_update_indep _ n _ n2).
          apply H0_2. symmetry. eassumption. symmetry. eassumption.
          apply H8. eassumption. eassumption. eassumption.
  Qed.

  (* Lemma subst_lemma:
   A key substitution lemma showing that if a well-typed expression e1 has a
   determinism type d2, and we substitute a well-typed expression e2 with
   compatible determinism type, then the result maintains a determinism type
   that is at least as specific as the original. *)
  Lemma subst_lemma : forall e1 e2 Rho t1 d2 d3 n,
    anyIn (freeVars e2) (n::boundVars e1) = false ->
    well_typed (update Nat.eqb Rho n t1) e1 ->
    typeOf Rho e2 = Some t1 ->
    let Gamma := mkCompatibleCtx Rho in
    let d1 := mkCompatible t1 in
    update Nat.eqb Gamma n d1 |- e1 ::: d2 ->
    more_specific d3 d1 = true ->
    Gamma |- e2 ::: d3 ->
    exists d4,
      more_specific d4 d2 = true /\
      Gamma |- subst n e2 e1 ::: d4.
  Proof.
    fix subst_lemma 1.
    --
    induction e1; intros.
    - inversion H2. subst. simpl.
      unfold update. destruct (Nat.eqb n n0) eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst.
        rewrite Nat.eqb_refl in *.
        exists d3. split. assumption. assumption.
      + rewrite Nat.eqb_sym in Heq. rewrite Heq in *.
        exists (update Nat.eqb Gamma n0 d1 n).
        unfold update. rewrite Heq. split.
        apply more_specific_refl.
        apply Rule_Var. reflexivity.
    - inversion H2. subst. simpl in *.
      exists D. split. apply more_specific_refl.
      apply Rule_Unit. reflexivity.
    - inversion H2. subst. simpl in *.
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_concat1 in HH1. destruct HH1 as [HH3 HH4].
      apply well_typed_Pair in H0. destruct H0 as [H0_1 H0_2].
      edestruct IHe1_1 in H7. apply anyIn_cons_r; eassumption. eassumption. eassumption. eassumption. eassumption.
      eassumption.
      edestruct IHe1_2 in H9. apply anyIn_cons_r; eassumption.
      eassumption. eassumption. eassumption. eassumption.
      eassumption. destruct H. destruct H0. eexists. split.
      shelve. eapply Rule_Pair. eassumption. eassumption.
      reflexivity. Unshelve. subst d1.
      destruct x, x0, d0, d4; try inversion H;
      try inversion H0; try rewrite H10; try reflexivity.
    - remember H0 as HWC. clear HeqHWC.
      apply well_typed_App in H0. destruct H0 as [H0_1 H0_2].
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_App in HH1. destruct HH1 as [HH3 HH4].
      inversion H2; subst.
      + eexists. split. apply more_specific_ND. simpl.
        edestruct IHe1_1 in H6; try apply anyIn_cons_r; try eassumption.
        edestruct IHe1_2 in H8; try apply anyIn_cons_r; try eassumption.
        destruct H. destruct H0. eapply Rule_AppND.
        apply H5. apply H7.
      + remember H4 as H4C. clear HeqH4C.
        edestruct IHe1_1 in H5; try apply anyIn_cons_r; try eassumption.
        edestruct IHe1_2 in H7; try apply anyIn_cons_r; try eassumption.
        destruct H. destruct H0. simpl. destruct x.
        * inversion H.
        * inversion H.
        * eexists. split. shelve.
          eapply Rule_AppFun. apply H6. apply H8. reflexivity.
          Unshelve. simpl in H. apply andb_true_iff in H.
          destruct H. unfold decide.
          destruct (more_specific d5 d0) eqn:Heq1.
          shelve. apply more_specific_ND. Unshelve.
          rewrite less_specific_more_specific in H.
          eapply (more_specific_transitive d5 d0 x1) in Heq1.
          eapply (more_specific_transitive x0 d5 x1) in Heq1.
          rewrite Heq1. assumption. assumption. assumption.
    - inversion H2. subst. remember H0 as HC. clear HeqHC.
      apply well_typed_Abs in H0.
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_Abs in HH1. destruct HH1 as [HH3 HH4].
      destruct (n0 =? n) eqn:Heq.
      + subst d1. apply Nat.eqb_eq in Heq. subst.
        eexists. simpl. rewrite Nat.eqb_refl.
        split. shelve. eapply Rule_Abs.
        reflexivity. subst Gamma'.
        rewrite double_update in H11. apply H11.
        Unshelve. simpl. rewrite less_specific_refl. rewrite more_specific_refl. reflexivity.
      + apply Nat.eqb_neq in Heq. subst Gamma'.
        rewrite double_update_indep in H0; try assumption.
        rewrite double_update_indep in H11; try assumption.
        edestruct IHe1 in H11. apply anyIn_cons_r; eassumption.
        eassumption. erewrite typeOf_unbound. eassumption. eassumption.
        eassumption. erewrite update_compatible. subst d1.
        erewrite update_update_compatible in H11. apply H11.
        reflexivity. reflexivity. subst Gamma. apply H3.
        erewrite <- update_compatible.
        apply hasDType_unbound. apply H4. assumption.
        reflexivity. destruct H. eexists. split. shelve. simpl.
        apply Nat.eqb_neq in Heq. rewrite Nat.eqb_sym in Heq.
        rewrite Heq. eapply Rule_Abs. reflexivity.
        erewrite update_compatible. apply H5. reflexivity.
        Unshelve. simpl. rewrite less_specific_refl.
        rewrite H. reflexivity.
    - inversion H2. subst.
      apply well_typed_Choice in H0. destruct H0 as [H0_1 H0_2].
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_concat1 in HH1. destruct HH1 as [HH3 HH4].
      edestruct IHe1_1 in H8. apply anyIn_cons_r; eassumption.
      eassumption. eassumption. eassumption. eassumption. eassumption.
      edestruct IHe1_2 in H10. apply anyIn_cons_r; eassumption.
      eassumption. eassumption. eassumption. eassumption. eassumption.
      destruct H, H0.
      exists ND. split. apply more_specific_ND. simpl.
      eapply Rule_Choice; eassumption.
    - destruct b; inversion H2; subst.
      * remember H0 as H0C. clear HeqH0C.
        apply well_typed_Case_Unit in H0.
        destruct H0 as [H0A H0B].
        apply anyIn_cons in H. destruct H as [HH1 HH2].
        apply anyIn_Case_Unit in HH1. destruct HH1 as [HH3 HH4].
        edestruct IHe1 in H0A. apply anyIn_cons_r; eassumption.
        eassumption. eassumption. eassumption. apply H3. eassumption.
        edestruct subst_lemma. apply anyIn_cons_r. apply HH4.
        eassumption. eassumption. eassumption. eassumption.
        eassumption. eassumption. destruct H, H0. destruct x.
        + exists x0. split. apply more_specific_ND. simpl.
          apply Rule_CaseDUnit. assumption. assumption.
        + exists ND. split. apply more_specific_ND. simpl.
          eapply Rule_CaseNDUnit. assumption. eassumption.
        + unfold well_typed in H0A. unfold well_typed in H0B.
          destruct (typeOf (update Nat.eqb Rho n t1) e1) eqn:Heq1;
          destruct (typeOf (update Nat.eqb Rho n t1) e) eqn:Heq2;
          try contradiction.
          eapply subst_preservation in H1. shelve.
          apply anyIn_cons_r. apply HH3. apply HH2. apply Heq1.
          Unshelve. edestruct compatibility. reflexivity.
          unfold well_typed. rewrite H1. reflexivity.
          apply H5. destruct H7. rewrite H1 in H7. inversion H7.
          subst. unfold well_typed in H0C. unfold typeOf in H0C.
          fold typeOf in H0C. rewrite Heq1 in H0C.
          destruct x; try inversion H9; contradiction.
      * remember H0 as H0C. clear HeqH0C.
        apply well_typed_Case_Unit in H0.
        destruct H0 as [H0A H0B].
        apply anyIn_cons in H. destruct H as [HH1 HH2].
        apply anyIn_Case_Unit in HH1. destruct HH1 as [HH3 HH4].
        edestruct IHe1 in H0A. apply anyIn_cons_r; eassumption.
        eassumption. eassumption. eassumption. apply H3. eassumption.
        edestruct subst_lemma. apply anyIn_cons_r. apply HH4.
        eassumption. eassumption. eassumption. eassumption.
        eassumption. eassumption. destruct H, H0. destruct x.
        + exists x0. split. assumption. simpl.
          apply Rule_CaseDUnit. assumption. assumption.
        + inversion H.
        + unfold well_typed in H0A. unfold well_typed in H0B.
          destruct (typeOf (update Nat.eqb Rho n t1) e1) eqn:Heq1;
          destruct (typeOf (update Nat.eqb Rho n t1) e) eqn:Heq2;
          try contradiction.
          eapply subst_preservation in H1. shelve.
          apply anyIn_cons_r. apply HH3. apply HH2. apply Heq1.
          Unshelve. edestruct compatibility. reflexivity.
          unfold well_typed. rewrite H1. reflexivity.
          apply H5. destruct H7. rewrite H1 in H7. inversion H7.
          subst. unfold well_typed in H0C. unfold typeOf in H0C.
          fold typeOf in H0C. rewrite Heq1 in H0C.
          destruct x; try inversion H9; contradiction.
      * remember H0 as H0C. clear HeqH0C.
        apply well_typed_Case_Pair in H0.
        destruct H0 as [H0A H0B].
        remember H12 as H12C. clear HeqH12C.
        apply anyIn_cons in H. destruct H as [HH1 HH2].
        apply anyIn_Case_Pair in HH1. destruct HH1 as [HH3 HH4].
        apply anyIn_cons in HH4. destruct HH4 as [HH5 HH6].
        apply anyIn_cons in HH5. destruct HH5 as [HH7 HH8].
        edestruct IHe1 in H0A. apply anyIn_cons_r; eassumption.
        eassumption. eassumption. eassumption. apply H3. eassumption.
        destruct H. simpl.
        destruct (n =? n1) eqn:Heq1, (n =? n2) eqn:Heq2.
        + apply Nat.eqb_eq in Heq1. apply Nat.eqb_eq in Heq2. subst.
          subst Gamma''. subst Gamma'.
          erewrite double_update in H12. erewrite double_update in H12.
          destruct x.
          ++  exists d. split. apply more_specific_ND.
              apply Rule_CaseDPair. assumption.
              erewrite double_update. apply H12.
          ++  exists ND. split. apply more_specific_ND. simpl.
              eapply Rule_CaseNDPair. assumption.
              erewrite double_update. eassumption.
          ++  unfold well_typed in H0A. unfold well_typed in H0B.
              destruct (typeOf (update Nat.eqb Rho n2 t1) e1) eqn:Heq1;
              destruct (typeOf (update Nat.eqb Rho n2 t1) e) eqn:Heq2;
              try contradiction.
        + apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. subst.
          subst Gamma''. subst Gamma'.
          erewrite double_update in H12.
          erewrite double_update_indep in H12. shelve. assumption.
          Unshelve. destruct x.
          ++  exists d. split. apply more_specific_ND.
              apply Rule_CaseDPair. assumption.
              erewrite double_update_indep. apply H12. assumption.
          ++  exists ND. split. apply more_specific_ND. simpl.
              eapply Rule_CaseNDPair. assumption.
              erewrite double_update_indep. eassumption. eassumption.
          ++  unfold well_typed in H0A. unfold well_typed in H0B.
              destruct (typeOf (update Nat.eqb Rho n1 t1) e1) eqn:Heq4;
              try contradiction.
              eapply subst_preservation in H1. shelve.
              apply anyIn_cons_r. apply HH3. apply HH2. apply Heq4.
              Unshelve. edestruct compatibility. reflexivity.
              unfold well_typed. rewrite H1. reflexivity. apply H0.
              destruct p0. subst. unfold well_typed in H0C.
              unfold typeOf in H0C. fold typeOf in H0C.
              rewrite Heq4 in H0C. destruct t; try contradiction.
              destruct H6. rewrite H1 in H6. inversion H6. subst.
              inversion H7.
        + apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. subst.
          subst Gamma''. subst Gamma'.
          erewrite double_update_indep in H12.
          erewrite double_update in H12.  shelve. assumption.
          Unshelve. destruct x.
          ++  exists d. split. apply more_specific_ND.
              apply Rule_CaseDPair. assumption.
              erewrite double_update_indep. apply H12. assumption.
          ++  exists ND. split. apply more_specific_ND. simpl.
              eapply Rule_CaseNDPair. assumption.
              erewrite double_update_indep. eassumption. eassumption.
          ++  unfold well_typed in H0A. unfold well_typed in H0B.
              destruct (typeOf (update Nat.eqb Rho n2 t1) e1) eqn:Heq4;
              try contradiction.
              eapply subst_preservation in H1. shelve.
              apply anyIn_cons_r. apply HH3. apply HH2. apply Heq4.
              Unshelve. edestruct compatibility. reflexivity.
              unfold well_typed. rewrite H1. reflexivity. apply H0.
              destruct p0. subst. unfold well_typed in H0C.
              unfold typeOf in H0C. fold typeOf in H0C.
              rewrite Heq4 in H0C. destruct t; try contradiction.
              destruct H6. rewrite H1 in H6. inversion H6. subst.
              inversion H7.
        + apply Nat.eqb_neq in Heq1. apply Nat.eqb_neq in Heq2.
          subst Gamma''. subst Gamma'. simpl.
          rewrite (double_update_indep _ n _ n1) in H0B.
          rewrite (double_update_indep _ n _ n2) in H0B.
          shelve. assumption. assumption. Unshelve.
          edestruct subst_lemma. apply anyIn_cons_r. apply HH7.
          eassumption. eassumption.
          erewrite typeOf_unbound. erewrite typeOf_unbound.
          apply H1. apply H1. assumption.
          erewrite typeOf_unbound. eassumption. eassumption.
          eassumption. eassumption.
          erewrite <- update_compatible.
          rewrite (double_update_indep _ n _ n1) in H12.
          rewrite (double_update_indep _ n _ n2) in H12.
          apply H12. assumption. assumption.
          apply update_compatible. reflexivity. apply H3.
          erewrite <- update_compatible with
            (Gamma := mkCompatibleCtx (update Nat.eqb Rho n1 t0)).
          erewrite <- update_compatible with
            (Gamma := mkCompatibleCtx Rho).
          eapply hasDType_unbound.
          eapply hasDType_unbound.
          apply H4. assumption. assumption. reflexivity. reflexivity.
          destruct H6. destruct x.
          ++  exists x0. split. apply more_specific_ND.
              apply Rule_CaseDPair. assumption.
              erewrite update_compatible. apply H7.
              apply update_compatible. reflexivity.
          ++  exists ND. split. apply more_specific_ND. simpl.
              eapply Rule_CaseNDPair. assumption.
              erewrite update_compatible. apply H7.
              apply update_compatible. reflexivity.
          ++  unfold well_typed in H0A. unfold well_typed in H0B.
              destruct (typeOf (update Nat.eqb Rho n t1) e1) eqn:Heq3;
              try contradiction.
              destruct (typeOf (update Nat.eqb (update Nat.eqb
                               (update Nat.eqb Rho n1 t0) n2 t2)
                                n t1) e) eqn:Heq4;
              try contradiction.
              eapply subst_preservation in H1. shelve.
              apply anyIn_cons_r. apply HH3. apply HH2. apply Heq3.
              Unshelve. edestruct compatibility. reflexivity.
              unfold well_typed. rewrite H1. reflexivity. apply H0.
              destruct p0. subst. unfold well_typed in H0C.
              unfold typeOf in H0C. fold typeOf in H0C.
              rewrite Heq3 in H0C. destruct t; try contradiction.
              destruct H8. rewrite H1 in H8. inversion H8. subst.
              inversion H9.
    * remember H0 as H0C. clear HeqH0C.
      apply well_typed_Case_Pair in H0.
      destruct H0 as [H0A H0B].
      remember H12 as H12C. clear HeqH12C.
      apply anyIn_cons in H. destruct H as [HH1 HH2].
      apply anyIn_Case_Pair in HH1. destruct HH1 as [HH3 HH4].
      apply anyIn_cons in HH4. destruct HH4 as [HH5 HH6].
      apply anyIn_cons in HH5. destruct HH5 as [HH7 HH8].
      edestruct IHe1 in H0A. apply anyIn_cons_r; eassumption.
      eassumption. eassumption. eassumption. apply H3. eassumption.
      destruct H. simpl.
      destruct (n =? n1) eqn:Heq1, (n =? n2) eqn:Heq2.
      + apply Nat.eqb_eq in Heq1. apply Nat.eqb_eq in Heq2. subst.
        subst Gamma''. subst Gamma'.
        erewrite double_update in H12. erewrite double_update in H12.
        destruct x.
        ++  exists d2. split. apply more_specific_refl.
            apply Rule_CaseDPair. assumption.
            erewrite double_update. apply H12.
        ++  inversion H.
        ++  inversion H.
      + apply Nat.eqb_eq in Heq1. apply Nat.eqb_neq in Heq2. subst.
        subst Gamma''. subst Gamma'.
        erewrite double_update in H12.
        erewrite double_update_indep in H12. shelve. assumption.
        Unshelve. destruct x.
        ++  exists d2. split. apply more_specific_refl.
            apply Rule_CaseDPair. assumption.
            erewrite double_update_indep. apply H12. assumption.
        ++  inversion H.
        ++  inversion H.
      + apply Nat.eqb_neq in Heq1. apply Nat.eqb_eq in Heq2. subst.
        subst Gamma''. subst Gamma'.
        erewrite double_update_indep in H12.
        erewrite double_update in H12.  shelve. assumption.
        Unshelve. destruct x.
        ++  exists d2. split. apply more_specific_refl.
            apply Rule_CaseDPair. assumption.
            erewrite double_update_indep. apply H12. assumption.
        ++  inversion H.
        ++  inversion H.
      + apply Nat.eqb_neq in Heq1. apply Nat.eqb_neq in Heq2.
        subst Gamma''. subst Gamma'. simpl.
        rewrite (double_update_indep _ n _ n1) in H0B.
        rewrite (double_update_indep _ n _ n2) in H0B.
        shelve. assumption. assumption. Unshelve.
        edestruct subst_lemma. apply anyIn_cons_r. apply HH7.
        eassumption. eassumption.
        erewrite typeOf_unbound. erewrite typeOf_unbound.
        apply H1. apply H1. assumption.
        erewrite typeOf_unbound. eassumption. eassumption.
        eassumption. eassumption.
        erewrite <- update_compatible.
        rewrite (double_update_indep _ n _ n1) in H12.
        rewrite (double_update_indep _ n _ n2) in H12.
        apply H12. assumption. assumption.
        apply update_compatible. reflexivity. apply H3.
        erewrite <- update_compatible with
          (Gamma := mkCompatibleCtx (update Nat.eqb Rho n1 t0)).
        erewrite <- update_compatible with
          (Gamma := mkCompatibleCtx Rho).
        eapply hasDType_unbound.
        eapply hasDType_unbound.
        apply H4. assumption. assumption. reflexivity. reflexivity.
        destruct H6. destruct x.
        ++  exists x0. split. assumption.
            apply Rule_CaseDPair. assumption.
            erewrite update_compatible. apply H7.
            apply update_compatible. reflexivity.
        ++  inversion H.
        ++  inversion H.
  Qed.

  Lemma subst_lemma2 :
    forall e1 e2 e3 Rho t1 t2 t3 n n3 d2' d3',
    anyIn (freeVars e2) (n3::n::boundVars e1) = false ->
    anyIn (freeVars e3) (n3::n::boundVars e1) = false ->
    anyIn (freeVars e2) (boundVars e3) = false ->
    well_typed (update Nat.eqb (update Nat.eqb Rho n3 t3) n t2) e1 ->
    typeOf Rho e2 = Some t2 ->
    typeOf Rho e3 = Some t3 ->
    n <> n3 ->
    let Gamma := mkCompatibleCtx Rho in
    let d1 := mkCompatible t1 in
    let d2 := mkCompatible t2 in
    let d3 := mkCompatible t3 in
    update Nat.eqb (update Nat.eqb Gamma n3 d3) n d2 |- e1 ::: d1 ->
    more_specific d2' d2 = true ->
    more_specific d3' d3 = true ->
    Gamma |- e2 ::: d2' ->
    Gamma |- e3 ::: d3' ->
    exists d4,
      more_specific d4 d1 = true /\
      Gamma |- subst n e2 (subst n3 e3 e1) ::: d4.
  Proof.
    intros.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H. destruct H.
    apply anyIn_cons in H0. destruct H0.
    apply anyIn_cons in H0. destruct H0.
    unfold well_typed in H2.
    destruct (typeOf (update Nat.eqb (update Nat.eqb Rho n3 t3) n t2)
                   e1) eqn:Heq1;
    try inversion H2.
    edestruct subst_lemma with (e1 := e1).
    + apply anyIn_cons_r. apply H0. apply H13.
    + unfold well_typed.
      rewrite double_update_indep in Heq1.
      rewrite Heq1. reflexivity. symmetry. assumption.
    + erewrite typeOf_unbound. apply H4. apply H4. assumption.
    + erewrite <- (update_compatible _ (Rho)).
      erewrite double_update_indep.
      apply H6. assumption. reflexivity.
    + apply H8.
    + erewrite <- update_compatible.
      eapply (hasDType_unbound).
      apply H10. assumption. reflexivity.
    + destruct H15.
      edestruct subst_lemma with (e1 := subst n3 e3 e1).
      - apply anyIn_cons_r. apply any_in_subst. apply H. apply H13.
        apply H1. apply H12.
      - unfold well_typed.
        erewrite subst_preservation. reflexivity.
        apply anyIn_cons_r. apply H0. apply H13.
        rewrite double_update_indep.
        rewrite Heq1. reflexivity. assumption.
        erewrite typeOf_unbound. assumption. eassumption. assumption.
      - assumption.
      - erewrite update_compatible. apply H16. reflexivity.
      - apply H7.
      - apply H9.
      - destruct H17. exists x0.
        split. eapply more_specific_transitive. apply H17.
        apply H15. apply H18.
  Qed.

  Lemma case_no_arrow : forall Rho e1 e2 d1 d2 b,
    let Gamma := mkCompatibleCtx Rho in
    (Gamma |- e1 ::: Arrow d1 d2 \/ Gamma |- e2 ::: Arrow d1 d2) ->
    well_typed Rho (Case (Or e1 e2) b) ->
    False.
  Proof.
    intros.
    remember H0 as H0C. clear HeqH0C.
    apply well_typed_Case in H0.
    apply well_typed_Choice in H0.
    destruct H0.
    destruct H; destruct b.
    - edestruct compatibility. reflexivity.
      apply H0. apply H. destruct H2.
      unfold well_typed in H0C.
      unfold typeOf in H0C. fold typeOf in H0C.
      destruct x; inversion H3.
      rewrite H2 in H0C.
      destruct (eqTypeS (Some (TArrow x1 x2))
                        (typeOf Rho e2)) eqn:Heq;
      try inversion H0C.
    - destruct p. edestruct compatibility. reflexivity.
      apply H0. apply H. destruct H2.
      unfold well_typed in H0C.
      unfold typeOf in H0C. fold typeOf in H0C.
      destruct x; inversion H3.
      rewrite H2 in H0C.
      destruct (eqTypeS (Some (TArrow x1 x2))
                        (typeOf Rho e2)) eqn:Heq;
      try inversion H0C.
    - edestruct compatibility. reflexivity.
      apply H1. apply H. destruct H2.
      unfold well_typed in H0C.
      unfold typeOf in H0C. fold typeOf in H0C.
      destruct x; inversion H3.
      rewrite H2 in H0C.
      destruct (eqTypeS (typeOf Rho e1)
                        (Some (TArrow x1 x2))) eqn:Heq;
      try inversion H0C.
      destruct (typeOf Rho e1) eqn:Heq2;
      try inversion H0C.
      destruct t; try inversion H0C. inversion Heq.
    - destruct p. edestruct compatibility. reflexivity.
      apply H1. apply H. destruct H2.
      unfold well_typed in H0C.
      unfold typeOf in H0C. fold typeOf in H0C.
      destruct x; inversion H3.
      rewrite H2 in H0C.
      destruct (eqTypeS (typeOf Rho e1)
                        (Some (TArrow x1 x2))) eqn:Heq;
      try inversion H0C.
      destruct (typeOf Rho e1) eqn:Heq2;
      try inversion H0C.
      destruct t; try inversion H0C. inversion Heq.
  Qed.

  (* Theorem preservation:
   Shows that if an expression e reduces to e', then the determinism type
   of e' is at least as specific as the determinism type of e.
   This is the core type safety property for the determinism type system. *)
  Theorem preservation : forall Rho e e' t d,
    let Gamma := mkCompatibleCtx Rho in
    e ==> e' ->
    typeOf Rho e = Some t ->
    compatible d t ->
    Gamma |- e ::: d ->
    exists d', more_specific d' d = true /\ compatible d' t
      /\ Gamma |- e' ::: d'.
  Proof.
    intro Rho. intro e.
    generalize dependent Rho.
    induction e; intros Rho e' t0 d0 Gamma H HW HC H0; inversion H.
    * inversion H1.
    * inversion H1.
    * inversion H1. inversion H0. subst.
      remember HW as HWC. clear HeqHWC.
      unfold typeOf in HW. fold typeOf in HW.
      destruct (typeOf Rho e1) eqn:Heq1; try inversion HW.
      destruct (typeOf Rho e2) eqn:Heq2;
      inversion HW; subst.
      destruct (step e1) eqn:Heq.
      + remember Heq1 as Heq1C. clear HeqHeq1C.
        destruct d1.
        - edestruct (IHe1 Rho e t D). apply Single_Step.
          apply Heq. eassumption. destruct t; try reflexivity.
          edestruct compatibility. reflexivity. unfold well_typed.
          rewrite Heq1. reflexivity. apply H7. destruct H2.
          rewrite H2 in Heq1C. inversion Heq1C. subst.
          inversion H4. apply H7.
          apply (step_preservation e1 e Rho t Heq) in Heq1.
          inversion H5. subst. destruct H2, H4, d2; subst.
          --  destruct x; inversion H2; subst.
              exists D. split. apply more_specific_refl.
              split. reflexivity. eapply Rule_Pair. apply H6. apply H9. reflexivity.
          --  exists ND. split. apply more_specific_ND. split. reflexivity.
              eapply Rule_Pair. apply H6. apply H9.
              destruct x; reflexivity.
          --  exists ND. split. apply more_specific_ND. split. reflexivity.
              eapply Rule_Pair. apply H6. apply H9.
              destruct x; reflexivity.
        - edestruct IHe1 with (d := ND). apply Single_Step.
          apply Heq. eassumption. reflexivity. apply H7.
          destruct H2, H4. inversion H5. subst.
          eexists. split. apply more_specific_ND.
          split. shelve. eapply Rule_Pair. apply H6. apply H9. reflexivity.
          Unshelve. destruct x, d2; reflexivity.
        - inversion H5. subst.
          edestruct IHe1 with (d := Arrow d1_1 d1_2). apply Single_Step.
          apply Heq. eassumption. edestruct compatibility. reflexivity.
          unfold well_typed. rewrite Heq1. reflexivity. apply H7. destruct H2.
          rewrite H2 in Heq1C. inversion Heq1C. subst. assumption. apply H7.
          destruct H2, H4. inversion H5. subst.
          eexists. split. apply more_specific_ND. split. shelve.
          eapply Rule_Pair. apply H6. apply H9. reflexivity.
          Unshelve. destruct x, d2; reflexivity.
      + destruct (step e2) eqn:Heq3; inversion H5.
        remember Heq2 as Heq2C. clear HeqHeq2C.
        destruct d2.
        - subst. edestruct (IHe2 Rho e t1 D). apply Single_Step. apply Heq3.
          apply Heq2. destruct t1; try reflexivity.
          edestruct compatibility. reflexivity. unfold well_typed.
          rewrite Heq2. reflexivity. apply H9. destruct H2.
          rewrite H2 in Heq2C. inversion Heq2C. subst.
          inversion H4. apply H9. destruct H2, H4, d1; subst.
          --  destruct x; try inversion H2.
              exists D. split. apply more_specific_refl. split. reflexivity.
              eapply Rule_Pair. apply H7. apply H6. reflexivity.
          --  destruct x; try inversion H2. eexists. split. apply more_specific_ND.
              split. shelve. eapply Rule_Pair. apply H7. apply H6. reflexivity.
              Unshelve. reflexivity.
          --  destruct x; try inversion H2. eexists. split. apply more_specific_ND.
              split. shelve. eapply Rule_Pair. apply H7. apply H6. reflexivity.
              Unshelve. reflexivity.
        - edestruct IHe2 with (d := ND). apply Single_Step.
          apply Heq3. eassumption. reflexivity. apply H9.
          destruct H2, H6. eexists. split. destruct d1; apply more_specific_ND.
          split. shelve. eapply Rule_Pair. apply H7. apply H8. reflexivity.
          Unshelve. destruct x, d1; reflexivity.
        - edestruct IHe2 with (d := Arrow d2_1 d2_2). apply Single_Step.
          apply Heq3. eassumption. edestruct compatibility. reflexivity.
          unfold well_typed. rewrite Heq2. reflexivity. apply H9. destruct H2.
          rewrite H2 in Heq2C. inversion Heq2C. subst. assumption. apply H9.
          destruct H2, H6. eexists. split. destruct d1; apply more_specific_ND. split. shelve.
          eapply Rule_Pair. apply H7. apply H8. reflexivity.
          Unshelve. destruct x, d1; reflexivity.
    * inversion H1. subst.
      remember H0 as H0C. clear HeqH0C.
      remember HW as HWC. clear HeqHWC.
      unfold typeOf in HW. fold typeOf in HW.
      destruct (typeOf Rho e1) eqn:Heq1; try inversion HW.
      destruct t eqn:Heq2; try inversion HW.
      destruct (typeOf Rho e2) eqn:Heq3; try inversion HW.
      destruct (eqType t1_1 t1) eqn:Heq4; try inversion HW.
      apply eq_Type_eq in Heq4. subst t1_1.
      destruct e1 eqn:Heq5.
      + simpl in H5. inversion H5.
      + inversion H5.
      (* App Pair *)
      + unfold well_typed in HWC.
        unfold typeOf in HWC. fold typeOf in HWC.
        destruct (typeOf Rho e3) eqn:Heq4;
        try inversion HWC.
        destruct (typeOf Rho e4) eqn:Heq6;
        try inversion HWC; subst.
      (* App App *)
      + destruct (step (App e3 e4)) eqn:Heq; inversion H5.
        inversion H0; subst.
        - edestruct IHe1 with (d := d1).
          apply Single_Step. apply Heq. eassumption.
          edestruct (compatibility (App e3 e4)). reflexivity.
          unfold well_typed. rewrite Heq1. reflexivity. apply H11.
          destruct H2. rewrite Heq1 in H2. inversion H2. subst.
          assumption. apply H11. destruct H2, H7, x.
          --  inversion H7.
          --  exists ND. split. apply more_specific_ND. split. reflexivity.
              eapply Rule_AppND. apply H8. apply H13.
          --  eexists. split. apply more_specific_ND. split. shelve.
              eapply Rule_AppFun. apply H8. apply H13. reflexivity.
              Unshelve. unfold decide. destruct (more_specific d2 x1).
              destruct H7. assumption. reflexivity.
        - edestruct IHe1 with (d := (Arrow d1 d2)).
          apply Single_Step. apply Heq. eassumption.
          edestruct (compatibility (App e3 e4)). reflexivity.
          unfold well_typed. rewrite Heq1. reflexivity. apply H10.
          destruct H2. rewrite Heq1 in H2. inversion H2. subst.
          assumption. apply H10. destruct H2, H7, x.
          --  inversion H7.
          --  inversion H2.
          --  simpl in H2. apply (andb_true_iff) in H2. destruct H2.
              simpl in H7. destruct H7.
              unfold decide. destruct (more_specific d3 d1) eqn:Heq2.
              ++  exists x2. split. assumption. split.
                  assumption. eapply Rule_AppFun.
                  apply H8. apply H12. unfold decide.
                  erewrite more_specific_transitive.
                  reflexivity. eassumption.
                  rewrite more_specific_less_specific.
                  assumption.
              ++  eexists. split.
                  apply more_specific_ND. split. shelve.
                  eapply Rule_AppFun. apply H8. apply H12.
                  reflexivity. Unshelve. unfold decide.
                  destruct (more_specific d3 x1).
                  assumption. reflexivity.
      (* App Abs *)
      + inversion H5. remember HWC as HWC2. clear HeqHWC2.
        unfold typeOf in HWC. fold typeOf in HWC.
        destruct (typeOf (update Nat.eqb Rho n t2) e) eqn:Heq4;
        try inversion HWC.
        destruct (typeOf Rho e2) eqn:Heq6;
        try inversion HWC; subst.
        destruct (anyIn (freeVars e2) (n :: boundVars e)) eqn:Heq7;
        try discriminate. inversion H5.
        destruct (eqType t2 t4) eqn:Heq8; try inversion HWC.
        apply eq_Type_eq in Heq8. subst. inversion H0.
        - inversion Heq3. inversion H12; subst.
          edestruct (compatibility (Abs n t1 e)). reflexivity.
          unfold well_typed. rewrite Heq1. reflexivity.
          apply H12. destruct H2. rewrite Heq1 in H2. inversion H2. subst.
          inversion H7. specialize (step_preservation _ _ _ _ H1 HWC2). intros.
          edestruct (compatibility e2). reflexivity.
          unfold well_typed. rewrite Heq6. reflexivity. eassumption.
          destruct H16. rewrite Heq6 in H16. inversion H16; subst.
          edestruct subst_lemma.
          eassumption. unfold well_typed.
          rewrite Heq4. reflexivity. assumption. apply H22. shelve.
          apply H14. destruct H18. eexists. split. apply more_specific_ND.
          split. shelve. apply H19. Unshelve.
          give_up. give_up.
        - inversion H11; subst. edestruct subst_lemma.
          eassumption. unfold well_typed. rewrite Heq4. reflexivity.
          apply Heq6. shelve. shelve. apply H13.
          destruct H2. eexists. split.
          shelve. split. shelve. apply H7. Unshelve.
          give_up. give_up. give_up. give_up. give_up.
      (* App Or *)
      + destruct d0.
        - inversion H0; inversion H6. inversion H9.
        - inversion H0; try inversion H9.
          exists ND. split. apply more_specific_ND.
          split. reflexivity. inversion H5. inversion HW. subst.
          unfold typeOf in Heq1. fold typeOf in Heq1.
          destruct (typeOf Rho e3) eqn:Heq6,
                   (typeOf Rho e4) eqn:Heq7; try discriminate.
          simpl in Heq1. destruct (eqType t t2) eqn:Heq8; try inversion Heq1.
          apply eq_Type_eq in Heq8. subst.
          eapply (step_preservation (App (Or e3 e4) e2)
                                    (Or (App e3 e2) (App e4 e2))) in HWC.
          shelve. assumption. Unshelve. unfold typeOf in HWC.
          fold typeOf in HWC. rewrite Heq6, Heq7, Heq3, eqTypeS_refl in HWC.
          rewrite eqType_refl in HWC.
          edestruct (completeness (App e3 e2)). reflexivity.
          unfold well_typed. unfold typeOf. fold typeOf.
          rewrite Heq6, Heq3, eqType_refl. reflexivity.
          edestruct (completeness (App e4 e2)). reflexivity.
          unfold well_typed. unfold typeOf. fold typeOf.
          rewrite Heq7, Heq3, eqType_refl. reflexivity.
          eapply Rule_Choice. eassumption. eassumption.
        - inversion H0; inversion H6. inversion H9.
      (* App Case *)
      + destruct (step (Case e b)) eqn:Heq; inversion H5; subst.
        inversion H0; subst.
        - edestruct (compatibility (Case e b)). reflexivity.
          unfold well_typed. rewrite Heq1. reflexivity. apply H9.
          destruct H2. rewrite Heq1 in H2. inversion H2. subst.
          edestruct IHe1. apply Single_Step. apply Heq. eassumption.
          eassumption. apply H9. destruct H8, H10, x.
          --  inversion H10.
          --  exists ND. split. apply more_specific_ND.
              split. reflexivity.
              eapply Rule_AppND. apply H12. apply H11.
          --  eexists. split. apply more_specific_ND.
              split. shelve.
              eapply Rule_AppFun. apply H12. apply H11. reflexivity.
              Unshelve. unfold decide.
              destruct (more_specific d2 x1).
              simpl in H10. destruct H10. assumption. reflexivity.
        - edestruct (compatibility (Case e b)). reflexivity.
          unfold well_typed. rewrite Heq1. reflexivity. apply H8.
          destruct H2. rewrite Heq1 in H2. inversion H2. subst.
          edestruct IHe1. apply Single_Step. apply Heq. eassumption.
          eassumption. apply H8. destruct H9, H11, x; inversion H11;
          inversion H9. apply andb_true_iff in H16. destruct H16.
          unfold decide. rewrite H15. rewrite H16. simpl.
          destruct (more_specific d3 d1) eqn:Heq2.
          --  rewrite less_specific_more_specific in H15.
              eapply more_specific_transitive in H15.
              eexists. split. shelve. split. shelve.
              eapply Rule_AppFun. apply H12. apply H10.
              reflexivity. apply Heq2. Unshelve.
              unfold decide. rewrite H15. assumption.
              unfold decide. rewrite H15. assumption.
          --  eexists. split. apply more_specific_ND.
              split. shelve. eapply Rule_AppFun. apply H12. apply H10. reflexivity. Unshelve.
              unfold decide. destruct (more_specific d3 x1).
              assumption. reflexivity.
    * inversion H1.
    (* Or *)
    * inversion H1. inversion H0. subst.
      unfold typeOf in HW. fold typeOf in HW.
      destruct (typeOf Rho e1) eqn:Heq1,
               (typeOf Rho e2) eqn:Heq11; try inversion HW.
      simpl in HW. destruct (eqType t t1) eqn:Heq2; try inversion HW.
      apply eq_Type_eq in Heq2. subst.
      destruct (step e1) eqn:Heq3.
      + inversion H5. subst.
        edestruct IHe1. apply Single_Step. eassumption.
        eassumption. shelve. eassumption.
        destruct H2, H4. exists ND. split. apply more_specific_refl.
        split. reflexivity. eapply Rule_Choice; eassumption.
        Unshelve. edestruct (compatibility e1). reflexivity.
        unfold well_typed. rewrite Heq1. reflexivity.
        eassumption. destruct H2.
        rewrite Heq1 in H2. inversion H2. subst. assumption.
      + destruct (step e2) eqn:Heq2; inversion H5. subst.
        edestruct IHe2. apply Single_Step. eassumption.
        eassumption. shelve. eassumption.
        destruct H2, H4. exists ND. split. apply more_specific_refl.
        split. reflexivity. eapply Rule_Choice; eassumption.
        Unshelve. edestruct (compatibility e2). reflexivity.
        unfold well_typed. rewrite Heq11. reflexivity.
        eassumption. destruct H2.
        rewrite Heq11 in H2. inversion H2. subst. assumption.
    (* Case *)
    * inversion H1. destruct e eqn:Heq1; inversion H5.
      + destruct b; inversion H5; subst. inversion H0; subst.
        - inversion H7. inversion H2.
        - exists d0. split. apply more_specific_refl.
          split. assumption. assumption.
      + destruct b; inversion H5; subst. destruct p.
        destruct (anyIn (freeVars e1_1 ++ freeVars e1_2)
                        (n1 :: n2 :: boundVars e1)) eqn:Heq1;
        inversion H5.
        destruct (anyIn (freeVars e1_2) (boundVars e1_1)) eqn:Heq2;
        inversion H5.
        apply anyIn_concat2 in Heq1. destruct Heq1 as [HH1 HH2].
        unfold typeOf in HW. fold typeOf in HW.
        destruct (typeOf Rho e1_1) eqn:Heq1; try discriminate.
        destruct (typeOf Rho e1_2) eqn:Heq3; try discriminate.
        destruct (eqType t1 t) eqn:Heq4; try discriminate.
        destruct (eqType t2 t3) eqn:Heq5; try discriminate.
        apply eq_Type_eq in Heq4. apply eq_Type_eq in Heq5. subst.
        simpl in HW.
        inversion H0; subst.
        - (* do it via completeness instead*)
          inversion H17. subst.
          edestruct (compatibility e1_1). reflexivity.
          unfold well_typed. rewrite Heq1. reflexivity.
          apply H9. destruct H4. rewrite Heq1 in H4. inversion H4. subst.
          edestruct (compatibility e1_2). reflexivity.
          unfold well_typed. rewrite Heq3. reflexivity.
          apply H12. destruct H10. rewrite Heq3 in H10. inversion H10. subst.
          edestruct subst_lemma2.
          apply HH2. apply HH1. assumption.
          unfold well_typed. rewrite HW. reflexivity.
          assumption. assumption.  symmetry. assumption.
          subst Gamma'. subst Gamma''. shelve. shelve. shelve.
          apply H12. apply H9. destruct H16. eexists. split.
          apply more_specific_ND. split. shelve. apply H19.
          Unshelve. shelve. shelve. give_up. give_up. give_up.
        - inversion H17. destruct d1, d2; inversion H15. subst.
          edestruct subst_lemma2.
          apply HH2. apply HH1. assumption.
          unfold well_typed. rewrite HW. reflexivity.
          assumption. assumption. symmetry. assumption.
          subst Gamma'. subst Gamma''. shelve. shelve. shelve.
          apply H12. apply H9.
          destruct H4. exists x. split. shelve.
          split. shelve. apply H8.
          Unshelve. give_up. give_up. give_up. give_up.
          give_up. give_up. give_up. give_up.
      + subst. inversion H0; try inversion H6; try inversion H7; subst.
        - remember HW as HWC. clear HeqHWC.
          unfold typeOf in HW. fold typeOf in HW.
          destruct (typeOf Rho e1_1) eqn:Heq1,
                   (typeOf Rho e1_2) eqn:Heq2;
          try discriminate. simpl in HW.
          destruct (eqType t t1) eqn:Heq3; try discriminate.
          apply eq_Type_eq in Heq3. subst.
          destruct t1; try discriminate.
          eexists ND. split. apply more_specific_refl.
          split. reflexivity.
          destruct d1; destruct d2.
          --  eapply Rule_Choice; eapply Rule_CaseDUnit;
              eassumption.
          --  eapply Rule_Choice. eapply Rule_CaseDUnit.
              eassumption. eassumption.
              eapply Rule_CaseNDUnit; eassumption.
          --  edestruct case_no_arrow.
              right. apply H13. unfold well_typed.
              rewrite HWC. reflexivity.
          --  eapply Rule_Choice. eapply Rule_CaseNDUnit.
              eassumption. eassumption.
              eapply Rule_CaseDUnit; eassumption.
          --  eapply Rule_Choice; eapply Rule_CaseNDUnit;
              eassumption.
          --  edestruct case_no_arrow.
              right. apply H13. unfold well_typed.
              rewrite HWC. reflexivity.
          --  edestruct case_no_arrow.
              left. apply H12. unfold well_typed.
              rewrite HWC. reflexivity.
          --  edestruct case_no_arrow.
              left. apply H12. unfold well_typed.
              rewrite HWC. reflexivity.
          --  edestruct case_no_arrow.
              right. apply H13. unfold well_typed.
              rewrite HWC. reflexivity.
        - remember HW as HWC. clear HeqHWC.
          unfold typeOf in HW. fold typeOf in HW.
          destruct (typeOf Rho e1_1) eqn:Heq1,
                   (typeOf Rho e1_2) eqn:Heq2;
          try discriminate. simpl in HW.
          destruct (eqType t t3) eqn:Heq3; try discriminate.
          apply eq_Type_eq in Heq3. subst.
          destruct t3; try discriminate.
          eexists ND. split. apply more_specific_refl.
          split. reflexivity.
          destruct d1, d2.
          --  eapply Rule_Choice; eapply Rule_CaseDPair;
              eassumption.
          --  eapply Rule_Choice. eapply Rule_CaseDPair.
              eassumption. eassumption.
              eapply Rule_CaseNDPair; eassumption.
          --  edestruct case_no_arrow.
              right. apply H15. unfold well_typed.
              rewrite HWC. reflexivity.
          --  eapply Rule_Choice. eapply Rule_CaseNDPair.
              eassumption. eassumption.
              eapply Rule_CaseDPair; eassumption.
          --  eapply Rule_Choice; eapply Rule_CaseNDPair;
              eassumption.
          --  edestruct case_no_arrow.
              right. apply H15. unfold well_typed.
              rewrite HWC. reflexivity.
          --  edestruct case_no_arrow.
              left. apply H14. unfold well_typed.
              rewrite HWC. reflexivity.
          --  edestruct case_no_arrow.
              left. apply H14. unfold well_typed.
              rewrite HWC. reflexivity.
          --  edestruct case_no_arrow.
              right. apply H15. unfold well_typed.
              rewrite HWC. reflexivity.
  Admitted.

  Theorem preservation_multi : forall e e' t,
    e ==>* e' ->
    forall Rho d,
    let Gamma := mkCompatibleCtx Rho in
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
      remember H1 as H1C. clear HeqH1C.
      eapply (step_preservation _ _ _ _ H4) in H1.
      apply (preservation Rho e1 e2 t d) in H; try assumption.
      destruct H, H, H5, H7.
      destruct (IHmulti_step_rel Rho x).
      assumption. assumption. apply H7. destruct H8, H9.
      exists x0. split. eapply more_specific_transitive.
      eassumption. eassumption. split; assumption.
  Qed.

  (* Theorem soundness:
   The main theorem showing that if an expression e has deterministic type D,
   then any expression e' that e reduces to will not be a non-deterministic choice.
   This validates that the determinism type system correctly tracks non-determinism. *)
  Theorem soundness : forall Rho e e' t,
    let Gamma := mkCompatibleCtx Rho in
    typeOf Rho e = Some t ->
    Gamma |- e ::: D ->
    compatible D t ->
    e ==>* e' ->
    notOr e'.
  Proof.
    intros. unfold well_typed in H. destruct (typeOf Rho e) eqn:Heq;
    try inversion H. edestruct (preservation_multi e e') in H0.
    - assumption.
    - rewrite Heq. reflexivity.
    - inversion H; apply H1.
    - assumption.
    - destruct H3. destruct H5. apply more_specific_D in H3.
      subst. destruct e'; try reflexivity; try inversion H6.
  Qed.

End Proofs.
