From Wasm Require Export datatypes_properties operations typing opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Bool Program NArith ZArith Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section intro_opsem.

Context `{ho: host}.

(* Reduction of an instruction sequence.
   There's no explicit rule that allows this, yet this is certainly an expected behaviour. Prove the following by finding one/several appropriate reduction rule(s) that allows the reduction:
 *) 
Lemma opsem_reduce_seq1: forall hs1 s1 f1 es1 hs2 s2 f2 es2 es0,
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (es1 ++ es0) hs2 s2 f2 (es2 ++ es0).
Proof.
   intros.
   eapply r_label. exact H.
   instantiate (1 := LH_base [::] es0).
   all: simpl; reflexivity.
Qed.

Lemma e_to_v_inv : forall v,
   is_const v -> v_to_e (e_to_v v) = v.
Proof.
   intros. destruct v. destruct b.
   all: unfold is_const, e_to_v_opt in H; try discriminate H; reflexivity.
Qed.

Lemma e_to_v_list_inv : forall vs, 
   const_list vs -> v_to_e_list (e_to_v_list vs) = vs.
Proof.
   intros. induction vs.
   - reflexivity.
   - simpl in H. unfold is_true in H. rewrite -> andb_true_iff in H. destruct H.
     simpl. f_equal.
     + apply e_to_v_inv. exact H.
     + apply IHvs. exact H0.
Qed.
  
(* The same applies for attaching a list of values on the left. *)
Lemma opsem_reduce_seq2: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs,
    const_list vs ->
    reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
    reduce hs1 s1 f1 (vs ++ es1) hs2 s2 f2 (vs ++ es2).
Proof.
   intros.
   eapply r_label. exact H0.
   instantiate (1 := LH_base (e_to_v_list vs) [::]).
   all: simpl; rewrite -> List.app_nil_r; f_equal; apply e_to_v_list_inv; exact H.
Qed.

Variable hs: host_state.

Lemma vref_to_e_neq_nop : forall vref,
   vref_to_e vref <> AI_basic BI_nop.
Proof.
   intros v H. destruct v;
   simpl in H; discriminate H.
Qed.

Lemma v_to_e_neq_nop : forall v,
   v_to_e v <> AI_basic BI_nop.
Proof.
   intros v H. destruct v;
   solve [
      simpl in H; discriminate H |
      simpl in H; destruct v; simpl in H; discriminate H ].
Qed.

(* Lemma v_to_e_list_neq_nop : forall vs es es',
   v_to_e_list vs ++ es = AI_basic BI_nop :: es' -> False.
Proof.
   intros vs es es' H.
   destruct vs; simpl in H.
   +  *)

(* Lemma opsem_reduce_simple_nop : forall es1 es2,
   reduce_simple (AI_basic BI_nop :: es1) (AI_basic BI_nop :: es2) -> False.
Proof.
   intros es1 es2 H.
   inversion H; subst;
   match goal with
   | H : _ |- _ => solve [
      apply vref_to_e_neq_nop in H; destruct H |
      apply v_to_e_neq_nop in H; destruct H]
   end.
Qed. *)

Lemma cons_app : forall T (e : T) (l : list T), 
   e :: l = [:: e] ++ l.
Proof.
   intros T e1 e2. reflexivity.
Qed.

Lemma middle_neq_empty : forall (T : Type) (x : T) (l1 l2 : list T),
  l1 ++ [:: x] ++ l2 <> [::].
Proof.
  intros T x l1 l2 H.
  destruct l1; simpl in H; discriminate H.
Qed.

Lemma middle2_left_empty : forall (T : Type) (x y x' y' : T) (l1 l2 : list T),
  l1 ++ [:: x; y] ++ l2 = [:: x'; y'] -> l1 = [::].
Proof.
  intros T x y x' y' l1 l2 H.
  destruct l1.
   - reflexivity.
   - injection H as ? H.
     destruct l1.
     + injection H as ? H. discriminate H.
     + injection H as ? H. 
       assert (Heq : l1 ++ [:: x, y & l2] = l1 ++ [:: x] ++ y :: l2) by trivial.
       rewrite -> Heq in H. clear Heq.
       apply middle_neq_empty with (l2 := y :: l2) in H. destruct H.
Qed.

Lemma middle2_right_empty : forall (T : Type) (x y x' y' : T) (l1 l2 : list T), 
  l1 ++ [:: x; y] ++ l2 = [:: x'; y'] -> l2 = [::].
Proof.
  intros T x y x' y' l1 l2 H.
  specialize (middle2_left_empty H) as Hl1. rewrite -> Hl1 in H. simpl in H.
  injection H as ? ? H. exact H.
Qed.

Lemma opsem_reduce_seq2'_tail_eq_empty : forall l1 l2 l,
   l1 ++ l = [:: AI_basic BI_nop; AI_basic BI_unreachable] -> 
   l2 ++ l = [:: AI_basic BI_nop; AI_trap] -> l = [::].
Proof.
   intros l1 l2 l H1 H2.
   destruct l as [|e l'] eqn:El; simpl in H1, H2.
   - reflexivity.
   - destruct l' as [|e' l''] eqn:El'; simpl in H1, H2.
      + rewrite -> cons_app with (l := [:: AI_basic BI_unreachable]) in H1.
        rewrite -> cons_app with (l := [:: AI_trap]) in H2.
        apply List.app_inj_tail in H1. destruct H1 as [_ H1].
        apply List.app_inj_tail in H2. destruct H2 as [_ H2].
        rewrite -> H1 in H2. discriminate H2.
      + assert (Heq1 : l1 ++ [:: e, e' & l''] = l1 ++ [:: e; e'] ++ l'') by trivial.
        assert (Heq2 : l2 ++ [:: e, e' & l''] = l2 ++ [:: e; e'] ++ l'') by trivial.
        rewrite -> Heq1 in H1. clear Heq1.
        rewrite -> Heq2 in H2. clear Heq2.
        specialize (middle2_left_empty H1) as Hl1.
        specialize (middle2_right_empty H2) as Hl2. subst.
        simpl in H1, H2.
        injection H1 as He He'. rewrite -> He' in H2.
        rewrite -> cons_app with (l := [:: AI_basic BI_unreachable]) in H2.
        rewrite -> cons_app with (l := [:: AI_trap]) in H2.
        rewrite -> List.app_assoc in H2.
        apply List.app_inj_tail in H2. destruct H2 as [_ H2]. discriminate H2.
Qed.

Lemma opsem_reduce_seq2'_r_label : forall k (lh : lholed k) es1 es2,
   lfill lh es1 = [:: AI_basic BI_nop;  AI_basic BI_unreachable] ->
   lfill lh es2 = [:: AI_basic BI_nop;  AI_trap] -> 
   es1 = [:: AI_basic BI_nop;  AI_basic BI_unreachable] /\ es2 = [:: AI_basic BI_nop;  AI_trap].
Proof.
   intros k lh es1 es2 H1 H2. split.
   { destruct lh as [vs es |k vs n cont lh' es] eqn:Elh; simpl in H1, H2.
      - rewrite -> List.app_assoc in H1, H2;
      specialize (opsem_reduce_seq2'_tail_eq_empty H1 H2) as Hes;
      rewrite -> Hes in H1, H2; rewrite -> List.app_nil_r in H1, H2.
      destruct vs as [|v vs'] eqn:Evs; simpl in H1, H2.
      + exact H1.
      + injection H1 as H1. apply v_to_e_neq_nop in H1. destruct H1.
      - destruct vs as [|v vs'] eqn:Evs; simpl in H1, H2.
      + injection H1 as H1. discriminate H1.
      + injection H1 as H1. apply v_to_e_neq_nop in H1. destruct H1. }
   { destruct lh as [vs es |k vs n cont lh' es] eqn:Elh; simpl in H1, H2.
      - rewrite -> List.app_assoc in H1, H2;
      specialize (opsem_reduce_seq2'_tail_eq_empty H1 H2) as Hes;
      rewrite -> Hes in H1, H2; rewrite -> List.app_nil_r in H1, H2.
      destruct vs as [|v vs'] eqn:Evs; simpl in H1, H2.
      + exact H2.
      + injection H1 as H1. apply v_to_e_neq_nop in H1. destruct H1.
      - destruct vs as [|v vs'] eqn:Evs; simpl in H1, H2.
      + injection H1 as H1. discriminate H1.
      + injection H1 as H1. apply v_to_e_neq_nop in H1. destruct H1. }
Qed.

Lemma opsem_reduce_seq2':
    {forall s1 f1 es1 s2 f2 es2 es0,
    reduce hs s1 f1 es1 hs s2 f2 es2 ->
    reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2)} +
    {exists s1 f1 es1 s2 f2 es2 es0,
    (reduce hs s1 f1 es1 hs s2 f2 es2 ->
     reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2)) -> False}.
Proof.
   apply right.
   set empty_record := Build_store_record [::] [::] [::] [::] [::] [::].
   exists empty_record. exists empty_frame. exists [:: AI_basic BI_unreachable].
   exists empty_record. exists empty_frame. exists [:: AI_trap].
   exists [:: AI_basic BI_nop].
   simpl. intros H.
   specialize (H (r_simple _ _ _ rs_unreachable)).
   dependent induction H.
   (* TODO: Name x0 and x properly *)
   - inversion H.
   - destruct vcs in x0; simpl in x0.
      + discriminate x0.
      + injection x0 as x0. apply v_to_e_neq_nop in x0. destruct x0.
   - apply IHreduce; clear IHreduce; try reflexivity.
      + specialize (opsem_reduce_seq2'_r_label x0 x) as [Hgoal _]. exact Hgoal.
      + specialize (opsem_reduce_seq2'_r_label x0 x) as [_ Hgoal]. exact Hgoal.
Qed.

(* Is the above true without the const_list assumption?
   Prove or disprove it by establishing a witness to the following: *)
Lemma opsem_reduce_seq2':
    {forall s1 f1 es1 s2 f2 es2 es0,
    reduce hs s1 f1 es1 hs s2 f2 es2 ->
    reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2)} +
    {forall es1 es2, exists s1 f1 s2 f2 es0,
    reduce hs s1 f1 es1 hs s2 f2 es2 /\
    (reduce hs s1 f1 (es0 ++ es1) hs s2 f2 (es0 ++ es2) -> False)}.
Proof.
   apply right.
   intros es1 es2.
   set empty_record := Build_store_record [::] [::] [::] [::] [::] [::].
   exists empty_record. exists empty_frame.
   exists empty_record. exists empty_frame.
   exists [::AI_basic BI_nop].
   remember (AI_basic BI_nop :: es1) as esl.
   remember (AI_basic BI_nop :: es2) as esr.
   induction H2; 
   (* TODO: Name variables *)
   try solve [discriminate Heqesr |
              injection Heqesl as Hcontra; discriminate Hcontra |
              injection Heqesr as Hcontra; discriminate Hcontra ];
   subst.
   - eapply opsem_reduce_simple_nop. exact H.
   - unfold result_to_stack in Heqesr. destruct r eqn:Er.
      + destruct l eqn:El.
         * simpl in Heqesr. discriminate Heqesr.
         * simpl in Heqesr. injection Heqesr as Heqesr.
           apply v_to_e_neq_nop in Heqesr. destruct Heqesr.
   - injection Heqesr as Heqesr. discriminate Heqesr.
   - apply IHreduce; clear IHreduce.
      + exact H1.
      + admit.
      + admit.
Admitted.
(* 
   apply right.
   set empty_record := Build_store_record [::] [::] [::] [::] [::] [::].
   exists empty_record. exists empty_frame.
   exists [::].
   exists empty_record. exists empty_frame.
   exists [::]. exists [::AI_basic BI_nop].
   simpl. intros H1 H2.
   
   inversion H2; subst.
   - inversion H.
   - rewrite -> H in H0. injection H0 as H0. discriminate H0.
   - rewrite -> H in H0. injection H0 as H0. discriminate H0.
   - rewrite -> H in H0. injection H0 as H0. discriminate H0.
   (* - simpl in H3. unfold lookup_N in H3. Check List.nth_error_None. *)
   - admit.
   - rewrite -> H in H0. injection H0 as H0. discriminate H0.
   - admit. *)

End intro_opsem.

Section intro_types.

Context `{ho: host}.

(* The newer proposals of Wasm introduces a notion of a subtyping relation <:,
   which did not exist in Wasm 1.0 (and not even formally in Wasm 2.0).

   This is implemented in the Coq mechanisation, which complicates the type
   system slightly. If a program can be associated with a function type, then
   it can also be associated with any supertype of that function type
   (`bet_subtyping`).

   The following exercise helps to understand how instruction subtyping works.
 *)
Lemma subtypes_1:
  instr_subtyping (Tf nil [::T_num T_i32]) (Tf [::T_num T_i32] [::T_num T_i32; T_num T_i32]).
Proof.
Admitted.

Notation "$N v" := (BI_const_num v) (at level 20).

(* Establish the following typing derivation by applying the composition
   rule `bet_composition`, with appropriate rewrites and other typing rules
   in the `be_typing` inductive definition. *)
Lemma types_composition: forall C c1 c2,
  be_typing C [:: $N (VAL_int32 c1); $N (VAL_int32 c2); BI_binop T_i32 (Binop_i BOI_add)] (Tf nil [::T_num T_i32]).
Proof.
Admitted.

(* The following 2 are slightly more difficult *)
(* It is slightly awkward to apply the `bet_composition` rule, since it only
   allows appending one instruction at a time instead of allowing arbitrary
   concatenation of instruction lists. The following composition typing lemma
   is a more general version. Prove it by an appropriate induction.
*)
Lemma bet_composition2: forall C es1 es2 ts1 ts2 ts3,
    be_typing C es1 (Tf ts1 ts2) ->
    be_typing C es2 (Tf ts2 ts3) ->
    be_typing C (es1 ++ es2) (Tf ts1 ts3).
Proof.
Admitted.

(* The following 'typing inversion lemma' is some sort of a converse to the
   one above. Prove it by an appropriate induction.
   These typing inversion lemmas are key to proving the soundness properties,
   as they provide a way to extract information from the typing premises.
 *)
Lemma be_composition_inversion: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C es2 (Tf t3s t2s).
Proof.
Admitted.

End intro_types.
