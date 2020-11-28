Require Export Program.Basics. Open Scope program_scope.
From Paco Require Export paco_rel.
From Paco Require Import paco_currying gpaco_internal.

Set Implicit Arguments.

Section INTERNAL.

Context (n : nat) {t : arityn n}.

Local Open Scope paco_scope.

Notation rel := (rel (aton t)).
Notation _rel := (_rel (aton t)).
Local Infix "<=" := le : paco_scope.
Local Notation "gf <2= gf'" := (forall r, gf r <= gf' r) : paco_scope.

Definition _rclo (clo : rel->rel) : rel -> rel :=
  curry_relT (rclo (uncurry_relT clo)).

Lemma le_transport (r0 r0' : _rel) :
  forall r1 r1',
  _le r1 r0 ->
  _le r0' r1' ->
  _le r0 r0' ->
  _le r1 r1'.
Proof.
  red; auto.
Qed.

Lemma le_uncurry_curry_l (gf gf' : _rel) :
  _le gf gf' ->
  _le (uncurry (curry gf)) gf'.
Proof.
  red; intros.
  eapply H, uncurry_curry; assumption.
Qed.

Lemma le_uncurry_curry_r (gf gf' : _rel) :
  _le gf gf' ->
  _le gf (uncurry (curry gf')).
Proof.
  red; intros.
  eapply uncurry_curry, H; assumption.
Qed.

Ltac simpl_le etc :=
  repeat 
    lazymatch goal with
    | [ |- _le_relT _ _ ] => let r := fresh "r" in intros r
    | [ |- forall r : rel1 _, _ ] =>
      let r := fresh r in intros r
    | _ => apply Reflexive_le + apply Reflexive_le_ + apply le_uncurry_curry_l + (red; apply rclo_mon_gen) + etc
    end.

Ltac finish_translate _L_ :=
  lazymatch goal with
  | [ |- le _ _ ] =>
    apply (proj2 (curry_le _ _)) + apply curry_le_r;
    try ((red; apply _L_) + revert _L_; apply le_transport)
  | [ |- _monotone _ ] =>
    try (apply curry_monotone, _L_);
    revert _L_; apply __monotone_adj;
    reflexivity +
    let r := fresh in
    let u := fresh in
    intros r u; split; revert u
  end.

Local Definition paco_remember@{u} {A : Type@{u}} (P : A) : A := P.
Local Definition paco_protect@{u} {A : Type@{u}} (P : A) : A := P.

Ltac translate__ cotranslate etc X :=
  let _L_ := fresh "_L_" in
  pose proof X as _L_;
  repeat lazymatch goal with
  | [ |- forall H : _, _ ] =>
    let H := fresh H in
    intros H;
    lazymatch type of H with
    | paco_remember _ =>
      red in H;
      let H' := fresh H in
      assert (H' := H); revert H'
    | rel -> rel =>
      specialize (_L_ (uncurry_relT H))
    | rel =>
      specialize (_L_ (uncurry H))
    | le_relT _ _ =>
      specialize (_L_ (uncurry_relT_le_relT H)); clear H
    | le _ _ =>
      apply uncurry_le in H;
      specialize (_L_ H); clear H
    | _monotone _ =>
      specialize (_L_ (uncurry_monotone H)); clear H
    | _ =>
      let e := fresh in
      evar (e : Prop); cut e; subst e;
      [ clear H;
        intros H;
        specialize (_L_ H);
        clear H
      | clear _L_; revert H; change ?goal with (paco_protect goal) ]
    end
  | [ |- paco_protect _ ] => fail
  | _ => finish_translate _L_
  end;
  lazymatch goal with
  | [ |- _ -> _ ] => idtac
  | [ |- paco_protect _ ] => cotranslate
  | _ => simpl_le etc
  end.

Ltac translate_ := translate__ idtac.

Section A.

Ltac translate X := translate_ fail (@X (tuple t)).

Lemma _rclo_mon_gen : forall clo clo' r r'
      (LEclo: le_relT clo clo')
      (LEr: r <= r'),
  _rclo clo r <= _rclo clo' r'.
Proof.
  translate rclo_mon_gen.
Qed.

Lemma _rclo_mon : forall clo, _monotone (_rclo clo).
Proof.
  translate rclo_mon.
Qed.

Lemma _rclo_clo : forall clo r,
  clo (_rclo clo r) <= _rclo clo r.
Proof.
  translate rclo_clo.
Qed.

Lemma _rclo_rclo : forall clo r,
  _rclo clo (_rclo clo r) <= _rclo clo r.
Proof.
  translate rclo_rclo.
Qed.

Lemma _rclo_compose : forall clo r,
  _rclo (_rclo clo) r <= _rclo clo r.
Proof.
  translate rclo_compose.
Qed.

End A.

Definition _gpaco (gf : rel -> rel) (clo : rel -> rel) (r rg : rel) : rel :=
  curry (gpaco (uncurry_relT gf) (uncurry_relT clo) (uncurry r) (uncurry rg)).

Definition _gupaco gf clo r := _gpaco gf clo r r.

Lemma _gupaco_equiv gf clo r x :
  uncurry (_gupaco gf clo r) x <->
  gupaco (uncurry_relT gf) (uncurry_relT clo) (uncurry r) x.
Proof.
  unfold _gupaco, _gpaco.
  apply uncurry_curry.
Qed.

Ltac simpl_paco :=
  assumption +
  (red; apply gpaco_mon_gen) +
  (apply uncurry_monotone; assumption) +
  (apply curry_le_l; apply Reflexive_le) +
  match goal with
  | [ |- _le _ _ ] => apply uncurry_le + apply _union_monotone
  | [ |- le _ _ ] => apply curry_le
  | [ H : _monotone ?gf |- le (?gf _) (?gf _) ] => apply H
  end +
  (try (let _r := fresh "r" in intros _r);
   try (unfold uncurry_relT);
   match goal with
   | [ |- ?G ] =>
     match G with
     | context _ctx [ curry (@uncurry _ _ ?r) ] =>
       destruct (paco_sigma.eq_sym (curry_uncurry t r))
     end
   end).

Section GPaco.

Ltac translate' := translate_ simpl_paco.
Ltac translate X := translate' (@X (tuple t)).

Lemma _gpaco_mon : forall gf clo r r' rg rg'
      (LEr: r <= r')
      (LErg: rg <= rg'),
  _gpaco gf clo r rg <= _gpaco gf clo r' rg'.
Proof.
  translate gpaco_mon.
Qed.

Lemma _gupaco_mon : forall gf clo, _monotone (_gupaco gf clo).
Proof.
  intros; eapply __monotone_adj; [ apply _gupaco_equiv | apply gupaco_mon ].
Qed.

Lemma _gpaco_base : forall gf clo r rg, r <= _gpaco gf clo r rg.
Proof.
  translate gpaco_base.
Qed.

Lemma _gpaco_gen_guard gf (gf_mon : _monotone gf) : forall clo r rg,
  _gpaco gf clo r (union rg r) <= _gpaco gf clo r rg.
Proof.
  translate' (@gpaco_gen_guard (tuple t) (uncurry_relT gf)).
Qed.

Lemma _gpaco_rclo : forall gf clo r rg,
  _rclo clo r <= _gpaco gf clo r rg.
Proof.
  translate gpaco_rclo.
Qed.

Lemma _gpaco_clo : forall gf clo r rg,
  clo r <= _gpaco gf clo r rg.
Proof.
  translate gpaco_clo.
Qed.

End GPaco.

Ltac cotranslate_end_really :=
  repeat
    apply Reflexive_le_ + (try red; apply gpaco_mon) + apply uncurry_curry.

Ltac cotranslate_end _H_ :=
  match type of _H_ with
  | le _ _ =>
    (apply curry_le in _H_ + apply curry_le_r in _H_ + apply uncurry_le in _H_);
    revert _H_; apply le_transport;
    cotranslate_end_really
  | _ => idtac
  end.

(* _gpaco_cofix and _gpaco_uclo *)
Ltac cotranslate :=
  let _H_ := fresh "_H_" in
  intros _H_;
  (repeat
  lazymatch type of _H_ with
  | (forall r : rel, _) =>
    let r := fresh r in
    intros r;
    specialize (_H_ (curry r))
  | (le ?r ?r' -> _) =>
    let H := fresh in
    intros H;
    apply curry_le_r in H;
    specialize (_H_ H);
    clear H
  | _ => fail
  end);
  cotranslate_end _H_.

Section GPacoMon.

Ltac translate' := translate__ cotranslate simpl_paco.
Ltac translate X := translate' (@X (tuple t)).

Lemma _gpaco_def_mon :
  forall gf, paco_remember (_monotone gf) ->
  forall clo, _monotone (compose gf (_rclo clo)).
Proof.
  translate gpaco_def_mon.
Qed.

Hint Resolve gpaco_def_mon : paco.

Lemma _gpaco_gen_rclo : forall gf,
  paco_remember (_monotone gf) ->
  forall clo r rg,
  _gpaco gf (_rclo clo) r rg <= _gpaco gf clo r rg.
Proof.
  translate gpaco_gen_rclo.
Qed.

Lemma _gpaco_step_gen : forall gf, paco_remember (_monotone gf) ->
  forall clo r rg,
  gf (_gpaco gf clo (union rg r) (union rg r)) <= _gpaco gf clo r rg.
Proof.
  translate gpaco_step_gen.
Qed.

Lemma _gpaco_step : forall gf, _monotone gf ->
  forall clo r rg,
  gf (_gpaco gf clo rg rg) <= _gpaco gf clo r rg.
Proof.
  translate gpaco_step.
Qed.

Lemma _gpaco_final : forall gf, _monotone gf -> forall clo r rg,
  (union r (_paco gf rg)) <= _gpaco gf clo r rg.
Proof.
  translate gpaco_final.
Qed.

Definition _or (r r' : _rel) := fun u => r u \/ r' u.

Ltac fold_or :=
  repeat
  match goal with
  | [ |- forall x : _, ?u x -> ?v x ] => fold (_le u v)
  | [ |- forall x : _, _ ] =>
    let x := fresh x in intros x;
    progress repeat
    (let H := match goal with | [ |- ?H ] => H end in
    match H with
    | context _r [ fun x => ?p x \/ ?q x ] => fold (_or p q)
    | context _r [ ?p ?x \/ ?q ?x ] => fold (_or p q x)
    end);
    revert x
  | [ |- _le _ (uncurry (union _ _)) ] =>
    eapply Transitive_le_; [ | intro; apply uncurry_curry ]
  end.

Lemma _gpaco_unfold : forall gf, paco_remember (_monotone gf) -> forall clo r rg,
  _gpaco gf clo r rg <= _rclo clo (union (gf (_gupaco gf clo (union rg r))) r).
Proof.
  translate gpaco_unfold. simpl_le ltac:(fold_or + simpl_paco).
Qed.

Lemma _gpaco_cofix : forall gf, _monotone gf -> forall clo r rg l
  (OBG: forall rr (INC: rg <= rr) (CIH: l <= rr), l <= _gpaco gf clo r rr),
  l <= _gpaco gf clo r rg.
Proof.
  translate gpaco_cofix.
Qed.

Lemma _gpaco_gupaco : forall gf, paco_remember (_monotone gf) -> forall clo r rg,
  _gupaco gf clo (_gpaco gf clo r rg) <= _gpaco gf clo r rg.
Proof.
  translate gpaco_gupaco.
Qed.

Lemma _gpaco_gpaco : forall gf, paco_remember (_monotone gf) -> forall clo r rg,
  _gpaco gf clo (_gpaco gf clo r rg) (_gupaco gf clo (union rg r)) <=
  _gpaco gf clo r rg.
Proof.
  translate gpaco_gpaco.
Qed.

Lemma _gpaco_uclo : forall gf, _monotone gf ->
  forall uclo clo r rg
         (LEclo : forall r, uclo r <= _gupaco gf clo r),
  uclo (_gpaco gf clo r rg) <= _gpaco gf clo r rg.
Proof.
  translate gpaco_uclo.
Qed.

Lemma _gpaco_weaken : forall gf, paco_remember (_monotone gf) ->
  forall clo r rg,
  _gpaco gf (_gupaco gf clo) r rg <= _gpaco gf clo r rg.
Proof.
  translate gpaco_weaken.
Qed.

End GPacoMon.

Section GeneralMonotonicity.

Context {gf: rel -> rel} {gf_mon : _monotone gf}.

Ltac translate' X :=
  revert gf gf_mon;
  translate__ cotranslate simpl_paco X.
Ltac translate X :=
  translate' (@X (tuple t)).

Lemma _gpaco_mon_gen : forall (gf' clo clo': rel -> rel) r r' rg rg'
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <= r')
      (LErg: rg <= rg'),
  _gpaco gf clo r rg <= _gpaco gf' clo' r' rg'.
Proof.
  translate gpaco_mon_gen.
Qed.

Lemma gpaco_mon_bot : forall (gf' clo clo': rel -> rel) r' rg'
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo'),
  _gpaco gf clo _bot _bot <= _gpaco gf' clo' r' rg'.
Proof.
  intros; apply _gpaco_mon_gen; assumption + apply paco_rel._bot_min.
Qed.

Lemma _gupaco_mon_gen : forall
      (gf' clo clo': rel -> rel) r r'
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <= r'),
  _gupaco gf clo r <= _gupaco gf' clo' r'.
Proof.
  intros; apply _gpaco_mon_gen; assumption.
Qed.

End GeneralMonotonicity.

Section CompatibilityDef.

Variable gf: rel -> rel.

Structure _compatible (clo: rel -> rel) : Prop :=
  compat_intro {
      compat_mon: _monotone clo;
      compat_compat : forall r,
          clo (gf r) <= gf (clo r);
    }.

Structure _wcompatible clo : Prop :=
  wcompat_intro {
      wcompat_mon: _monotone clo;
      wcompat_wcompat : forall r,
          clo (gf r) <= gf (_gupaco gf clo r);
    }.

Lemma curry_uncurry_relT (tr : rel -> rel) r
  : paco_eq (curry (uncurry_relT tr r)) (tr (curry r)).
Proof. apply curry_uncurry. Qed.

Lemma ap_uncurry_relT (tr : rel -> rel) r
  : paco_eq (uncurry_relT tr (uncurry r)) (uncurry (tr r)).
Proof.
  unfold uncurry_relT.
  apply f_equal. apply f_equal. apply curry_uncurry.
Qed.

Lemma curry_ap_uncurry_relT (tr : rel -> rel) r
  : paco_eq (curry (uncurry_relT tr (uncurry r))) (tr r).
Proof.
  destruct (eq_sym (ap_uncurry_relT tr r)).
  apply curry_uncurry.
Qed.

Lemma _compatible_equiv clo
  : compatible (uncurry_relT gf) (uncurry_relT clo) <-> _compatible clo.
Proof.
  split; intros [MON COMPAT]; constructor.
  - apply uncurry_monotone_l. assumption.
  - intros r. specialize (COMPAT (uncurry r)).
    apply uncurry_relT_le in COMPAT.
    destruct (curry_ap_uncurry_relT gf r).
    destruct (curry_ap_uncurry_relT clo r).
    assumption.
  - apply uncurry_monotone. assumption.
  - intros r. apply uncurry_relT_le.
    destruct (eq_sym (curry_uncurry_relT gf r)).
    destruct (eq_sym (curry_uncurry_relT clo r)).
    apply COMPAT.
Qed.

Lemma _compatible_impl (_clo : _rel -> _rel)
  : compatible (uncurry_relT gf) _clo -> _compatible (curry_relT _clo).
Proof.
  intros [MON COMPAT]; constructor.
  - apply curry_monotone, MON.
  - intros r. specialize (COMPAT (uncurry r)).
    apply curry_le_l.
    destruct (ap_uncurry_relT gf r).
    exact COMPAT.
Qed.

End CompatibilityDef.

Section Compatibility.
Local Infix "\1/" := union : paco_scope.

Ltac translate' X :=
  translate__ cotranslate simpl_paco X.
Ltac translate X :=
  translate' (@X (tuple t)).

(*
Lemma curry_uncurry_ctx:
  forall (n : nat) (t : arityn n) (R S : Type)
    (f : tuple t -> R)
    (g : tuple t -> R -> S),
  paco_eq
    (curry (fun u : tuple t => g u (uncurry (curry f) u)))
    (curry (fun u : tuple t => g u (f u))).
Admitted.
*)

Lemma apply_eq {A B} (x : A) (f g : forall x : A, B x) : paco_eq f g -> paco_eq (f x) (g x).
Proof. intros []; constructor. Qed.

Lemma _rclo_dist : forall clo
      (MON: _monotone clo)
      (DIST: forall r1 r2, clo (r1 \1/ r2) <= (clo r1 \1/ clo r2)),
  forall r1 r2, _rclo clo (r1 \1/ r2) <= (_rclo clo r1 \1/ _rclo clo r2).
Proof.
  translate rclo_dist. unfold uncurry_relT, union.
  assert (I := curry_uncurry_ctx (n := n) (fun _ : unit => t) (fun _ : unit => r1) (fun (_ : unit) u z => z \/ r2 u)).
  apply (apply_eq tt) in I.
  match type of I with
  | paco_eq _ ?x => remember x eqn:E
  end.
  destruct I; clear E.
  assert (I := curry_uncurry_ctx (n := n) (fun _ : unit => t) (fun _ : unit => r2) (fun (_ : unit) u z => uncurry (curry r1) u \/ z)).
  apply (apply_eq tt) in I.
  destruct I.
  apply Reflexive_le_.
Qed.

Context {gf : rel -> rel} (gf_mon: _monotone gf).

Local Notation _compatible := (_compatible gf).
Local Notation _wcompatible := (_wcompatible gf).

Lemma _wcompatible_equiv clo
  : wcompatible (uncurry_relT gf) (uncurry_relT clo) <-> _wcompatible clo.
Proof.
  split; intros [MON COMPAT]; constructor.
  - apply uncurry_monotone_l. assumption.
  - intros r. specialize (COMPAT (uncurry r)).
    apply uncurry_relT_le in COMPAT.
    destruct (curry_ap_uncurry_relT gf r).
    exact COMPAT.
  - apply uncurry_monotone. assumption.
  - intros r. apply uncurry_relT_le.
    destruct (eq_sym (curry_uncurry_relT gf r)).
    specialize (COMPAT (curry r)).
    apply (Transitive_le _ _ _ COMPAT).
    apply gf_mon.
    apply curry_le.
    apply gupaco_mon.
    apply uncurry_curry.
Qed.

Lemma _wcompatible_impl (_clo : _rel -> _rel)
  : wcompatible (uncurry_relT gf) _clo -> _wcompatible (curry_relT _clo).
Proof.
  intros [MON COMPAT]; constructor.
  - apply curry_monotone, MON.
  - intros r. specialize (COMPAT (uncurry r)).
    apply curry_le_l.
    destruct (ap_uncurry_relT gf r).
    apply (Transitive_le_ COMPAT).
    apply uncurry_le.
    apply gf_mon.
    apply curry_le.
    unfold _le.
    apply (@gupaco_mon_gen (tuple t)).
    + apply uncurry_monotone. assumption.
    + exact (fun _ _ p => p).
    + intros r1. apply le_uncurry_curry_r, MON, le_uncurry_curry_r, Reflexive_le_.
    + exact (fun _ p => p).
Qed.

Lemma rclo_compat clo (COM : _compatible clo) : _compatible (_rclo clo).
Proof.
  apply _compatible_impl.
  apply rclo_compat; [ apply uncurry_monotone, gf_mon | ].
  apply _compatible_equiv.
  assumption.
Qed.

Lemma rclo_wcompat (clo : rel -> rel) (COM : _wcompatible clo) : _wcompatible (_rclo clo).
Proof.
  apply _wcompatible_impl.
  apply rclo_wcompat; [ apply uncurry_monotone, gf_mon | ].
  apply _wcompatible_equiv.
  assumption.
Qed.

Lemma compat_wcompat clo (CMP : _compatible clo) : _wcompatible clo.
Proof.
  apply _wcompatible_equiv.
  apply compat_wcompat; [ apply uncurry_monotone, gf_mon | ].
  apply _compatible_equiv.
  assumption.
Qed.

Lemma wcompat_compat clo (WCMP : _wcompatible clo) : _compatible (_gupaco gf clo).
Proof.
  apply (_compatible_impl (_clo := gupaco (uncurry_relT gf) (uncurry_relT clo))).
  apply wcompat_compat; [ apply uncurry_monotone, gf_mon | ].
  apply _wcompatible_equiv.
  assumption.
Qed.

Lemma wcompat_union clo1 clo2
      (WCMP1: _wcompatible clo1)
      (WCMP2: _wcompatible clo2):
  _wcompatible (fun r => clo1 r \1/ clo2 r).
Proof.
  apply _wcompatible_equiv.
  unfold uncurry_relT.
  assert (E := eq_sym (uncurry_union_ n (fun (_ : _rel) => t) (fun r => clo1 (curry r)) (fun r => clo2 (curry r)))).
  cbn in E.
  destruct E.
  apply wcompat_union; [ apply uncurry_monotone, gf_mon | | ].
  all: apply _wcompatible_equiv; assumption.
Qed.

End Compatibility.

Section Soundness.

Context {gf: rel -> rel} {gf_mon: _monotone gf}.

Lemma uncurry_bot
  : paco_eq (uncurry (t := t) _bot) bot1.
Proof.
Admitted.

Lemma gpaco_compat_init clo
      (CMP: _compatible gf clo):
  _gpaco gf clo _bot _bot <= _paco gf _bot.
Proof.
  apply curry_le.
  pose (bot := uncurry (t := t) _bot).
  change (uncurry (t := t) _bot) with bot.
  assert (e := eq_sym uncurry_bot : paco_eq bot1 bot).
  destruct e.
  red; apply gpaco_compat_init; [ apply uncurry_monotone, gf_mon | ].
  apply _compatible_equiv.
  assumption.
Qed.

Lemma gpaco_init clo
      (WCMP: _wcompatible gf clo):
  _gpaco gf clo _bot _bot <= _paco gf _bot.
Proof.
  apply curry_le.
  pose (bot := uncurry (t := t) _bot).
  change (uncurry (t := t) _bot) with bot.
  assert (e := eq_sym uncurry_bot : paco_eq bot1 bot).
  destruct e.
  red; apply gpaco_init; [ apply uncurry_monotone, gf_mon | ].
  apply _wcompatible_equiv; [ apply gf_mon | ].
  assumption.
Qed.

Lemma gpaco_unfold_bot clo
      (WCMP: _wcompatible gf clo):
  _gpaco gf clo _bot _bot <= gf (_gpaco gf clo _bot _bot).
Proof.
  apply curry_le_l.
  unfold _gpaco.
  pose (bot := uncurry (t := t) _bot).
  change (uncurry (t := t) _bot) with bot.
  assert (e := eq_sym uncurry_bot : paco_eq bot1 bot).
  destruct e.
  red. apply gpaco_unfold_bot; [ apply uncurry_monotone, gf_mon | ].
  apply _wcompatible_equiv; [ apply gf_mon | ].
  assumption.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Lemma gpaco_dist clo r rg
      (CMP: wcompatible gf clo)
      (DIST: forall r1 r2, clo (r1 \1/ r2) <1= (clo r1 \1/ clo r2)):
  gpaco gf clo r rg <1= (paco gf (rclo clo (rg \1/ r)) \1/ rclo clo r).
Proof.
  intros x PR. apply gpaco_unfold in PR.
  apply rclo_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x H.
  pcofix_ CIH; intros x PR.
  apply rclo_wcompat in PR; [|apply CMP].
  apply paco_fold. monotonic gf_mon PR. intros x PR.
  apply gpaco_unfold in PR.
  apply rclo_compose in PR.
  apply rclo_dist in PR; [|apply CMP|apply DIST].
  destruct PR as [PR|PR].
  - right. apply CIH.
    monotonic rclo_mon PR. apply gf_mon. intros x PR.
    apply gpaco_gupaco.
    apply gpaco_gen_rclo.
    monotonic gupaco_mon PR. intros x PR.
    destruct PR as [PR|PR]; apply PR.
  - assert (REL: @rclo clo (rclo clo (gf (gupaco gf clo ((rg \1/ r) \1/ (rg \1/ r))) \1/ (rg \1/ r))) x).
    { monotonic rclo_mon PR. intros. apply gpaco_unfold in PR; assumption. }
    apply rclo_rclo in REL.
    apply rclo_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL as [REL|REL]; [| apply Hr0, REL].
    apply CIH.
    monotonic rclo_mon REL. apply gf_mon, gupaco_mon.
    destruct 1 as [PR1|PR1]; apply PR1.
Qed.

Lemma gpaco_dist_reverse clo r rg:
  (paco gf (rclo clo (rg \1/ r)) \1/ rclo clo r) <1= gpaco gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco_rclo. apply H.
  - econstructor. apply rclo_base. left.
    revert x0 H. pcofix_ CIH; intros x PR.
    apply paco_unfold in PR; [|apply gf_mon].
    apply paco_fold.
    monotonic gf_mon PR. intros x PR.
    destruct PR as [PR|PR].
    + apply rclo_base. auto.
    + monotonic rclo_mon PR. auto.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Inductive cpn (r: rel) x0 : Prop :=
| cpn_intro
    clo
    (COM: compatible gf clo)
    (CLO: clo r x0)
.

Lemma cpn_mon: monotone cpn.
Proof.
  red; red. destruct 2. exists clo.
  - apply COM.
  - eapply compat_mon; [apply COM|apply LE|apply CLO].
Qed.

Lemma cpn_greatest: forall clo (COM: compatible gf clo), clo <2= cpn.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn_compat: compatible gf cpn.
Proof.
  econstructor; [apply cpn_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - intros. econstructor; [apply COM|apply PR].
  - eapply (compat_compat COM); apply CLO.
Qed.

Lemma cpn_wcompat: wcompatible gf cpn.
Proof. apply compat_wcompat, cpn_compat. Qed.

Lemma cpn_gupaco:
  gupaco gf cpn <2= cpn.
Proof.
  intros. eapply cpn_greatest, PR. apply wcompat_compat. apply cpn_wcompat.
Qed.

Lemma cpn_cpn r:
  cpn (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_gupaco, gpaco_gupaco, gpaco_clo.
  eapply cpn_mon; [ apply gpaco_clo | apply PR ].
Qed.

Lemma cpn_base r:
  r <1= cpn r.
Proof.
  intros. apply cpn_gupaco. apply gpaco_base, PR.
Qed.

Lemma cpn_clo
      r clo (LE: clo <2= cpn):
  clo (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_cpn, LE, PR.
Qed.

Lemma cpn_step r:
  gf (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_gupaco. apply gpaco_step.
  monotonic gf_mon PR; apply gpaco_clo.
Qed.

Lemma cpn_uclo uclo
      (MON: monotone uclo)
      (WCOM: forall r, uclo (gf r) <1= gf (gupaco gf (uclo \2/ cpn) r)):
  uclo <2= gupaco gf cpn.
Proof.
  intros. apply gpaco_clo.
  exists (gupaco gf (uclo \2/ cpn)).
  - apply wcompat_compat.
    econstructor.
    + apply monotone_union. apply MON. apply cpn_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat_compat with (gf:=gf) in H; [| apply cpn_compat].
        monotonic gf_mon H. intros.
        apply gpaco_clo. right. apply PR0.
  - apply gpaco_clo. left. apply PR.
Qed.

End Companion.
End GeneralizedPaco.
