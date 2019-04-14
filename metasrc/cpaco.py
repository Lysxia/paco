from __future__ import print_function
import sys
from pacolib import *
if len(sys.argv) < 2:
    sys.stderr.write("\nUsage: "+sys.argv[0]+" relsize\n\n")
    sys.exit(1)
n = int(sys.argv[1])

print ("Require Export Program.Basics. Open Scope program_scope.")
print ("Require Import paco"+str(n)+" pacotac cpn"+str(n)+".")
print ("Set Implicit Arguments.")
print ("")
print ("Section CompatiblePaco"+str(n)+".")
print ("")
for i in range(n):
    print ("Variable T"+str(i)+" : "+ifpstr(i,"forall"),end="")
    for j in range(i):
        print (" (x"+str(j)+": @T"+str(j)+itrstr(" x",j)+")",end="")
    print (ifpstr(i,", ")+"Type.")
print ("")
print ("Local Notation rel := (rel"+str(n)+""+itrstr(" T", n)+").")
print ("")
print ("Section CompatiblePaco"+str(n)+"_main.")
print ("")
print ("Variable gf: rel -> rel.")
print ("Hypothesis gf_mon: monotone"+str(n)+" gf.")
print ("")
print ("Variable clo : rel -> rel.")
print ("Hypothesis clo_compat: compatible"+str(n)+" gf clo.")
print ("")
print ("Inductive cpaco"+str(n)+" r rg"+itrstr(" x", n)+" : Prop :=")
print ("| cpaco"+str(n)+"_intro (IN: rclo"+str(n)+" clo (paco"+str(n)+" (compose gf (rclo"+str(n)+" clo)) (r \\"+str(n)+"/ rg) \\"+str(n)+"/ r)"+itrstr(" x", n)+")")
print (".")
print ("")
print ("Definition cupaco"+str(n)+" r := cpaco"+str(n)+" r r.")
print ("")
print ("Lemma cpaco"+str(n)+"_def_mon : monotone"+str(n)+" (compose gf (rclo"+str(n)+" clo)).")
print ("Proof.")
print ("  eapply monotone"+str(n)+"_compose. apply gf_mon. apply rclo"+str(n)+"_mon.")
print ("Qed.")
print ("")
print ("Hint Resolve cpaco"+str(n)+"_def_mon : paco.")
print ("")
print ("Lemma cpaco"+str(n)+"_mon r r' rg rg'"+itrstr(" x", n)+"")
print ("      (IN: @cpaco"+str(n)+" r rg"+itrstr(" x", n)+")")
print ("      (LEr: r <"+str(n)+"= r')")
print ("      (LErg: rg <"+str(n)+"= rg'):")
print ("  @cpaco"+str(n)+" r' rg'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  destruct IN. econstructor.")
print ("  eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR; [|right; apply LEr, H].")
print ("  left. eapply paco"+str(n)+"_mon. apply H.")
print ("  intros. destruct PR.")
print ("  - left. apply LEr, H0.")
print ("  - right. apply LErg, H0.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_cofix r rg ")
print ("      l (OBG: forall rr (INC: rg <"+str(n)+"= rr) (CIH: l <"+str(n)+"= rr), l <"+str(n)+"= cpaco"+str(n)+" r rr):")
print ("  l <"+str(n)+"= cpaco"+str(n)+" r rg.")
print ("Proof.")
print ("  assert (IN: l <"+str(n)+"= cpaco"+str(n)+" r (rg \\"+str(n)+"/ l)).")
print ("  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }")
print ("  clear OBG. intros. apply IN in PR.")
print ("  destruct PR. econstructor.")
print ("  eapply rclo"+str(n)+"_mon. apply IN0.")
print ("  clear"+itrstr(" x", n)+" IN0.")
print ("  intros. destruct PR; [|right; apply H].")
print ("  left. revert"+itrstr(" x", n)+" H.")
print ("  pcofix CIH. intros.")
print ("  _punfold H0; [..|apply cpaco"+str(n)+"_def_mon]. pstep.")
print ("  eapply gf_mon. apply H0. intros.")
print ("  apply rclo"+str(n)+"_rclo. eapply rclo"+str(n)+"_mon. apply PR.")
print ("  intros. destruct PR0.")
print ("  - apply rclo"+str(n)+"_base. right. apply CIH. apply H.")
print ("  - destruct H; [|destruct H].")
print ("    + apply rclo"+str(n)+"_base. right. apply CIH0. left. apply H.")
print ("    + apply rclo"+str(n)+"_base. right. apply CIH0. right. apply H.")
print ("    + apply IN in H. destruct H.")
print ("      eapply rclo"+str(n)+"_mon. apply IN0.")
print ("      intros. destruct PR0.")
print ("      * right. apply CIH. apply H.      ")
print ("      * right. apply CIH0. left. apply H.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_cupaco r rg:")
print ("  cupaco"+str(n)+" (cpaco"+str(n)+" r rg) <"+str(n)+"= cpaco"+str(n)+" r rg.")
print ("Proof.")
print ("  eapply cpaco"+str(n)+"_cofix.")
print ("  intros. destruct PR. econstructor.")
print ("  apply rclo"+str(n)+"_rclo. eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR.")
print ("  - apply rclo"+str(n)+"_base. left.")
print ("    eapply paco"+str(n)+"_mon. apply H.")
print ("    intros. right; apply CIH.")
print ("    econstructor. apply rclo"+str(n)+"_base. right.")
print ("    destruct PR as [PR|PR]; apply PR.")
print ("  - destruct H. eapply rclo"+str(n)+"_mon. apply IN0.")
print ("    intros. destruct PR; [| right; apply H].")
print ("    left. eapply paco"+str(n)+"_mon. apply H.")
print ("    intros. destruct PR. left; apply H0.")
print ("    right. apply INC, H0.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_uclo (uclo: rel -> rel) r rg ")
print ("      (LEclo: uclo <"+str(n+1)+"= cupaco"+str(n)+") :")
print ("  uclo (cpaco"+str(n)+" r rg) <"+str(n)+"= cpaco"+str(n)+" r rg.")
print ("Proof.")
print ("  intros. apply cpaco"+str(n)+"_cupaco. apply LEclo, PR.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_base r rg: r <"+str(n)+"= cpaco"+str(n)+" r rg.")
print ("Proof.")
print ("  econstructor. apply rclo"+str(n)+"_base. right. apply PR.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_rclo r:")
print ("  rclo"+str(n)+" clo r <"+str(n)+"= cupaco"+str(n)+" r.")
print ("Proof.")
print ("  intros. econstructor.")
print ("  eapply rclo"+str(n)+"_mon. apply PR.")
print ("  intros. right. apply PR0.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_clo r:")
print ("  clo r <"+str(n)+"= cupaco"+str(n)+" r.")
print ("Proof.")
print ("  intros. apply cpaco"+str(n)+"_rclo. apply rclo"+str(n)+"_clo.")
print ("  eapply clo_compat. apply PR.")
print ("  intros. apply rclo"+str(n)+"_base. apply PR0.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_step r rg:")
print ("  gf (cpaco"+str(n)+" rg rg) <"+str(n)+"= cpaco"+str(n)+" r rg.")
print ("Proof.")
print ("  intros. econstructor. apply rclo"+str(n)+"_base. left.")
print ("  pstep. eapply gf_mon. apply PR.")
print ("  intros. destruct PR0. eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR0.")
print ("  - left. eapply paco"+str(n)+"_mon. apply H. right. destruct PR0; apply H0.")
print ("  - right. right. apply H.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_init:")
print ("  cpaco"+str(n)+" bot"+str(n)+" bot"+str(n)+" <"+str(n)+"= paco"+str(n)+" gf bot"+str(n)+".")
print ("Proof.")
print ("  intros. destruct PR. revert"+itrstr(" x", n)+" IN.")
print ("  pcofix CIH. intros.")
print ("  pstep. eapply gf_mon; [| right; apply CIH, rclo"+str(n)+"_rclo, PR]. ")
print ("  apply compat"+str(n)+"_compat with (gf:=gf). apply rclo"+str(n)+"_compat. apply gf_mon. apply clo_compat.")
print ("  eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. pclearbot. _punfold PR; [..|apply cpaco"+str(n)+"_def_mon].")
print ("  eapply cpaco"+str(n)+"_def_mon. apply PR.")
print ("  intros. pclearbot. left. apply PR0.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_final r rg:")
print ("  (r \\"+str(n)+"/ paco"+str(n)+" gf rg) <"+str(n)+"= cpaco"+str(n)+" r rg.")
print ("Proof.")
print ("  intros. destruct PR. apply cpaco"+str(n)+"_base, H.")
print ("  econstructor. apply rclo"+str(n)+"_base.")
print ("  left. eapply paco"+str(n)+"_mon_gen. apply H.")
print ("  - intros. eapply gf_mon. apply PR.")
print ("    intros. apply rclo"+str(n)+"_base. apply PR0.")
print ("  - intros. right. apply PR.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_unfold:")
print ("  cpaco"+str(n)+" bot"+str(n)+" bot"+str(n)+" <"+str(n)+"= gf (cpaco"+str(n)+" bot"+str(n)+" bot"+str(n)+").")
print ("Proof.")
print ("  intros. apply cpaco"+str(n)+"_init in PR. _punfold PR; [..|apply gf_mon].")
print ("  eapply gf_mon. apply PR.")
print ("  intros. pclearbot. apply cpaco"+str(n)+"_final. right. apply PR0.")
print ("Qed.")
print ("")
print ("End CompatiblePaco"+str(n)+"_main.")
print ("")
print ("Lemma cpaco"+str(n)+"_mon_gen (gf gf' clo clo': rel -> rel)"+itrstr(" x", n)+" r r' rg rg'")
print ("      (IN: @cpaco"+str(n)+" gf clo r rg"+itrstr(" x", n)+")")
print ("      (MON: monotone"+str(n)+" gf)")
print ("      (LEgf: gf <"+str(n+1)+"= gf')")
print ("      (LEclo: clo <"+str(n+1)+"= clo')")
print ("      (LEr: r <"+str(n)+"= r')")
print ("      (LErg: rg <"+str(n)+"= rg') :")
print ("  @cpaco"+str(n)+" gf' clo' r' rg'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply cpaco"+str(n)+"_mon; [|apply LEr|apply LErg].")
print ("  destruct IN. econstructor.")
print ("  eapply rclo"+str(n)+"_mon_gen. apply IN. apply LEclo.")
print ("  intros. destruct PR; [| right; apply H].")
print ("  left. eapply paco"+str(n)+"_mon_gen. apply H.")
print ("  - intros. eapply LEgf.")
print ("    eapply MON. apply PR.")
print ("    intros. eapply rclo"+str(n)+"_mon_gen. apply PR0. apply LEclo. intros; apply PR1.")
print ("  - intros. apply PR.")
print ("Qed.")
print ("")
print ("Lemma cpaco"+str(n)+"_mon_bot (gf gf' clo clo': rel -> rel)"+itrstr(" x", n)+" r' rg'")
print ("      (IN: @cpaco"+str(n)+" gf clo bot"+str(n)+" bot"+str(n)+""+itrstr(" x", n)+")")
print ("      (MON: monotone"+str(n)+" gf)")
print ("      (LEgf: gf <"+str(n+1)+"= gf')")
print ("      (LEclo: clo <"+str(n+1)+"= clo'):")
print ("  @cpaco"+str(n)+" gf' clo' r' rg'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply cpaco"+str(n)+"_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.")
print ("Qed.")
print ("")
print ("End CompatiblePaco"+str(n)+".")
print ("")
print ("Hint Resolve cpaco"+str(n)+"_base : paco.")
print ("Hint Resolve cpaco"+str(n)+"_step : paco.")
print ("Hint Resolve cpaco"+str(n)+"_final : paco.")
print ("Hint Resolve rclo"+str(n)+"_base : paco.")