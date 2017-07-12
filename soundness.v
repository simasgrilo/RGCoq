Require Import main.
Require Import Classes.EquivDec.
Require Import List.
Require Import Bool.
Import rhs.exports.
Import ListNotations.

(*Note: compile main.v before running this .v file *)

(* Lemmas about functions within the rhs module          *)
Section rhs_lemmas.
(*the following lemma states that isEmpty won't return a value different from false or true *)
  Lemma isEmpty_sound  :forall NT T, forall r:rhs.t T NT, rhs.isEmpty r = false \/ rhs.isEmpty r = true.
    Proof.
    intros.
    destruct rhs.isEmpty;auto.
    Qed.
  (* this lemma states that the function isEmpty only returns true when the RHS of a given rule*)
  (* is empty, i.e., a rule is in the form A -> e, e meaning the empty string.                 *)
  Lemma isEmpty_true : forall NT T, forall r:rhs.t T NT, rhs.isEmpty r = true <-> r = Empty.
  Proof.
  intros.
  split.
  - intros. destruct r. reflexivity. simpl in H. discriminate. simpl in H. discriminate.
  - intros. rewrite H. reflexivity.
  Qed.

End rhs_lemmas.

(*Lemmas about the soundness of functions within the reg_grammar module        *)
Section reg_grammar_lemmas.
  Variable T NT : Type.
  Context  `{EqDec T eq} `{EqDec NT eq}.
  (*The following lemma states that a grammar returned by build_grammar shall has the start *)
  (*symbol and the rules passed as the parameters.                                          *)
    Lemma build_grammar_sound : forall nt:NT, forall rules:list (NT * rhs.t T NT), reg_grammar.build_grammar nt rules = {|
      reg_grammar.start_symbol := nt;
      reg_grammar.rules := rules |}.
  Proof.
  intros. unfold reg_grammar.build_grammar. reflexivity. Qed.

  (*the following lemma states that the function step_rhs is sound                         *)
  Lemma step_rhs_sound : forall t:T, forall rhs: rhs.t T NT, reg_grammar.step_rhs t rhs = [] \/
  reg_grammar.step_rhs t rhs = [None] \/ (exists nt, reg_grammar.step_rhs t rhs = [Some nt]).
  Proof.
  intros t rhs.
  destruct rhs; auto.
  simpl. destruct equiv_dec. auto.
  auto.
  simpl. destruct equiv_dec eqn:I;auto. 
  right. right. exists (n). reflexivity.
  Qed.

  (*hold on:*)
  Lemma getRHS_sound : forall nt, forall rules, reg_grammar.getRHS nt rules = [] \/
  (exists r:rhs.t T NT,exists a: (NT * rhs.t T NT),In (r) (reg_grammar.getRHS nt rules)
  /\ r = snd a /\ fst a = nt).
  Proof.
  intros. destruct rules.
  - left. simpl. reflexivity.
  - right. exists (snd p). exists p. split.
    + simpl. case p. intros. destruct equiv_dec. simpl. left. reflexivity.
     Abort.

  (*The following lemma states the soundness of the step_nt function. *)
  Lemma step_nt_sound : forall rules,forall t, forall nt, reg_grammar.step_nt rules t nt =  [] \/
  In None (reg_grammar.step_nt rules t nt)  \/ (exists n:NT, In (Some n) (reg_grammar.step_nt rules t nt)).
  Proof.
  intros.
  destruct reg_grammar.step_nt.
  - left. reflexivity.
  - destruct o. right. right. simpl. exists n. left. reflexivity.
    right. left. simpl. left. reflexivity. Qed.

  (*The following lemma states the soundness of the step function *)
  Definition step_sound: forall rules, forall t, forall acc, reg_grammar.step rules t acc = [] \/
  In (None) (reg_grammar.step rules t acc) \/ (exists nt:NT, In (Some nt)(reg_grammar.step rules t acc)).
  Proof.
  intros.
  destruct reg_grammar.step.
  - left. reflexivity.
  - destruct o. right. right. exists n. simpl. left. reflexivity.
    right. left. simpl. left. reflexivity.
  Qed.

  (*The following lemmas states the soundness of the parse' function, the main parser loop.*)
  (*By the definition of parse', it should return or a empty list, or a list that has None *)
  (*or a list that contains Some nt in it, some NT being a nonterminal symbol              *)
  Definition parse'_sound: forall rules, forall lt, forall lnt, reg_grammar.parse' rules lt lnt = [] 
  \/ In (None) (reg_grammar.parse' rules lt lnt) \/ (exists nt:NT, In (Some nt) (reg_grammar.parse' rules lt lnt)).
  Proof.
  intros.
  destruct reg_grammar.parse'.
  - left. reflexivity.
  - destruct o. right. right. exists n. simpl. left. reflexivity.
    right. left. simpl. left. reflexivity.
  Qed.

  Lemma parse'_app_nil : forall g l acc, acc |> reg_grammar.parse' g (l ++ []) = acc 
  |> reg_grammar.parse' g l \/ acc |> reg_grammar.parse' g ([]++ l) = acc |> reg_grammar.parse' g l.
  Proof.
  induction l; simpl;auto.
  Qed.
  Lemma parse'_nil :
    forall g l ,
      reg_grammar.parse' g l [] = [].
  Proof.
    induction l; simpl; auto.
  Qed.
  Lemma parse'_app :
    forall g l1 l2 acc,
      acc |> reg_grammar.parse' g (l1 ++ l2) =
      acc |> reg_grammar.parse' g l1 |> reg_grammar.parse' g l2.
  Proof.
    induction l1; simpl; auto.
  Qed.

  (*The following lemma state that the is_final function may always return true or false*)
  Lemma is_final_sound : forall r:list (NT * rhs.t T NT),forall l:list (option NT), reg_grammar.is_final r l = true \/ 
  reg_grammar.is_final r l = false.
 Proof.
    intros r l.
    destruct reg_grammar.is_final;auto.
  Qed.

  (*As defined by is_final's behaviour, it should return true iff there is a None *)
  (* in the list of nonterminal symbols, meaning it reached a valid rule which is from the *)
  (* kind A -> "a" or A -> e, "a" being a terminal character and e means the empty string char. *)
  Lemma is_final_true : forall r:list (NT * rhs.t T NT),forall a:list (option NT), exists l,
  reg_grammar.is_final r l = true <-> In (None) l.
  Proof.
  intros.
  exists (None::a).
  split.
  - intros. simpl. left. reflexivity. 
  - intros. simpl. reflexivity.
  Qed.


  (*The following lemmas states properties about the soundness of the grammar parser *)
  Lemma parse_companion : forall grammar, forall l, reg_grammar.parse grammar l = true \/ 
  reg_grammar.parse grammar l = false.
  Proof.
  intros.
  destruct reg_grammar.parse;auto.
  Qed.



  (*a word is recognizable by the parser if it can be generated by the grammar's rules *)
  (*In this sense, the parser returns true iff exists an final state in the grammar, which *)
  (*is reachable by applying parse' in the list of terminals, starting in the start symbol *)
  (*of the grammar                                                                       *)
  Lemma parse_returns_true : forall grammar, forall l: list T,exists s,
  reg_grammar.parse grammar l = true <-> 
  reg_grammar.is_final (reg_grammar.rules grammar) s = true.
  Proof.
  intros.
  exists (reg_grammar.parse' (reg_grammar.rules grammar) l
   ([Some (reg_grammar.start_symbol grammar)])).
  split.
  - intros. rewrite <- H1. reflexivity.
  - intros. symmetry. rewrite <- H1. reflexivity.
  Qed.

End reg_grammar_lemmas.

Section dfa_lemmas.
  Variables (S A T NT : Type).
  Variable g: reg_grammar.g T NT.
  Context `{EqDec T eq} `{EqDec NT eq}.

  (*The following lemma asserts that a is_final function should always return true or false *)
  Lemma run_companion : forall m:dfa.t S A, forall l, dfa.run m l = true \/ dfa.run m l = false.
    Proof.
    intros.
    destruct dfa.run;auto.
    Qed.

  (* The following lemma asserts that a run in a list of terminal symbols with a automata *)
  (* shall return true iff there is an final state that is reachable from the initial state.*)
  Lemma run_soundness :forall grammar:reg_grammar.g T NT,forall l:list T, exists final,
  dfa.run (powerset_construction.dfa g) l = true 
  <-> dfa.is_final (powerset_construction.dfa g) final = true.
  Proof.
  intros.
  exists (dfa.run' (dfa.next (powerset_construction.dfa g))
  l  (dfa.initial_state (powerset_construction.dfa g ))).
  split.
  - intros. rewrite <- H1. simpl. simpl in H1.  reflexivity. 
  - intros. rewrite <- H1. reflexivity.
  Qed.

End dfa_lemmas.