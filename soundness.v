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

  Lemma isEmpty_false : forall NT T, forall r:rhs.t T NT, rhs.isEmpty r = false <-> (r <> Empty).
  Proof.
  intros.
  rewrite <- isEmpty_true.
  rewrite not_true_iff_false.
  reflexivity.
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

   (*hold on*)(*
  Definition getRHS `{EqDec NT eq}
           (nt : NT) : list (NT * rhs.t T NT) ->
                       list (rhs.t T NT) :=
    filterMap (fun rule => let '(nt', rhs) := rule in
                        if nt == nt' then Some rhs else None). *)(*
  Lemma getRHS_sound : forall nt, forall rules, reg_grammar.getRHS nt rules = [] \/
  (exists a: (NT * rhs.t T NT),exists n:NT,In (snd a) (reg_grammar.getRHS (nt) rules) /\ n = fst a).
  intros. destruct rules.
  Proof.
  - left. reflexivity.
  - right. exists p. exists nt. 
  Lemma getRHS_sound : forall nt, forall rules, reg_grammar.getRHS nt rules = [] \/
  (exists n:(NT),exists rhs: rhs.t T NT, exists rule: NT * rhs.t T NT,
  In (rhs) (reg_grammar.getRHS (nt) rules) /\ fst rule = nt /\ snd rule = rhs).
  Proof.
  intros.
  destruct rules.
  - left. reflexivity.
  - right. exists nt. exists (snd p). exists p.
    simpl.
    destruct equiv_dec with (x:=fst p)(y:= nt).
    rewrite e.  
  Admitted.*)

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

  (* -- In (None) a prob. *)(*
  Inductive final_state (g:reg_grammar.g T NT)  : (list (option NT)) -> Prop :=
  | state_final_e :
                  (reg_grammar.is_final (reg_grammar.rules g) [] = true) -> final_state g []

  | state_final :  forall a, (In (None) a \/
                  (exists n,(In (Some n) a /\ reg_grammar.is_final (reg_grammar.rules g) (a) = true))) -> final_state g a.

  (*testing with inductive proposition*)
  Lemma is_final_true_inductive : forall l,forall g:reg_grammar.g T NT,
  reg_grammar.is_final (reg_grammar.rules g) l = true <-> final_state g l.
  Proof.
  intros.
  split.
  - intros. destruct l. inversion H1. apply state_final with (g:= g).
    destruct o. right. exists n. split. 
        + simpl. left. reflexivity.
        + assumption. 
        + left. simpl. left. reflexivity.
  - intros. destruct H1.
    + assumption.
    + destruct H1 as [left | right]. destruct a. inversion left. inversion left. rewrite H1. reflexivity.
    (*stuck*) *)

  (*As defined by is_final's behaviour, it should return true if there is a None *)
  (* in the list of nonterminal symbols, meaning it reached a valid rule which is from the *)
  (* kind A -> "a" or A -> e, "a" being a terminal character and e means the empty string char. *)
  Lemma is_final_true : forall g:reg_grammar.g T NT, forall l: list (option NT),
  reg_grammar.is_final (reg_grammar.rules g) l = true -> (reg_grammar.is_final (reg_grammar.rules g) [] = true 
  \/  (In (None) (l) \/ exists n,(In (Some n) l /\ reg_grammar.is_final (reg_grammar.rules g) (l) = true))).
  Proof.
  intros.
  - intros. destruct l. left. assumption.
    right. destruct o. right. exists n. split.
    + simpl; auto.
    + assumption.
    + left. simpl. auto.
  Qed.

  (* -- (In (None) (l) prob; same with inductive proposition.
   Lemma is_final_true_forall : forall g:reg_grammar.g T NT, forall l: list (option NT),
  reg_grammar.is_final (reg_grammar.rules g) l = true <-> (reg_grammar.is_final (reg_grammar.rules g) l = true 
  \/  (In (None) (l) \/ exists n,(In (Some n) l /\ reg_grammar.is_final (reg_grammar.rules g) (l) = true)))).
  Proof.
  intros.
  split.
  - intros. destruct l. left. assumption.
    right. destruct o. right. exists n. split.
    + simpl; auto.
    + assumption.
    + left. simpl. auto.
    - intros. destruct l. destruct H1 as [left | right]. assumption. 
      + destruct right as [left' | right']. inversion left'. destruct right'. destruct H1. inversion H1.
      + destruct H1 as [left | right]. assumption. destruct right as [left' | right']. destruct o.
      rewrite H1. reflexivity. Admitted. *)

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
  (*of the grammar. incomplete lemma.                                                      *)
  (* Lemma parse_returns_true : forall grammar, forall l: list T,exists s,
  reg_grammar.parse grammar l = true <-> 
  reg_grammar.is_final (reg_grammar.rules grammar) s = true.
  Proof.
  intros.
  exists (reg_grammar.parse' (reg_grammar.rules grammar) l
   ([Some (reg_grammar.start_symbol grammar)])).
  split.
  - intros. rewrite <- H1. reflexivity.
  - intros. symmetry. rewrite <- H1. reflexivity.
  Qed. *)

  (*this inductive proposition states when the parser for a given grammar in a list of *)
  (*terminal symbols should return true. This comes straight from parse's definition. *)
  Inductive parse_true (g: reg_grammar.g T NT) : list T -> Prop :=
  | parse_t : forall l: list T,
                 ([Some (reg_grammar.start_symbol g)] |> reg_grammar.parse' (reg_grammar.rules g) l |> 
                  reg_grammar.is_final (reg_grammar.rules g) = true) -> parse_true g l.

  (*This lemma states that for all list of terminal symbols, the parse on those lists will return true iff it *)
  (* is in agreement with the conditions where the parser should return true, stated in parse_true. *)
  Lemma parse_returns_true_forall : forall grammar, forall l: list T,
  reg_grammar.parse grammar l = true <-> parse_true grammar l.
  Proof.
  intros.
  split.
  - intros. apply parse_t. rewrite <- H1. unfold reg_grammar.parse. reflexivity.
  - intros. destruct H1. rewrite <- H1. reflexivity.
  Qed.

  (*following the idea presented above, we can define the following proposition as the proposition *)
  (*that states when the parser should return false:                                               *)
  Inductive parse_false (g: reg_grammar.g T NT) : list T -> Prop :=
  | parse_f : forall l,
                 ([Some (reg_grammar.start_symbol g)] |> reg_grammar.parse' (reg_grammar.rules g) l |> 
                  reg_grammar.is_final (reg_grammar.rules g) = false) -> parse_false g l.

  (*Now, the lemma that states the parser should return false iff it meets the requirements to return false: *)
  Lemma parse_returns_false_forall : forall grammar, forall l: list T,
  reg_grammar.parse grammar l = false <-> parse_false grammar l.
  Proof.
  intros.
  split.
  - intros. apply parse_f. rewrite <- H1. unfold reg_grammar.parse. reflexivity.
  - intros. destruct H1. rewrite <- H1. reflexivity.
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


  (* The following lemma asserts that a run in a list of terminal symbols with a automata   *)
  (* shall return true iff there is an final state that is reachable from the initial state.*)
  (* incomplete lemma: we prove for a specific case.                                        *)

  (*Lemma run_soundness :forall grammar:reg_grammar.g T NT,forall l:list T, exists final,
  dfa.run (powerset_construction.dfa g) l = true 
  <-> dfa.is_final (powerset_construction.dfa g) final = true.
  Proof.
  intros.
  exists (dfa.run' (dfa.next (powerset_construction.dfa g))
  l  (dfa.initial_state (powerset_construction.dfa g ))).
  split.
  - intros. rewrite <- H1. simpl. simpl in H1. reflexivity. 
  - intros. rewrite <- H1. reflexivity.
  Qed. *)

  (* the following inductive proposition states that, after running a word in a automata built from a grammar, *)
  (* if it reaches a final state, then we have the run of a given list of terminals on the automata is valid   *)
  (* returns true                                                                                              *)
  Inductive run_true (g: reg_grammar.g T NT) : list T -> Prop := 
  |run_t : forall l:list T, 
    (dfa.is_final (powerset_construction.dfa g)
    (dfa.run' (dfa.next (powerset_construction.dfa g)) l
     (dfa.initial_state (powerset_construction.dfa g))) = true)-> run_true g l.

  (* The following lemma states that, for all runs on list of terminals for all automata built from a given grammar*)
  (* it retuns true iff it reaches a final state after running the word on the automata, starting in the initial   *)
  (*state of the automata, as stated in "run_true".                                                                 *)
  Lemma run_soundness_true_forall: forall grammar:reg_grammar.g T NT, forall l:list T,
  dfa.run (powerset_construction.dfa g) l = true  <-> run_true g l.
  Proof.
  intros.
  split.
  - intros. apply run_t. rewrite <- H1. reflexivity.
  - intros. destruct H1. rewrite <- H1. reflexivity.
  Qed.

  (*Following the idea presented above, we can define the soundness in the case the automata *)
  (*should return false after a run in a given list of terminal symbols:                     *)
  Inductive run_false (g: reg_grammar.g T NT) : list T -> Prop := 
  |run_f : forall l:list T, 
    (dfa.is_final (powerset_construction.dfa g)
    (dfa.run' (dfa.next (powerset_construction.dfa g)) l
     (dfa.initial_state (powerset_construction.dfa g))) = false)-> run_false g l.

  Lemma run_soundness_false_forall: forall grammar:reg_grammar.g T NT, forall l:list T,
  dfa.run (powerset_construction.dfa g) l = false  <-> run_false g l.
  Proof.
  intros.
  split.
  - intros. apply run_f. rewrite <- H1. reflexivity.
  - intros. destruct H1. rewrite <- H1. reflexivity.
  Qed.
  (* Then, we can conclude that both the parser for a given grammar and the automata built from *)
  (* the same grammar does the same work. This is possible thanks to the way the automata's     *)
  (* behaviour is defined from a grammar.                                                       *)
  Lemma dfa_and_parser : forall l, reg_grammar.parse g l = dfa.run (powerset_construction.dfa g) l.
    Proof.
      reflexivity.
    Qed.

End dfa_lemmas.
