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

  (* Otherwise, it returns false iff the rule is not empty.                                   *)
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

  (* The following lemma states that the function step_rhs is sound. The step_rhs function checks if given *)
  (* the RHS of a derivation rule and a terminal symbol, the rule can be used to derive this symbol.       *)
  (* According to its definition, the resulting list is empty if the RHS is empty or the terminal symbol   *)
  (* differs from the one that the RHS has.                                                                *)
  (* This lemma states that for all executions of this function, it will return either an empty list,      *)
  (* [None], which means a Rule "Single t" could be used or [Some nt], which means that a rule             *)
  (* "Continue t nt" was used to derive the given "t"                                                      *)
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

  (* The following lemma states the soundness of the step_nt function. This function tries to apply all    *)
  (* the possible derivation rules for a given nonterminal symbol and a terminal symbol. It returns either *)
  (* a empty list (if the terminal symbol being analyzed cannot be derived by the nonterminal symbol,      *)
  (* a list that contains [None], which mean "there is a possible derivation from this nonterminal symbol" *)
  (* "that uses the rule Single t, meaning this terminal symbol can be derived and the derivation can end" *)
  (* or exists a nonterminal symbol that will be in the resulting list, meaning that a rule of the type    *)
  (* "Continue t nt" could be used to derive the terminal symbol, being able to continue the derivation    *)
  (* from "nt", which is another nonterminal symbol.                                                       *)
  Lemma step_nt_sound : forall rules,forall t, forall nt, reg_grammar.step_nt rules t nt =  [] \/
  In None (reg_grammar.step_nt rules t nt)  \/ (exists n:NT, In (Some n) (reg_grammar.step_nt rules t nt)).
  Proof.
  intros.
  destruct reg_grammar.step_nt.
  - left. reflexivity.
  - destruct o. right. right. simpl. exists n. left. reflexivity.
    right. left. simpl. left. reflexivity. Qed.

  (* The following lemma states the soundness of the step function. In other words, this function applies *)
  (* "step_nt" to a list of possible nonterminal symbols, in which the derivation could be done. it works *)
  (* just like the above function: an empty list is returned if in the list of nonterminal symbols, none  *)
  (* of them can derive the given terminal symbol, a list containing at least None, which means there was *)
  (* at least a RHS "Single t'" that could derive the t, or a list containing at least Some nt, where a   *)
  (* rule of the kind "Continue t' nt" could be used to derive the terminal symbol t                      *)
  Definition step_sound: forall rules, forall t, forall acc, reg_grammar.step rules t acc = [] \/
  In (None) (reg_grammar.step rules t acc) \/ (exists nt:NT, In (Some nt)(reg_grammar.step rules t acc)).
  Proof.
  intros.
  destruct reg_grammar.step.
  - left. reflexivity.
  - destruct o. right. right. exists n. simpl. left. reflexivity.
    right. left. simpl. left. reflexivity.
  Qed.

  (* The following lemmas states the soundness of the parse' function, the main parser loop. By the      *)
  (* definitionof parse', it should return or a empty list, or a list that has None or a list that       *)
  (* or a list that contains Some nt in it, some NT being a nonterminal symbol. Recall that this function*)
  (* will return a list of possible terminal symbols. works like the above function, but now for all the *)
  (* terminal symbols given as input, it will try to apply valid rules on this list.                     *)
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
  Lemma is_final_check : forall r:list (NT * rhs.t T NT),forall l:list (option NT), reg_grammar.is_final r l = true \/ 
  reg_grammar.is_final r l = false.
 Proof.
    intros r l.
    destruct reg_grammar.is_final;auto.
  Qed.


  (* The "is_final" function should return true if it is verifying a final state. *)
  (*As defined by is_final's behaviour, it should return true if there is a None  *)
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

  (* This inductive proposition states when the parser for a given grammar in a list of terminal     *)
  (* symbols should return true. This comes straight from parse's definition, where it should return *)
  (* true if for all list of terminal symbols, from the starting symbol of the grammar, the parse'   *)
  (* returns a accepting state (which means it was possible to derive this list.                     *)
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

  (* The following lemma states the soundness of the "get_nondetermism" function, which  *)
  (* means: returns true iff there is at least a rule in the list of rules that goes to  *)
  (* at least 2 different states in a given nonterminal symbol and with the same         *)
  (* terminal symbol.                                                                    *)

  (*
  Lemma get_nondeterminism_true : forall rules, reg_grammar.get_nondeterminism rules rules
  = true <-> (exists r:(NT * rhs.t T NT),
  (In r rules) /\ 
 (reg_grammar.get_all_t rules (fst r) |> reg_grammar.count (reg_grammar.get_t_from_rhs(snd r))) >= 2).
  Proof.
  intros.
  split.
  - intros. destruct rules. inversion H1. exists p. split.
    + simpl. auto.
    + inversion H1.
 (* maybe it will be needed a indutcive proposition *)
  Admitted. *)

End reg_grammar_lemmas.

Section dfa_lemmas.
  Variables (S A T NT : Type).
  Variable g: reg_grammar.g T NT.
  Variable m: dfa.t T NT.
  Context `{EqDec T eq} `{EqDec NT eq}.

  (*The following lemma asserts that a is_final function should always return true or false *)
  Lemma run_companion : forall m:dfa.t S A, forall l, dfa.run m l = true \/ dfa.run m l = false.
    Proof.
    intros.
    destruct dfa.run;auto.
    Qed.

  (* The proposition "run_true_dfa" states that, given a valid DFA that can be built from a        *)
  (* grammar it returns true iff after running over a word, the automaton is in a final state. *)
  Inductive run_true_dfa (g: reg_grammar.g T NT) : list T -> Prop := 
  |run_t : forall l:list T,
  (dfa.is_final (powerset_construction.build_dfa g)
    (dfa.run' (dfa.next (powerset_construction.build_dfa g)) l
     (dfa.initial_state (powerset_construction.build_dfa g))) = true) -> run_true_dfa g l.

  (* The following lemma states that, for all runs on list of terminals for all automata built from a given grammar*)
  (* it retuns true iff it reaches a final state after running the word on the automata, starting in the initial   *)
  (*state of the automaton, as stated in "run_true_dfa".                                                                 *)
  Lemma run_soundness_true_forall: forall g :reg_grammar.g T NT, forall l:list T,
  dfa.run (powerset_construction.build_dfa g) l = true  <-> run_true_dfa g l.
  Proof.
  intros.
  split.
  - intros. apply run_t. destruct H1. split.
  - intros.  destruct H1. rewrite <- H1. reflexivity. 
  Qed. 

  (*Following the idea presented above, we can define the soundness in the case the automaton *)
  (*should return false after a run in a given list of terminal symbols:                     *)
 Inductive run_false_dfa (g: reg_grammar.g T NT) : list T -> Prop := 
  |run_f : forall l:list T,
  (dfa.is_final (powerset_construction.build_dfa g)
    (dfa.run' (dfa.next (powerset_construction.build_dfa g)) l
     (dfa.initial_state (powerset_construction.build_dfa g))) = false) -> run_false_dfa g l.

  Lemma run_soundness_false_forall: forall g :reg_grammar.g T NT, forall l:list T,
  dfa.run (powerset_construction.build_dfa g) l = false <-> run_false_dfa g l.
  Proof.
  intros.
  split.
  - intros.  inversion H1. apply run_f. rewrite <- H3. reflexivity.
  - intros. destruct H1. destruct H1. reflexivity.
  Qed. 

  (* Then, we can conclude that both the parser for a given grammar and the automata built from *)
  (* the same grammar does the same work. This is possible thanks to the way the automata's     *)
  (* behaviour is defined from a grammar.                                                       *)
  (* If the method to construct a valid DFA returns a valid value for a DFA, then we can con*)
  (* clude that the DFA built from a grammar and the parser does the same work.            *)
  (* In other words, the automaton and the parser has the same rules, the same initial sta-*)
  (* te and the same final states.                                                         *) 
  Lemma dfa_and_parser : forall l,
  reg_grammar.parse g l = dfa.run (powerset_construction.build_dfa g) l .
    Proof.
      intros.
      reflexivity.
    Qed. 


  Lemma dfa_to_regular_grammar_sound: forall m:dfa.t S A, dfa.dfa_to_regular_grammar m
  = {| reg_grammar.start_symbol := (dfa.initial_state m);
      reg_grammar.rules := (dfa.dfa_rules_to_regular_grammar m (dfa.transition_rules m))|}.
  Proof.
  intros. reflexivity. Qed.
  Check dfa.dfa_to_regular_grammar.


  (* Problem: the transition rules of the DFA is not being used explicitely in the *)
  (* next function of the DFA. *)
  (*Lemma parser_and_dfa: forall l, dfa.run (m) l = 
  reg_grammar.parse (dfa.dfa_to_regular_grammar m) l.
  Proof.
  intros.
  unfold dfa.dfa_to_regular_grammar. unfold dfa.run.
  destruct l. Abort.*)

End dfa_lemmas.

Section nfa_lemmas (* under construction *).
  Variables (S A : Type).
  Variable nfa : nfa.t S A.
  Context `{EqDec S eq} `{EqDec A eq}.

  Lemma run'_companion : forall m:nfa.t S A, forall l, nfa.run m l = true \/ nfa.run m l = false.
    Proof.
    intros.
    destruct nfa.run;auto.
    Qed.

  (* pode ser o caso de state não ser final... nfa.verify_final_state nfa states = true *)
  (* e o estado que pode ser veradeiro pode não ser state.                              *)
  Lemma verify_final_state_true : forall states,
  nfa.verify_final_state nfa states = true
  ->  exists state: S, In state (states) /\ nfa.is_final nfa state = true.
  Proof.
  intros.
  induction states.
    + inversion H1.
    + destruct H1.  exists a. split. simpl;auto. (*no evidence that a is a final state...*)
      case (nfa.is_final nfa a == true).
      intros.  (* opa *)
      intros. Admitted.

(* TODO *)

  Inductive nfa_true (nfa: nfa.t S A) : list A -> Prop :=
  | nfa_t : forall l: list A,
        nfa.verify_final_state nfa (nfa.run' (nfa) l  ([(nfa.initial_state nfa)])) = true -> nfa_true nfa l.

  (* The NFA returns true iff it reaches a possible final state after a run. *)
  Lemma nfa_returns_true: forall l:list A, nfa.run nfa l = true
  <-> nfa_true nfa l.
  Proof.
  intros.
  split.
  - intros. apply nfa_t. rewrite <- H1. reflexivity.
  - intros. unfold nfa.run. inversion H1. apply H2.
  Qed.
  (*Lemma nfa_returns_true : forall l:list A, nfa.run nfa l = true <->
  exists state: S, In state (nfa.run' nfa l [nfa.initial_state nfa])
   /\ nfa.is_final nfa state = true. *)

   Inductive nfa_false (nfa: nfa.t S A) : list A -> Prop :=
  | nfa_f : forall l: list A,
   nfa.verify_final_state nfa (nfa.run' (nfa) l  ([(nfa.initial_state nfa)])) = false -> nfa_false nfa l.

  Lemma nfa_returns_false: forall l:list A, nfa.run nfa l = false
  <-> nfa_false nfa l.
  Proof.
  intros.
  split.
  - intros. apply nfa_f. rewrite <- H1. reflexivity.
  - intros. unfold nfa.run. inversion H1. apply H2.
  Qed.

End nfa_lemmas.