Require Import main.
Require Import Classes.EquivDec.
Require Import List.
Require Import Bool.
Require Import ListSet.
Import rhs.exports.
Import ListNotations.
Import nfa_epsilon_transitions.exports.

(*Note: compile main.v before running this .v file *)

(* Lemmas about functions within the rhs module          *)
Section rhs_lemmas.
(*the following lemma states that isEmpty won't return a value different from false or true *)
  Lemma isEmpty_sound  :forall NT T : Type, forall r:rhs.t T NT, rhs.isEmpty r = false \/ rhs.isEmpty r = true.
    Proof.
    intros.
    destruct rhs.isEmpty;auto.
    Qed.
  (* this lemma states that the function isEmpty only returns true when the RHS of a given rule*)
  (* is empty, i.e., a rule is in the form A -> e, e meaning the empty string.                 *)
  Lemma isEmpty_true : forall NT T : Type, forall r:rhs.t T NT, rhs.isEmpty r = true <-> r = Empty.
  Proof.
  intros.
  split.
  - intros. destruct r. reflexivity. simpl in H. discriminate. simpl in H. discriminate.
  - intros. rewrite H. reflexivity.
  Qed.

  (* Otherwise, it returns false iff the rule is not empty.                                   *)
  Lemma isEmpty_false : forall NT T : Type, forall r:rhs.t T NT, rhs.isEmpty r = false <-> (r <> Empty).
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
    Lemma build_grammar_sound : forall nt:NT, forall rules: set (NT * rhs.t T NT),
    forall alphabet: set T, forall nonterminals: set NT,
    reg_grammar.build_grammar nt rules alphabet nonterminals = {|
      reg_grammar.start_symbol := nt;
      reg_grammar.rules := add_list_to_set rules; 
      reg_grammar.terminal_symbols := add_list_to_set alphabet;
      reg_grammar.nonterminal_symbols := add_list_to_set nonterminals |}.
  Proof.
  intros. unfold reg_grammar.build_grammar. reflexivity. Qed.

  (* The following lemma states that the function step_rhs is sound. The step_rhs function checks if given *)
  (* the RHS of a derivation rule and a terminal symbol, the rule can be used to derive this symbol.       *)
  (* According to its definition, the resulting set is empty if the RHS is empty or the terminal symbol   *)
  (* differs from the one that the RHS has.                                                                *)
  (* This lemma states that for all executions of this function, it will return either an empty set,      *)
  (* [None], which means a Rule "Single t" could be used or [Some nt], which means that a rule             *)
  (* "Continue t nt" was used to derive the given "t"                                                      *)
  Lemma step_rhs_sound : forall t:T, forall rhs: rhs.t T NT, reg_grammar.step_rhs t rhs = [] \/
  reg_grammar.step_rhs t rhs = [None] \/ (exists nt, reg_grammar.step_rhs t rhs = [Some nt]).
  Proof.
  intros t rhs.
  destruct rhs. auto.
  simpl. destruct equiv_dec. auto.
  auto.
  simpl. destruct equiv_dec. right. right. exists (n). auto. 
  left. reflexivity.
  Qed.

  (* The function step_rhs returns None iff the rule used is of the kind Single x, and x equals the x*)
  (*given as a parameter to the function. *)
  Lemma step_rhs_none : forall t:T, forall rhs: rhs.t T NT, reg_grammar.step_rhs t rhs = [None]
  <-> rhs = Single t.
  Proof.
  intros. split.
  - intros. destruct rhs. 
     + inversion H1.
     + simpl in H1. destruct equiv_dec. rewrite e. reflexivity. inversion H1.
     + simpl in H1. destruct equiv_dec. inversion H1. inversion H1.
  - intros. 
    rewrite H1. simpl. destruct equiv_dec. 
    reflexivity. exfalso. apply c. reflexivity.
  Qed.

  Lemma step_rhs_some : forall t:T, forall rhs: rhs.t T NT, forall nt:NT,
  reg_grammar.step_rhs t rhs = [Some nt] <-> rhs = Continue t nt.
  Proof.
  intros.
  split.
  - intros. destruct rhs. 
    + inversion H1.
    + simpl in H1. destruct equiv_dec. inversion H1. inversion H1.
    + simpl in H1. destruct equiv_dec. rewrite <- e. inversion H1. reflexivity. inversion H1.
  - intros. rewrite H1. simpl. destruct equiv_dec. 
    +  reflexivity.
    +  exfalso. apply c. reflexivity. 
  Qed.

  Lemma step_rhs_nil: forall t:T, forall rhs: rhs.t T NT, reg_grammar.step_rhs t rhs = [] <->
  (rhs = Empty \/ exists x:T, (rhs = Single x /\ x =/= t) \/ 
  (exists nt:NT, rhs = Continue x nt /\ x=/=t)).
  Proof.
  intros.
  split.
  - intros. destruct rhs.
    + left. reflexivity.
    + right. exists t0. left. split. reflexivity.
      simpl in H1. destruct equiv_dec. inversion H1. congruence.
    + right. exists t0. right. exists n. split. reflexivity.
      simpl in H1. destruct equiv_dec. inversion H1. congruence.
  - intros. destruct rhs.
    + simpl. reflexivity.
    + simpl. destruct H1.  inversion H1. destruct H1. destruct H1 as [H2 | H3].
    { destruct H2. inversion H1. destruct equiv_dec. exfalso. 
    apply H2. inversion e. reflexivity. reflexivity. }
    destruct H3. destruct H1. inversion H1.
    + simpl. destruct H1.
    inversion H1. destruct H1. destruct H1 as [H2 | H3]. destruct H2. inversion H1.
    destruct H3. destruct equiv_dec. destruct H1. congruence. reflexivity.
  Qed.

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

  Lemma getRHS_sound : forall nt:NT, forall rules: list (NT * rhs.t T NT),  reg_grammar.getRHS nt rules = []
  \/ exists rule:rhs.t T NT, In (rule) (reg_grammar.getRHS nt rules) .
  Proof.
  intros.
  destruct reg_grammar.getRHS.
  - left. reflexivity.
  - right. exists t. simpl. auto.
  Qed.

  (* The following lemmas states the soundness of the parse' function, the main parser loop. By the      *)
  (* definitionof parse', it should return or a empty list, or a list that has None or a list that       *)
  (* or a list that contains Some nt in it, some NT being a nonterminal symbol. Recall that this function*)
  (* will return a list of possible terminal symbols. works like the above function, but now for all the *)
  (* terminal symbols given as input, it will try to apply valid rules on this list.                     *)
  Lemma parse'_sound: forall rules, forall lt, forall lnt, reg_grammar.parse' rules lt lnt = [] 
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
  Lemma is_final_check : forall r:set (NT * rhs.t T NT),forall l:set (option NT), reg_grammar.is_final r l = true \/ 
  reg_grammar.is_final r l = false.
 Proof.
    intros r l.
    destruct reg_grammar.is_final;auto.
  Qed.

  (* (reg_grammar.getRHS n (reg_grammar.rules g) |> existsb rhs.isEmpty) = true))).*)

  (* The "is_final" function should return true if it is verifying a final state. *)
  (*As defined by is_final's behaviour, it should return true if there is a None  *)
  (* in the list of nonterminal symbols, meaning it reached a valid rule which is from the *)
  (* kind A -> "a" or A -> e, "a" being a terminal character and e means the empty string char. *)
  Lemma is_final_true : forall g:reg_grammar.g T NT, forall l: list (option NT),
  reg_grammar.is_final (reg_grammar.rules g) l = true -> (In (None) (l)) \/ (exists n,(In (Some n) l /\ 
  reg_grammar.is_final (reg_grammar.rules g) l = true)).
  Proof.
  intros.
  - intros. destruct l. left. inversion H1.
    destruct o. right. exists n. split.
    + simpl; auto.
    + assumption.
    + left. simpl. auto.
  Qed.

  (*The following lemmas states properties about the soundness of the grammar parser *)
  Lemma parse_companion : forall grammar, forall l, reg_grammar.parse grammar l = true \/ 
  reg_grammar.parse grammar l = false.
  Proof.
  intros.
  destruct reg_grammar.parse;auto.
  Qed.

  (*This lemma states that for all list of terminal symbols, the parse on those lists will return true iff it *)
  (* is in agreement with the conditions where the parser should return true, stated in parse_true. *)
  Lemma parse_returns_true_forall : forall grammar, forall l: list T,
  reg_grammar.parse grammar l = true <-> ([Some (reg_grammar.start_symbol grammar)] 
                  |> reg_grammar.parse' (reg_grammar.rules grammar) l |> 
                  reg_grammar.is_final (reg_grammar.rules grammar) = true).
  Proof.
  intros.
  split.
  - intros.  rewrite <- H1. unfold reg_grammar.parse. reflexivity.
  - intros. rewrite <- H1. unfold reg_grammar.parse. reflexivity.
  Qed.

  (*Now, the lemma that states the parser should return false iff it meets the requirements to return false: *)
  Lemma parse_returns_false_forall : forall grammar, forall l: list T,
  reg_grammar.parse grammar l = false <-> ([Some (reg_grammar.start_symbol grammar)] 
                  |> reg_grammar.parse' (reg_grammar.rules grammar) l |> 
                  reg_grammar.is_final (reg_grammar.rules grammar) = false).
  Proof.
  intros.
  split.
  - intros. rewrite <- H1. unfold reg_grammar.parse. reflexivity.
  - intros.  rewrite <- H1. unfold reg_grammar.parse. reflexivity.
  Qed.

End reg_grammar_lemmas.

Section dfa_lemmas.
  Variables (T NT : Type).
  Variable g: reg_grammar.g T NT.
  Variable m: dfa.t NT T.
  Context `{EqDec T eq} `{EqDec NT eq}.

  (*The following lemma asserts that a is_final function should always return true or false *)
  Lemma run_companion : forall m:dfa.t NT T, forall l, dfa.run m l = true \/ dfa.run m l = false.
    Proof.
    intros.
    destruct dfa.run;auto.
    Qed.

  (* The following lemma states that, for all runs on list of terminals for all automata built from a given grammar*)
  (* it retuns true iff it reaches a final state after running the word on the automata, starting in the initial   *)
  (*state of the automaton                                                                                         *)
  Lemma run_soundness_true_forall: forall m: dfa.t NT T, forall l:list T,
  dfa.run m l = true  <-> 
    (dfa.is_final m
    (dfa.run' (dfa.next m) l
     (dfa.initial_state m)) = true).
  Proof.
  intros.
  split.
  - intros. rewrite <- H1. reflexivity.
  - intros.  rewrite <- H1. reflexivity. 
  Qed.

  Lemma run_soundness_false_forall: forall m:dfa.t NT T, forall l:list T,
  dfa.run m l = false <-> (dfa.is_final m
    (dfa.run' (dfa.next m) l
     (dfa.initial_state m)) = false).
  Proof.
  intros.
  split.
  - intros.  rewrite <- H1. reflexivity.
  - intros. destruct H1. reflexivity.
  Qed. 

  (* Then, we can conclude that both the parser for a given grammar and the automata built from *)
  (* the same grammar does the same work. This is possible thanks to the way the automata's     *)
  (* behaviour is defined from a grammar.                                                       *)
  (* If the method to construct a valid DFA returns a valid value for a DFA, then we can con*)
  (* clude that the DFA built from a grammar and the parser does the same work.             *)
  (* In other words, the automaton and the parser has the same rules, the same initial sta- *)
  (* te and the same final states, which means they behave the same way.                    *) 
  Lemma dfa_and_parser : forall l, forall g,
  reg_grammar.parse g l = dfa.run (powerset_construction.build_dfa g) l .
    Proof.
      intros.
      unfold dfa.run. unfold reg_grammar.parse;unfold powerset_construction.build_dfa.
      reflexivity.
    Qed.
  (*TODO the below lemma: add_list_to_set necessary? *)
  Lemma dfa_to_regular_grammar_sound: forall m:dfa.t NT T, 
  dfa.dfa_to_regular_grammar m
  = {| reg_grammar.start_symbol := (dfa.initial_state m);
      reg_grammar.rules := add_list_to_set (dfa.dfa_transitions_to_grammar_rules m (dfa.states m) (dfa.alphabet m));
      reg_grammar.terminal_symbols := add_list_to_set (dfa.alphabet m); 
      reg_grammar.nonterminal_symbols := add_list_to_set(dfa.states m)|}.
  Proof.
  intros. reflexivity. Qed.

  (* Lemmas about NFAs built from DFAs *)

  Lemma same_initial_state : (dfa.initial_state m) = (nfa.initial_state (dfa.dfa_to_nfa m)).
  Proof.
  reflexivity.
  Qed.
  Lemma same_final_states : (dfa.is_final m) = nfa.is_final (dfa.dfa_to_nfa m).
  Proof.
  reflexivity.
  Qed.
  Lemma same_result_of_a_step :forall a:T, forall s:NT, [(dfa.next m s a)] = dfa.nfa_step m a s.
  Proof. reflexivity. Qed.

  (* For any state obtained after running the DFA or the NFA built from the DFA *)
  (* The corresponding state in the NFA is final iff the state obtained in the  *)
  (* DFA is final and vice-versa                                                *)
  Lemma dfa_to_nfa_sound_aux : forall l, forall s,
  dfa.is_final m (dfa.run' (dfa.next m) l (s)) =
  nfa.verify_final_state' (dfa.dfa_to_nfa m) (nfa.run' (dfa.dfa_to_nfa m) l [s]).
  Proof. 
  induction l.
  - simpl. intros s. destruct dfa.is_final; auto.
  - intros. simpl. rewrite IHl. reflexivity. Qed.

  (* We can conclude that both the DFA and the NFA obtained from the DFA has the *)
  (* same behaviour                                                              *)

  Lemma dfa_to_nfa_sound : forall l,
    dfa.run m l = nfa.run (dfa.dfa_to_nfa m) l.
   Proof. 
   unfold nfa.run. unfold dfa.run.
   induction l.  
   -  simpl. destruct dfa.is_final. reflexivity. reflexivity. 
   - rewrite dfa_to_nfa_sound_aux. reflexivity. Qed. 

  Lemma minimal_check_soundness : 
    dfa.is_minimal (m) = true <-> dfa.has_equivalent_states m (dfa.states m) (dfa.states
    m) (dfa.alphabet m) = false.
  Proof.
  split.
  - intros. unfold dfa.is_minimal in H1. 
    destruct dfa.has_equivalent_states. 
    simpl in H1. inversion H1. reflexivity.
  - intros. unfold dfa.is_minimal. destruct dfa.has_equivalent_states.
    inversion H1.
    simpl. reflexivity.
  Qed.

  (*TODO*)
  Lemma has_equivalent_states_sound : forall s,forall l,
    dfa.has_equivalent_states m s s l = true <-> exists a: NT, 
     In a s /\ dfa.check_a_pair_states m (a) s l = true.
  Proof.
  intros.
  split.
  - intros. destruct s.
    + inversion H1.

    + unfold dfa.has_equivalent_states in H1. exists n. split. simpl;auto.
      simpl in H1. rewrite <- H1. unfold dfa.check_a_pair_states.
  Admitted.
End dfa_lemmas.

Section nfa_lemmas. 
  Variables (S A : Type).
  Variable nfa : nfa.t S A.
  Context `{EqDec S eq} `{EqDec A eq}.

  Lemma run'_companion : forall m:nfa.t S A, forall l, nfa.run m l = true \/ nfa.run m l = false.
    Proof.
    intros.
    destruct nfa.run;auto.
    Qed.

  (* The NFA returns true iff it reaches a possible final state after a run. *)
  Lemma nfa_returns_true: forall l:list A, nfa.run nfa l = true
  <-> nfa.verify_final_state' nfa (nfa.run' (nfa) l  ([(nfa.initial_state nfa)])) = true.
  Proof.
  intros.
  split.
  - intros. rewrite <- H1. unfold nfa.run. reflexivity.
  - intros. unfold nfa.run. inversion H1. reflexivity.
  Qed.

  Lemma nfa_returns_false: forall l:list A, nfa.run nfa l = false
  <-> nfa.verify_final_state' nfa (nfa.run' (nfa) l  ([(nfa.initial_state nfa)])) = false.
  Proof.
  intros.
  split.
  - intros. rewrite <- H1. reflexivity.
  - intros. unfold nfa.run. inversion H1. reflexivity.
  Qed.

  (* We have that the DFA built from a NFA is correct *)
  Lemma nfa_to_dfa: forall l, nfa.run nfa l = dfa.run (nfa_to_dfa.build_dfa_from_nfa nfa) l.
  Proof.
  reflexivity.
  Qed.

End nfa_lemmas.

Section nfa_e_lemmas.
  Variables (ST A : Type).
  Variable nfa_e : nfa_epsilon.t ST A.
  Context `{EqDec ST eq} `{EqDec A eq}.

  (* Lemma next_state_w_e_sound: forall l: set (nfa_epsilon_transitions.ep_trans ST A), 
  forall t:ST, forall a: A, forall x
  set_mem equiv_dec (t) (nfa_epsilon.next_state_w_e l)) = true <-> *)

  Lemma next_state_w_e_sound: forall s: set (nfa_epsilon_transitions.ep_trans ST A), nfa_epsilon.next_state_w_e s = [] \/ 
  exists a: ST, In (a) (nfa_epsilon.next_state_w_e s).
  intros. destruct s.
  - left;reflexivity.
  - right. simpl. Admitted.

  Lemma ep_trans_is_epsilon_sound:forall s:nfa_epsilon_transitions.ep_trans ST A,
  nfa_epsilon.ep_trans_is_epsilon s = true <-> (exists t:ST, s = Epsilon  t).
  Proof.
  intros.
  split.
  - intros. destruct s. exists s. reflexivity.
  simpl. inversion H1.
  - intros. destruct H1. rewrite H1. reflexivity.
  Qed.

  (* Given a number of steps taken in the search (the depth of the search) *)
  (* the function bounded_search will always end, returning either true or *)
  (* false                                                                 *)
  Lemma bounded_search_nfa_e_sound : forall n:nat, forall i j : ST,
    nfa_epsilon.bounded_search nfa_e n i j = true \/ 
    nfa_epsilon.bounded_search nfa_e n i j = false.
  Proof.
  intros. destruct nfa_epsilon.bounded_search.
  - left;reflexivity.
  - right;reflexivity.
  Qed.


