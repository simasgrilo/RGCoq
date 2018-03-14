Require Import main.
Import ListNotations.
Import rhs.exports.
Import nfa_epsilon_transitions.exports.

Module non_terminal.
    Inductive t:Type :=
      A | B.

    Obligation Tactic := unfold complement, equiv ; program_simpl.
    Program Instance eqdec : EqDec t eq :=
      { equiv_dec x y :=
          match x, y with
          | A, A => in_left
          | B, B => in_left
          | A, B | B, A => in_right
          end
      }.

  End non_terminal.

  Module terminal.
    Inductive t : Type :=
      a | b.

    Program Instance eqdec : EqDec t eq :=
      { equiv_dec x y :=
          match x, y with
          | a, a => in_left
          | b, b => in_left
          | a, b | b, a => in_right
          end
      }.
  End terminal.

  Definition a_b_rules: set (non_terminal.t * rhs.t terminal.t non_terminal.t):=
    [(non_terminal.A, Continue terminal.a non_terminal.A);
     (non_terminal.A, Continue terminal.b non_terminal.B);
     (non_terminal.A, Empty);
     (non_terminal.B, Continue terminal.b non_terminal.B);
     (non_terminal.B, Empty)].

  Definition a_b_grammar : reg_grammar.g terminal.t non_terminal.t :=
    {| reg_grammar.start_symbol := non_terminal.A;
       reg_grammar.rules := a_b_rules;
       reg_grammar.terminal_symbols := [terminal.a;terminal.b];
       reg_grammar.nonterminal_symbols := [non_terminal.A; non_terminal.B] |}.

  (* A few examples. *)
  Eval vm_compute in reg_grammar.parse a_b_grammar [].
  Eval vm_compute in reg_grammar.parse a_b_grammar [terminal.a].
  Eval vm_compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.a].
  Eval vm_compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.b].
  Eval vm_compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.b].
  Eval vm_compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.a].

  (*An NFA built from the grammar given above *)

  Definition nfa_from_a_b_grammar := grammar_to_nfa.build_nfa_from_grammar a_b_grammar.
  Eval vm_compute in nfa.path nfa_from_a_b_grammar [].
  Eval vm_compute in nfa.run nfa_from_a_b_grammar [terminal.a; terminal.a;terminal.b; terminal.a].
  Eval vm_compute in nfa.run nfa_from_a_b_grammar [terminal.a; terminal.a].
  Eval vm_compute in nfa.run nfa_from_a_b_grammar [terminal.a; terminal.b].
  Eval vm_compute in nfa.run nfa_from_a_b_grammar [terminal.b; terminal.a].
  Eval vm_compute in nfa.states nfa_from_a_b_grammar.
  Definition back := nfa.build_grammar_from_nfa nfa_from_a_b_grammar.
  Check back.
  Eval vm_compute in (reg_grammar.rules back).
  Eval vm_compute in reg_grammar.parse back [terminal.b; terminal.a].

  (* A hand rolled DFA for the same language. *)
  Definition a_b_next (s : option non_terminal.t) (t : terminal.t) : option non_terminal.t :=
    match s with
    | None => None
    | Some non_terminal.A =>
      match t with
      | terminal.a => Some non_terminal.A
      | terminal.b => Some non_terminal.B
      end
    | Some non_terminal.B =>
      match t with
      | terminal.a => None
      | terminal.b => Some non_terminal.B
      end
    end.

  Definition a_b_is_final (s : option non_terminal.t) : bool :=
    match s with
    | None => false
    | Some _ => true
    end.

  Definition a_b_states := [Some non_terminal.A; Some non_terminal.B].

  Definition a_b_dfa : dfa.t _ _  :=
    {| dfa.initial_state := Some non_terminal.A;
       dfa.is_final := a_b_is_final;
       dfa.next := a_b_next;
       dfa.states := a_b_states;
       dfa.alphabet := [terminal.a;terminal.b] |}.


  Extraction a_b_dfa.

  (* Examples running the DFA. *)
  Eval vm_compute in dfa.run a_b_dfa [].
  Eval vm_compute in dfa.run a_b_dfa [terminal.a].
  Eval vm_compute in dfa.run a_b_dfa [terminal.b].
  Eval vm_compute in dfa.run a_b_dfa [terminal.a; terminal.a].
  Eval vm_compute in dfa.run a_b_dfa [terminal.b; terminal.b].
  Eval vm_compute in dfa.run a_b_dfa [terminal.a; terminal.b].
  Eval vm_compute in dfa.run a_b_dfa [terminal.b; terminal.b;terminal.a].
  Eval vm_compute in dfa.path a_b_dfa [terminal.b;terminal.b;terminal.a;terminal.a].
  Definition xy := dfa.dfa_to_regular_grammar a_b_dfa.
  Eval vm_compute in reg_grammar.rules (xy).
  Eval vm_compute in reg_grammar.nonterminal_symbols xy.

  (* Automatically construct a DFA using the powerset construction. *)
  Check a_b_grammar.
  Definition a_b_dfa' := powerset_construction.build_dfa a_b_grammar.
  Eval vm_compute in dfa.states a_b_dfa'.
  Check a_b_dfa'.
  Eval vm_compute in reg_grammar.nonterminal_symbols a_b_grammar.
  Eval vm_compute in dfa.dfa_transitions_to_grammar_rules a_b_dfa'
  (dfa.states a_b_dfa') (dfa.alphabet a_b_dfa').
  Definition back_to_grammar := dfa.dfa_to_regular_grammar a_b_dfa'.
  Eval vm_compute in (reg_grammar.rules back_to_grammar).

  (* Examples running the second DFA. *)
  Eval vm_compute in dfa.run a_b_dfa' [].
  Eval vm_compute in dfa.run a_b_dfa' [terminal.a].
  Eval vm_compute in dfa.run a_b_dfa' [terminal.a; terminal.a].
  Eval vm_compute in dfa.run a_b_dfa' [terminal.b; terminal.b].
  Eval vm_compute in dfa.run a_b_dfa' [terminal.a; terminal.b].
  Eval vm_compute in dfa.run a_b_dfa' [terminal.a; terminal.b;terminal.b].
  Eval vm_compute in dfa.run a_b_dfa' [terminal.b; terminal.a].

  (*We can check if the automaton is a minimal automaton: *)
  Eval vm_compute in dfa.is_minimal a_b_dfa'.
  Eval vm_compute in dfa.states a_b_dfa'.

  (*We can build a NFA from the DFA given above :*)

  Definition nfa_from_dfa_a_b := dfa.dfa_to_nfa a_b_dfa.
  Check dfa.dfa_to_nfa.
  Check nfa_from_dfa_a_b.
  Check a_b_dfa'.

  Eval vm_compute in nfa.run nfa_from_dfa_a_b [].
  Eval vm_compute in nfa.run nfa_from_dfa_a_b [terminal.a;terminal.a;terminal.b;terminal.a].
  Eval vm_compute in nfa.run nfa_from_dfa_a_b [terminal.a; terminal.a].
  Eval vm_compute in nfa.run nfa_from_dfa_a_b [terminal.b; terminal.b].
  Eval vm_compute in nfa.run nfa_from_dfa_a_b [terminal.a; terminal.b].
  Eval vm_compute in nfa.run nfa_from_dfa_a_b [terminal.a; terminal.b;terminal.b].
  Eval vm_compute in nfa.run nfa_from_dfa_a_b [terminal.b; terminal.a].

  (* And from the grammar: *)
  Definition nfa_from_grammar_ab := grammar_to_nfa.build_nfa_from_grammar a_b_grammar.
  Eval vm_compute in nfa.run nfa_from_grammar_ab [].
  Eval vm_compute in nfa.run nfa_from_grammar_ab [terminal.a;terminal.a;terminal.b;terminal.a].
  Eval vm_compute in nfa.run nfa_from_grammar_ab [terminal.a; terminal.a].
  Eval vm_compute in nfa.run nfa_from_grammar_ab [terminal.b; terminal.b].
  Eval vm_compute in nfa.run nfa_from_grammar_ab [terminal.a; terminal.b].
  Eval vm_compute in nfa.run nfa_from_grammar_ab [terminal.a; terminal.b;terminal.b].
  Eval vm_compute in nfa.run nfa_from_grammar_ab [terminal.b; terminal.a].
  Check nfa.next (nfa_from_grammar_ab).

  (* We can also build a grammar from the automaton given above: *)
  Definition a_b_grammar2 := dfa.dfa_to_regular_grammar a_b_dfa.
  Eval vm_compute in dfa.states a_b_dfa'.
  Eval vm_compute in dfa.alphabet a_b_dfa.
  Eval vm_compute in reg_grammar.rules a_b_grammar2.

  Eval vm_compute in reg_grammar.parse a_b_grammar2 [].
  Eval vm_compute in reg_grammar.parse a_b_grammar2 [terminal.a;terminal.b;terminal.a].
  Eval vm_compute in reg_grammar.parse a_b_grammar2 [terminal.b;terminal.b].
  Eval vm_compute in reg_grammar.parse a_b_grammar2 [terminal.a;terminal.b;terminal.b].

  Inductive non_terminal1 := S| S1 | S2 | S3 |S4.
  Inductive terminal1 := a | b |c | d.

  Definition grammar_rules: list (non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S, Continue a S1); (S, Empty);
     (S1, Continue b S2);
     (S2, Continue c S3);
     (S3, Single d);(S3, Continue a S)].

  Program Instance eqdec : EqDec non_terminal1 eq :=
      { equiv_dec x y :=
          match x, y with
          | S,S => in_left
          | S1, S1 => in_left
          | S2, S2 => in_left
          | S3, S3 => in_left
          | S4, S4 => in_left
          | S, S1|S1,S| S, S2 | S2, S | S, S3 | S3, S | S1, S2 | S2, S1 | S1, S3 | S3, S1 
          | S2, S3 | S3, S2| S4, S | S4, S1 | S4, S2 | S4, S3| S,S4 |S1, S4| S2, S4| S3,S4 => in_right
          end
      }.
    Program Instance eqdec2 : EqDec terminal1 eq :=
      { equiv_dec x y :=
          match x, y with
          | a,a => in_left
          | b, b => in_left
          | c, c => in_left
          | d, d => in_left
          | a, b| b,a| a, c | c, a | a, d | d, a | b, c | c, b | b, d | d, b 
          | c, d | d, c => in_right
          end
      }.

  Definition grammar_example := reg_grammar.build_grammar S grammar_rules
     [a;b;c;d;a;b;c;c;c;d] [S;S1;S2;S3;S4].
  Eval vm_compute in reg_grammar.terminal_symbols grammar_example.
  Definition automata_example := powerset_construction.build_dfa grammar_example.
  Eval vm_compute in (dfa.states automata_example).
  Eval vm_compute in powerset_construction.power_states grammar_example.

  Eval vm_compute in dfa.path automata_example [].
  Eval vm_compute in dfa.run automata_example [a;b;c;d].
  Eval vm_compute in dfa.run automata_example [].

  Definition rules_example_2 : set (non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S,Continue a S1);(S, Single a);(S,Continue b S2);(S1, Continue a S1);(S1,Continue c S3);(S2,Continue b S2);
  (S2, Continue d S4);(S3, Single c);(S3,Continue c S);
  (S4, Single d);(S4,Continue d S)].

  (* Another example of a DFA built from a grammar: *)
  Definition grammar_example_2 := reg_grammar.build_grammar S rules_example_2
    [b;c;a;d] [S;S1;S2;S3;S4].
  Definition automata_example_2 := powerset_construction.build_dfa grammar_example_2.
  Eval vm_compute in powerset_construction.power_states grammar_example_2.
  Eval vm_compute in dfa.states automata_example_2.

  Eval vm_compute in dfa.run automata_example_2 [b;d;d]. (*returns true*)
  Eval vm_compute in dfa.run automata_example_2 [b;d;d;c]. (*returns false*)
  Eval vm_compute in dfa.run automata_example_2 [a;c;c]. (*returns true*)
  Eval vm_compute in dfa.run automata_example_2 [a;c;c;b;d;d]. (*returns true*)
  Eval vm_compute in dfa.run automata_example_2 [b;d;d;a;b;c;c].    (*returns false*)
  Eval vm_compute in dfa.run automata_example_2 [b;b;b;b;b;b;b;d;d;a;c;c]. (*returns true*)
  Eval vm_compute in dfa.run automata_example_2 [b;d;d;a;c;c;b;d;d;b;d;d]. (*returns true*)
  Eval vm_compute in dfa.run automata_example_2 [a;a;a;a;a;a;a;c;c]. (*returns true *)
  Eval vm_compute in dfa.run automata_example_2 [b;a;d;a;c;c].  (*returns false*)

  (* The above automaton is not minimal: *)
  Eval vm_compute in dfa.is_minimal automata_example_2.
  (* Then, the list of pairs of equivalent states is an empty list. *)
  Eval vm_compute in dfa.check_equivalent_states automata_example_2.

  Definition grammar_rules2: set (non_terminal1 * rhs.t terminal1 non_terminal1) :=
    [(S1, Continue b S2);(S2, Continue c S3);(S3, Single d);
     (S, Continue d S1);(S1, Continue d S1);(S1,Continue c S2);(S2, Continue b S3);
     (S, Continue a S1);(S3, Single a);(S1, Continue a S1)].

  Definition grammar := reg_grammar.build_grammar S grammar_rules2
    [a;b;c;d] [S;S1;S2;S3].

  Definition grammar_automaton := powerset_construction.build_dfa grammar.
  Eval vm_compute in dfa.run grammar_automaton [d;d;b;c;a].
  Eval vm_compute in dfa.path grammar_automaton [d;d;b;c;a].
  Eval vm_compute in dfa.run grammar_automaton [b].
  Eval vm_compute in dfa.path grammar_automaton [b].
  Eval vm_compute in dfa.states grammar_automaton.
  Eval vm_compute in dfa.is_minimal grammar_automaton.

  (* Example : grammmar that have aa or bb as a subword *)
  Definition grammar_aa_bb_rules := [(S, Continue b S); (S, Continue a S1);
  (S1, Continue a S3);(S, Continue b S2); (S2, Continue b S3); (S3, Continue a S3);
  (S3, Continue b S3);(S3, Empty);(S, Continue a S)].

  Definition grammar_aa_bb := reg_grammar.build_grammar S grammar_aa_bb_rules
    [a;b] [S;S1;S2;S3].

  Eval vm_compute in reg_grammar.parse grammar_aa_bb [a;a].
  Eval vm_compute in reg_grammar.parse grammar_aa_bb [a;b;b].
  Eval vm_compute in reg_grammar.parse grammar_aa_bb [a;b].

  Definition automata_aa_bb := powerset_construction.build_dfa grammar_aa_bb.

  Eval vm_compute in dfa.run automata_aa_bb  [a;b;a;a;a;b].
  Eval vm_compute in dfa.run2 automata_aa_bb [a;b;a;a;a;b].
  Eval vm_compute in dfa.path automata_aa_bb [a;b;a;a;a;b].


 (* ---------------------------------------------------------------------------------- *)
 (* A hand-made NFA for the same language.                                            *)

  Definition aa_bb_next (t:terminal1) (state : non_terminal1) : set non_terminal1 :=
  match state with
  | S => match t with
        | a => [S;S1]
        | b => [S;S2]
        | c => []
        | d => []
        end
  | S1 => match t with
        | a => [S3]
        | b => []
        | c => []
        | d => []
        end
  | S2 => match t with
            | a => []
            | b => [S3]
            | c => []
            | d => []
            end
  | S3 => match t with
            | a => [S3]
            | b => [S3]
            | c => []
            | d => []
            end
  | S4 => []
  end.

  Definition aa_bb_is_final (state: non_terminal1) : bool :=
  match state with 
  | S3 => true
  | _ => false
  end.

  Definition aa_bb_nfa := {|
    nfa.initial_state := S;
    nfa.is_final := aa_bb_is_final;
    nfa.next := aa_bb_next;
    nfa.states := [S;S1;S2;S3];
    nfa.alphabet := [a;b] |}.

  Eval vm_compute in powerset (nfa.states aa_bb_nfa).

  Eval vm_compute in nfa.path aa_bb_nfa [a;a;b;a;a;a;a;a].
  Eval vm_compute in nfa.run aa_bb_nfa [a;b;a].
  Eval vm_compute in nfa.run aa_bb_nfa [b;a;b;b].
  Eval vm_compute in nfa.path aa_bb_nfa [b;a;b;b;b;b;a].
  Eval vm_compute in nfa.run2 aa_bb_nfa [b;a;b;b;b;b;b;b;b].
  Eval vm_compute in nfa.path aa_bb_nfa [b;a;b;b;b;b;b;b;b].

  Eval vm_compute in nfa.get_all_related_states aa_bb_nfa S.
  (*And we can build a DFA from the NFA defined above *)

  Definition aa_bb_dfa := nfa_to_dfa.build_dfa_from_nfa aa_bb_nfa.
  (* The set of states of the DFA built from a NFA *)
  Eval vm_compute in (dfa.states aa_bb_dfa).
  Eval vm_compute in (dfa.is_minimal aa_bb_dfa).
  Eval vm_compute in dfa.path aa_bb_dfa [a;a;a;a].
  Eval vm_compute in dfa.run aa_bb_dfa [a;a;a;a;b;b].

  (*NEW we can also build a grammar from the NFA defined above *)
  Definition aa_bb_grammar := nfa.build_grammar_from_nfa aa_bb_nfa.
  Eval vm_compute in reg_grammar.rules aa_bb_grammar.
  Eval vm_compute in reg_grammar.parse aa_bb_grammar [a;a;b;a;a;a;a;a].

  Definition test := [(S, Continue a S); (S, Single b)].

  Definition grammar4 := reg_grammar.build_grammar S test [a;b] [S].

  Eval vm_compute in reg_grammar.rules grammar4.

  Inductive naoterminal := A | B | C | D | E | F | G.
  Inductive terminal := x|y.

  Program Instance exemplo : EqDec naoterminal eq :=
      { equiv_dec x y :=
          match x, y with
          | A,A => in_left
          | B,B => in_left
          | C,C=> in_left
          | D,D => in_left
          | E,E => in_left
          | F,F => in_left
          | G, G => in_left
          | A,B | B,A | A,C| C, A| A,D| D,A | A,E| E,A |A,F | F,A| B,C| C,B |B ,D
          | D,B | B,E |E,B |B,F |F,B | C,D| D,C | C,E | E,C | C,F|F,C| D,E |E,D
          | E,F |F, E | D,F | F, D | A, G | G, A | B, G| G,B |G, C | C, G
          | G,D| D,G |E, G |G ,E | G, F| F, G => in_right
          end
      }.

  Program Instance exemplo2 : EqDec terminal eq :=
    {equiv_dec x y :=
      match x, y with
      | x,x => in_left
      | y,y => in_left
      | x,y |y,x => in_right
      end
    }.

  Definition regras := [(A, Continue a A);(A, Continue a B);(A, Continue b C); (B, Continue a D);
  (B, Continue a E); (C, Continue a E); (C, Continue a D); (D, Continue a F);
  (E, Continue b F); (F, Empty) ;(G, Continue c F)].

  Definition gramática := reg_grammar.build_grammar A regras [a;b] [A;B;C;D;E;F;G].

  Definition automato_gramatica := powerset_construction.build_dfa gramática.
  
  Eval vm_compute in dfa.is_minimal automato_gramatica.
  Eval vm_compute in dfa.check_equivalent_states automato_gramatica.
  Eval vm_compute in dfa.path automato_gramatica [a].

  Eval vm_compute in dfa.run automato_gramatica [b;a;a;c].
  Eval vm_compute in dfa.path automato_gramatica [b;a;a;c].
  Eval vm_compute in dfa.run2 automato_gramatica [c].


  (* an example of an automaton that is not minimal *)
  Module e.
    Inductive states := q0 |q1 | q2 |q3 | q4.
    Inductive alphabet := a | b.

    Program Instance eqstates : EqDec states eq := 
	    {equiv_dec x y := 
		    match x, y with 
		    | q0,q0 => in_left 
		    | q1,q1 => in_left 
		    | q2,q2 => in_left 
		    | q3,q3 => in_left 
		    | q4,q4 => in_left 
		    | q0,q1 => in_right 
		    | q0,q2 => in_right 
		    | q0,q3 => in_right 
		    | q0,q4 => in_right 
		    | q1,q0 => in_right 
		    | q1,q2 => in_right 
		    | q1,q3 => in_right 
		    | q1,q4 => in_right 
		    | q2,q0 => in_right 
		    | q2,q1 => in_right 
		    | q2,q3 => in_right 
		    | q2,q4 => in_right 
		    | q3,q0 => in_right 
		    | q3,q1 => in_right 
		    | q3,q2 => in_right 
		    | q3,q4 => in_right 
		    | q4,q0 => in_right 
		    | q4,q1 => in_right 
		    | q4,q2 => in_right 
		    | q4,q3 => in_right 
		    end 
	    }.

    Program Instance eqalphabet : EqDec alphabet eq :=
      {equiv_dec x y := 
		    match x, y with 
        | a,a | b,b => in_left
        | a,b | b,a => in_right
        end
      }.
  End e.

  Definition example_next (s: option e.states) (a: e.alphabet) :=
    match s with
      | None => None
      |Some e.q0 => match a with
               |e.a => Some e.q1
               |e.b => None
               end
      |Some e.q1 => match a with
             |e.a => Some e.q3
             |e.b => Some e.q2
              end
      |Some e.q2 => match a with
             |e.a => Some e.q4
             |e.b => Some e.q2
             end
      |Some e.q3 => match a with
             |e.a => Some e.q3
             |e.b => Some e.q2
              end
      |Some e.q4 => match a with
             |e.a => Some e.q3
             |e.b => Some e.q2
              end
    end.

  Definition example_is_final (s: option e.states) :=
    match s with
      | Some e.q4 | Some e.q3 => true
      | None | Some _=> false
    end.

  Definition nonminimal_automaton :=
    {| dfa.initial_state := Some e.q0;
       dfa.is_final := example_is_final;
       dfa.next := example_next;
       dfa.states := [Some e.q0;Some e.q1;Some e.q2;Some e.q3;Some e.q4];
       dfa.alphabet := [e.b;e.a] |}.

  Eval vm_compute in dfa.run nonminimal_automaton [e.a;e.b;e.a].
  Eval vm_compute in dfa.is_minimal nonminimal_automaton.
  Eval vm_compute in dfa.check_equivalent_states nonminimal_automaton.

(* Examples with NFA with epsilon transitions:                        *)
Module nfa_e_test.
Inductive test := a | b | c.
 Inductive test2 := q0 | q1 | q2.

  
  Program Instance eqdec : EqDec test eq :=
      { equiv_dec x y :=
          match x, y with
          | a, a => in_left
          | b, b => in_left
          | c, c => in_left
          | a,b | b,a  | a, c | c, a | b, c | c, b => in_right
          end
      }. 

  Program Instance eqdec2 : EqDec test2 eq :=
      { equiv_dec x y :=
          match x, y with
          | q0, q0 => in_left
          | q1, q1 => in_left
          | q2, q2 => in_left
          | q0, q1 | q1, q0  | q0, q2 | q2, q0 | q1, q2| q2, q1 => in_right
          end
      }. 

  Definition next_test (state: test2): set (nfa_epsilon_transitions.ep_trans test2 test) :=
  match state with
  | q0 => [Epsilon q1;Goes a q0]
  | q1 => [Goes b q1; Epsilon q2]
  (*| q2 => [Goes c q2]*)
  | q2 => [Goes c q2;Epsilon q0] 
  end.

  Definition is_f (s:test2) :=
  match s with
    | q2 => true
    | _ => false
  end.

  Definition nfa_e := {|
  nfa_epsilon.initial_state := q0;
  nfa_epsilon.is_final := is_f;
  nfa_epsilon.next := next_test;
  nfa_epsilon.states := [q0;q1;q2];
  nfa_epsilon.alphabet := [a;b;c] |}.

  Eval vm_compute in nfa_epsilon.epsilon_clos nfa_e q0. 
  Eval vm_compute in nfa_epsilon.epsilon_clos nfa_e q1.
  Eval vm_compute in nfa_epsilon.next_nfa nfa_e.
  
  (*We can convert the above NFA with epsilon transitions to one with no *)
  (* epsilon transitions                                                 *)
  Definition cool_nfa_e := nfa_epsilon.nfa_e_to_nfa nfa_e.
  Check cool_nfa_e.
  Eval vm_compute in nfa.run cool_nfa_e [a;a;a;b;c].
  Eval vm_compute in nfa.run cool_nfa_e [c].
  Eval vm_compute in nfa.get_all_related_states cool_nfa_e (nfa.initial_state cool_nfa_e).
  (* Another example:                                                    *)
  Definition next2 (state: test2): set (nfa_epsilon_transitions.ep_trans test2 test) :=
  match state with
  | q0 => [Epsilon q1;Epsilon q2]
  | q1 => [Goes b q1;Epsilon q0]
  | q2 => [Goes c q2]
  end.

  Definition is_final2 (s:test2) :=
    false.
  
  Definition nfa_e2 := {|
  nfa_epsilon.initial_state := q0;
  nfa_epsilon.is_final := is_final2;
  nfa_epsilon.next := next2;
  nfa_epsilon.states := [q0;q1;q2];
  nfa_epsilon.alphabet := [a;b;c] |}.

  Definition another_nfa_w_e := nfa_epsilon.nfa_e_to_nfa nfa_e2.
  Eval vm_compute in nfa_epsilon.next_nfa nfa_e2.

  (*Another example *)
  Definition next3 (state: test2): set (nfa_epsilon_transitions.ep_trans test2 test) :=
  match state with
  | q0 => [Epsilon q1]
  | q1 => [Epsilon q0]
  | q2 => [Epsilon q0; Epsilon q1; Epsilon q2]
  end.
  (*NFA with only two epsilon transitions between two states *)
  Definition nfa_e3 := {|
  nfa_epsilon.initial_state := q0;
  nfa_epsilon.is_final := is_final2;
  nfa_epsilon.next := next3;
  nfa_epsilon.states := [q0;q1;q2];
  nfa_epsilon.alphabet := [a;b;c] |}.

  Eval vm_compute in nfa_epsilon.epsilon_clos nfa_e3 q1.
  Eval vm_compute in nfa_epsilon.next_nfa nfa_e3.
  Definition nfa_from_nfa_e3 := nfa_epsilon.nfa_e_to_nfa nfa_e3.
  Eval compute in nfa.run2 nfa_from_nfa_e3 [a;b;c].
End nfa_e_test.

(* Modelling of Smart Cities entities as Cyber-Physical System by means of NFA *)
Inductive cityEntities := 
road | parkingPlace1 | parkingPlace2 | parkingPlace3
| sensor1 | sensor2 | sensor3.

Inductive entitiesRelation := contains | actsOn | has.

Definition cityNFAnext (a:entitiesRelation) (s: cityEntities): set (cityEntities) :=
  match s with
  | road => match a with 
            | contains => []
            | actsOn => []
            | has => [parkingPlace1;parkingPlace2;parkingPlace3]
            end
  | parkingPlace1 => match a with 
            | contains => [sensor1]
            | actsOn => []
            | has => []
            end
  | parkingPlace2 => match a with 
            | contains => [sensor2]
            | actsOn => []
            | has => []
            end
  | parkingPlace3 => match a with 
            | contains => [sensor3]
            | actsOn => []
            | has => []
            end
  | sensor1 => match a with 
            | contains => []
            | actsOn => [parkingPlace1]
            | has => []
            end
  | sensor2 => match a with 
            | contains => []
            | actsOn => [parkingPlace2]
            | has => []
            end
  | sensor3 => match a with 
            | contains => []
            | actsOn => [parkingPlace3]
            | has => []
            end
  end.

Definition NFAfinal (s: cityEntities) : bool := true.

Program Instance stateEqdec : EqDec cityEntities eq := 
	{equiv_dec x y := 
		match x, y with 
		| road,road => in_left 
		| parkingPlace1,parkingPlace1 => in_left 
		| parkingPlace2,parkingPlace2 => in_left 
		| parkingPlace3,parkingPlace3 => in_left 
		| sensor1,sensor1 => in_left 
		| sensor2,sensor2 => in_left 
		| sensor3,sensor3 => in_left 
		| road,parkingPlace1 => in_right 
		| road,parkingPlace2 => in_right 
		| road,parkingPlace3 => in_right 
		| road,sensor1 => in_right 
		| road,sensor2 => in_right 
		| road,sensor3 => in_right 
		| parkingPlace1,road => in_right 
		| parkingPlace1,parkingPlace2 => in_right 
		| parkingPlace1,parkingPlace3 => in_right 
		| parkingPlace1,sensor1 => in_right 
		| parkingPlace1,sensor2 => in_right 
		| parkingPlace1,sensor3 => in_right 
		| parkingPlace2,road => in_right 
		| parkingPlace2,parkingPlace1 => in_right 
		| parkingPlace2,parkingPlace3 => in_right 
		| parkingPlace2,sensor1 => in_right 
		| parkingPlace2,sensor2 => in_right 
		| parkingPlace2,sensor3 => in_right 
		| parkingPlace3,road => in_right 
		| parkingPlace3,parkingPlace1 => in_right 
		| parkingPlace3,parkingPlace2 => in_right 
		| parkingPlace3,sensor1 => in_right 
		| parkingPlace3,sensor2 => in_right 
		| parkingPlace3,sensor3 => in_right 
		| sensor1,road => in_right 
		| sensor1,parkingPlace1 => in_right 
		| sensor1,parkingPlace2 => in_right 
		| sensor1,parkingPlace3 => in_right 
		| sensor1,sensor2 => in_right 
		| sensor1,sensor3 => in_right 
		| sensor2,road => in_right 
		| sensor2,parkingPlace1 => in_right 
		| sensor2,parkingPlace2 => in_right 
		| sensor2,parkingPlace3 => in_right 
		| sensor2,sensor1 => in_right 
		| sensor2,sensor3 => in_right 
		| sensor3,road => in_right 
		| sensor3,parkingPlace1 => in_right 
		| sensor3,parkingPlace2 => in_right 
		| sensor3,parkingPlace3 => in_right 
		| sensor3,sensor1 => in_right 
		| sensor3,sensor2 => in_right 
		end 
	}.
Program Instance relationEqDec : EqDec entitiesRelation eq := 
	{equiv_dec x y := 
		match x, y with 
		| contains,contains => in_left 
		| has,has => in_left 
		| actsOn,actsOn => in_left 
		| contains,has => in_right 
		| contains,actsOn => in_right 
		| has,contains => in_right 
		| has,actsOn => in_right 
		| actsOn,contains => in_right 
		| actsOn,has => in_right 
		end 
	}.
Definition nfa := {|
  nfa.initial_state := road;
  nfa.is_final := NFAfinal;
  nfa.next := cityNFAnext;
  nfa.states := [road; parkingPlace1; parkingPlace2; parkingPlace3 ;sensor1; sensor2; sensor3];
  nfa.alphabet := [contains; actsOn; has]
  |}.

Eval vm_compute in nfa.get_all_related_states nfa road.
Lemma road_has_sensor1 : In (sensor1) (nfa.get_all_related_states nfa road).
Proof. simpl;auto. Qed.

