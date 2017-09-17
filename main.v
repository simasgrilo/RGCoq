Require Import List.
Import ListNotations.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Bool.

(*leave the type inference at maximum level in Coq, not being necessary to declare the type*)
(*of parameters of functions, as seen in https://coq.inria.fr/cocorico/CoqNewbieQuestions *)

Set Implicit Arguments.
(*Coq will try to infer at maximum level the arguments' types *)
Set Maximal Implicit Insertion.

(* First, some library helper functions and notations. *)
(* https://coq.inria.fr/distrib/current/refman/Reference-Manual023.html#hevea_command261/ *)
(*Instance: in this case, the Instance keyword creates a instance of the EqDec class,i.e, *)
(*creates an instance of an equality relation for the type option A (A: Type)             *)
(*Program : gives a way to write programs as if they were written in a regular functional *)
(*programming language, such as Haskell, using the Coq proof apparatus to generate a sound*)
(*program from the specification given.                                                   *)

(*eq: equality relation, it is an inductive proposition that gives the notion of equality *)
(*between 2 elements of the same type. It is in Coq.Init.Logic.                           *)

Obligation Tactic := unfold complement, equiv ; program_simpl.
(*needed tactic, so the obligations generated by Program to deal with the proof of the sound*)
(*ness is solved automatically by the Program keyword.                                     *)

Program Instance option_eqdec A `(EqDec A eq) : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.

Definition filterMap {A B} (f : A -> option B) : list A -> list B :=
  fix rec (l : list A) : list B :=
    match l with
    | [] => []
    | x :: l => match f x with
               | None => rec l
               | Some y => y :: rec l
               end
    end.

Notation "x |> f" := (f x) (left associativity, at level 69, only parsing).

(* A type representing valid right-hand sides of left-regular grammar rules.
   The original email used a much looser representation of rules, which did not
   separate the LHS from the RHS, and which did not enforce regularity. By
   restricting the representation, we make it easier to write a parser. *)
Module rhs.
  (*RHS: Right Hand Side: How right linear regular grammar should behave:its rules should*)
  (*be A -> a, A -> a B or A -> e, where A and B denotes nonterminal symbols and a denotes.*)
  (* a terminal symbol.                                                                   *)

  Inductive t T NT :=
  | Empty : t T NT
  | Single : T -> t T NT
  | Continue : T -> NT -> t T NT.
  (* Coq will infer the type of the arguments of the constructors of the RHS type, as seen in *)
  (*https://coq.inria.fr/distrib/current/refman/Reference-Manual004.html#hevea_command59      *)
  (* so we don't have to worry about expliciting the types every now and then. *)

  Arguments Empty {_} {_}.
  Arguments Single {_} {_} _.
  Arguments Continue {_} {_} _ _.
  (*the function below checks whether a rule is empty or not, given the terminal and nonterminal    *)
  (*and the RHS of a rule, returns true if this RHS is Empty, otherwise, returns false        *)
  Definition isEmpty (T NT : Type) (rhs : rhs.t T NT) : bool :=
    match rhs with
    | Empty => true
    | _ => false
    end.

  Module exports.
    Notation Empty := Empty.
    Notation Single := Single.
    Notation Continue := Continue.
  End exports.
End rhs.
Import rhs.exports.

Module reg_grammar.
  Section reg_grammar.
    Variable T NT : Type.
    Context  `{EqDec T eq} `{EqDec NT eq}.
    (*When using this, it is possible to use the notion of equality between elements of type*)
    (* T and NT                                                                             *)
  Record g : Type:= {
      start_symbol: NT;
      rules : list(NT * rhs.t T NT)
  }.

  Definition build_grammar (nt: NT) rules: g :={|
      start_symbol := nt;
      rules := rules |}.

  (* Next, we're going to write a function [parse] that decides whether a string
     is in the language represented by the grammar. The parser keeps track of
     the set of nonterminal symbols it's currently in, with the additonal
     special symbol None representing "end of string when the last rule applied
     had RHS [Single]". *)

  (* It may help to scroll down to the function [parse] first, and read
     backwards up to here. *)

  (* Given the RHS of a rule and a terminal, decides whether the RHS can be used. *)
  (* In others words, given a RHS of a rule and a terminal symbol, it checks how, if it *)
  (* can be used, the RHS will be used.                                            *)
  Definition step_rhs (t : T) (rhs : rhs.t T NT) : list (option NT) :=
    match rhs with
    | Empty => []
    | Single t' => if t == t' then [None] else []
    | Continue t' nt => if t == t' then [Some nt] else []
    end.

  (* Finds all the productions for a given nonterminal. *)
  (*Note: this list will never be empty, if the nt symbol belongs to the grammar   *)
  Definition getRHS `{EqDec NT eq}
           (nt : NT) : list (NT * rhs.t T NT) ->
                       list (rhs.t T NT) :=
    filterMap (fun rule => let '(nt', rhs) := rule in
                        if nt == nt' then Some rhs else None).


  (* Given a nonterminal [nt], applies all possible rules,applying step_rhs on the             *)
  (* list of nonterminal symbols obtained by applying getRHS nt with the rules of the grammar  *)
  Definition step_nt (rules : list(NT * rhs.t T NT)) (t : T) (nt : NT) : list (option NT) :=
    rules |> getRHS nt  |> flat_map (step_rhs t).


  (* Given a *list* of nonterminals, takes all possible next steps. *)
  (*map: returns 1 value for each application of the function for each element of the list. *)
  (*flat_map: returns 0 or more values for each application of the function in each list element.*)
  (*if applyable *)
  Definition step (rules : list(NT * rhs.t T NT)) (t : T) (acc : list NT) : list (option NT) :=
  acc |> flat_map (step_nt rules t) |> nodup equiv_dec.


  (* The main parser loop. Repeatedly steps the current set of states using
     terminals from the string. *)
  Definition parse' (rules : list(NT * rhs.t T NT))
           : list T -> list (option NT) -> list (option NT) :=
    fix rec l acc :=
      match l with
      | [] => acc
      | t :: l =>
    (*filtermap id : acc gets the elements of t::l. *)
        acc |> filterMap id
            |> step rules t
            |> rec l
      end.
  (* Checks to see if the current state represents an accepting state.  In this
     representataion of state, a state is accepting if it contains [None] or if
     it contains [Some nt] and there is a rule [(nt, Empty)].  *)
  Definition is_final (rules : list (NT * rhs.t T NT)) (l : list (option NT)) : bool :=
  (*existsb: boolean exists, chech whether a condition can
  be met by any of the elements in l*)
  (*This function is in Coq.Lists, where o is an element of the list l.*)
  (* Note that the order of the elements in this list does not affect the result,*)
  (* because for all elements of the list it is checked whether a state is final *)
  (*according to the rules.                                                      *)
    existsb (fun o => match o with
                   | None => true
                   | Some nt => getRHS nt rules |> existsb rhs.isEmpty
                   end)
            l.
  (* Top-level parse function. Calls [parse'] with the initial symbol and checks
     to see whether the resulting state is accepting. *)
  Definition parse (grammar : reg_grammar.g) (l : list T): bool :=
    [Some (start_symbol grammar)] |> parse' (rules grammar) l |> is_final (rules grammar).

  Definition parse_aux (grammar: reg_grammar.g) (l:list T) :=
   [Some (start_symbol grammar)] |> parse' (rules grammar) l.
(* vacation *)

  (* Get all nonterminal symbols from a grammar *)
  Fixpoint get_all_nt (rules: list (NT * rhs.t T NT)) : list NT :=
  match rules with
  | [] => []
  | a::t => [(fst a)] ++ get_all_nt t 
  end |> nodup equiv_dec.

  (* Get all terminal symbols that can be used by a given nt         *)
   Fixpoint get_all_t_nt (rules: list (NT * rhs.t T NT)) (nt:NT) : list T :=
   match rules with
   | [] => []
   | a::t => match snd a with
             |Empty => []
             |Single x => if (fst a) == nt then [x] else []
             |Continue x _ => if (fst a) == nt then [x] else []
            end
            ++ (get_all_t_nt t nt)
  end |> nodup equiv_dec.

  Definition get_t_from_rhs(rhs:rhs.t T NT): list T :=
  match rhs with
    |Empty => []
    |Single x => [x] 
    |Continue a _ => [a]
  end.


  Definition get_nt_from_rhs(rhs:rhs.t T NT): list NT :=
  match rhs with
    |Continue _ x => [x]
    | _ => []
  end.

  (* This function is a part of the minimization algorithm. In this case, it gets all possible *)
  (* terminals symbols from the grammar to check whether a given state is reachable            *)
  Definition get_all_possible_t : list(NT * rhs.t T NT) -> list T :=
  fix rec l :=
    match l with
      |[] => []
      |a::t => get_t_from_rhs (snd a) ++  rec t
    end  |> nodup equiv_dec.

   (* Get all states that can be reachable from a state *)
  Definition get_all_states (rules:list(NT * rhs.t T NT)) (nt: NT): list T -> list (option NT):=
  fix rec l := 
    match l with
      |[] => []
      | c::d => (reg_grammar.step_nt rules c nt) ++ rec d 
    end |> nodup equiv_dec.

  End reg_grammar.
End reg_grammar.

(* the type of transtion rules of NFA and DFA *)
(* Goes : transition that consumes a symbol from the automaton's alphabet *)
(* Goes_empty: epsilon transitions. TODO: NFA with epsilon transitions. *)
Module fa_rules.
  Inductive fa_transitions A S :=
  | Goes : A -> S -> fa_transitions A S.
  (* | Goes_empty : S -> fa_transitions A S. *)
  Module exports_fa.
    Notation Goes := Goes.
  (*  Notation Goes_empty := Goes_empty. *)
  End exports_fa.
End fa_rules.
Import fa_rules.exports_fa.

(* Nondeterministic finite automata *)
Module nfa.
  Section nfa.
    Variable (S A : Type).
    Context  `{EqDec S eq} `{EqDec A eq}.

    Record t := NFA {
      initial_state : S;
      is_final : S -> bool;
      next : A -> S -> list S;
      transition_rules : list(S * fa_rules.fa_transitions A (list S))
   }.

    (* run' is the function that does the verification steps of the automata, applying     *)
    (* the transition functions in the list of terminal symbols, returning a state, which  *)
    (* can be final or not.                                                                *)

    Definition step (nfa:t) (states : list S) (t:A) : list S :=
    states |> flat_map (next nfa t).

    (* Since a NFA can have multiple paths for a single run, we have to check them all. *)
    Definition run' (m: t)
           : list A -> list S -> list S :=
    fix rec l acc :=
      match l with
      | [] => acc
      | t :: l => step m acc t
               |> rec l
      end.

    (* The acceptance criteria is sliglty modified : since we can reach more than one state *)
    (* while going through a word, we have to check whether the nfa can be at (at least) one*)
    (* final state. The verify_final_state function goes though a list of possible states   *)
    (* and checks if one of them is a final state. The run function will go through a word, *)
    (* returning true iff the nfa reached a final state, otherwise it returns false.        *)

    Fixpoint verify_final_state (m:t) (states : list S) :=
    match states with
      | [] => false
      | a::t => if is_final m a then true else verify_final_state m t 
    end.

    (* We call the above function to check whether the run in the nfa returns true or false. *)
    Definition run (m : t) (l : list A) : bool :=
     verify_final_state m ((run' (m) l  ([initial_state m]))).
    Definition run2 (m :t) (l : list A) : list S :=
      nodup equiv_dec (run' (m) l  ([initial_state m])).

    (* The path function returns all the states the automata have been while consuming the *)
    (* word given to be checked whether it is recognizable by the automata or not.         *)
    Definition get_trace (m:t) : list A -> list S -> list (list S) -> list (list S):=
      fix rec l acc res :=
        match l with
        | [] => res
        | t::l => (res ++ ([step m acc t |> nodup equiv_dec])) |> rec l (step m acc t)
        end.
    Definition path (m:t) (l:list A) : list (list S) :=
      get_trace m l [initial_state m] [[initial_state m]].

  End nfa.
End nfa.

(* TODO: soundness *)
 (* From a regular grammar we can build a NFA that recgonizes the same language *)
Module grammar_to_nfa.
  Section grammar_to_nfa.

  Variables T NT: Type.
  Context `{EqDec T eq} `{EqDec NT eq}.
  Check nfa.t (option NT) T.
  Variable g : reg_grammar.g T NT.

  Definition state : Type := option NT.

  Definition init := Some (reg_grammar.start_symbol g).

  Definition final (s : state) : bool :=
    match s with
      | None => true
      | Some nt => reg_grammar.getRHS nt (reg_grammar.rules g) |> existsb rhs.isEmpty
    end.
  Definition next (t : T) (s:state) : list state :=
      reg_grammar.step (reg_grammar.rules g) t (filterMap id [s]).

  Definition rules: list(state * fa_rules.fa_transitions T (list state)) := [].

  Definition build_nfa_from_grammar := nfa.NFA (init) (final) (next) (rules).

  Lemma same_initial_state :  Some (reg_grammar.start_symbol g) = 
  nfa.initial_state (build_nfa_from_grammar).
  Proof. reflexivity. Qed.

  Definition nfa_to_grammar_aux : forall l, forall s,
  reg_grammar.is_final (reg_grammar.rules g)
    (reg_grammar.parse' (reg_grammar.rules g) l
      s) =
  nfa.verify_final_state build_nfa_from_grammar
    (nfa.run' build_nfa_from_grammar l
      s).
  Proof.
  intros l s.
  generalize dependent s.
  induction l. 
  - intros s. unfold reg_grammar.is_final. unfold nfa.verify_final_state. simpl. Admitted.

  Definition nfa_to_grammar_sound : forall l,
  reg_grammar.parse g l = nfa.run (build_nfa_from_grammar) l.
  Proof.
  unfold reg_grammar.parse. unfold nfa.run. rewrite same_initial_state.
  induction l.
  - simpl. reflexivity.
  - simpl. Admitted.

  End grammar_to_nfa.
End grammar_to_nfa.

Module dfa.
  Section dfa.
    Variables S A: Type.
    Context  `{EqDec S eq} `{EqDec A eq}.

    Record t := DFA {
      initial_state : S;
      is_final : S -> bool;
      next : S -> A -> S;
      transition_rules : list(S * fa_rules.fa_transitions A S)
    }.

    (*run' is the function that does the verification steps of the automata, applying     *)
    (*the transition functions in the list of terminal symbols, returning a state, which can*)
    (*be final or not.                                                                    *)
    (*acc is a accumulator, a variable that stores the result of the processing upon each ele-*)
    (* ment of the list of terminal symbols. In this case, it receives the result of applying a*)
    (*transition function for each of the elements of the list (if possible). using the fold_left iterator*)

    Definition run' (step: S -> A -> S) (l : list A) (acc : S) : S :=
      fold_left step l acc.
    Definition run (m : t) (l : list A) : bool :=
      is_final m (run' (next m) l (initial_state m)).
    Definition run2 (m :t) (l : list A) : S :=
      run' (next m) l  (initial_state m).

    Definition get_trace (m:t) : list A ->  S -> list S -> list S:=
      fix rec l s res :=
        match l with
        | [] => res
        | t::l => (res ++ [next m s t] ) |> rec l (next m s t)
        end.
    Definition path (m:t) (l:list A) : list S :=
      get_trace m l (initial_state m) [initial_state m].

   
  (* Since DFAs are NFAs with a "restriction" in the set of rules, we can easily create a *)
  (* NFA from a DFA in a way that does not change the original automata's language: given *)
  (* a list of rules, we just create another rule from the start symbol that goes to ano- *)
  (* ther nonterminal symbol which is not final (so it doesn't change the language of the *)
  (* automata                                                                             *)
  (* TODO: DEPRECATED *)
  Fixpoint dfa_rules_to_nfa_rules (rules : list(S * fa_rules.fa_transitions A S)) : list(S * fa_rules.fa_transitions A (list S)) :=                                             
  match rules with
   | [] => []
   | a::t => match (snd a) with
             | Goes t c => [(fst a, Goes t [c])]
             end
             ++ dfa_rules_to_nfa_rules t
  end.

  (* Converting a DFA to a regular grammar. *)
  (* This function converts the list of transition rules to a list of production rules of a *)
  (* grammar. All rules of the automata are converted to rules of the kind A -> aB, and when*)
  (* A is a final state in the automata, a rule A -> epsilon is added too.                  *)
  (* TODO: soundness of this thing? : construction algorithm 4! DONE*)
  Fixpoint dfa_rules_to_regular_grammar(m:t) (transitions: list(S * fa_rules.fa_transitions A S)) 
  : list (S * rhs.t A S) :=
  match transitions with
  | [] => []
  | a::t => match (snd a) with
           | Goes x y => if (is_final m y) then
                         [((fst a), Continue x y)] ++ [(y, Empty)]
                         else [((fst a), Continue x y)]
           end ++ dfa_rules_to_regular_grammar m t
  end.

  Definition recgonizes (dfa: dfa.t) (l: list A) :=
  dfa.run dfa l = true.

  Definition dfa_to_regular_grammar (m:t): reg_grammar.g A S :=
    reg_grammar.build_grammar (initial_state m) (dfa_rules_to_regular_grammar m (transition_rules m)).

  (* We can build an NFA from a DFA. *)
  Variable m : t.

  (* The first step is to rewrite the next function of the DFA as the same way it behaves for the NFA*)
  Definition nfa_step(t:A) (s:S) :=
    [dfa.next m s t].

  Definition dfa_to_nfa := nfa.NFA (dfa.initial_state m) (dfa.is_final m)
  (nfa_step) (dfa.dfa_rules_to_nfa_rules (dfa.transition_rules m)).

  Lemma dfa_to_nfa_sound_aux : forall l, forall s,
  dfa.is_final m (dfa.run' (dfa.next m) l (s)) =
  nfa.verify_final_state (dfa.dfa_to_nfa) (nfa.run' (dfa.dfa_to_nfa) l [s]).
  Proof. 
  intros.
  generalize dependent s.
  induction l.
  - simpl. intros s.  destruct dfa.is_final;auto.
  - intros. simpl. rewrite IHl. reflexivity. Qed.

  Lemma dfa_to_nfa_sound : forall l,
    dfa.run m l = nfa.run (dfa.dfa_to_nfa) l.
   Proof. 
   unfold nfa.run. unfold dfa.run.
   induction l.  
      simpl. destruct dfa.is_final. reflexivity. reflexivity. 
   - rewrite dfa_to_nfa_sound_aux. reflexivity. Qed. 

  End dfa.
End dfa.


(* We can also explicitly construct a DFA corresponding to the grammar. In fact, all
   the hard work was already done in our grammar parser. *)
Module powerset_construction.
  Section powerset_construction.
    (* The soundness of the algorithm hereby implemented is *)
    (* is seen in construction algorithm 1 *)
    Variable T NT : Type.
    Context `{EqDec T eq} `{EqDec NT eq}.
    (*a valid regular grammar shall follow the rules of g, where T and NT are, respectively, *)
    (* the terminal and nonterminal symbols.                                                 *)
    Variable g : reg_grammar.g T NT.
    Definition state : Type := list (option NT).
    (* The automata's inital state is the same as the start symbol of the grammar.           *)

    Definition init : state := [Some (reg_grammar.start_symbol g)].
    (*The same goes to a final state in the automaton. *)
    Definition is_final (s : state) : bool :=
      reg_grammar.is_final (reg_grammar.rules g) s.
    Definition next (s : state) (t : T) : state :=
      reg_grammar.step (reg_grammar.rules g) t (filterMap id s).

    Definition alphabet := reg_grammar.get_all_possible_t (reg_grammar.rules g).

    Definition get_states_from_state (s:state) : list T -> list state :=
    fix rec l :=
    match l with
    | [] => []
    | a::t => if (powerset_construction.next s a <> [])
              then [powerset_construction.next s a] ++ rec t
              else rec t
    end.
    (* bugged *)
    Fixpoint list_state (rules: list(NT * rhs.t T NT)) : list state :=
      match rules  with
      | [] => []
      | a::t => [[Some (fst a)]] ++ (get_states_from_state ([Some (fst a)]) (alphabet)) 
                ++ list_state t 
      end |> nodup equiv_dec. 

    Definition build_dfa_rule (s: state) (t: T) :=
    [(s, Goes t (powerset_construction.next (s) (t)))].

    Fixpoint build_rules_from_state (s:state) (l : list T) :=
    match l with
    | [] => []
    | a::r => if (powerset_construction.next (s) (a) == [])
              then build_rules_from_state s r
              else build_dfa_rule s a ++ build_rules_from_state s r
    end.


    Fixpoint get_all_rules (ls: list state) :=
    match ls with
    | [] => []
    | a::r => build_rules_from_state (a) (reg_grammar.get_all_possible_t (reg_grammar.rules g)) ++
      get_all_rules (r)
    end.

    (*Get all terminals from a given nonterminal *)
    Fixpoint get_all_t2 (rules: list (NT * rhs.t T NT)) (nt:NT) : list T :=
    match rules with
    | [] => []
    | a::t => match snd a with
              |Empty => []
              |Single x => if (fst a) == nt then [x] else []
              |Continue x _ => if (fst a) == nt then [x] else []
             end
            ++ (get_all_t2 t nt)
    end.

    (* Count the occorrences of a terminal in a list *)
    Fixpoint count (t:list T) (l: list T) : nat :=
      match l with
      | [] => 0
      | a::r => if ([a]==t) then 1 + count t r else count t r
    end.

    Definition build_dfa := dfa.DFA (init) (is_final) (next)
   (get_all_rules (list_state (reg_grammar.rules g))).

  Check build_dfa.

  End powerset_construction.
End powerset_construction.

Module examples.
  Module non_terminal.
    Inductive t:Type :=
      A | B.

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

  Definition a_b_rules: list(non_terminal.t * rhs.t terminal.t non_terminal.t):=
    [(non_terminal.A, Continue terminal.a non_terminal.A);
     (non_terminal.A, Continue terminal.b non_terminal.B);
     (non_terminal.A, Empty);
     (non_terminal.B, Continue terminal.b non_terminal.B);
     (non_terminal.B, Empty)].

  Definition a_b_grammar : reg_grammar.g terminal.t non_terminal.t :=
    {| reg_grammar.start_symbol := non_terminal.A;
       reg_grammar.rules := a_b_rules |}.

  (* A few examples. *)
  Eval compute in reg_grammar.parse a_b_grammar [].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.a].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.a].

  (*An NFA built from the grammar given above *)

  Definition nfa_from_a_b_grammar := grammar_to_nfa.build_nfa_from_grammar a_b_grammar.
  Eval compute in nfa.run nfa_from_a_b_grammar [].
  Eval compute in nfa.run nfa_from_a_b_grammar [terminal.a; terminal.a;terminal.b; terminal.a].
  Eval compute in nfa.run nfa_from_a_b_grammar [terminal.a; terminal.a].

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

  Definition a_b_transition_rules : list (option non_terminal.t * fa_rules.fa_transitions terminal.t (option non_terminal.t)) :=
  [(Some non_terminal.A, Goes terminal.a (Some non_terminal.A));
     (Some non_terminal.A, Goes terminal.b (Some non_terminal.B));
     (Some non_terminal.B, Goes terminal.b (Some non_terminal.B))].

  Definition a_b_dfa : dfa.t _ _  :=
    {| dfa.initial_state := Some non_terminal.A;
       dfa.is_final := a_b_is_final;
       dfa.next := a_b_next;
       dfa.transition_rules := a_b_transition_rules |}.


  (* Examples running the DFA. *)
  Eval compute in dfa.run a_b_dfa [].
  Eval compute in dfa.run a_b_dfa [terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.b;terminal.a].
  Eval compute in dfa.path a_b_dfa [terminal.b;terminal.b;terminal.a;terminal.a].

  (* Automatically construct a DFA using the powerset construction. *)
  Check a_b_grammar.
  Definition a_b_dfa' := powerset_construction.build_dfa a_b_grammar.
  Check a_b_dfa'.

  (* Examples running the second DFA. *)
  Eval compute in dfa.run a_b_dfa' [].
  Eval compute in dfa.run a_b_dfa' [terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.b; terminal.b].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.b].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.b;terminal.b].
  Eval compute in dfa.run a_b_dfa' [terminal.b; terminal.a].

  (*We can build a NFA from the DFA given above :*)

  Definition nfa_from_dfa_a_b := dfa.dfa_to_nfa a_b_dfa.

  Check dfa.dfa_to_nfa.
  Check nfa_from_dfa_a_b.
  Check a_b_dfa'.

  Eval compute in nfa.run nfa_from_dfa_a_b [].
  Eval compute in nfa.run nfa_from_dfa_a_b [terminal.a;terminal.a;terminal.b;terminal.a].
  Eval compute in nfa.run nfa_from_dfa_a_b [terminal.a; terminal.a].
  Eval compute in nfa.run nfa_from_dfa_a_b [terminal.b; terminal.b].
  Eval compute in nfa.run nfa_from_dfa_a_b [terminal.a; terminal.b].
  Eval compute in nfa.run nfa_from_dfa_a_b [terminal.a; terminal.b;terminal.b].
  Eval compute in nfa.run nfa_from_dfa_a_b [terminal.b; terminal.a].

  (*and we have that they run as the same formalism: *)
  Lemma nfa_from_dfa_a_b_good : forall l, dfa.run a_b_dfa l = nfa.run nfa_from_dfa_a_b l.
  Proof.
  apply dfa.dfa_to_nfa_sound.
  Qed.

  (* We can also build a grammar from the automaton given above: *)

  Definition a_b_grammar2 := dfa.dfa_to_regular_grammar a_b_dfa'.

  Eval compute in reg_grammar.parse a_b_grammar2 [terminal.a;terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar2 [].
  Eval compute in reg_grammar.parse a_b_grammar2 [terminal.b;terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar2 [terminal.a;terminal.b;terminal.b;terminal.a].

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

   Eval compute in reg_grammar.get_all_possible_t grammar_rules.

  Definition grammar_example := reg_grammar.build_grammar S grammar_rules.
  Definition automata_example := powerset_construction.build_dfa grammar_example.
  Eval compute in dfa.transition_rules automata_example.

  Eval compute in dfa.run automata_example [a;b;c;d].
  Lemma tree : dfa.recgonizes automata_example [a;b;c;d].
  Proof. unfold dfa.recgonizes. reflexivity. Qed. 

  Eval compute in dfa.run automata_example [a;b;c].
  Eval compute in dfa.run automata_example [a;b;b;c;d].
  Eval compute in dfa.run automata_example [].

  Definition rules_example_2 : list(non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S,Continue a S1);(S, Single a);(S,Continue b S2);(S1, Continue a S1);(S1,Continue c S3);(S2,Continue b S2);
  (S2, Continue d S4);(S3, Single c);(S3,Continue c S);
  (S4, Single d);(S4,Continue d S)].

  Eval compute in reg_grammar.getRHS S rules_example_2.

  (* Another example of a DFA built from a grammar: *)
  Definition grammar_example_2 := reg_grammar.build_grammar S rules_example_2.
  Definition automata_example_2 := powerset_construction.build_dfa grammar_example_2.


  Eval compute in dfa.run automata_example_2 [b;d;d]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [b;d;d;c]. (*returns false*)
  Eval compute in dfa.run automata_example_2 [a;c;c]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [a;c;c;b;d;d]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [b;d;d;a;b;c;c].    (*returns false*)
  Eval compute in dfa.run automata_example_2 [b;b;b;b;b;b;b;d;d;a;c;c]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [b;d;d;a;c;c;b;d;d;b;d;d]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [a;a;a;a;a;a;a;c;c]. (*returns true *)
  Eval compute in dfa.run automata_example_2 [b;a;d;a;c;c].  (*returns false*)

  (*
  Definition grammar_rules_2 : list (non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S, Continue a S);(S, Continue a S1);(S, Continue a S2);(S2, Empty);(S1, Single b)].*)

   Definition grammar_rules2: list (non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S1, Continue b S2);(S2, Continue c S3);
     (S3, Single d);
     (S, Continue d S1);(S1, Continue d S1);(S1,Continue c S2);(S2, Continue b S3);
     (S, Continue a S1);(S3, Single a);(S1, Continue a S1)].

  Definition grammar := reg_grammar.build_grammar S grammar_rules2.

  Definition grammar_automaton := powerset_construction.build_dfa grammar.

  Eval compute in dfa.transition_rules grammar_automaton.
  Eval compute in dfa.run grammar_automaton [d;d;b;c;a].
  Eval compute in dfa.path grammar_automaton [d;d;b;c;a].
  Eval compute in dfa.run grammar_automaton [b].
  Eval compute in dfa.path grammar_automaton [b].

  (* Example : grammmar that have aa or bb as a subword *)
  Definition grammar_aa_bb_rules := [(S, Continue b S); (S, Continue a S1);
  (S1, Continue a S3);(S, Continue b S2); (S2, Continue b S3); (S3, Continue a S3);
  (S3, Continue b S3);(S3, Empty);(S, Continue a S)].

  Definition grammar_aa_bb := reg_grammar.build_grammar S grammar_aa_bb_rules.

  Eval compute in reg_grammar.parse grammar_aa_bb [a;a].
  Eval compute in reg_grammar.parse grammar_aa_bb [a;b;b].
  Eval compute in reg_grammar.parse_aux grammar_aa_bb [a;b].

  Definition automata_aa_bb := powerset_construction.build_dfa grammar_aa_bb.

  Eval compute in dfa.run automata_aa_bb  [a;b;a;a;a;b].
  Eval compute in dfa.run2 automata_aa_bb [a;b;a;a;a;b].
  Eval compute in dfa.path automata_aa_bb [a;b;a;a;a;b].
  Eval compute in dfa.path automata_aa_bb [a;b;a;a;a;b].
  Eval compute in (dfa.transition_rules automata_aa_bb).

 (* ---------------------------------------------------------------------------------- *)
 (* A hand-made NFA for the same language.                                            *)

  Definition aa_bb_next (t:terminal1) (state : non_terminal1) : list non_terminal1 :=
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

  Definition aa_bb_list_transitions := [(S, Goes a [S;S1]); (S, Goes b [S;S2]);
  (S2, Goes b [S3]); (S1, Goes a [S3]); (S3, Goes a [S3]); 
  (S3, Goes b [S3])].

  Definition aa_bb_nfa := {|
    nfa.initial_state := S;
    nfa.is_final := aa_bb_is_final;
    nfa.next := aa_bb_next;
    nfa.transition_rules := aa_bb_list_transitions |}.

  Eval compute in nfa.path aa_bb_nfa [a;a;b;a;a;a;a;a].
  Eval compute in nfa.run aa_bb_nfa [a;a;b;a].
  Eval compute in nfa.run aa_bb_nfa [b;a;b;b].
  Eval compute in nfa.path aa_bb_nfa [b;a;b;b;b;b;a].
  Eval compute in nfa.run2 aa_bb_nfa [b;a;b;b;b;b;b;b;b].
  Eval compute in nfa.path aa_bb_nfa [b;a;b;b;b;b;b;b;b].

  Definition test := [(S, Continue a S); (S, Single b)].

  Definition grammar4 := reg_grammar.build_grammar S test.

  Eval compute in reg_grammar.rules grammar4.

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
          | G,D| D,G |E, G |G ,E | G, F| F, G=> in_right
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

  Definition regras := [(A, Continue a B);(A, Continue b C); (B, Continue a D);
  (B, Continue a E); (C, Continue a E); (C, Continue a D); (D, Continue a F);
  (E, Continue b F); (F, Empty) ;(G, Continue c F)].

  Definition gramática := reg_grammar.build_grammar A regras.

  Definition automato_gramatica := powerset_construction.build_dfa gramática.

  Eval compute in dfa.transition_rules automato_gramatica.

  Eval compute in dfa.run automato_gramatica [b;a;a;c].
  Eval compute in dfa.path automato_gramatica [b;a;a;c].
  Eval compute in dfa.run2 automato_gramatica [c].

End examples.
