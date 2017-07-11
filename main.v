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

  (*abaixo, deixamos para os construtores Single e Empty o escopo do argumento aberto para Type.*)
  (*afim de não ter que se preocupar com o Tipo que o construtor vai receber: deixa que o Coq infere *)
  (*como no exemplo : https://coq.inria.fr/distrib/current/refman/Reference-Manual004.html#hevea_command59*)
  (*dessa forma, não é necessário explicitar o tipo que tais construtores recebem toda vez que forem invocados*)
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
    (*graças à isso, é possível usar a noção de igualdade aqui dentro para variáveis do *)
    (*tipo T e NT *)

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
  (*essa função pega a parte direita de uma regra de derivação e vê se possui derivações à*)
  (*partir dela                                                                    *)
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
    existsb (fun o => match o with
                   | None => true
                   | Some nt => getRHS nt rules |> existsb rhs.isEmpty
                   end)
            l.
  (* Top-level parse function. Calls [parse'] with the initial symbol and checks
     to see whether the resulting state is accepting. *)
  Definition parse (grammar : reg_grammar.g) (l : list T): bool :=
    [Some (start_symbol grammar)] |> parse' (rules grammar) l |> is_final (rules grammar).

  End reg_grammar.
End reg_grammar.

Module dfa.
  Section dfa.
    Variable (S A : Type).
    Record t := DFA {
      initial_state : S;
      is_final : S -> bool;
      next : S -> A -> S
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
  End dfa.
End dfa.

(* We can explicitly construct a DFA corresponding to the grammar. In fact, all
   the hard work was already done in our grammar parser. *)
Module powerset_construction.
  Section powerset_construction.
    Variable T NT : Type.
    Context `{EqDec T eq} `{EqDec NT eq}.
    (*a valid regular grammar shall follow the rules of g, where T and NT are, respectively, *)
    (* the terminal and nonterminal symbols.                                                 *)
    Variable g : reg_grammar.g T NT.
    Definition state : Type := list (option NT).
    (* The automata's inital state is the same as the start symbol of the grammar.           *)
    Definition init : state := [Some (reg_grammar.start_symbol g)].
    (*The same goes to a final state in the automata. *)
    Definition is_final (s : state) : bool :=
      reg_grammar.is_final (reg_grammar.rules g) s.
    Definition next (s : state) (t : T) : state :=
      reg_grammar.step (reg_grammar.rules g) t (filterMap id s).

    Definition dfa := dfa.DFA init is_final next.

    (* Because of the way we carefully set this up, simulation holds
       *definitionally*, which is pretty cool. *)
    (*Then, we can conclude that both the parser and the automata does the same thing. *)
    Theorem simulation : forall l, dfa.run dfa l = reg_grammar.parse g l.
    Proof.
      reflexivity.
    Qed.

  End powerset_construction.
End powerset_construction.

(* A simple example language over the alphabet {a,b} corresponding to the
   regular expression
       a*b*
   (Note that the original email contained an incorrect grammar for this
   language. A correct one is given below.) *)

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

  Definition a_b_dfa : dfa.t _ _ :=
    {| dfa.initial_state := Some non_terminal.A;
       dfa.is_final := a_b_is_final;
       dfa.next := a_b_next
    |}.

  (* Examples running the DFA. *)
  Eval compute in dfa.run a_b_dfa [].
  Eval compute in dfa.run a_b_dfa [terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.b;terminal.a].

  (* Automatically construct a DFA using the powerset construction. *)
  Check a_b_grammar.
  Definition a_b_dfa' := powerset_construction.dfa a_b_grammar.
  Check a_b_dfa'.

  (* Examples running the second DFA. *)
  Eval compute in dfa.run a_b_dfa' [].
  Eval compute in dfa.run a_b_dfa' [terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.b; terminal.b].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.b;terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.b;terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.b; terminal.a].



  Definition a_b_loose_rules: list(list(non_terminal.t + terminal.t)) :=
    [[inl non_terminal.A; inr terminal.a; inl non_terminal.A];
     [inl non_terminal.A; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.A];
     [inl non_terminal.B; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.B]].

  Inductive non_terminal1 := S| S1 | S2 | S3 |S4.
  Inductive terminal1 := a | b |c | d.

  Definition grammar_rules: list (non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S, Continue a S1);
     (S1, Continue b S2);
     (S2, Continue c S3);
     (S3, Single d);(S3, Continue d S3);(S3, Single a)].


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


  Definition grammar_example := reg_grammar.build_grammar S grammar_rules.
  Definition automata_example := powerset_construction.dfa grammar_example.

  Eval compute in dfa.run automata_example [a;b;c;d].
  Eval compute in dfa.run automata_example [a;b;c].
  Eval compute in dfa.run automata_example [a;b;b;c;d].
  


  Definition rules_example_2:list(non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S,Continue a S1);(S,Continue b S2);(S1, Continue a S1);(S1,Continue c S3);(S2,Continue b S2);
  (S2, Continue d S4);(S3, Single c);(S3,Continue c S);
  (S4, Single d);(S4,Continue d S)].

  Eval compute in reg_grammar.getRHS S rules_example_2.
  Definition grammar_example_2 := reg_grammar.build_grammar S rules_example_2.
  Definition automata_example_2 := powerset_construction.dfa grammar_example_2.

  Eval compute in dfa.run automata_example_2 [b;d;d]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [b;d;d;c]. (*returns false*)
  Eval compute in dfa.run automata_example_2 [a;c;c]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [a;c;c;a]. (*returns false*)
  Eval compute in dfa.run automata_example_2 [b;d;d;a;c;c]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [b;b;b;b;b;b;b;d;d;a;c;c]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [b;d;d;a;c;c;b;d;d;b;d;d]. (*returns true*)
  Eval compute in dfa.run automata_example_2 [a;a;a;a;a;a;a;c;c]. (*returns true *)
  Eval compute in dfa.run automata_example_2 [b;a;d;a;c;c].  (*returns false*)

End examples.
