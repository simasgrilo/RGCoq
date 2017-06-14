Require Import List.
Import ListNotations.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.


Set Implicit Arguments.
Set Maximal Implicit Insertion.

(* First, some library helper functions and notations. *)
(* https://coq.inria.fr/distrib/current/refman/Reference-Manual023.html#hevea_command261/ *)
Obligation Tactic := unfold complement, equiv ; program_simpl.
Program Instance option_eqdec A `(EqDec A eq) : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.

(*função que aplica a função, filtrando os resultados numa lista resultante da aplicação *)
(*fica na lista quem a função pôde ser aplicada *)
Definition filterMap {A B} (f : A -> option B) : list A -> list B :=
  fix rec (l : list A) : list B :=
    match l with
    | [] => []
    | x :: l => match f x with
               | None => rec l
               | Some y => y :: rec l
               end
    end.
(*função que pega uma lista de "option A" e retorna um tipo option de list A*)
(*onde a estrutura indutiva é em cima do tipo A de entrada, denotado pelo {A} *)
Fixpoint list_option_traverse {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | x :: l =>
    match x with
    | None => None
    | Some a =>
      match list_option_traverse l with
      | None => None
      | Some l => Some (a :: l)
      end
    end
  end.

Notation "x |> f" := (f x) (left associativity, at level 69, only parsing) .

(* A type representing valid right-hand sides of left-regular grammar rules.
   The original email used a much looser representation of rules, which did not
   separate the LHS from the RHS, and which did not enforce regularity. By
   restricting the representation, we make it easier to write a parser. *)
Module rhs.
  (*RHS: Right Hand Side: gramáticas regulares linearmente crescentes à direita *)
  (*como uma gramática regular deve se comportar: *)
  (* S -> a, S -> a S ou S -> e *)
  Inductive t T NT :=
  | Empty : t T NT
  | Single : T -> t T NT
  | Continue : T -> NT -> t T NT.

  (*abaixo, deixamos para os construtores Single e Empty o escopo do argumento aberto para Type.*)
  (*afim de não ter que se preocupar com o Tipo que o construtor vai receber: deixa que o Coq infere *)
  (*como no exemplo : https://coq.inria.fr/distrib/current/refman/Reference-Manual004.html#hevea_command59*)
  Arguments Empty {_} {_}.
  Arguments Single {_} {_} _.
  (*função que verifica que uma regra é vazia, dados os terminal, não terminal e a regra de derivação.*)
  Definition isEmpty (T NT : Type) (rhs : rhs.t T NT) : bool :=
    match rhs with
    | Empty => true
    | _ => false
    end.
   Lemma isEmpty_sound  :forall NT T, forall r:rhs.t T NT, isEmpty r = false \/ isEmpty r = true.
   intros.
   destruct isEmpty;auto.
   Qed.

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
    Context `{EqDec T eq} `{EqDec NT eq}.
    (*graças à isso, é possível usar a noção de igualdade aqui dentro para variáveis do *)
    (*tipo T e NT *)

  Record t : Type:= {
      start_symbol: NT;
      rules : list(NT * rhs.t T NT)
  }.

  (* Next, we're going to write a function [parse] that decides whether a string
     is in the language represented by the grammar. The parser keeps track of
     the set of nonterminal symbols it's currently in, with the additonal
     special symbol None representing "end of string when the last rule applied
     had RHS [Single]". *)

  (* It may help to scroll down to the function [parse] first, and read
     backwards up to here. *)

  (* Given the RHS of a rule and a terminal, decides whether the RHS can be used. *)
  Definition step_rhs (t : T) (rhs : rhs.t T NT) : list (option NT) :=
    match rhs with
    | Empty => []
    | Single t' => if t == t' then [None] else []
    | Continue t' nt => if t == t' then [Some nt] else []
    end.

  (* Finds all the productions for a given nonterminal. *)
  Definition getRHS T NT `{EqDec NT eq}
           (nt : NT) : list (NT * rhs.t T NT) ->
                       list (rhs.t T NT) :=
    filterMap (fun rule => let '(nt', rhs) := rule in
                        if nt == nt' then Some rhs else None).
  
  (* Given a nonterminal [nt], applies all possible rules. *)
  Definition step_nt (rules : list(NT * rhs.t T NT)) (t : T) (nt : NT) : list (option NT) :=
    rules |> getRHS nt  |> flat_map (step_rhs t).
  
  (* Given a *list* of nonterminals, takes all possible next steps. *)
  Definition step (rules : list(NT * rhs.t T NT)) (t : T) (acc : list NT) : list (option NT) :=
    acc |> flat_map (step_nt rules t)|> nodup equiv_dec.

  (* The main parser loop. Repeatedly steps the current set of states using
     terminals from the string. *)
  Definition parse' (rules : list(NT * rhs.t T NT))
           : list T -> list (option NT) -> list (option NT) :=
    fix rec l acc :=
      match l with
      | [] => acc
      | t :: l =>
        acc |> filterMap id
            |> step rules t
            |> rec l
      end.

  Lemma parse'_app_nil : forall g l acc, acc |> parse' g (l ++ []) = acc |> parse' g l \/ acc |> parse' g ([]++ l) = acc |> parse' g l.
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
      acc |> parse' g (l1 ++ l2) =
      acc |> parse' g l1 |> parse' g l2.
  Proof.
    induction l1; simpl; auto.
  Qed.

  (* Checks to see if the current state represents an accepting state.  In this
     representataion of state, a state is accepting if it contains [None] or if
     it contains [Some nt] and there is a rule [(nt, Empty)].  *)
  Definition is_final (rules : list (NT * rhs.t T NT)) (l : list (option NT)) : bool :=
  (*existsb: exists booleano *)
    existsb (fun o => match o with
                   | None => true
                   | Some nt => getRHS nt rules |> existsb rhs.isEmpty
                   end)
            l.
  Lemma is_final_sound : forall r l, is_final r l = true \/ is_final r l = false.
 Proof.
    intros r l.
    destruct is_final;auto.
  Qed.

  (* Top-level parse function. Calls [parse'] with the initial symbol and checks
     to see whether the resulting state is accepting. *)
  Definition parse (grammar : reg_grammar.t) (l : list T): bool :=
    [Some (start_symbol grammar)] |> parse' (rules grammar) l |> is_final (rules grammar).
  (*importante notar que a função parse retorna verdadeiro se a palavra de entrada *)
  (* é derivável do conjunto de regras da gramática. O que seria a corretude dessa função?*)



(*função que faz o parser em cima da lista de regras e passa para uma fórmula válida de uma*)
(*gramática regular *)
  Definition rhs_from_lose (l : list (NT + T)) : option (rhs.t T NT) :=
    match l with
    | [] => Some Empty
    | [inr t] => Some (Single t)
    | [inr t; inl A] => Some (Continue t A)
    | _ => None
    end.
(*função que lê uma lista de caracteres terminais e não terminais, assim como a nossa forma *)
(*inicial de expressar a gramática *)
  Definition rule_from_loose (l : list (NT + T)) : option (NT * rhs.t T NT) :=
    match l with
    | inl A :: rhs =>
      match rhs_from_lose rhs with
      | None => None
      | Some rhs => Some (A, rhs)
      end
    | _ => None
    end.
(*essa função faz o mesmo que a de cima, mas para a lista das listas. *)
  Definition rules_from_loose (l : list (list (NT + T))) : option (list (NT * rhs.t T NT)) :=
    l |> map rule_from_loose |> list_option_traverse.

  Definition from_loose (start : NT) (l : list (list (NT + T))) : option t :=
    match rules_from_loose l with
    | None => None
    | Some rs => Some {| start_symbol := start;
                        rules := rs |}
    end.

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
    (*função que faz os passos de verificação do autômato (aplica as funções de transição do DFA)*)
    (*ela retorna um estado S, que pode ser final ou não *)
    Definition run' (step: S -> A -> S) (l : list A) (acc : S) : S :=
      fold_left step l acc.

    Definition run (m : t) (l : list A) : bool :=
      is_final m (run' (next m) l (initial_state m)).

    (*A prova de que a função que percorre uma palavra e diz se ela pertence à linguagem *)
    (*pode ser pensada como sendo: após percorrer toda a palavra,estamos em um estado final *)
    (* da linguagem que o autômato reconhece                                         *)
    (*ou poderíamos, em função do parser da gramática, ver que o parser reconhece a mesma *)
    (*linguagem de um automato, dado que os 2 tenham as mesmas "regras" de transição   *)
    Definition run_sound : forall m:t, forall l, forall s:S, 
    run m l = true -> is_final m s = true.
    intros;destruct is_final.
    reflexivity.
    rewrite <- H.
    (*isso tá estranho *)
    
  End dfa.
End dfa.

(* We can explicitly construct a DFA corresponding to the grammar. In fact, all
   the hard work was already done in our grammar parser. *)
Module powerset_construction.
  Section powerset_construction.
    Variable T NT : Type.
    Context `{EqDec T eq} `{EqDec NT eq}.
(*uma gramática regular válida segue as regras de t, com T sendo terminal e NT não terminal. *)
    Variable g : reg_grammar.t T NT.
    Definition state : Type := list (option NT).

    Definition init : state := [Some (reg_grammar.start_symbol g)].

    Definition is_final (s : state) : bool :=
      reg_grammar.is_final (reg_grammar.rules g) s.

    Definition next (s : state) (t : T) : state :=
      reg_grammar.step (reg_grammar.rules g) t (filterMap id s).
   (*função que chama o construtor de um DFA do módulo DFA, após ter convertido as regras para*)
    (*formato de regras válidas                                                           *)
    Definition dfa := dfa.DFA init is_final next.
    Check dfa.

    (* Because of the way we carefully set this up, simulation holds
       *definitionally*, which is pretty cool. *)
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

Module a_b_example.
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

  Definition a_b_grammar : reg_grammar.t terminal.t non_terminal.t :=
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


  (* The same (corrected) grammar, represented in the loose format used in the
     original email. *)
  Definition a_b_loose_rules: list(list(non_terminal.t + terminal.t)) :=
    [[inl non_terminal.A; inr terminal.a; inl non_terminal.A];
     [inl non_terminal.A; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.A];
     [inl non_terminal.B; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.B]].

  Inductive non_terminal1 := S| S1 | S2 | S3.
  Inductive terminal1 := a | b |c | d.
  Definition loose_rules_2 : list (list(non_terminal1 + terminal1)) :=
  [[inl S;inr a;inl S1];[inl S1;inr b;inl S2];[inl S2;inr c;inl S3];[inl S3;inr d]].
  (*alternativamente, as regras externas podem ter essa representação *)
  Definition loose_rules_3: list (non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S, Continue a S1);
     (S1, Continue b S2);
     (S2, Continue c S3);
     (S3, Single d)].

  (* We can see that it gets converted to the "tight" representation given
     above. *)
  Eval compute in reg_grammar.from_loose non_terminal.A a_b_loose_rules.

  Eval compute in reg_grammar.from_loose S loose_rules_2.

  Definition new_grammar := reg_grammar.from_loose S loose_rules_2.
  Check new_grammar.
  Check a_b_grammar.

  Definition one := reg_grammar.from_loose non_terminal.A a_b_loose_rules.
  Check one.
  Check a_b_grammar.
  Check a_b_grammar.

  (* Definition dfa3 := powerset_construction.dfa grammar_for_loose_rules_3. *)
  (*Ltac: linguagem de tática da Gallina. a ideia abaixo foi do James. Isso resolve o *)
  (*problema pautado no caderno do option A *)
  Ltac grab_option x :=
    let x' := eval compute in x in
    match x' with
    | Some ?v => exact v
    end.
(*abaixo, as regras de decidibilidade para a gramática que gera apenas a palavra abcd *)
  Program Instance eqdec : EqDec non_terminal1 eq :=
      { equiv_dec x y :=
          match x, y with
          | S,S => in_left
          | S1, S1 => in_left
          | S2, S2 => in_left
          | S3, S3 => in_left
          | S, S1|S1,S| S, S2 | S2, S | S, S3 | S3, S | S1, S2 | S2, S1 | S1, S3 | S3, S1 
          | S2, S3 | S3, S2 => in_right
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


  Definition a_b_from_loose := ltac:(grab_option (reg_grammar.from_loose non_terminal.A a_b_loose_rules)).
  Definition automata_from_loose := powerset_construction.dfa a_b_from_loose.
  Definition example3 := ltac:(grab_option (new_grammar)).
  Definition automata_from_ex3 := powerset_construction.dfa example3.
  Definition automata_from_example_3 := powerset_construction.dfa a_b_from_loose.
  Check automata_from_example_3.
  Eval compute in dfa.run automata_from_ex3 [a; b;c;d].

End a_b_example.
