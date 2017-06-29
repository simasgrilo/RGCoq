Require Import List.
Import ListNotations.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import Bool.

(*deixa a inferência de tipos máxima no Coq, não sendo necessário declarar o tipo das vari *)
(*áveis em chamadas de função, por exemplo:https://coq.inria.fr/cocorico/CoqNewbieQuestions*)
Set Implicit Arguments.
(*inserção máxima de argumentos implícitos: o Coq vai tentar inferir ao máximo os tipos dos argumentos *)
Set Maximal Implicit Insertion.


(* First, some library helper functions and notations. *)
(* https://coq.inria.fr/distrib/current/refman/Reference-Manual023.html#hevea_command261/ *)
(*Instance: cria uma instância da classe EqDec (ou seja, uma instância de relação de igual- *)
(* dade para o tipo option A                                                          *)
(*Program: fornece uma forma de escrever programas de linguagens funcionais no Coq, usando o *)
(*aparato que o Coq possui para construir esse programa de forma certificada (correta *)
(*eq :relação de igualdade, uma proposição indutiva que dá a ideia de igualdade entre 2 ele- *)
(*mentos de um mesmo tipo, presente em Coq.Init.Logic                           *)
Obligation Tactic := unfold complement, equiv ; program_simpl.
(*tática usada para lidar com obligations criadas em relação a igualdade *)
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
(*fica na lista quem a função pôde ser aplicada: mapeia para depois filtrar *)
(*útil na extração do tipo dentro de option tipo. *)
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

Notation "x |> f" := (f x) (left associativity, at level 69, only parsing).

(* A type representing valid right-hand sides of left-regular grammar rules.
   The original email used a much looser representation of rules, which did not
   separate the LHS from the RHS, and which did not enforce regularity. By
   restricting the representation, we make it easier to write a parser. *)
Module rhs.
  (*RHS: Right Hand Side: gramáticas regulares linearmente crescentes à direita *)
  (*como uma gramática regular deve se comportar: *)
  (* S -> a, S -> a S ou S -> e . Esse módulo trata justamente do lado direito da seta.*)
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
  (*função que verifica que uma regra é vazia, dados os terminal, não terminal e a regra de derivação.*)
  Definition isEmpty (T NT : Type) (rhs : rhs.t T NT) : bool :=
    match rhs with
    | Empty => true
    | _ => false
    end.
   (*Lemma isEmpty_sound  :forall NT T, forall r:rhs.t T NT, isEmpty r = false \/ isEmpty r = true.
   intros.
   destruct isEmpty;auto.
   Qed.*)

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
    (*graças à isso, é possível usar a noção de igualdade aqui dentro para variáveis do *)
    (*tipo T e NT *)

  Record g : Type:= {
      start_symbol: NT;
      rules : list(NT * rhs.t T NT)
  }.

  Definition build_grammar (nt: NT) rules: g :={|
      start_symbol := nt;
      rules := rules |}.
  (*Lemma build_grammar_sound : forall nt, forall rules, build_grammar nt rules = {|
      start_symbol := nt;
      rules := rules |}.
  Proof.
  intros. unfold build_grammar. reflexivity. Qed.*)

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
  (*isso aqui realmente serve para algo? *)
  (*forall n: isso deveria ser forall ou exists na condição onde ele é usado? R: EXISTS!!!*)
  (* O lema abaixo diz que, pra qualquer terminal e o lado direito de uma regra de derivação, ou não existe uma possí- *)
  (* vel derivação,ou existe uma derivação que para no estado atual (Single) ou é possível ir para um outro estado a partir*)
  (* do lado direito dado na entrada                                                                                *)
  (*Lemma step_rhs_sound : forall t:T, forall rhs: rhs.t T NT, step_rhs t rhs = [] \/
  step_rhs t rhs = [None] \/ (exists nt, step_rhs t rhs = [Some nt]).
  Proof.
  intros t rhs.
  destruct rhs; auto.
  simpl. destruct equiv_dec. auto.
  auto.
  simpl. destruct equiv_dec eqn:I;auto. 
  right. right. exists (n). reflexivity.
  Qed. *)
 
  (* Finds all the productions for a given nonterminal. *)
  (*Note: this list will never be empty, if the nt symbol belongs to the grammar         *)
  Definition getRHS T NT `{EqDec NT eq}
           (nt : NT) : list (NT * rhs.t T NT) ->
                       list (rhs.t T NT) :=
    filterMap (fun rule => let '(nt', rhs) := rule in
                        if nt == nt' then Some rhs else None).
  (*essa função que eu não tô sabendo manipular *)
  Lemma getRHS_sound : forall nt, forall rules, getRHS nt rules = [] \/
  (exists rule:rhs.t T NT,In (rule) (getRHS nt rules)).
  Proof.
  intros. induction rules0.
  - left. unfold getRHS. reflexivity.
  - right. exists (snd a). simpl. Abort.


  (* Given a nonterminal [nt], applies all possible rules. *)
  (*aplica step_rhs na lista de regras obtida em getRHS nt *)
  Definition step_nt (rules : list(NT * rhs.t T NT)) (t : T) (nt : NT) : list (option NT) :=
    rules |> getRHS nt  |> flat_map (step_rhs t).
  (*Lemma step_nt_sound : forall rules,forall t, forall nt, step_nt rules t nt =  [] \/
  In None (step_nt rules t nt)  \/ (exists n:NT, In (Some n) (step_nt rules t nt)).
  Proof.
  intros.
  destruct step_nt.
  - left. reflexivity.
  - destruct o. right. right. simpl. exists n. left. reflexivity.
    right. left. simpl. left. reflexivity. Qed. *)


  (* Given a *list* of nonterminals, takes all possible next steps. *)
  (*map: retorna 1 valor para cada aplicação da função por elemento da lista *)
  (*flat_map: retorna 0 ou mais valores para cada aplicação da função por elemento da lista*)
  Definition step (rules : list(NT * rhs.t T NT)) (t : T) (acc : list NT) : list (option NT) :=
  (*nodup: sem passos que possam ser duplicados. equiv_dec é a relação de equivalência *)
  (* entre os tipos de caracteres não terminais (que estarão em acc), necessário para nodup*)
  (*verificar se os elementos já se encontram na lista ou não *)
  acc |> flat_map (step_nt rules t) |> nodup equiv_dec.

  Definition step_sound: forall rules, forall t, forall acc, step rules t acc = [] \/
  In (None) (step rules t acc) \/ (exists nt:NT, In (Some nt)(step rules t acc)).
  Proof.
  intros.
  destruct step.
  - left. reflexivity.
  - destruct o. right. right. exists n. simpl. left. reflexivity.
    right. left. simpl. left. reflexivity.
  Qed.

  (* The main parser loop. Repeatedly steps the current set of states using
     terminals from the string. *)
  (*Definition parse (grammar : reg_grammar.g) (l : list T): bool :=
    [Some (start_symbol grammar)] |> parse' (rules grammar) l |> is_final (rules grammar).*)
  Definition parse' (rules : list(NT * rhs.t T NT))
           : list T -> list (option NT) -> list (option NT) :=
    fix rec l acc :=
      match l with
      | [] => acc
      | t :: l =>
    (*filtermap id : acc recebe todos os elementos da lista t::l. *)
        acc |> filterMap id
            |> step rules t
            |> rec l
      end.

  Definition parse'_sound: forall rules, forall lt, forall lnt, parse' rules lt lnt = [] 
  \/ In (None) (parse' rules lt lnt) \/ (exists nt:NT, In (Some nt) (parse' rules lt lnt)).
  Proof.
  intros.
  destruct parse'.
  - left. reflexivity.
  - destruct o. right. right. exists n. simpl. left. reflexivity.
    right. left. simpl. left. reflexivity.
  Qed.

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
  (*existsb: exists booleano, verifica se uma condição pode ser satisfeita por algum *)
  (*elemento da lista. Presente m Coq.Lists. O o é um elemento da lista de regras da entrada. *)
    existsb (fun o => match o with
                   | None => true
                   | Some nt => getRHS nt rules |> existsb rhs.isEmpty
                   end)
            l.
  (*Lemma is_final_sound : forall r l,  is_final r l = true \/ is_final r l = false.
 Proof.
    intros r l.
    destruct is_final;auto.
  Qed.*)

  (* Top-level parse function. Calls [parse'] with the initial symbol and checks
     to see whether the resulting state is accepting. *)
  Definition parse (grammar : reg_grammar.g) (l : list T): bool :=
    [Some (start_symbol grammar)] |> parse' (rules grammar) l |> is_final (rules grammar).
  (*importante notar que a função parse retorna verdadeiro se a palavra de entrada *)
  (* é derivável do conjunto de regras da gramática. O que seria a corretude dessa função?*)
  (* creio que só isso abaixo não serve para nada.                                       *)
  (*Lemma parse_companion : forall grammar, forall l, parse grammar l = true \/ parse grammar l = false.
  Proof.
  intros.
  destruct parse;auto.
  Qed.*)

  (*Definition string_belongs_to_the_grammar(g:reg_grammar.g)(l:list non_terminal) :Prop := forall l, forall acc: list (option NT),
  exists nt, (parse' (rules grammar) l acc) = nt /\ In None nt.*)

  Definition nt_is_final (g:reg_grammar.g) (lnt: list (option NT)) : Prop :=
  is_final (rules g) lnt = true.

  (*Lemma parse_sound: forall grammar, forall l,
  parse grammar l = true -> exists nt, nt_is_final grammar nt /\ string_belongs_to_the_grammar.
  intros.
  destruct grammar.
  unfold nt_is_final. simpl. unfold is_final. destruct is_final. destruct H1;assumption. Abort.
*)


  (*o parser estar correto quer dizer que se ele retorna true, então está num estado final *)
  (*Lemma parse_sound: forall grammar, forall l, forall lnt, parse grammar l = true -> 
  (is_final (rules grammar) lnt) = true /\ lnt = parse' l (rules grammar).*)

  (*função que faz o parser em cima da lista de regras e passa para uma fórmula válida de uma*)
  (*gramática regular *)
  Definition rhs_from_loose (l : list (NT + T)) : option (rhs.t T NT) :=
    match l with
    | [] => Some Empty
    | [inr t] => Some (Single t)
    | [inr t; inl A] => Some (Continue t A)
    | _ => None
    end.

  Lemma rhs_from_loose_sound : forall l, (rhs_from_loose l = Some Empty) \/ 
  (exists t, rhs_from_loose l = Some (Single t)) \/ 
  (exists t, exists A, rhs_from_loose l = Some (Continue t A)) \/
  (rhs_from_loose l = None).
  Proof.
  intros.
  destruct l.
  - simpl. auto.
  - destruct rhs_from_loose. destruct t.
    + left. reflexivity.
    + right. left. exists t. reflexivity.
    + right. right. left. exists t. exists n. reflexivity.
    + right. right. right. reflexivity.
  Qed.


(*função que lê uma lista de caracteres terminais e não terminais, assim como a nossa forma *)
(*inicial de expressar a gramática. Note que a leitura deve começar com um não terminal. *)
  Definition rule_from_loose (l : list (NT + T)) : option (NT * rhs.t T NT) :=
    match l with
    | inl A :: rhs =>
      match rhs_from_loose rhs with
      | None => None
      | Some rhs => Some (A, rhs)
      end
    | _ => None
    end.
  Lemma rule_from_loose_sound : forall l, rule_from_loose l = None \/ 
  exists rhs,exists A, rule_from_loose l = Some (A,rhs).
  Proof.
  intros.
  destruct rule_from_loose.
  - destruct p. right. exists t. exists n. reflexivity.
  - left. reflexivity.
  Qed.

  (*essa função faz o mesmo que a de cima, mas para a lista das listas com as regras. *)
  Definition rules_from_loose (l : list (list (NT + T))) : option (list (NT * rhs.t T NT)) :=
    l |> map rule_from_loose |> list_option_traverse.
  Lemma rules_from_loose_sound : forall l, rules_from_loose l = None \/
  exists list, rules_from_loose l = Some list.
  Proof.
  intros.
  destruct rules_from_loose.
  - right. exists l0. reflexivity.
  - left. reflexivity.
  Qed.

  (*essa função gera a gramática, baseada na conversão da lista de regras solta dada como *)
  (*entrada, a gramatática gerada vem com as regras já convertidas para gramática regular. *)
  Definition from_loose (start : NT) (l : list (list (NT + T))) : option g :=
    match rules_from_loose l with
    | None => None
    | Some rs => Some {| start_symbol := start;
                        rules := rs |}
    end.

  Lemma from_loose_sound : forall start, forall l, from_loose start l = None \/ 
  exists rs, from_loose start l = Some {| start_symbol := start;
                        rules := rs |}.
  Proof.
  intros.
  unfold from_loose. destruct l.
  - destruct rules_from_loose. right. exists (l). reflexivity.
    left. reflexivity.
  - destruct rules_from_loose. right.  exists (l1). reflexivity.
    left. reflexivity.
  Qed.

  End reg_grammar.
End reg_grammar.

Module dfa.
  Section dfa.
    (* Definição manual do autômato. Provar a corretude aqui vai ser difícil, pois a entrada *)
    (* nessa seção é puramente manual.                                                       *)
    Variable (S A : Type).
    Record t := DFA {
      initial_state : S;
      is_final : S -> bool;
      next : S -> A -> S
   }.
    (*função que faz os passos de verificação do autômato (aplica as funções de transição do DFA)*)
    (*ela retorna um estado S, que pode ser final ou não *)
    (*acc é um acumulador, variável que armazena o resultado do processamento em cima de cada um*)
    (*das variáveis da lista. Nesse caso, ela vai recebendo o resultado de cada função de transi-*)
    (*ção do autômato                                                                       *)
    Definition run' (step: S -> A -> S) (l : list A) (acc : S) : S :=
      fold_left step l acc.
    Definition run (m : t) (l : list A) : bool :=
      is_final m (run' (next m) l (initial_state m)).
    Definition run2 (m :t) (l : list A) : S :=
      run' (next m) l  (initial_state m).
    (*isso ajuda em algo?*)
    (*Lemma run_companion : forall m:t, forall l, run m l = true \/ run m l = false.
    Proof.
    intros.
    destruct run;auto.
    Qed.*)
  End dfa.
End dfa.

(* We can explicitly construct a DFA corresponding to the grammar. In fact, all
   the hard work was already done in our grammar parser. *)
Module powerset_construction.
  Section powerset_construction.
    Variable T NT : Type.
    Context `{EqDec T eq} `{EqDec NT eq}.
    (*uma gramática regular válida segue as regras de t, com T sendo terminal e NT não terminal. *)
    Variable g : reg_grammar.g T NT.
    Definition state : Type := list (option NT).
    (* o estado inicial a gente retira da gramática *)
    Definition init : state := [Some (reg_grammar.start_symbol g)].
    (*os estados finais também, seguindo a ideia explícita em reg_grammar.is_final *)
    Definition is_final (s : state) : bool :=
      reg_grammar.is_final (reg_grammar.rules g) s.
    Definition next (s : state) (t : T) : state :=
      reg_grammar.step (reg_grammar.rules g) t (filterMap id s).
    (*função que chama o construtor de um DFA do módulo DFA, após ter convertido as regras para*)
    (*formato de regras válidas                                                          *)
    Definition dfa := dfa.DFA init is_final next.

    (* faltando algo abaixo? ver melhor isso aqui.                                 *)
    (*Definition state_is_accepting (s:state): Prop := forall s, is_final s = true. *)

    (*a dfa should only accept words that are within its language, in other words *)
    (*if a dfa accepts a word, it should be in a final state                      *)
   (*Lemma dfa_from_grammar_sound :  forall s, forall l, dfa.run dfa l = true 
    <-> state_is_accepting s.
    Proof.
    intros.
    split.
    - intros;induction l. unfold state_is_accepting. destruct is_final. Abort.*)

    (* Because of the way we carefully set this up, simulation holds
       *definitionally*, which is pretty cool. *)
    (*Aqui, a gente chega na conclusão de que o autõmato e o parser fazem a *)
    (* mesma coisa, por conta da forma que ambos foram implementados.       *)
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


  (* The same (corrected) grammar, represented in the loose format used in the
     original email. *)
  Definition a_b_loose_rules: list(list(non_terminal.t + terminal.t)) :=
    [[inl non_terminal.A; inr terminal.a; inl non_terminal.A];
     [inl non_terminal.A; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.A];
     [inl non_terminal.B; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.B]].

  Inductive non_terminal1 := S| S1 | S2 | S3 |S4.
  Inductive terminal1 := a | b |c | d | e.
  (*S => estado de entrada do autômato. Só se passa por ele 1x. *)
  Definition loose_rules_2 : list (list(non_terminal1 + terminal1)) :=
  [[inl S;inr a;inl S1];[inl S1;inr b;inl S2];[inl S2;inr c;inl S3];[inl S3;inr d];
  [inl S3;inr d;inl S3]; [inl S3; inr a; inl S1]].
  (*alternativamente, as regras externas podem ter essa representação *)
  Definition rules_3: list (non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S, Continue a S1);
     (S1, Continue b S2);
     (S2, Continue c S3);
     (S3, Single d);(S3, Continue d S3);(S3, Single a)].

  (* We can see that it gets converted to the "tight" representation given
     above. *)
  Eval compute in reg_grammar.from_loose non_terminal.A a_b_loose_rules.

  Eval compute in reg_grammar.from_loose S loose_rules_2.

  (*new_grammar, que é a gramática que eu tô testando, é uma gramática que gera um a seguido de um *)
  (* b seguido de um c seguido de vários d.De um d, caso leia um a, deve ser seguido por um b, por um c e por um ou mais d*)
  Definition new_grammar := reg_grammar.from_loose S loose_rules_2.
  Check new_grammar.
  Check a_b_grammar.

  Definition one := reg_grammar.from_loose non_terminal.A a_b_loose_rules.
  Check one.
  Check a_b_grammar.
  Check a_b_grammar.

  (* Definition dfa3 := powerset_construction.dfa grammar_for_loose_rules_3. *)
  (*Ltac: linguagem de tática da Gallina. a ideia abaixo foi do James. Isso resolve o *)
  (*problema pautado no caderno do option A. Perceba que isso aqui é poderosíssimo, uma vez que permite *)
  (* a solução de problemas utilizando a linguagem de táticas do Coq *)
  Ltac grab_option x :=
    let x' := eval compute in x in
    match x' with
    | Some ?v => exact v
    end.

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
          | e,e => in_left
          | a, b| b,a| a, c | c, a | a, d | d, a | b, c | c, b | b, d | d, b 
          | c, d | d, c| a, e| e , a| b, e| e, b | e, c| c, e| d, e| e,d => in_right
          end
      }.


  Definition das := reg_grammar.build_grammar S rules_3.
  Definition automata_example := powerset_construction.dfa das.
  Check automata_example.
  Eval compute in dfa.run2 automata_example [a;b;c;d].
  Eval compute in dfa.run automata_example [a;b;c;d].


  Definition rules_example_2:list(non_terminal1 * rhs.t terminal1 non_terminal1) :=
  [(S,Continue a S1);(S,Continue b S2);(S1, Continue a S1);(S1,Continue c S3);(S2,Continue b S2);
  (S2, Continue d S4);(S3, Single c);(S3,Continue c S);
  (S4, Single d);(S4,Continue d S)].
  Eval compute in reg_grammar.getRHS S4 rules_3.
  
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
  

  Definition a_b_from_loose := ltac:(grab_option (reg_grammar.from_loose non_terminal.A a_b_loose_rules)).
  Definition automata_from_loose := powerset_construction.dfa a_b_from_loose.
  Definition example3 := ltac:(grab_option (new_grammar)).
  Definition automata_from_ex3 := powerset_construction.dfa example3.
  Definition automata_from_example_3 := powerset_construction.dfa a_b_from_loose.
  Check automata_from_example_3.
  
  Definition dec := dfa.run2 automata_from_ex3 [a; b;c;d].
  Eval compute in (filterMap id dec).
  (*teste para o caso [a;b;e;c;d] e veja *)
  Definition dec2 := dfa.run2 automata_from_ex3 [a;b;c;d;d;d;d;d;d].
  Definition dec3 := dfa.run automata_from_ex3 [a; b;c].
  Definition dec4 := dfa.run automata_from_ex3 [a;b;c;d;d;d;d;d;d].
  Eval compute in dec.
  Eval compute in dec2.
  Eval compute in dec3.
  Eval compute in dec4.

End a_b_example.

