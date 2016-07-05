List extensions for the specification language
==============================================

The specification language was updated to support the following constructs, adding support
for lists of integers. The notations n, a, a1, a2, ..., an are used for expressions of type
integer and L, L1, ..., Ln for expressions of type list.

* returning list:

[| a1, a2, ..., an |]
		creates a list containing the elements a1, a2, ..., an; the symbol [| |]
		specifies the empty list;

a ::: L
		constructs a list using the element a as a head and the list L as a tail;

tail(L)
		returns the tail of the list L or the empty list if L has less then one element;

app(L1, L2, ..., Ln)
		returns a list built by appending the lists L1, L2, ..., Ln;

rev(L)
		returns the list L reversed (with the same elements, but in a reversed order);

* returning integer:

head(L)
		returns the head of the list L (the first element of the list), or 0 if the list
		is empty;

len(L)
		returns the length of the list L (the number of elements).

* returning bool:

a inlist L
		returns true if the list L contains the element a, false otherwise;

a notinlist L
		returns true if the list L does not contain the element a, false if a is included
		in the list L;

alln(n, L)
		returns true if L is an empty list or if all the elements of L are equal with n,
		false otherwise;

perm(L1, L2)
		returns true if L1 and L2 contain the same elements, maybe in a different order;
		in other words, L2 must be a permutation of L1.



Updates in lexer (ilexer.mll)
=============================

The following keywords were added in the hashtable: alln (ALLN), app (APPEND), head (HEAD),
inlist (INLIST), len (LENGTH), notinlist (NOTINLIST), perm (PERM), rev (REVERSE), tail (TAIL).

Also, the lexer is instructed to recognize the following symbols: open list [| (OLIST),
closed lsit |] (CLIST) and list constructor ::: (COLONCOLONCOLON).



Updates in parser (iparser.mly)
===============================

Defined tokens OLIST, CLIST, COLONCOLONCOLON (with right associativity) and added the syntax
rules implementing the constructs presented above. When such a rule is matched, the corresponding
branch in the IAST (Input Abstract Syntax Tree) is created. The types associated with IAST elements
are defined in 'Ipure.ml'.



Updates in other hip files
==========================

- ipure.ml:
	* added the types associated with the new constructs in the IAST (ListIn, ListNotIn,
		ListAllN, ListPerm, List, ListCons, ListHead, ListTail, ListLength, ListAppend,
		ListReverse);
	* updated the functions that search for free variables (bfv, afv);
	* updated the functions that search for anonymous variables (look_for_anonymous_b_formula,
		look_for_anonymous_pure_formula and look_for_anonymous_exp);
	* updated the functions that replace variables (b_apply_one, e_apply_one);
	* updated the function that returns the position of an expression (pos_of_exp);
	* added a function that tests if an expression is a list (is_list);
	
- iast.ml:
	* updated the function that returns the name of a given type (name_of_type);

- iformula.ml:
	* updated the functions float_out_min_max and float_out_exp_min_max (that extracts min /
		max expressions from formulas);

- iprinter:
	* added pretty-printing for list formulas in IAST;

- astsimp.ml:
	* updated the functions that make transition from IAST (Input Abstract Syntax Tree) to
		CAST (Core Abstract Syntax Tree): trans_pure_b_formula, trans_pure_exp;
	* updated the functions that collect and check the expression types:
		collect_type_info_b_formula, collect_type_info_arith, collect_type_info_bag_list_content,
		collect_type_ino_listl;

- solver.ml:
	* updated simpl_b_formula;

- cpure.ml:
	* added the types associated with the new constructs in the CAST (ListIn, ListNotIn,
		ListAllN, ListPerm, List, ListCons, ListHead, ListTail, ListLength, ListAppend,
		ListReverse);
	* updated the function that returns the type of a given expression: get_exp_type;
	* added a function that tests if an expression is a list (is_list);
	* updated the functions that search for free variables (bfv, afv);
	* updated the function that returns the name of a given type (name_of_type);
	* updated the function that returns the position of an expression (pos_of_exp);
	* updated the functions that replace variables (b_apply_one, e_apply_one);
	* updated the functions that test the equality of two expressions (eq_b_formula, eq_exp);
	* updated the functions: b_apply_subs, a_apply_subs, b_apply_par_term, a_apply_par_term,
		b_apply_one_term, a_apply_one_term, b_apply_one_exp, e_apply_one_exp, simpl_mult, 
		purge_mult, arith_simplify;
	
- cast.ml:
	* updated the function that returns the name of a given type (name_of_type);

- cprinter:
	* added pretty-printing for list formulas in CAST;

- tpdispatcher.ml:
	* added a function that tests if a constraint/expression contains lists
		(is_list_constraint, is_list_constraint_exp);

- cvclite.ml, isabelle.ml, mona.ml, omega.ml, setmona.ml (interfaces with theorem provers that
	don't support lists): added error messages when reaching list constraints.



Interface with COQ (coq.ml)
===========================

- added pretty-printing for the new constructs with lists:
	* [| a1, a2, ..., an |] -> a1 :: a2 :: ... :: an
	* a ::: L -> a :: L
	* tail(L) -> tail L
	* app(L1, L2, ..., Ln) -> L1 ++ L2 ++ ... ++ Ln
	* rev(L) -> rev L
	* head(L) -> hd 0 L
	* len(L) -> Z_of_nat ( length L )
	* a inlist L -> In a L
	* a notinlist L -> not ( In a L )
	* alln(n, L) -> alln L n (* alln is defined in 'decidez.v'*)
	* perm(L1, L2) -> Permutation L1 L2

- added pretty-printing for constructs with bags (bag tactics are not yet implemented):
	* { a1, a2, ..., an } -> ZSets.add a1 (ZSets.add a2 (ZSets.add ... (ZSets.add an
		ZSets.empty)));
	* union(B1, B2, ..., Bn) -> ZSets.union B1 (ZSets.union B2 (ZSets.union ... Bn));
	* intersect(B1, B2, ..., Bn) -> ZSets.inter B1 (ZSets.inter B2 (ZSets.inter ... Bn));
	* diff(B1, B2) -> ZSets.diff B1 B2
	* a in B -> ZSets.mem a B = true
	* a notin B -> ZSets.mem a B = false
	* B1 subset B2 -> ZSets.subset B1 B2
	(ZSets is defined as Module ZSets := FSets.Make(Z_as_OT).)

- COQ is now launched only once, at the beginning and each formula is sent to it using a pipe;
COQ is closed at the end, after proving the last formula. After each launch, COQ must load the
necessary libraries (and this operation is time-consuming); thus, this change has brought a massive
improvement in performance.
  The function that starts the prover is named 'start_prover'. It is defined in 'tpdispatcher.ml'
and called from 'main.ml', before sending the first formula. 'start_prover' in 'tpdispatcher.ml'
is calling the corresponding function from the prover interface file (in our case 'start_prover'
from 'coq.ml', COQ being the only prover that is started only once).
  In the case of COQ, 'start_prover' creates the COQ process ('coqtop -require decidez 2> /dev/null')
and stores the communication pipe handle in the variable 'coq_channels'. Also, the variable
'coq_running' is updated to reflect that COQ is now running and waiting for formulas.
  When sending a formula, the function 'write' assembles the body of the lemma that must be proven
and calls 'send_formula'. 'send_formula' sends the lemma through the pipe and parses the result.
If there is an error reading from the pipe, it is assumed that COQ has crashed and it is restarted.
If COQ crashes two times on the same formula, it is assumed that the formula COQ could not prove
the formula. The second parameter of the function 'send_formula' keeps track of the number of
retrys left.
  At the end, after the last formula is processed, COQ is closed in the following way: 'main.ml'
calls 'stop_prover' from 'tpdispatcher.ml', which, in turn, calls 'stop_prover' from 'coq.ml'. In
this way, it will be easy to update the other provers to be used in the same way as COQ.

- the function 'imply' was updated to keep the implication, taking advantage of the fact that COQ
knows how to handle implications (for other provers, P -> Q is translated to ~P \/ Q).


The COQ library file (decidez.v)
================================

- This file was completely rewritten.

- The first section contains the proofs for the lemmas used for simplifying the expressions with
lists. These lemmas are applicable for lists with a generic element type, so it will be easy to
implement also lists containing elements with a type different from int. The lemmas are proven in
both ways (<->) so they can be used for rewriting in hypothesis and conclusions.
  If adding a new lemma to this database, one must take great care not to make a looping rewriting
system (even autorewrite can loop if provided with a wrong lemma database!).

- The second section contains the definition for 'alln' and the theorems supporting the 'alln'
construct. These are needed because 'alln' is not present in the standard COQ libraries.

- The formulas with lists can be simplifyed in two ways: using a lemma database and the automatic
tactic 'autorewrite' or using a hand-written tactic that searches for subexpressions and simplifies
them using the lemmas. The first approach is easier to be implemented but less efficient end also
less flexible.
  The hint database for autorewrite, named 'simpl_lists_db', is created in the third section of the
file.

- The next section contains the implementation for the manual tactic that makes the simplifications
(named 'sim'). This tactic searches for subexpressions that can be simplified (the left side of the
lemmas) and rewrites them using the lemmas defined in the first section (replaces the left side with
the right side). The advantage of this method is that it is faster and it supports some more
optimisations (each individual case can be treated in a different way).
  The search for the subexpressions is implemented using the 'context' construct; there are separate
entries matching hypothesis and conclusions (there isn't a unified way to search for an expression in
both hypothesis and conclusions).

- The last section contains the definition of 'hyp', a collection of general tactics dealing with
existential quantification, conjunction, disjunction etc. For a conjunction or disjunction present in
a hypothesis, the hypothesis is destroyed (using 'destruct'). For a conjunction present in the
conclusion, the goal is splitted (using 'split'). For a disjunction present in the conclusion, the
tactic is trying to solve the goal using the left part and then, if this fails, using the right part.
If this fails too, the tactic replaces the conclusion with 'False'. The order of these tactics is
very important, greatly affecting the performance.
  The main tactic, that is called when trying to prove a formula, is named 'decidez'. First of all,
existential quantification is eliminated (using the tactic 'solve_exists') by adding existential
variables (the ones starting with ?), trying to simplify the goal and after that to instantiate the
existential variables (with instantiate). In this way all the simple cases are solved (the majority,
when the solution is already there), but not all (there are cases when the result must be guessed,
and I was not able to come up with a solution that can cover all these cases).
  The goal is simplified (or even solved) by the 'solve_all' tactic, which calls, in a repeat loop,
the tactics 'hyp', 'sim' (for simplifications of expressions containing lists) and 'subst' (which
replaces duplicate identifiers). After that, the goal may be proved with the tactic 'auto'.
  If, after all these, the goal still cannot be proven, the tactic tries one more time, after replacing
the conclusion with 'False' (there are situations where the goal is provable by contradicting a hypothesis). 



Compiling the COQ library file
==============================

teodor@loris-7:~/sleekex$ coqc decidez.v



Running hip with COQ
====================

teodor@loris-7:~/sleekex$ ./hip -tp coq examples/list_examples/ll.ss

Processing file "examples/list_examples/ll.ss"
Parsing...
Coq started
Translating global variables to procedure parameters...
Translating to core language...
Checking procedure reverse$node~node...
Procedure reverse$node~node SUCCESS
Checking procedure create_list$int...
Procedure create_list$int SUCCESS
Checking procedure delete_val$node~int...
Procedure delete_val$node~int SUCCESS
Checking procedure delete$node~int...
Procedure delete$node~int SUCCESS
Checking procedure insert$node~int...
Procedure insert$node~int SUCCESS
Checking procedure get_next_next$node...
Procedure get_next_next$node SUCCESS
Checking procedure set_null$node...
Procedure set_null$node SUCCESS
Checking procedure set_next$node~node...
Procedure set_next$node~node SUCCESS
Checking procedure get_next$node...
Procedure get_next$node SUCCESS
Checking procedure ret_first$node...
Procedure ret_first$node SUCCESS
Checking procedure append$node~node...
Procedure append$node~node SUCCESS
Coq stopped

0 false contexts at: ()

Total verification time: 8.33 second(s)
        Time spent in main process: 0.39 second(s)
        Time spent in child processes: 7.94 second(s)



Examples
========

- Some examples with lists are located in the directory 'examples/list_examples'. All these
examples should be successfully checked by hip.