
#include <stdio.h>
#include <stdlib.h>

/*Program that generates the equivalence decision procedure for inductive types using the Program Instance tactic. For proper functioning, the first argument is the name of the instance and the second argument is the name of the inductive type for which the EqDec instance is being created. The remaining arguments are the inductive types' inhabitants. This is part of the RGCoq repository in github: https://github.com/simasgrilo/RGCoq.

Remember to use "Obligation Tactic := unfold complement, equiv ; program_simpl." so Program Instance can work properly. The default tactic to solve obligations (only program_simpl) won't work.*/

int main(int argc, char** argv){
	FILE * fp = fopen("eqdec.txt","wt");
	int i,j;
	if(argc > 3){
		fprintf(fp,"Program Instance %s : EqDec %s eq := \n",argv[1],argv[2]);
		fprintf(fp,"\t{equiv_dec x y := \n");
		fprintf(fp,"\t\tmatch x, y with \n");
		for(i = 3; i < argc; i++) fprintf(fp,"\t\t| %s,%s => in_left \n",argv[i],argv[i]);
		for(i = 3; i < argc; i++){
			for(j = 3; j < argc;j++){
				if(argv[i] != argv[j])fprintf(fp,"\t\t| %s,%s => in_right \n",argv[i],argv[j]);
			}
		}
		fprintf(fp,"\t\tend \n");
		fprintf(fp,"\t}.");
	}
	fclose(fp);
	return 0;
}

/*Soundness proof of the above function: let l be the list of arguments passed to the main function by the terminal and n the number of elements of l. let P(n) be the proposition "The program runs with a list l with n elements and will write (in a file named "eqdec.txt") in_left specifications only when the inhabitant of the inductive type equals to itself and in_right specifications for all cases where the inhabitant is different from all the other inhabitants of the inductive type, generating exactly k "in_left" specifications and (k^2 - k) "in_right" specifications (k is the number of the inhabitants of the terminal symbol, k < n).

The proof is done by induction on the number of the inductive type's inhabitants.

(i) induction basis : We want to show that P(1) holds. Notice that the case k = 0 is not useful, since it won't create no valid relation (as it can be seen in the program). Since the function only prints its contents if it has received more than 3 arguments (including the name of the program, which in this case is always the first element of the list), it only creates a valid EqDec relation iff there is the identifier of the relation,
the inductive type it refers to and at least a inductive element (which is an inhabitant of the inductive type passed as an argument to this function). In this case, it generates a valid relation for a single inhabitant of the inductive type (which is equal to itself), printing only one "in_left" specification and no "in_right" specifications. Then, P(1) holds.

(ii) induction hypothesis : let us assume P(n) holds, n a natural number.

(iii) induction step : let us prove that P(n+1) holds. From the program, we can see that it will print "|x,y => in_left" only for all the elements that equals to itself (when x = y, forall x and y inhabitants of the inductive type) and it prints |x,y => in_right, for all cases when x <> y. From the induction hypothesis, it is generated (n "in_left" specifications, in the cases that a inhabitant equals to itself, and n²-n "in_right" specifications, for all different pairs of different inhabitants. if it is added 1 inhabitant to the list, we can see that it will generate n+1 "in_left" specifications (adding 1, to the case the new terminal symbol equals to itself) and ((n+1)² - (n+1)) "in_right" specifications, in which it will generate "in_right" specifications for each case the new inhabitant differs from itself.

*/
/*Usage example: given one has a inductive type as follows:
Inductive symbols := A | B | C.

compiling the above program as gcc -o <name> eqdecGenerator.c and then running "./<name> <identifier> symbols A B C", where <identifier> is the name you want to
give to the instance and symbols in this case is the identifier of the inductive type. The output will be as shown below:

Program Instance example : EqDec symbols eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| C,C => in_left 
		| A,B => in_right 
		| A,C => in_right 
		| B,A => in_right 
		| B,C => in_right 
		| C,A => in_right 
		| C,B => in_right 
		end 
	}.
*/

