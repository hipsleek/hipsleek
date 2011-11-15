+++++++++++++++++++++++++++++++++++
Problem 2:
+++++++++++++++++++++++++++++++++++

+++++++++++++++++++++++++++++++++++
Implementation Task.
+++++++++++++++++++++++++++++++++++
1. We use the following data type:
data anode {
  int val;  
  anode fn;
  anode arg;
}

Regarding the val field, we make the following convention: value is 0 for application, 1 for the K combinator, and 2 for the S combinator. The fn and arg fields will only contain useful information when val is 0. The reduction function is given in file prob2-1.ss.

+++++++++++++++++++++++++++++++++++
Verification Task 1:
+++++++++++++++++++++++++++++++++++
The solution is provided in the file prob2-1.ss. 
----------------------------------
To run: 
----------------------------------   
./hip prob2-1.ss -tp auto. The output will show the verification result for each method and some statistics regarding the timings. 

----------------------------------
Solution description:   
----------------------------------
We make use of the following inductive heap predicates for denoting term and value, where p1 * p2 denotes the fact that p1 and p2 hold for disjoint portions of the heap. The special variable "self" denotes the root pointer into the data structure, from which all the nodes are reachable.

term<> ==
// denotes an apply: the value corresponding to the val field is 0, 
// f corresponds to the fn field, and a corresponds to the arg field
  self::anode<0,f,a> * f::term<> * a::term<>		
// denotes a K combinator: val is 1, f and a are null  
  or self::anode<1,null,null> 						
// denotes a S combinator: val is 2, f and a are null  
  or self::anode<2,null,null> 						
// invariant, which is true for all terms  
  inv self!=null;									

value<> ==
// denotes K 
  self::anode<1,null,null>  									
// denotes S   
  or self::anode<2,null,null>  									
// denotes (K v) - it's an apply (self::anode<0,f,a>), 
// where f is a K (f::anode<1,null,null>), and arg is a value  
  or self::anode<0,f,a> * f::anode<1,null,null> * a::value<> 	
// denotes (S v) - it's an apply (self::anode<0,f,a>), 
// where f is an S (f::anode<2,null,null>), and arg is a value   
  or self::anode<0,f,a> * f::anode<2,null,null> * a::value<> 	
// denotes ((S v) v) - it's an apply (self::anode<0,f,a>), 
// f is again an apply (f::anode<0,f1,a1>), f.fn is an S (f1::anode<2,null,null>), 
//f.arg is a value (a1::value<>), and a is a value (a::value<>)  
  or self::anode<0,f,a> * f::anode<0,f1,a1> * 
      f1::anode<2,null,null> * a1::value<> * a::value<> 		
// invariant, which is true for all values		  
  inv self!=null;												
  
The reduction function has the following signature and specification:
anode reduction (anode t)
	requires t::term<>
	ensures  res::value<>;  

The precondition denoted by the keyword "requires" expects the input argument t to be a term. The postcondition, denoted by the "ensures" keyword, establishes that the result returned by the function is a value. The keyword "res" is used to denote the result of the function.

For clarity, we employ three auxiliary functions: isApply, isCombK, isCombS. These functions return true whenever their input is an apply, a K combinator, or an S combinator, respectively. For illustration, we provide below the specification for isApply:

bool isApply(anode t)
	requires t::anode<v,_,_>@I
	ensures true & (v=0 & res | v!=0 & !res);
  
The precondition requires t to be an anode of the form t::anode<v,_,_>@I. As we are only interested in the val field, for the other two fields, fn and arg, we use the anonymous value "_". The "@I" annotation specifies that the function is only allowed to read the input anode and cannot mutate it. Consequently, the input anode does not need to be added in the postcondition (due to the immutability annotation this does not cause a memory leak). The postcondition specifies that true is returned whenever the val field (corresponding to the v value) is 0, and false otherwise.

An additional method that we need is clone. As the heap predicate for term requires the function and the argument to be stored in disjoint portions of the heap, for the reduction C[(((S v1) v2) v3)] -> C[((v1 v3) (v2 v3))] we need to duplicate v3. Hence, we use the clone method to produce a disjoint duplicate of the input value. As the method only reads the input value, this is set as immutable in the precondition and omitted from the postcondition. 

anode clone (anode t)   
	requires t::value<>@I
	ensures  res::value<>;

During the verification process, when encountering the method call reduction(t) at line 97, a check is performed for establishing that the method's precondition holds. In order for the precondition to hold, t needs to be a term (t::term<>). For this purpose, t has to be folded back into a term by replacing the definition of term<> with its name. The definition requires both fn and arg to be terms. However, the information from the program state about the args val2 and val2c is that they are values, and the verification process is not able to establish the fact that a value is also a term. In order to make the connection between a value and a term, we add an explicit coercion (line 22). All the user provided coercions are automatically checked by our system.	
	coercion self::value<> -> self::term<>; 

+++++++++++++++++++++++++++++++++++
Verification Task 2:
+++++++++++++++++++++++++++++++++++
The solution is provided in the file prob2-2.ss. 
----------------------------------
To run: 
----------------------------------   
./hip prob2-2.ss -tp auto. 

----------------------------------
Solution description:   
----------------------------------
We use the predicates termK<n> and valueK<>. They are similar to term<> and valuek<> from the first verification task, with the difference that they only allow the presence of the K combinator. Moreover, termK has an argument n, representing the number of applications in the term. In the inductive case (self::anode<0,f,a> * f::termK<n1> * a::termK<n2> & n=1+n1+n2), the number of applications is equal with the sum between the number of applications in the function and argument plus 1. In the base case when there is only a K combinator (self::anode<1,null,null> & n=0), the number of applications is 0.


termK<n> ==
// denotes an apply 
     self::anode<0,f,a> * f::termK<n1> * a::termK<n2> & n=1+n1+n2		
// denotes the K combinator	 
  or self::anode<1,null,null> & n=0  									
  inv self!=null & n>=0;


valueK<> ==
// denotes K
  self::anode<1,null,null>  
// denotes (K v)  
  or self::anode<0,f,a> * f::anode<1,null,null> * a::valueK<> 			
  inv self!=null;

Similarly to the situation from the first verification task, we need a coercion to relate valuek<> and termk<>: coercion self::valueK<> -> self::termK<>.

We provide the following specification for the reduction function:
	requires t::termK<n>
	variance (1) [n]
	ensures  res::valueK<> ;
The variance specification variance (1) [n] sets the decreasing measure to n, the number of applications in the input term. 
	
+++++++++++++++++++++++++++++++++++
Verification Task 3:
+++++++++++++++++++++++++++++++++++
The solution is provided in the file prob2-3.ss. 
----------------------------------
To run: 
----------------------------------   
./hip prob2-2.ss -tp auto. 

----------------------------------
Solution description:   
----------------------------------
We use two inductive heap predicates: value<>, which was already described in verification task 1, and ks<n>.

ks<n> == self::anode<1,null,null> & n = 0 							// denotes K
      or self::anode<0,f,a> * f::ks<n-1> * a::anode<1,null,null> 	// denotes ((ks n-1) K)
inv n >= 0;

We provide the following specification for the reduction function:

anode reduction (anode t)
requires (exists k: t::ks<n> & n=2*k & k>=0)
ensures res::anode<1,null,null>;
requires (exists k: t::ks<n> & n=2*k+1 & k>=0)
ensures res::anode<0,f,a> * f::anode<1,null,null> * a::anode<1,null,null>;

This specification consists of two pairs of pre/post-conditions. The first one describes the case when the reduction is applied to the term (ks n) with n even, while the second one corresponds to the case when n is odd. In the former case, the result is K (res::anode<1,null,null>), while in the latter, the result is K K (res::anode<0,f,a> * f::anode<1,null,null> * a::anode<1,null,null>). res::anode<0,f,a> * f::anode<1,null,null> * a::anode<1,null,null> denotes K K as it is an apply (res::anode<0,f,a>), where the function is K (f::anode<1,null,null>), and the argument is also K (a::anode<1,null,null>).
 

  
  
  






