/* singly linked lists */

/* representation of a node */

data pair {
	int fst; 
	int snd;	
}


int foo(pair x)
/* OK & err with @L nodes
  requires x::pair<_,a>@L
  ensures  res=a+1 ;
*/
/* OK
  requires x::pair<_@A,a@L>
  ensures  res=a+1 ;
*/
  requires x::pair<_@A,a@M>
  ensures  x::pair<_@A,a@M> & res=a+1 ;

{
  int r = x.snd;
  dprint;
  return r+1;
}

void main(pair x)
  requires x::pair<a,b>
  ensures x::pair<a,b>;
/*
Successful States:
[
 Label: 
 State:EXISTS(Anon_577: x::pair<a@M,b@A>@M[Orig] * x'::pair<Anon_577@A,a_571@M>@M[Orig]&x'=x & 0<=0 & Anon_11=a & a_571=b & x!=null & 0<=0 & 0<=3 & r_23'=1+a_571&{FLOW,(22,23)=__norm})[]
       es_var_measures: MayLoop

 ]

Post condition cannot be derived:
  (must) cause:  mismatched annotation
*/

{ 
  int r = foo(x);
  dprint;
}




