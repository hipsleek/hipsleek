/* singly linked lists */

/* representation of a node */

data pair {
	int fst; 
	int snd;	
}

void foo(pair x)
/*  OK
  requires x::pair<_@A,_>
  ensures x::pair<_@A,3>;
*/
  requires x::pair<_@A,_@M>
  ensures x::pair<_@A,3@M>;
/*
WHY parser error for above?
 --error: Stream.Error("GT expected after [opt_data_h_args] (in [simple_heap_constr])")
 at:caught

Exception occurred: Stream.Error("GT expected after [opt_data_h_args] (in [simple_heap_constr])")
*/
{
  x.snd = 3;
}

int foo2(pair x)
  requires x::pair<_@A,a@L>
  ensures  res=a+1 ;
/*
  requires x::pair<a,b>
  ensures x::pair<_,_> & res=b ;
*/
{
  int r = x.snd;
  dprint;
  return r+1;
}




