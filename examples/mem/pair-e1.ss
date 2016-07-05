/* singly linked lists */

/* representation of a node */

data pair {
	int fst; 
	int snd;	
}

void foo(pair x)
/*
Translating global variables to procedure parameters...
Stop Omega... 20 invocations caught

Exception occurred: Failure("hd")
Error(s) detected at main 
*/
  requires true
  ensures true;
{
  dprint;
  x.snd = 3;
  dprint;
}
/*
int foo2(pair x)
  requires x::pair<_@A,a@L>
  ensures x::pair<_@A,_@L> & res=a+1 ;
/*
  requires x::pair<a,b>
  ensures x::pair<_,_> & res=b ;
*/
{
  int r = x.snd;
  return r+1;
}
*/



