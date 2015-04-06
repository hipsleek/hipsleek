int id(int x)
/*@
  case {
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
 */
{
  if (x==0) return 0;
  int ret = id(x-1) + 1;
  if (ret > 3) return 3;
  return ret;
}



int main(int input)
/*@
  requires true
  ensures true;
*/

{
  // int input = __nondet_int();
  int result = id(input);
   // dprint;
  if (result == 2) {
    //@ dprint;
    //@ assert false;
    //@ assert true;
    //@ dprint;
    return 1;
  }

  return 0;
}


/*

Successful States:
[
 Label: []
 State:or[htrue&result'=tmp' & input'<=3 & 0<=input' & tmp'=input' & input'=input&{FLOW,(4,5)=__norm#E}[]
; 
         htrue&result'=tmp' & 3<input' & tmp'=3 & input'=input&{FLOW,(4,5)=__norm#E}[]
]
 ]

assert:fail/ex1-id2-b3.c:29: 1:  : ok

 */
