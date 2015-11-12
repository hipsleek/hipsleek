#include<stdlib.h>

//@ HeapPred P(char_star s).

void loop (char* s)
/*@
  infer [
    @shape_pre
    //P
    ,@pure_field
    ,@classic
    ,@size
    ,@term
  ]
  //requires P(s)
  requires true
  ensures true;
  
  //requires s::WSS<p>
  //ensures Q(s, s');

  //requires s::WFSegN<q, n> * q::char_star<0, p>
  //requires s::WSSN<p, n> * p::MEM<>
  //ensures s::WFSegN<s', n-1> * s'::char_star<0, p> * p::MEM<>;
*/
{
  int x = *s;
  if (x != '\0') {
  //if (x != 'a') { // UNSAFE
    s++;
    loop(s);
  }
}

int main () 
/*@
  infer [@term]
  requires true
  ensures true;
*/
{
  int length = __VERIFIER_nondet_int();
  if (length < 1) { length = 1; }
  char* nondetString = (char*) alloca(length * sizeof(char));
  //@ dprint;
  nondetString[length-1] = '\0';
  //@ dprint;
  loop(nondetString);
  return 0;
}

