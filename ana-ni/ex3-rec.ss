data node {
  int val;
  node next;
}


relation R(node x).
relation P(node x).

bool rand()
   requires true
  ensures true;

int hoo(node x,node y)
  infer [@ana_ni,R,P]
  requires  R(x) & P(y)
  ensures true;
{
  int t = x.val;
  if (rand()) return  t;
    else return hoo(y,x);
 }


/*
*****pure relation assumption 1 *******
*************************************
[RELASS [R]: ( R(x)) -->  2<=x,
RELDEFN P: ( 2<=x' & R(x')) -->  P(x'),
RELDEFN R: ( P(y')) -->  R(y')]
*************************************

 */


