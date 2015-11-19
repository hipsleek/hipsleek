data node {
  int val;
  node next;
}


relation R(node x,node y).

bool rand()
   requires true
  ensures true;

int hoo(node x,node y)
  infer [@ana_ni,R]
  requires R(x,y)
  ensures true;
{
  int t = x.val;
  if (rand()) return  t;
    else return hoo(y,x);
 }


/*
# ex2a.ss --ana-ni

# Need to consider greatest fix-point compute..

[RELASS [R]: ( R(x,y)) -->  2<=x,
RELDEFN R: ( 2<=x' & R(x',y')) -->  R(y',x')]

              htrue&{FLOW,(4,5)=__norm#E}[]

*/


