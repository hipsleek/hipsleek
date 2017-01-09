

relation P(int x).

relation R(int x).
  relation R2(int x,int y).

int fact(int i)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
//infer [P,@classic,@pure_field]
//  requires P(i)
  infer [P]
  // requires P(i) ensures  true;
  requires P(i) ensures  false;
{    
  if (i==0) return 1;
  else return i + fact(i-1);
}

/*
# ex20g4a.ss 

  infer [P]
  requires P(i)
  ensures  true;
{
  if (i==0) return 1;
  else return i + fact(i-1);
}

# relAssume for pre-codition

[RELDEFN P: ( P(i) & i=1+v_int & (v_int+1)!=0) 
   -->  P(v_int)]

The inductive definition is:

  P(i) -> (i=1+v_int & (v_int+1)!=0 --> P(v_int))

In this case greatest fix-point should give just:

  P(i) -> true.

=================================
Given:

  requires P(i) ensures  false;

  # We derive:

[RELDEFN P: ( P(i) & i=1+v_int & (v_int+1)!=0) -->  P(v_int),
RELASS [P]: ( P(i)) -->  i!=0]

This gives inductive defn:

  P(i)  --> (i=1+v_int & (v_int+1)!=0) -> P(v_int)
            /\ i!=0

The GFP computation should give:
  P(i) --> i<0


*/
