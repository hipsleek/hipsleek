relation H(int a).
relation H1(int a).

int xZero0(int input)
  requires true
  ensures res!=0;
{
  int x = 1; //8:
  int y = input - 42; //y

  if (y<0){
    x=0; //12
  }
  //dprint;
  return x;
}

/*

Checking procedure xZero0$int... 
Post condition cannot be derived:
  path trace:  [(,0 ); (,0 )]  (must) cause:  res=0 |-  res!=0. LOCS:[6;12;15] (must-bug)

In the case of conditional, how do we include 9 ?
This arises because 12 is dependent on if test at 11
which is in term dependent on 9. I guess we presently have
formula dependency (thru slicing) but not statement dependency.

Statement dependency are of the form:
    y -> 12
which says that statement 12 depends on y. Currently, we have
formula which depends on some statements, e.g:
    {9} -> y'<0
    {}  -> x'=0
I think for handling conditional, we also need to
add in statement that depends formula:
    {y'}  -> x'=0
As y' depends on 9, I guess this will then be translated to:
    {9}  -> x'=0
so that in the end, we will only have formula that depends on
statements.

*/

