relation H(int a).
relation H1(int a).

int xZero0(int input)
  requires true
  ensures res!=0;
{
  int x = 1; //8:
  int y = input - 42; //9

  if (y<0){//11
    x=0; //12
  }
  y=y+1;
  return x;
}

/*

Checking procedure xZero0$int... 
Post condition cannot be derived:
  path trace:  [(,0 ); (,0 )]  (must) cause:  res=0 |-  res!=0. LOCS:[6;12;15] (must-bug)

In the case of conditional, we  should include 9 from cond.
This arises because 12 is dependent on if test at 11
which is in term dependent on 9. I guess we presently have
statement dependency (supported by slicing) but not 
path dependency.

Statement dependency are of the form:
    {9}: y'=input'-42
    {11}: y'<0
    {12}: x'=0

which says that expression x'=0 came from 12, but there isn't
a dependency on y'. I would suggest, we capture path dependency
using no-op expression path(expr,[id]).

In our example, we would capture it using:
    {12}: path(x'=0,[y'])

In that way, when we can use it when performing substitution:

    {9}: y'=input'-42 & {11}: y'<0 & {12}: path(x'=0,[y'])
    === subs y'=input'-42 ==>
    {9,11}: input'-42<0 & {9,12}: path(x'=0,[input'])

We can also use it in slicing:
    {9}: y'=input'-42 & {11}: y'<0 & {12}: path(x'=0,[y']) |- ..x'..
    === slicing {x'} ==>
    {9,12}: path(x'=0,[input']) |- ..x'..

Thus, when performing substitution

    y in vs  nvs=fvars[expr]-fvars[e]
  --------------------------------------
   [y->expr] path(e,vs) 
    ==> path([e->expr],vs-{y}+nvs)



*/

