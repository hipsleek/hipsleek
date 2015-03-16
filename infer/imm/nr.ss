data cell {int val;}

int sum (cell i, cell j)
  infer[v1,v2]
  requires i::cell<a>@v1*j::cell<b>@v2
  ensures  i::cell<a>@v1*j::cell<b>@v2 & res=a+b;
{
  return i.val + j.val;
}

/*
PROBLEM : inferred @L instead of @M
  v1<:@L  & v2<:@L & v1<:@M & v2<:@M
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v1; a; v2; b](ex)i::cell<a>@L[Orig] * 
                  j::cell<b>@L[Orig]&true&{FLOW,(20,21)=__norm}[]
*/
void swap (cell i, cell j)
  infer[v1,v2]
  requires i::cell<a>@v1*j::cell<b>@v2
  ensures  i::cell<b>@v1*j::cell<a>@v2;
{
  int t = i.val;
  i.val = j.val;
  j.val = t;
}
