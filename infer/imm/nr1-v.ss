data cell {int val;}

/* steps
   (1) infer access pattern
   (2) determine non-aliasing
*/

int sum (cell i, cell j)
  //infer[v1,v2]
  requires i::cell<a>@L*j::cell<b>@L
  ensures  res=a+b;
  requires (i::cell<a>@L & j::cell<b>@L)
  ensures  res=a+b;
  requires i::cell<a>@v1*j::cell<b>@v2 & v1<:@L & v2<:@L
  ensures  res=a+b;
  /* requires (i::cell<a>@v1 & j::cell<b>@v2) & v1<:@L & v2<:@L */
  /* ensures  res=a+b; */
{
  return i.val + j.val;
}

void swap (cell i, cell j)
  requires i::cell<a>@M*j::cell<b>@M
  ensures i::cell<b>@M*j::cell<a>@M;
  requires i::cell<a>@v1*j::cell<b>@v1 & v1<:@M
  ensures i::cell<b>@v1*j::cell<a>@v1;
{
  int t = i.val;
  i.val = j.val;
  j.val = t;
}
