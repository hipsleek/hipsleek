data cell {int val;}

int sum (cell i, cell j)
/* // below fails - ok
  infer[v1,v2,v3,v4]
  requires i::cell<a>@v1*j::cell<b>@v2 * k::cell<c>@A
  ensures  i::cell<a>@v3*j::cell<b>@v4 * k::cell<c>@I & res=a+b;*/

/* // success - ok
  infer[v1,v2,v3,v4]
  requires i::cell<a>@v1*j::cell<b>@v2 * k::cell<c>@A
  ensures  i::cell<a>@v3*j::cell<b>@v4 & res=a+b;*/

  infer[v1,v2,v3]
  requires i::cell<a>@v1*j::cell<b>@v2 * k::cell<c>@v3
  ensures  i::cell<a>@v1*j::cell<b>@v2 * k::cell<c>@A & res=a+b;

{
  return i.val + j.val;
}

int get_val (cell i, cell j)

/*  requires i::cell<a>@A //fails
    ensures  res=a;*/

/*  requires i::cell<a>@L * j::cell<_>@A //success
  ensures  res=a;*/

  infer [v,v1]
  requires i::cell<a>@v1 * j::cell<_>@v
  ensures  res=a;

/*  infer[v1,v3]
  requires i::cell<a>@v1 * k::cell<c>@v3 // @v3 should be @A, but it's @L
  ensures  i::cell<a>@v1 * k::cell<c>@v3 & res=a;*/

{
  return i.val;
}


