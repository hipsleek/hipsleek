data cell { int val; }

void f(cell x)
  requires x::cell<_>@L // * @lend[x]
  ensures true;
{
  x.val = x.val + 1;
}
