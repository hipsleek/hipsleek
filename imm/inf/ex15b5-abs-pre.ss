
data cell{
 int fst;
}

relation Q(ann v).

int foo2(cell c)
infer [Q]
  requires c::cell<_>@aaa & Q(aaa)
  ensures c::cell<_>@bbb;
{
  int x = 5;
  return x;
}

/*
# ex15b5.ss

Given below. 

infer [Q]
  requires c::cell<_>@aaa & Q(aaa)
  ensures c::cell<_>@bbb;

# Why aren't we getting Q(aaa) == aaa=@A

Since there is no requirement on pre-condition,
we should make above assumption
*/
