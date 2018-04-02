data Cell {
  int val;
}
data Pair {
  Cell p1;
  Cell p2;
}

int sum_1(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Lo & c2 <? @Lo
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_2(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Lo & c2 <? @Lo
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_3_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Lo & c2 <? @Hi
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_4(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Lo & c2 <? @Hi
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_5_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Hi & c2 <? @Lo
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_6(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Hi & c2 <? @Lo
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_7_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Hi & c2 <? @Hi
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_8(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Lo & c1 <? @Hi & c2 <? @Hi
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_9(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Lo & c2 <? @Lo
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_10(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Lo & c2 <? @Lo
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_11_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Lo & c2 <? @Hi
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_12(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Lo & c2 <? @Hi
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_13_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Hi & c2 <? @Lo
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_14(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Hi & c2 <? @Lo
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_15_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Hi & c2 <? @Hi
  ensures res = 3 %% res <? @Lo;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_16(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true %% p <? @Hi & c1 <? @Hi & c2 <? @Hi
  ensures res = 3 %% res <? @Hi;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_S1(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true
  ensures res = 3 %% res <? p |_| c1 |_| c2;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_S2_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true
  ensures res = 3 %% res <? p |_| c1;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_S3_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true
  ensures res = 3 %% res <? p |_| c2;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_S4_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true
  ensures res = 3 %% res <? c1 |_| c2;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_S5_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true
  ensures res = 3 %% res <? p;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_S6_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true
  ensures res = 3 %% res <? c1;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}

int sum_S7_fail(Pair p)
  requires p::Pair<c1,c2> * c1::Cell<1> * c2::Cell<2> & true
  ensures res = 3 %% res <? c2;
{
  int x1 = p.p1.val;
  int x2 = p.p2.val;
  return x1 + x2;
}
