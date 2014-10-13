data int_star {
  int val;
  int offset;
}

int main() {
  int_star p = malloc_int_star(1024);
  int_star q = p;
  int_star r = add(p, 1);
  int v = get_val(p);
  return 0;
}

void loop(int_star p, int_star q)
  infer [@term]
  //requires p::int_star<_, op> * q::int_star<_, oq> //& Term[op+1024-oq]
  //ensures true;
  
  requires p::int_star<_, opp>
  case {
    p = q -> requires true ensures true;
    p != q -> requires q::int_star<_, oqq> ensures true;
  }
  
{
  //dprint;
  if (less_than(q, add(p, 1024))) {
    dprint;
    int_star r = add(q, 1);
    //dprint;
    loop(p, r);
  }
}

int_star malloc_int_star(int s)
  case {
    s <= 0 -> ensures res = null;
    s > 0 -> ensures res::int_star<_, o>;
  }

int_star add(int_star p, int i) 
  requires p::int_star<v, o> & 0 <= i & Term // & i < s
  ensures p::int_star<v, o> * res::int_star<_, o+i>;
  
bool less_than(int_star p, int_star q)
  requires p::int_star<vp, op> * q::int_star<vq, oq> & Term
  case {
    op <  oq -> ensures p::int_star<vp, op> * q::int_star<vq, oq> & res;
    op >= oq -> ensures p::int_star<vp, op> * q::int_star<vq, oq> & !res; }
  
int get_val(int_star p)
  requires p::int_star<v, o>
  ensures p::int_star<v, o> & res = v;
  
