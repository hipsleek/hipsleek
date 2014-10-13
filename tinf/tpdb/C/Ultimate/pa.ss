data int_star {
  int val;
  int offset;
  int size;
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
  requires p::int_star<_, op, sp> * q::int_star<_, oq, sq> //& Term[op+1024-oq]
  ensures true;
  /*
  requires p::int_star<_, op, sp>
  case {
    p = q -> requires true ensures true;
    p != q -> requires q::int_star<_, oq, sq> ensures true;
  }
  */
{
  if (less_than(q, add(p, 1024))) {
    int_star r = add(q, 1);
    //dprint;
    loop(p, r);
  }
}

int_star malloc_int_star(int s)
  case {
    s <= 0 -> ensures res = null;
    s > 0 -> ensures res::int_star<_, o, s>;
  }

int_star add(int_star p, int i) 
  requires p::int_star<_, o, s> & 0 <= i & Term // & i < s
  ensures p::int_star<_, o, s> * res::int_star<_, o+i, s-i>;
  
bool less_than(int_star p, int_star q)
  requires p::int_star<vp, op, sp> * q::int_star<vq, oq, sq> & Term
  case {
    op <  oq -> ensures p::int_star<vp, op, sp> * q::int_star<vq, oq, sq> & res;
    op >= oq -> ensures p::int_star<vp, op, sp> * q::int_star<vq, oq, sq> & !res; }
  
int get_val(int_star p)
  requires p::int_star<v, o, s>
  ensures p::int_star<v, o, s> & res = v;
  
