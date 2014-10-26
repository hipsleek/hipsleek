void loop3(int* p, int* q)
  /*
    infer [@term]
    requires p::int*<_, op> * q::int*<vq, oq> & op>=0 & oq>=0
    ensures true;
  */
  /*
    //infer [@term]
    requires p::int*<_, op> & op>=0
    case {
      p = q -> requires Term ensures true;
      p != q -> requires q::int*<vq, oq> & oq>=0 & Term[op+1024-oq] ensures true;
    }
  */
  /*@
    //infer [@term]
    requires p::int*<vp, op> & op>=0
    case {
      p = q -> requires Term ensures true;
      p != q -> requires q::int*<vq, oq> & oq>=0 & Term[op+1024-oq] ensures true;
    }
  */
{
  if (q < p + 1024) {
    q++;
    loop3(p, q);
  }
}

