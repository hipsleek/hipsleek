void loop2(int* p)
  /*@
    infer [@term]
    requires p::int*<vp, op, sp>
    ensures true;
   */
{
  if (*p >= 0) {
    (*p)--;
    loop2(p);
  }
}
