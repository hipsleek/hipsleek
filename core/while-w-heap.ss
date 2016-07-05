/*

  Example with complex specs including heap nodes in WHILE LOOP
 */

void main()
  requires true
  ensures true;
{
  int_ptr i= new int_ptr(0);
  int N = 10;
  while (i.val < N)
    requires i::int_ptr<old_i>
    case{ old_i < N ->  ensures i'::int_ptr<new_i> & i'=i & new_i =N & N'=N;
          old_i >=N -> ensures i'::int_ptr<new_i> & i'=i& new_i= old_i & N'=N;
    }
    /* requires i<=N & N'=N */
    /* ensures i'=N & N'=N; //' */
  {
    int_ptr p = i;
    p.val = p.val +1;
    //dprint;
  }
  //dprint;
  int z = i.val;
  assert (z'=10);//'
}
