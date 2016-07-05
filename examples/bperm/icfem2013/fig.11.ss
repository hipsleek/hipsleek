/*

  The nested fork/join example in Fig. 11 of the report.

  Example for static barriers.
  Two different groups of threads operate on two different
  barriers in a nested fork/join manner.

 */

hip_include 'barrier_static_header.ss'


void participant(barrier b)
  requires b::barrier(1,2,0)<0>
  ensures b::barrier(1,2,0)<1>;
{
  waitBarrier(b);
}

void group(barrier b)
  requires b::barrier(2,2,0)<0>
  ensures b::barrier(2,2,0)<1>;
{
  int id1 = fork(participant,b);
  int id2 = fork(participant,b);

  join(id1);
  join(id2);
}

void main()
  requires emp
  ensures emp;
{
  barrier b1 = newBarrier(2);
  barrier b2 = newBarrier(2);

  int idg1 = fork(group,b1);
  int idg2 = fork(group,b2);

  join(idg1);
  join(idg2); 

  destroyBarrier(b1);
  destroyBarrier(b2);

}
