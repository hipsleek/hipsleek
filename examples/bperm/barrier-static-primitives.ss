/*
 Example for static barriers
 */

hip_include 'barrier_static_header.ss'

void main()
  requires emp
  ensures emp;
{
  barrier b = newBarrier(1);
  //dprint;
  waitBarrier(b);
  //dprint;
  destroyBarrier(b);
  //dprint;
}
