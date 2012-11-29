/*
  Race condition on stack variables
  Inspired by Smallfoot example "passive_stack_race.sf" at
  http://www.dcs.qmul.ac.uk/research/logic/theory/projects/smallfoot/
 */

void assign(ref int x, int y)
  requires true //@full[x] & @value[y]
  ensures  x'=y; // & @full[x] //'
{
  x = y;
}

void stack_race()
requires true
  ensures true;
{
  int x,y;
  int id1,id2;
  id1 = fork(assign,x,42);
  id2 = fork(assign,y,x); //this failed because
  //main thread thread does not have permission of x
  join(id1);
  join(id2);
}
