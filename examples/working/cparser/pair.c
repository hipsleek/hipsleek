struct pair {
  int x;
  int y;
};

int first(struct pair p)
/*@
  requires p::pair<a,b>
  ensures p::pair<a,b> & res = a;
*/
{
  return p.x;
}

int first2(struct pair* p)
/*@
  requires p::pair*<q> * q::pair<a,b>
  ensures  p::pair*<q> * q::pair<a,b> & res = a;
  //requires p::pair^<a,b>
  //ensures  p::pair^<a,b> & res = a;
*/
{
  return p->x;
}

int first3(struct pair** p)
/*@
  requires p::pair**<q> * q::pair*<r> * r::pair<a,b>
  ensures  p::pair**<q> * q::pair*<r> * r::pair<a,b> & res = a;
  //requires p::pair^^<a,b>
  //ensures  p::pair^^<a,b> & res = a;
*/
{
  return (*p)->x;
}

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

/*@
pair__star cast_general_pointer_to_pair__star(void__star p)
  case {
    p = null  -> ensures res = null;
    p != null -> ensures res::pair__star<q> * q::pair<_,_>;
  }
*/

int foo1()
/*@
  requires true
  ensures  res=1;
*/
{
  struct pair* v = malloc(1);
  v->x = 1;
  v->y = 2;
  return v->x;
}

int foo2()
/*@
  requires true
  ensures  res=1;
*/
{
  struct pair v;
  v.x = 1;
  v.y = 2;
  return v.x;
}



/*


pair v_48 = new pair();
{(pair v_48;
{(({(int v_int_44_909;
(v_int_44_909 = 1;
bind v_48 to (x_44_910,y_44_911) [write] in 
x_44_910 = v_int_44_909))};
{(int v_int_45_912;
(v_int_45_912 = 2;
bind v_48 to (x_45_913,y_45_914) [write] in 
y_45_914 = v_int_45_912))});
(int v_int_46_917;
(v_int_46_917 = bind v_48 to (x_46_915,y_46_916) [read] in 
x_46_915;
ret# v_int_46_917)))})}
free_pair(v_48)

{(37,0),(47,1)}

 */
