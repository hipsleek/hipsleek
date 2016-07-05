/* selection sort */

data node {
	int val; 
	node next; 
}

class e1 extends __Exc {}

node bindex(node x, node y)
  requires x::node<a,b> 
  ensures  x::node<_,b> & flow e1 ;
{
  {
    raise new e1();
    dprint;}
     dprint;;
    //y=x;
}

/*
{(
((
(dprint;
dprint);
(e1 v_e1_16_548;
(v_e1_16_548 = {new e1()};
123::throw v_e1_16_548:{,(19,20)=e1})));
dprint);
dprint)}

(raise ?; dprint);dprint
*/
