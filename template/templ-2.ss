template int r(int x, int y).

void loop (int x, int y)
	infer[r]
	requires Term[r(x, y)]
	ensures true;
/*
	case {
		x >= y -> requires Term ensures true;
		x < y -> requires Term[r(x, y)] ensures true;
	}
*/	
	/*
	requires true
	ensures true;
	*/
{
	if (x >= y) return;
  else loop (x+1, y);
}

/*
# templ-2.ss --gts

 template int r(int x,int y) == r_0+(r_x*x)+(r_y*y).

infer [r]  y=y' & x=x' |-  0<=(r( x, y)).

  this seems to be boundedness check at pre-condition
  I suppose we should have >=0 at recursive call, namely:

  y=y' & x'<y' & xx=x+1 & x'=x |-  0<=(r( xx, y)).
 
infer [r]  y=y' & x=x' & x'<y' & !(v_bool_18_851') & x'<y' & !(v_bool_18_851') & 
v_int_19_850'=1+x' |-  (r( x, y))>(r( v_int_19_850', y')).
template_solve.
*/
