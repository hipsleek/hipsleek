constrs:{HX(x) * HY(y) & x!=null -> HX1(b,x) * x::node<_,b> & true,
HX1(b,x) * x1::node<a,y> & x!=null -> HX(b) * HY(x1),
G(x1, x0, x1, y0) * HX1(b,x) * HY(y) * x1::node<a,y>  -> G(x, x0,y, y0),
HX(x) * HY(y) & x = null & x0 = null -> G(x, x0,y, y0)
}

