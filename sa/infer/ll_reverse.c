void reverse(node x, node y){
	if(x!= null){
		node tmp = x.next;
		x.next = y;
		y = x;
		x = tmp;
		reverse(x,y);
	}
}

Pre: HX(x) * HY(y)
Post: GX(x,x') * GY(y,y')

func call (x != null)
[HX, HY, GX, GY] HX(x) * HY(y) |- true -* (b & x!= null) v (!b &x=null)

state after then branch:
[HX, HY, GX, GY] HX(x) * HY(y) & x != null

for x.next
[HX, HY, GX, GY] HX(x) * HY(y) & x != null |- x::node<a,b>
[HX, HY, GX, GY, HX1] HX1(x, b) * HY(y) * x::node<a,b>
with HX(x) --> HX1(x, b) * x::node<a,b>

tmp = x.next
[HX, HY, GX, GY, HX1] HX1(x, b) * HY(y) * x::node<a,b> & tmp = b

x.next = y
[HX, HY, GX, GY, HX1] HX1(x, b) * HY(y) * x'::node<a,y> & tmp = b

y = x
[HX, HY, GX, GY, HX1] HX1(x, b) * HY(y) * x'::node<a,y> & tmp = b & y' = x'

x = tmp
[HX, HY, GX, GY, HX1] HX1(x, b) * HY(y) * x0::node<a,y> & tmp = b & y' = x0 & x' = tmp

recursice func call
[HX, HY, GX, GY, HX1] HX1(x, b) * HY(y) * x0::node<a,y> & tmp = b & y' = x0 & x' = tmp |- HX(x') * HY(y') -* GX(x', x'') * GY(y', y'')

[HX, HY, GX, GY, HX1] GX(x1, x') * GY(y', y'') * HX1(x, b) * HY(y) * x0::node<a,y> & tmp = b & y' = x0 & x1 = tmp 
with HX1(x, b) * HY(y) * x0::node<a,y> & y' = x0 & x' = b -> HX(x') * HY(y')

post-cond for then branch: 
[HX, HY, GX, GY, HX1] GX(x1, x') * GY(y', y'') * HX1(x, b) * HY(y) * x0::node<a,y> & tmp = b & y' = x0 & x1 = tmp  |- GX(x, x') * GY(y, y')
with GX(x1, x') * GY(y', y'') * HX1(x, b) * HY(y) * x0::node<a,y> & y' = x0  -> GX(x, x') * GY(y, y')

state after else branch:
[HX, HY, GX, GY] HX(x) * HY(y) & x = null

post-cond else then branch: 
[HX, HY, GX, GY]  HX(x) * HY(y) & x = null & x' = null |- GX(x, x') * GY(y, y')
with HX(x) * HY(y) & x = null & x' = null -> GX(x, x') * GY(y, y')

Constrains:

(1) HX(x) -> HX1(x, b) * x::node<a,b>
(2) HX1(x, b) * HY(y) * x0::node<a,y> & y' = x0 & x' = b -> HX(x') * HY(y')
(3) GX(x1, x') * GY(y', y'') * HX1(x, b) * HY(y) * x0::node<a,y> & y' = x0  -> GX(x, x') * GY(y, y')
(4) HX(x) * HY(y) & x = null & x' = null -> GX(x, x') * GY(y, y')

 H1(x) * H2(y) & x!=null  --> x::node<val_18_528',next_18_529'> * HP_549(next_18_529')
 H1(x) * H2(y) * x::node<val_18_562,y> & x!=null & y'=x & x'=tmp_19' --> H1(x') * H2(y')
 H1(x) * H2(y) * x::node<val_18_562,y> * G1(tmp_566,x') * G2(x,y') & x!=null --> G1(x,x') * G2(y,y')
 H1(x) * H2(y) & x'=x & y'=y & x'=null --> G1(x,x') * G2(y,y')

Normalization:
From (2) HX1(x, b) * HY(y) * x0::node<a,y> & y' = x0 & x' = b -> HX(x') * HY(y')
(5) HX1(x, b) & x' = b -> HX(x')
(6) HY(y) * x0::node<a,y> & y' = x0 ->HY(y') ==> HY(y) * y'::node<a,y> ->HY(y')


From HX(x) * HY(y) & x = null & x' = null -> GX(x, x') * GY(y, y')
(7) HX(x) & x = null& x' = null -> GX(x, x')
(8)  HY(y) -> GY(y, y')

From (7) HX(x) -> x = null -> GX(x, x')
From (1)(5) HX(x) -> HX1(x, b) * x::node<a,b> -> HX(b) *  x::node<a,b>
==> HX(x) -> (x = null ) v ( HX(b) *  x::node<a,b>)

From(3) GX(x1, x') * GY(y', y'') * HX1(x, b) * HY(y) * x0::node<a,y> & y' = x0  -> GX(x, x') * GY(y, y')
(9) GX(x1, x') * HX1(x, b) -> GX(x, x')
(10) GY(y', y'') * HY(y) * y'::node<a,y> -> GY(y, y')

GX(x,y) = GX1(x) * GX2(y)
GY(x,y) = GY1(x) * GY2(y)
From (9)
GX2(x') -> GX2(x')
HX1(x, b) -> GX1(x)
From (10) 
GY1(y') * y'::node<a,y>  -> GY2(y')
HY(y) -> GY1(y)
From (6) HY(y) * y'::node<a,y> -> HY(y')
==> HY(y) * y'::node<a,y> -> GY1(y')

From (4) HX(x) * HY(y) & x = null& x' = null  -> GX(x, x') * GY(y, y')
HX(x) & x = null& x' = null -> GX(x, x')
x = null -> GX1(x)
x' = null -> GX2(x')

HY(y) -> GY1(y)
true -> GY2(y')

Equalize:
x::node<a,b> v x = null -> GX1(x)
GX2(x') <-> x' = null
GX(x,x') <-> (x::node<a,b> v x = null) & x' = null
GY1(y) * y'::node<a,y> -> GY1(y')
GY1(y') -> GY2(y')
true -> GY2(y')
GY(y,y') <-> GY1(y) * GY1(y')

Thus, we have 
HX(x) -> (x = null ) v ( HX(b) *  x::node<a,b>)
HY(y) * y'::node<a,y> -> HY(y')
GX(x,x') <-> (x::node<a,b> v x = null) & x' = null
GY(y,y') <-> GY1(y) * GY1(y')
GY1(y) * y'::node<a,y> -> GY1(y')




















