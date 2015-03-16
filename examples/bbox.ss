data node {
	int t; // op;
	int l; // eft;
	int b; // ottom;
	int r; // ight;
	node nw;
	node ne;
	node sw;
	node se;
}

bbox<t,l,b,r> == self=null
	or self::node<t,l,b,r, nw, ne, sw, se>
		* nw::bbox<nwt,nwl,nwb,nwr>
		* ne::bbox<net,nel,neb,ner>
		* sw::bbox<swt,swl,swb,swr>
		* se::bbox<set,sel,seb,ser>
		& nwr <= nel & nwb <= swt
		& swr <= swl & neb <= set
		& t=min(nwt, net) & l=min(nwl, swl)
		& b=max(swb, seb) & r=max(ner, ser);

node build1() 
	requires true ensures res::bbox<0,0,10,10>;
{
	return new node(0,0, 10,10, null, null, null, null);
}

node build2(node nw, node ne, node sw, node se)
static	requires nw::bbox<nwt,nwl,nwb,nwr>
				* ne::bbox<net,nel,neb,ner>
				* sw::bbox<swt,swl,swb,swr>
				* se::bbox<set,sel,seb,ser>
				& nw,ne,sw,se!=null
		ensures true;
dynamic	requires nw::bbox<nwt,nwl,nwb,nwr>
				* ne::bbox<net,nel,neb,ner>
				* sw::bbox<swt,swl,swb,swr>
				* se::bbox<set,sel,seb,ser>
				& nw,ne,sw,se!=null
		ensures true;
{
	int t = get_min(nw.t, ne.t);
	int l = get_min(nw.l, sw.l);
	int b = get_max(sw.b, se.b);
	int r = get_max(ne.r, se.r);

	node tmp = new  node(t, l, b, r, nw, ne, sw, se);
	return tmp;
}

int get_max(int a, int b)
	requires true ensures res=max(a,b);
{
	if (a < b) return b;
	else return a;
}

int get_min(int a, int b)
	requires true ensures res=min(a,b);
{
	if (a < b) return a;
	else return b;
}
