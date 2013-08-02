data cell{
	int val;
	cell next;
}

data scope{
	cell v;
	scope next;
	scope proto;
}

store<> == self = null
	or self::scope<_,n,p> * n::store<> U* p::store<>;

void storeassign(scope lg, scope lp, cell lhs, cell rhs)
requires rhs::cell<v,p> * lg::store<>
ensures lhs::cell<v,p> * rhs::cell<v,p> * lg::scope<lhs,null,lp> U* lp::store<>;

void storenew(scope s, cell lhs)
requires s::store<>
ensures s::scope<lhs,null,p> U* p::store<> & lhs = null;

void ex1(scope lg,scope lp)
requires lg::store<> U* lp::store<>
ensures lg::store<> U* lp::store<>;
{
cell x,y,z,v;
// x = null;
storenew(lg,x);
//y = null;
//dprint;
storenew(lg,y);
//z = null;
storenew(lg,z);
//dprint;
//v.val = 5;
cell tmp = new cell(5,null);
//dprint;
storeassign(lg,lp,v,tmp);
//dprint;
//z = v;
//storeassign(lg,lp,z,v);
//dprint;
assert v'::cell<5,_>;
}
	

