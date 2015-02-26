data node {
	int val; 
    node next;
}


node f(node x)
requires x::node<3,_> ensures res::node<3,_>;
{
	while (true)
	requires x::node<3,_> ensures eres::node<3,_> & flow __RET;
	{
		return x;
	}
}
