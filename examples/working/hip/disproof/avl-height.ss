data node {
	int val;
	int height;
	node left;
	node right;
}

avl<size, height> == self = null & size = 0 & height = 0 
	or self::node<_, height, p, q> * p::avl<size1, height1> * q::avl<size2, height2> & size = 1+size1+size2 & 
        height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1 
	inv size >= 0 & height >= 0;

int height(node x)
	requires x::avl<m, n>
	ensures x::avl<m, n> & res = n;	
{
	if (x == null)
		return 0;
	else
		return x.height;        
}



synthesize [node x]
 x::avl<m,n>&x!=null
~>
 (exists ht94,Anon_4495,p_4496,size1_4497,height1_4498,q_4499,
size2_4500,
height2_4501: x::node<Anon_4495,ht94,p_4496,q_4499> * 
              p_4496::avl<size1_4497,height1_4498> * 
              q_4499::avl<size2_4500,height2_4501>&
n=res & m=size2_4500+1+size1_4497 & height2_4501<=(1+height1_4498) & 
height1_4498<=(1+height2_4501) & 
exists(max_2034:n=1+max_2034 & max_2034=max(height1_4498,height2_4501)) & 
ht94=n).
