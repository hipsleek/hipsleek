/* red black trees */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}

/* view for red-black trees */
rb1<n, cl, bh, S> == self = null & bh = 1 & cl = 0 & n=0 & S={}
	or self::node<v, 1, l, r> * l::rb1<nl, 0, bhl, S1> * r::rb1<nr, 0, bhr, S2> & cl = 1 & n=1+nl+nr & bhl = bh & bhr = bh & S = union(S1, S2, {v})
	or self::node<v, 0, l, r> * l::rb1<nl, _, bhl, S1> * r::rb1<nr, _, bhr, S2> & cl = 0 & n=1+nl+nr & bhl = bhr & bh = 1 + bhl & S = union(S1, S2, {v})
	inv n>=0 & bh >= 1 & 0 <= cl <= 1;

/* rotation case 3 */
relation ROT3(bag a, bag b, bag c, bag d).
node rotate_case_3(node a, node b, node c)
  infer [ROT3]
	requires a::rb1<na, 1, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 0, bha, S3> 
	ensures res::rb1<na+nb+nc+2, 0, bha + 1, S4> & ROT3(S4,S1,S2,S3);//& S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, b, c);
	
	return new node(0, 0, a, tmp);
}

/* rotation case 3 */
node rotate_case_3_1(node a, node b, node c)

	requires a::rb1<na, 1, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 0, bha, S3> 
	ensures res::rb1<na+nb+nc+2, 0, bha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});


/* rotation to transform case 2 in case 3, then apply case 3 */
relation ROT2(bag a, bag b, bag c, bag d, bag e).
node case_2(node a, node b, node c, node d)
  infer [ROT2]
	requires a::rb1<na, 0, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 0, bha, S3> * d::rb1<nd, 0, bha, S4> 
	ensures res::rb1<na+nb+nc+nd+3, 0, bha + 1, S5> & ROT2(S5,S1,S2,S3,S4);//S5 = union(S1, S2, S3, S4, {0}, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, a, b);

	return  rotate_case_3_1(tmp, c, d);
}

/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2_1(node a, node b, node c, node d)
	requires a::rb1<na, 0, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 0, bha, S3> * d::rb1<nd, 0, bha, S4> 
	ensures res::rb1<na+nb+nc+nd+3, 0, bha + 1, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0});


relation ROT3R(bag a, bag b, bag c, bag d).
node rotate_case_3r(node a, node b, node c)
  infer [ROT3R]
	requires a::rb1<na, 0, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 1, bha, S3>
	ensures res::rb1<na+nb+nc+2, 0, bha + 1, S4> & ROT3R(S4,S1,S2,S3);//S4 = union(S1, S2, S3, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, a, b);
	
	return new node(0, 0, tmp, c);
}

/* RIGHT */
/* rotation case 3 */
node rotate_case_3r_1(node a, node b, node c)
	requires a::rb1<na, 0, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 1, bha, S3>
	ensures res::rb1<na+nb+nc+2, 0, bha + 1, S4> & S4 = union(S1, S2, S3, {0}, {0});

relation ROT2R(bag a, bag b, bag c, bag d, bag e).
node case_2r(node a, node b, node c, node d)
  infer [ROT2R]
	requires a::rb1<na, 0, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 0, bha, S3> * d::rb1<nd, 0, bha, S4>
	ensures res::rb1<na+nb+nc+nd+3, 0, bha + 1, S5> & ROT2R(S5,S1,S2,S3,S4);//S5 = union(S1, S2, S3, S4, {0}, {0}, {0});

{
	node tmp;

	tmp = new node(0, 1, c, d);

	return rotate_case_3r_1(a, b, tmp);
}

/* rotation to transform case 2 in case 3, then apply case 3 */
node case_2r_1(node a, node b, node c, node d)
	
	requires a::rb1<na, 0, bha, S1> * b::rb1<nb, 0, bha, S2> * c::rb1<nc, 0, bha, S3> * d::rb1<nd, 0, bha, S4>
	ensures res::rb1<na+nb+nc+nd+3, 0, bha + 1, S5> & S5 = union(S1, S2, S3, S4, {0}, {0}, {0});

/* function to check if a node is red */
relation RED1(bag a, bag b).
relation RED2(bag a, bag b).
bool is_red(node x)
	infer [RED1,RED2]
	requires x::rb1<n, cl, bh, S>
	ensures x::rb1<n, cl, bh, S1> & cl = 1 & res & RED1(S1,S)
		or x::rb1<n, cl, bh, S2> & cl = 0 & !res & RED2(S2,S);

{

	if (x == null)
		return false; 
	else 
		if (x.color == 0) 
			return false;
		else
			return true;
}

/* function to check if a node is red */
bool is_red_1(node x)
	requires x::rb1<n, cl, bh, S>
	ensures x::rb1<n, cl, bh, S> & cl = 1 & res
		or x::rb1<n, cl, bh, S> & cl = 0 & !res;


/* function to check if a node is black */
relation BLACK1(bag a, bag b).
relation BLACK2(bag a, bag b).
bool is_black(node x)
	infer [BLACK1,BLACK2]
	requires x::rb1<n, cl, bh, S>
	ensures x::rb1<n, cl, bh, S1> & cl = 1 & !res & BLACK1(S1,S)
		or x::rb1<n, cl, bh, S2> & cl = 0 & res & BLACK2(S2,S);

{
	if (x == null)
		return true; 
	else
 
		if (x.color == 0) 
			return true;
		else
			return false;
}

/* function to check if a node is black */
bool is_black_1(node x)
	requires x::rb1<n, cl, bh, S>
	ensures x::rb1<n, cl, bh, S> & cl = 1 & !res
		or x::rb1<n, cl, bh, S> & cl = 0 & res;


