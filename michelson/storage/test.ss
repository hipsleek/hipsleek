pred_prim Money<n:int> inv n >= 0;

data User {
	int key;
	Money wallet;
}

void identity(User u1)
	requires u1::User<k,w1> * w1::Money<n>
	ensures u1::User<k,w1> * w1::Money<n>;
{
	Money n = u1.wallet;
	dprint;
	return;
}
