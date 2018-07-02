data ACC {
	int key;
	Wallet wallet;
}

data wallet {
	int amount;
}
	
pred_prim Wallet<n:int>
	inv n >= 0;

lemma "split" self::Wallet<n> & a>=0 & b>=0 & n=a+b -> self::Wallet<a> * self::Wallet<b>;
lemma "combine" self::Wallet<a> * self::Wallet<b> -> self::Wallet<a+b>;

Wallet create_wallet(int n)
	requires true
	ensures res::Wallet<n>;

ACC create_user(int key)
	requires true
	ensures res::ACC<key,w> * w::Wallet<100>;
{
	Wallet w = create_wallet(100);
	return new ACC(key,w);
}

int balance(ref Wallet w)
	requires w::Wallet<n>
	ensures res = n;

void transfer(ref Wallet w1, ref Wallet w2, int amount)
	requires w1::Wallet<amount> * w2::Wallet<m>
	ensures w1'::Wallet<0> * w2'::Wallet<m+amount>;

void test()
	requires emp
	ensures emp;
{
	dprint;
	ACC w1 = create_user(1);
	ACC w2 = create_user(2);
	dprint;
	transfer(w1.wallet,w2.wallet,100); //I assume what we want is that here we split the wallet for w1 into amount and n-amount?
	dprint;
	return;
}
/*
ACC create_account() with %P
	requires true
	ensures res::User{%P}<> * res::Wallet<100>;

int balance(ACC a)
	requires a::User{%P}<>@L * a::Wallet<n>@L
	ensures res=n;

void transfer(ACC a, ACC b, int amount)
	requires a::Wallet<n> * b::Wallet<m>
	case {
		n >= amount -> ensures a::Wallet<n-amount> * b::Wallet<n+amount>;
		n < amount -> ensures a::Wallet<n> * b::Wallet<m>;
	}

void main()
	requires emp ensures emp;
{
	Ident a, b;
	int v;
	dprint;
	ACC acc_a = create_account() with a'::Ident<_>;
	ACC acc_b = create_account() with b'::Ident<_>;
	dprint;
	int bal = balance(acc_a);
	dprint;
	transfer(acc_b, acc_a, 10);
	bal = balance(acc_a);
	dprint;
}
*/
