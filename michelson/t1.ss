data Storage {
	int value;
	int key;
}

data Money {
	int key;
	float amount;
}

data Transfer {
	int from_key;
	int to_key;
	float amount;
}

data Modify {
	int value;
	int key;
}

int update(Storage x, Modify r)
	requires x::Storage<value,key> * r::Modify<value2,key2> & key = key2
	ensures x::Storage<value2,key>;
	requires x::Storage<value,key> * r::Modify<value2,key2> & !(key = key2)
	ensures x::Storage<value,key>; 
{
	if (x.key == r.key){
		x.value = r.value;
	}
	return 0;
}
