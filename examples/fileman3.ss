/*
	Specifications: only shapes

	File Manager:
	- tree of folders (left child/right sibling)
	- each folder holds a list of files and a list of folders

	Operations:
	- Create folder/file
	- Remove folder/file
	- Move/copy file/folder

	There is always a non-null root folder.

	Calling these operations: 
	simulating user inputs by using functions that ensures true/no size
*/

data str {
}

bool streq(str s1, str s2)
	requires true ensures true;

// path entry
data pentry {
	str ent;
	pentry next;
}

path<> == self = null
	or self::pentry<next = r> * r::path<>;

data file {
	str name;

	file next;
}

data folder {
	str name;
	
	file files;

	folder child;
	folder sib;
}

flist<> == self = null
	or self::file<name = fl, next = r> 
		* r::flist<>;

ftree<> == self = null
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<>
		* chd::ftree<> * sb::ftree<>;

fseg<p> == self = p
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<>
		* chd::ftree<> * sb::fseg<p>;

lemma self::ftree<> <- self::fseg<x> * x::ftree<>;

/*
	Search for a name in a folder list by following the sib link.
*/
folder search_name(str name, folder flist)
	requires flist::ftree<>
	ensures flist::ftree<> & res = null
		or flist::fseg<res> * res::ftree<> & res != null;
{
	if (flist != null) {
		if (streq(flist.name, name)) {
			return flist;
		}
		else {
			folder tmp = search_name(name, flist.sib);
			return tmp;
		}
	}
	else {
		return null;
	}
}

/*
	Make a folder with path pa in the folder tree rooted at fldr.
*/
bool mkdir(folder fldr, pentry pa)
	requires fldr::ftree<> * pa::path<> & fldr != null
	ensures fldr::ftree<> * pa::path<>;
{
	bool ok = true;

	if (pa != null) {
		folder tmp = search_name(pa.ent, fldr.child);
		if (tmp != null) {
			ok = mkdir(tmp, pa.next);
			return ok;
		}
		else {
			// make a sub-folder as the left-most child
			tmp = new folder(pa.ent, null, null, fldr.child);
			fldr.child = tmp;
			ok = mkdir(tmp, pa.next);
			return ok;
		}
	}
	else {
		return ok;
	}
}
