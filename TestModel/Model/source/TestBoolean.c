typedef int bool;
#define true 1
#define false 0

/*@	requires bool_pre : b1 == \true || b1 == \false && b2 || !b2 ;
	assigns \nothing;
	ensures bool_post : \result == b1 && b2 || \result == b1 || b2 || \result == b1 ^^ b2 ;
*/
bool booleans(bool b1, bool b2, int option){
	switch(option){
	case 0 :
		return b1 && b2;
	case 1 :
		return b1 || b2;
	case 3 :
		return b1 ^ b2;
	default:
		return false;
	}
}
