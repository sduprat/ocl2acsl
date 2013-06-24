/*@	requires add_pre : a >= 0 && b > 0 ;
	assigns \nothing;
	ensures add_post : \result == a + b && b == \result - a ;
*/
int add(int a, int b) {
	return a + b;
}

/*@	assigns \nothing;
	ensures mult_post : (\result == a * b && \result / a == b) && (a * b) % a == 0 ;
*/
int mult(int a, int b) {
	return a * b;
}

/*@	assigns \nothing;
	ensures max_post : \result == \max(a, b) ;
*/
int max(int a, int b) {
	if (a >= b)
		return a;
	return b;
}

/*@	requires \valid(n);
	assigns *n;
	ensures zero_post : *n == 0 ;
*/
void zero(int *n) {
	*n = 0;
}
